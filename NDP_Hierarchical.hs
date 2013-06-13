{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- A place to explore some early ideas about nested data parallelism on
-- hierarchical architectures.
--------------------------------------------------------------------------------

import Data.Map as M
import Prelude as P
import Text.PrettyPrint.GenericPretty (Out(doc,docPrec), Generic)
import System.Random as R

----------------------------------------------------           
-- Example machine hierarchies:
----------------------------------------------------

quadcpu :: Level
quadcpu = Level "socket" static
          [ Level "core1" static []
          , Level "core2" static []
          , Level "core3" static []
          , Level "core4" static [] ]

-- | A GPU model.  This description mixes static entities (HW) with dynamic entities
-- (with HW scheduling support) such as kernels, grids, and blocks.
gpu :: Level
gpu = Level "gpu" static
      [Level "kernel" [] -- Unlimited DAG of kernels.
       [Level "block" [Bounded$ 65535 * 65535 * 65535]
        [Level "thread" [Bounded 1024] []]]]

-- | A complete machine could have a CPU and GPU.
machine :: Level
machine =
  Level "machine" static [ quadcpu, gpu ]

static :: [LevelProp]
static = [Bounded 1]

-- Note that these examples do not currently model the separate sequential steps
-- within a thread or a core.  Some tilings or static schedulings would need to refer
-- to those explicitly.

------------------------------------------------------------

-- | A level of a hierarchical machine:
data Level =
  Level
  { name :: String
  , props :: [LevelProp]  
  , children :: [Level]
  }
  deriving (Eq, Show, Read, Ord, Generic)

-- | The properties of one level of a machine hierarchy.
data LevelProp =
    Bounded Int -- | Max number of entities at this level.  For now they have no
                -- particular topology; only a cardinatality.
  | MemModel  -- FinishMe
  | CostModel -- FinishMe
  deriving (Eq, Show, Read, Ord, Generic)

-- TODO: probably need to distinguish which levels can do work independently, if any
-- non-leaf levels can....

--------------------------------------------------------------------------------
-- Fine grained dataflow-graph topology constraints
--------------------------------------------------------------------------------

data Constraint = Exists (Var -> Constraint)
                | ForAll (Var -> Constraint)
                | And Constraint Constraint
                | Or  Constraint Constraint
                | Not Constraint  
                | Eql Operand Operand
                | Leq Operand Operand

-- | 
data Operand = Task Var
             | Var  Var 
             | ArrElem Var Var

-- | Simply names for now:
type Var = String

-- | The properties of an aggregate operator:
data OpProps = Ordering Constraint

data Op = MAP | FOLD | SCAN
  deriving (Eq, Show, Read, Ord, Generic)
-- permute, backpermute, replicate, generate etc etc

opTable :: Map Op OpProps
opTable = M.fromList $
  [ (FOLD, Ordering (fc "arr")) -- Need the name of the input array.
  ]

-- | The fine grained ordering constrainst for a Fold dataflow graph.  Note that fold
-- is very flexible; it is not constrained to a single topology.
--
-- What this says is that for all tasks created by the fold there exist two upstream
-- dependencies for that task (two inputs), each of which may either be an array
-- element, or the intermediate result produced by another task.
-- 
-- NOTE: This ASSUMES that the tasks are indexed by a disjoint set of keys (numbers) than
-- the array subscripts.  Otherwise the Not.Eql bit below is wrong.
fc :: Var -> Constraint
fc arr = -- Exists $ \ arr ->
     ForAll $ \ i -> -- This is really limited to the scope of the fold's tasks.
     Exists $ \ j ->
     Exists $ \ k ->
     Not (Var j `Eql` Var k)       `And`
     ((ArrElem arr j `Leq` Task i) `Or`
      (Task j `Leq` Task i))       `And`
     ((ArrElem arr k `Leq` Task i) `Or`
      (Task k `Leq` Task i))       

--------------------------------------------------------------------------------
-- Random mappings
--------------------------------------------------------------------------------

-- A mapping with of a linearly [n] nested task on a linear [d] hierarchy is
-- straightforward (requires only computing a random subset of n+d positions).  It's
-- much more complicated when both are trees.

data OpTree a = OpTree Op a [OpTree a]
  deriving (Eq, Show, Read, Ord, Generic)
  -- Note: this doesn't really account for operations with multiple lambda arguments
  -- that could independently contain nested parallel computations....

leaf a = OpTree a () []

-- | An OpTree where every Op has been assigned the name of a Level
type MappedTree = OpTree String

-- | Create a random "Natural" (descending) mapping between nested ops and levels of
-- a machine hierarchy.
randomMapping :: RandomGen g => Level -> OpTree a -> g -> (MappedTree, g)
randomMapping mach optree gen = testAndDiscardLoop gen
  -- TODO: first, simplest implementation.  Randomly assign ops to levels and then
  -- see if it is a "natural" (descending) mapping.
  where
    allLvls (Level str _ chldrn) = str : concatMap allLvls chldrn
    lvlList = allLvls mach
    numLvls = length lvlList

    decorate :: [String] -> OpTree a -> OpTree String
    decorate supply op = head $ fst $ decorLst supply [op]
    decorLst rands [] = ([],rands)
    decorLst (target:rst) (OpTree op _ ls : moreops) =
      let (ls',      rst')  = decorLst rst ls
          (moreops', rst'') = decorLst rst' moreops in
      (OpTree op target ls' : moreops', rst'')
    decorLst [] _ = error "impossible"
    
    testAndDiscardLoop g =
      let (g1,g2)   = R.split g
          randLvls  = P.map (lvlList!!) $ randomRs (0,numLvls-1) g1
          candidate = decorate randLvls optree
      in if verifyOrdered candidate (makeLEQ mach)
         then (candidate,g2)
         else testAndDiscardLoop g2

-- | Returns a less-than-or-equal op to capture the depth partial order in a machine
-- hierarchy.  (Root is "least".)
--
-- Really a data structure should be used to cache the transitive closure of this
-- relation.  `makeLEQ` is just a naive implementation that traverses the whole tree
-- on each test.
makeLEQ mach left right
  | left == right = True
  | otherwise     = loop mach
  where
    loop (Level name _ chlds)
        | name == left  = any (contains right) chlds
        | name == right = False
        | otherwise     = any loop chlds
    contains name (Level str _ chldrn)
      | name == str = True
      | otherwise   = any (contains name) chldrn

-- | Assumes that the LEQ op is a valid partial order.  Thus this only checks
-- child/parent neighbors in the tree.
verifyOrdered (OpTree _ tag ls) leq =
    all (loop tag) ls
  where
    loop last (OpTree _ trg chldrn)
      | last `leq` trg = all (loop trg) chldrn
      | otherwise      = False

ex1 = OpTree FOLD () [leaf MAP, leaf FOLD]

mp1 = domap gpu     ex1
mp2 = domap machine ex1

domap mach ex = do
  g <- getStdGen
  let (mp,g') = randomMapping mach ex g
  setStdGen g'
  return mp  
  
--------------------------------------------------------------------------------
-- Codegen interfaces:
--------------------------------------------------------------------------------

-- Each level exposes various common concepts (parallel loops, sequential loops) as
-- well as metadata/properties.

-- Directly invoking codegen tactics at higher levels of abstraction means foregoing
-- control.  It must always be possible, however, to allow randomly generated
-- mappings to succeed.


--------------------------------------------------------------------------------

instance Show Constraint where
  show x = fst (loop x nameSupply)
   where
     nameSupply = P.map (("i"++) . show) [0..]
     parens x = "("++ x ++ ")"
     loop _ [] = error "not possible"
     loop x ns@(vr:rst) =
       let binop op c1 c2 =
             let (c1',ns')  = loop c1 ns 
                 (c2',ns'') = loop c2 ns' in
             (parens (c1' ++" "++op++" "++ c2'), ns'')
       in
       case x of
         Exists fn -> let (str,ns') = loop (fn vr) rst in
                      ("Exists "++vr++" . "++parens str, ns')
         ForAll fn -> let (str,ns') = loop (fn vr) rst in
                      ("ForAll "++vr++" . "++parens str, ns') 
         Not c1 -> let (str,ns') = loop c1 rst in
                   ("!"++ parens str, ns')
         Eql v1 v2 -> (show v1 ++ " == " ++ show v2, ns)
         Leq v1 v2 -> (show v1 ++ " <= " ++ show v2, ns)
         And c1 c2 -> binop "&&" c1 c2
         Or  c1 c2 -> binop "||" c1 c2

instance Show Operand where
  show (Task i) = i
  show (Var i)  = i
  show (ArrElem a i) = a ++ "["++i++"]"

instance Out Level
instance Out LevelProp
instance Out Op
instance Out a => Out (OpTree a)

-- A random set of K numbers between 0 and N-1
-- randKofN k n = 
