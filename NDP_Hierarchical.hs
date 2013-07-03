{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- A place to explore some early ideas about nested data parallelism on
-- hierarchical architectures.
--------------------------------------------------------------------------------

module NDP_Hierarchical where

import Data.Map as M
import Prelude as P
import Text.PrettyPrint.GenericPretty (Out(doc,docPrec), Generic)
import System.Random as R

----------------------------------------------------           
-- Example machine hierarchies:
----------------------------------------------------

quadcpu :: Level
quadcpu = Level "socket" static
          [Level "core" [Sync PtToPt, Bounded 4] []]
  -- OR:
          -- [ Level "core1" static []
          -- , Level "core2" static []
          -- , Level "core3" static []
          -- , Level "core4" static [] ]

-- | A GPU model.  This description mixes static entities (HW) with dynamic entities
-- (with HW scheduling support) such as kernels, grids, and blocks.
gpu :: Level
gpu = Level "gpu" static
      [Level "kernel" [Sync NoSync] -- Unlimited DAG of kernels.
                                    -- No sync between code inside different kernels.
       [Level "block" [Sync NoSync, Bounded$ 65535 * 65535 * 65535]
        [Level "thread" [Sync Barrier, Bounded 1024] []]]]
        -- Barriers allowed between threads within the same block.

-- | A complete machine could have a CPU and GPU.
machine :: Level
machine =
  Level "machine" static [ quadcpu, gpu ]

static :: [LevelProp]
static = [Bounded 1]

-- Note that these examples do not currently model the separate sequential steps
-- within a thread or a core.  Some tilings or static schedulings would need to refer
-- to those explicitly.

-- Example mappings:
--------------------

ex1 = OpTree FOLD () [leaf MAP, leaf FOLD]

mp1 = domap gpu     ex1
mp2 = domap machine ex1

domap mach ex = do
  g <- getStdGen
  let (mp,g') = randomMapping mach ex g
  setStdGen g'
  return mp  

--------------------------------------------------------------------------------
-- Machine description Schemas
--------------------------------------------------------------------------------  

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
  | Sync SyncCapability
  | MemModel  -- FinishMe
  | CostModel -- FinishMe
    -- TODO: topology: DAG, sequence, etc
  deriving (Eq, Show, Read, Ord, Generic)
-- TODO: probably need to distinguish which levels can do work independently, if any
-- non-leaf levels can....


-- | A qualitative description of the synchronization capabalities of a piece of
-- hardware.  Obviously, a barrier could be implemented with PtToPt, but that would
-- be expensive.
data SyncCapability = NoSync -- ^ Separate tasks in the parallel region may not sync.
                    | PtToPt -- ^ Separate tasks may sync on a pairwise point-to-point basis.
                    | Barrier -- ^ Separate threads/tasks may partake in a global barrier across the parallel region.
  deriving (Eq, Show, Read, Ord, Generic)
  -- TODO: add costs.  For example, on the GPU, within a warp barriers are free,
  -- whereas __syncthreads within a block is not.

--------------------------------------------------------------------------------
-- Fine grained dataflow-graph topology constraints
--------------------------------------------------------------------------------
-- This part is very speculative.

-- | Graphs of aggregate operators are coarse-grained, but induce fine-grained task
-- graphs at runtime.  These constraints describe the topology of those fine-grained
-- graphs.
--
-- A far-out goal would be to be able to infer costs from the combination of these
-- constraints and the cost models associated with machines (and their memory
-- hierarchies).
data Constraint = Exists (Var -> Constraint)
                | ForAll (Var -> Constraint)
                | And Constraint Constraint
                | Or  Constraint Constraint
                | Not Constraint  
                | Eql Operand Operand
                | Leq Operand Operand

data Operand = Task Var
             | Var  Var 
             | ArrElem Var Var

-- | Simply names for now:
type Var = String

-- | The properties of an aggregate operator:
data OpProp = Ordering Constraint
            | NeedsSync SyncCapability

data Op = MAP | FOLD | SCAN
  deriving (Eq, Show, Read, Ord, Generic)
-- permute, backpermute, replicate, generate etc etc

opTable :: Map Op [OpProp]
opTable = M.fromList $
  [ (FOLD, [ NeedsSync PtToPt,
             Ordering (fc "arr")]) -- Need the name of the input array.
  -- TODO: SCAN, MAP, etc
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
-- Random mapping of operators onto machine levels
--------------------------------------------------------------------------------

-- A mapping with of a linearly [n] nested task on a linear [d] hierarchy is
-- straightforward (requires only computing (n+d) choose n).  It's
-- much more complicated to count the possibilities when both are trees.

-- | This datatype is not a complete program, but an (easily extracted) simple
-- abstraction of the nested structure of an NDP program: namely, which operators
-- contain nested sub-operators.
-- 
-- The effect of traditional (NESL-style) NDP flattening transformations is to lift
-- out and flatten all nested operations which would result in none of these OpTree's
-- having any children.
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
  
--------------------------------------------------------------------------------
-- Codegen interfaces:
--------------------------------------------------------------------------------

-- The idea is that each level exposes various common concepts (parallel loops,
-- sequential loops) as well as metadata/properties.

-- Directly invoking codegen tactics at higher levels of abstraction means foregoing
-- control.  It must always be possible, however, to allow randomly generated
-- mappings to succeed.

-- Case in Point: FOLD
----------------------

-- The metadata for the fold operator should make clear how many tasks it generates,
-- their valid topologies, and the sync requirements.

-- The code generator for the fold operator should deal with the level it is assigned
-- by inspecting its metadata and then invoking its methods to generate parallel or
-- sequential loops.

-- For example, a common implementation is to have a fold execute as a "block" on the
-- GPU, enabling barrier synchronization.  The topology selected is not a binary
-- tree, rather it's several "straight lines" merging into a binary tree at the end.
-- That is, the first phase is for N threads to independently reduce N chunks of
-- contiguous (or interleaved) elements in the source.  The second phase is the
-- binary tree: progressively fewer threads (N/2, N/4) to reduce individual pairs of
-- elements, with barriers inbetween until there is only one left.

-- (This separation of phases could be reified explicitly by transforming the program
--  from "fold f arr" into "fold f (map (fold f) (split N arr))".)

-- So a typical codegen for fold looks like a single kernel launching a single
-- (large) block that first performs a sequential loop and then performs the
-- alternating barriers and single reductions (with conditionals that cause half the
-- threads to drop out at each level).

-- IF Fold is assigned a high level in the hierarchy, for example bridging multiple
-- devices.  Some kind of fissioning of the workload must occur, which perhaps could
-- happen via explicit program rewritting followed by patching up the mapping.

-- IF Fold is mapped to a leaf thread, then it must generate a single sequential loop.
    
-- IF fold is mapped to a level with parallelism but no synchronization between its
-- children, then it is again forced to fission.  It can do the communication-free
-- partial reduction in parallel, but the final summing of intermediate results must
-- happen at a later point either sequentially or in parallel (with synchronization).
-- This later phase can be anywhere above or below the current level, for example in
-- a separate kernel after the current one (implicit kernel-level barriers), or on
-- the CPU host rather than the GPU.

-- [NOTE: the above, simple machine hierarchies need to do more to model the
-- synchronization that goes on between the GPU and CPU.]

--------------------------------------------------------------------------------
-- Misc utilities and boilerplate
--------------------------------------------------------------------------------  

-- TODO: switch this to pretty printing:
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
instance Out SyncCapability
instance Out Op
instance Out a => Out (OpTree a)

