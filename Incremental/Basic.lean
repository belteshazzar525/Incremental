/-- What do I have right now?
1. You can construct a static graph from var and maps
2. Each time you modify the graph, you get back a new graph where all previous NodeIds are still valid and a newly valid NodeId
3. The way this implementation works right now, no NodeId created by a call to one of the builder functions will _ever_ be invalid. That seems okay at present because Nat is infinite, and the DAG is entirely static. You _can_ however create invalid graphs by using fake NodeId's as the parents in the builder functions. _However_, there is an easy check for a valid NodeId in a builder arg: if it is greater than the length of g.nodes! This points to an option or a proof in the builder APIs.
4. Every time you "modify" the graph, you get a new one. There are three kinds of modifications: 1) changing the structure of the graph; 2) changing the value of a var; and 3) stabilization. The incrementalism on input changes is still better than recomputing everything, but this will likely not be that fast because every input means a new Graph object. If the purpose of this is to build an executable spec with proofs, I should try to figure out what can I feasibly prove here that is relevant.

TODO:
1. Proof mechanism, either in the APIs or the data structure itself to ensure NodeId's are always valid
2. Bind

Question: why did I need the dirty count?
NOTES:
1. Lots of g.nodes[n]! calls. I would love to clean these up with proofs
2. topoOrder is a partial function. Remains to see how that matters. Good choice for a zulip q
3. Remaining FP in Lean is definitely still useful...
-/

abbrev NodeId := Nat

inductive NodeTy where
  | var
  | const
  | map : NodeId → (Float → Float) → NodeTy
  | map2 : NodeId → NodeId → (Float → Float → Float) → NodeTy
  -- | bind : NodeId → (Float → NodeId) → NodeTy

instance : ToString NodeTy where
  toString t := match t with
  | .var => "var"
  | .const => "const"
  | .map .. => "map"
  | .map2 .. => "map2"
  -- | .bind .. => "bind"

structure Node where
  id : NodeId
  ty : NodeTy
  val : Option Float
  parents : List NodeId

instance : Inhabited Node where
  default := ⟨0, NodeTy.const, none, []⟩

/-- Graphviz that just shows ID and type per node -/
def Node.toGraphviz (n : Node) : String :=
  s!"{n.id} [label=\"{n.id} ({n.ty})\", val=\"{n.val}\"]"

/-- Graphviz that shows ID, type, and value per node -/
def Node.toGraphvizVerbose (n : Node) : String :=
  s!"{n.id} [label=\"{n.id} ({n.ty}): {n.val}\", parents=\"{n.parents}\"]"

instance : BEq Node where
  beq a b := a.id == b.id

instance : ToString Node where
  toString n := s!"({n.id}, {n.ty}, {n.val}, {n.parents})"

structure InputChange where
  n: NodeId
  val: Float

structure Graph where
  nodes : List Node
  inputs : List NodeId
  dirtyInputs : List NodeId
  newInputVals : List Float

def Graph.new : Graph :=
  { nodes := [], inputs := [], dirtyInputs := [], newInputVals := [] }

instance : Inhabited Graph where
  default := Graph.new

instance : ToString Graph where
  toString g := s!"inputs = {g.inputs}\ndirtyInputs={g.dirtyInputs}\nnewInputVals={g.newInputVals}\nnodes = [\n  {"\n  ".intercalate (toString <$> g.nodes)}\n]"

/-- Graphviz that just shows ID and type per node -/
def Graph.toGraphviz (g : Graph) : String :=
  "digraph {\n  " ++
    "rankdir=\"BT\"\n  " ++
    "\n  ".intercalate (Node.toGraphviz <$> g.nodes) ++
    "\n  " ++
    "\n  ".intercalate ((fun u => "\n  ".intercalate ((fun v => s!"{u.id} -> {v}") <$> u.parents)) <$> g.nodes) ++
    "\n}"

/-- Graphviz that shows ID, type, and value per node -/
def Graph.toGraphvizVerbose (g : Graph) : String :=
  "digraph {\n  " ++
    "rankdir=\"BT\"\n  " ++
    "\n  ".intercalate (Node.toGraphvizVerbose <$> g.nodes) ++
    "\n  " ++
    "\n  ".intercalate ((fun u => "\n  ".intercalate ((fun v => s!"{u.id} -> {v}") <$> u.parents)) <$> g.nodes) ++
    "\n}"

abbrev Graph.numNodes (g : Graph) : Nat :=
  g.nodes.length

def Graph.var (g : Graph) (init : Float) : (Graph × NodeId) :=
  let newId := g.numNodes
  let newVar := { id := newId, ty := NodeTy.var, val := none, parents := [] }
  let newG := {
    nodes := g.nodes.concat newVar,
    inputs := g.inputs.concat newId,
    dirtyInputs := g.dirtyInputs.concat newId,
    newInputVals := g.newInputVals.concat init }

  (newG, newId)

def Graph.setVar (g : Graph) (v : NodeId) (val : Float) : Graph :=
  let dInIdx := g.dirtyInputs.idxOf v
  let newDirtyIn := if dInIdx == g.dirtyInputs.length
    then g.dirtyInputs.concat v
    else g.dirtyInputs

  let newNewInputVals := if dInIdx == g.newInputVals.length
    then g.newInputVals.concat val
    else g.newInputVals.set dInIdx val

  { g with dirtyInputs := newDirtyIn, newInputVals := newNewInputVals }

def Graph.map (g : Graph) (a : NodeId) (f : Float → Float) : (Graph × NodeId) :=
  let newId := g.numNodes
  let newMap := { id := newId, ty := NodeTy.map a f, val := none, parents := [] }

  let aNode := g.nodes[a]!
  let newA := { aNode with parents := aNode.parents.concat newId}

  let newG := { g with nodes := (g.nodes.replace aNode newA).concat newMap }
  (newG, newId)

def Graph.map2 (g : Graph) (a b : NodeId) (f : Float → Float → Float) : (Graph × NodeId) :=
  let newId := g.numNodes
  let newMap2 := { id := newId, ty := NodeTy.map2 a b f, val := none, parents := [] }

  let aNode := g.nodes[a]!
  let newA := { aNode with parents := aNode.parents.concat newId }

  let bNode := g.nodes[b]!
  let newB := { bNode with parents := bNode.parents.concat newId }

  let newG := { g with nodes := ((g.nodes.replace aNode newA).replace bNode newB).concat newMap2 }
  (newG, newId)

-- def Graph.bind (g : Graph) (a : NodeId) (f : Float → NodeId) : (Graph × NodeId) :=
--   let newId := g.numNodes
--   let newBind := { id := newId, ty := NodeTy.bind a f, val := none, parents := [] }

--   let aNode := g.nodes[a]!
--   let newA := { aNode with parents := aNode.parents.concat newId }

--   let newG := { g with nodes := (g.nodes.replace aNode newA).concat newBind }
--   (newG, newId)

namespace StabilizeHelpers

/--
Source: https://en.wikipedia.org/wiki/Topological_sorting#Depth-first_search
-/
partial def Graph.topoSort (g : Graph) : List NodeId :=
  let rec visit (n : NodeId) (permMarks tempMarks : List Bool) (sortedNodes : List NodeId) : (List Bool × List Bool × List NodeId) :=
    if permMarks[n]! then
      (permMarks, tempMarks, sortedNodes)
    else if tempMarks[n]! then
      panic! "Graph has at least one cycle"
    else
      let newTempMarks := tempMarks.set n true
      let rec innerLoop (ms : List NodeId) (permMarks tempMarks : List Bool) (sortedNodes : List NodeId) : (List Bool × List Bool × List NodeId) :=
        match ms with
        | [] => (permMarks, tempMarks, sortedNodes)
        | m :: ms' =>
          let (newPermMarks, newTempMarks, newSortedNodes) := visit m permMarks tempMarks sortedNodes
          innerLoop ms' newPermMarks newTempMarks newSortedNodes

      let (newPermMarks, newTempMarks, newSortedNodes) := innerLoop g.nodes[n]!.parents permMarks newTempMarks sortedNodes
      let newPermMarks := newPermMarks.set n true
      let newSortedNodes := n :: newSortedNodes
      (newPermMarks, newTempMarks, newSortedNodes)

  let rec outerLoop (permMarks tempMarks : List Bool) (sortedNodes : List NodeId) : List NodeId :=
    if permMarks.all id then
      sortedNodes
    else
      let n := permMarks.idxOf false
      let (newPermMarks, newTempMarks, newSortedNodes) := visit n permMarks tempMarks sortedNodes
      outerLoop newPermMarks newTempMarks newSortedNodes

  let initPermMarks := List.replicate g.numNodes false
  let initTempMarks := List.replicate g.numNodes false

  outerLoop initPermMarks initTempMarks []

inductive DirtyMark where
  | undirty
  | dirty : Nat → DirtyMark
deriving Inhabited

def DirtyMark.incr : DirtyMark → DirtyMark
  | undirty => dirty 1
  | dirty c => dirty (c + 1)

def DirtyMark.decr : DirtyMark → DirtyMark
  | undirty | dirty 0 => undirty
  | dirty c => dirty (c - 1)

def incrMarks (marks : List DirtyMark) (idxs : List NodeId) : List DirtyMark :=
  idxs.foldl (fun ms idx => ms.set idx ms[idx]!.incr) marks

def decrMarks (marks : List DirtyMark) (idxs : List NodeId) : List DirtyMark :=
  idxs.foldl (fun cs idx => cs.set idx (cs[idx]!.decr)) marks

def markDirtyInputs (dirtyIns : List NodeId) (marks : List DirtyMark) : List DirtyMark :=
    match dirtyIns with
    | [] => marks
    | dIn :: remainingDirtyIns => markDirtyInputs remainingDirtyIns (marks.set dIn (.dirty 0))

def markDirtyParents (g : Graph) (topoOrder : List NodeId) (marks : List DirtyMark) : List DirtyMark :=
    match topoOrder with
    | [] => marks
    | n :: remainingNodes =>
      match marks[n]! with
      | .undirty => markDirtyParents g remainingNodes marks
      | .dirty _ =>
        markDirtyParents g remainingNodes (incrMarks marks g.nodes[n]!.parents)

/-- NOTE: return val is a parallel array to g.nodes _not_ topoOrder! -/
def markDirtyNodes (g : Graph) (topoOrder : List Nat) : List DirtyMark :=
  let initMarks := List.replicate g.numNodes .undirty
  let inputsMarked := markDirtyInputs g.dirtyInputs initMarks
  markDirtyParents g topoOrder inputsMarked

def undirty (g : Graph) (n : NodeId) : Graph :=
  let node := g.nodes[n]!
  match node.ty with
  | .var =>
    -- 1. Set g.nodes[n].val to the value from newInputVars
    -- 2. Remove n from dirtyInputs and the parallel entry in newInputVars
    let dInIdx := g.dirtyInputs.idxOf n
    let newVal := g.newInputVals[dInIdx]!
    let newNode := { node with val := some newVal }

    { g with
      nodes := g.nodes.replace node newNode
      dirtyInputs := g.dirtyInputs.eraseIdx dInIdx
      newInputVals := g.newInputVals.eraseIdx dInIdx }
  | .map a f =>
    let aVal := g.nodes[a]!.val.get!
    let newVal := f aVal
    let newNode := { node with val := some newVal }

    { g with nodes := g.nodes.replace node newNode }
  | .map2 a b f =>
    let aVal := g.nodes[a]!.val.get!
    let bVal := g.nodes[b]!.val.get!
    let newVal := f aVal bVal
    let newNode := { node with val := some newVal }

    { g with nodes := g.nodes.replace node newNode }
  -- | .bind a f =>
  --   -- 1. Get the value of Node a
  --   -- 2. Call f which can create a new graph and NodeId.
  --   -- f would create the new graph via the builder apis: map, map2, and bind
  --   -- Those would guarantee that dirtyInputs/newInputVals are updated
  --   -- TODO
  --   g
  | .const => panic! s!"unreachable: {node}"

def recompute (g : Graph) (topoOrder : List NodeId) (dirtyMarks : List DirtyMark) : Graph :=
  match topoOrder with
  | [] => g
  | n :: remainingNodes =>
    match dirtyMarks[n]! with
    | .undirty => recompute g remainingNodes dirtyMarks
    | .dirty 0 =>
      let newG := undirty g n
      let newDirtyMarks := decrMarks dirtyMarks (n :: g.nodes[n]!.parents)
      recompute newG remainingNodes newDirtyMarks
    | .dirty c => panic! s!"unreachable: n = {n}, c = {c}"

end StabilizeHelpers

open StabilizeHelpers in
def Graph.stabilize (g : Graph) : Graph :=
  let topoOrder := g.topoSort
  -- First pass
  let dirtyMarks := markDirtyNodes g topoOrder
  -- Second pass
  recompute g topoOrder dirtyMarks

--- Map, Map2, and (TODO) Bind example
structure HelloGraph where
  g: Graph
  a: NodeId
  b: NodeId
  c: NodeId
  d: NodeId

def testHelloGraph : HelloGraph :=
  let g := Graph.new
  let (g, a) := g.var 1.0
  let (g, b) := g.var 3.0
  let (g, c) := g.var 4.0

  let (g, a_is_even) := g.map a fun x => if x.toInt64 % 2 == 0 then 1.0 else 0.0
  let (g, b_plus_c) := g.map2 b c fun x y => x + y

  let (g, d) := g.map2 a_is_even b_plus_c fun x y => x * y

  ⟨g, a, b, c, d⟩

def hello := testHelloGraph

#eval hello.g
#eval IO.println hello.g.toGraphviz
#eval IO.println hello.g.toGraphvizVerbose

open StabilizeHelpers in
#eval hello.g.topoSort

def g1 := hello.g.stabilize
#eval g1
#eval IO.println g1.toGraphviz
#eval IO.println g1.toGraphvizVerbose

def g2 := g1.setVar hello.a 2.0
#eval g2
#eval IO.println g2.toGraphviz
#eval IO.println g2.toGraphvizVerbose

def g3 := g2.stabilize
#eval g3
#eval IO.println g3.toGraphviz
#eval IO.println g3.toGraphvizVerbose

-- TODO: make it bad again!
def testBadGraph (g : Graph) (a : Float) : (Graph × NodeId) :=
  let (g, a) := g.var a
  let (g, b) := g.map a (· + 1)
  (g, b)

def badG := testBadGraph Graph.new 1.0
#eval badG.fst
#eval IO.println badG.fst.toGraphviz
