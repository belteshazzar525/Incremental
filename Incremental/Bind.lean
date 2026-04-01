import Std.Data.HashMap.Basic
import Std.Data.HashSet.Basic

abbrev NodeId := Nat

abbrev StabilizeId := Nat

inductive Scope where
  | top
  | bind : NodeId → Scope

instance : ToString Scope where
  toString s := match s with
  | .top => "Top"
  | .bind n => s!"Bind {n}"

inductive NodeTy γ where
  | var
  -- | const
  | map : NodeId → (Float → Float) → NodeTy γ
  | map2 : NodeId → NodeId → (Float → Float → Float) → NodeTy γ
  | map3 : NodeId → NodeId → NodeId → (Float → Float → Float → Float) → NodeTy γ
  | bind : NodeId → (Float → γ × NodeId) → NodeTy γ

instance : ToString (NodeTy γ) where
  toString t := match t with
  | .var => "var"
  -- | .const => "const"
  | .map .. => "map"
  | .map2 .. => "map2"
  | .map3 .. => "map3"
  | .bind .. => "bind"

structure Node γ where
  id : NodeId
  ty : NodeTy γ
  label : String
  value : Float
  createdIn : Scope
  height : Nat
  lastChangedAt : StabilizeId
  lastRecomputedAt : Option StabilizeId

instance : Inhabited (Node γ) where
  default := ⟨0, NodeTy.var, "", 0.0, Scope.top, 0, 0, none⟩

instance : BEq (Node γ) where
  beq a b := a.id == b.id

def Node.toGraphviz (n : Node γ) : String :=
  let nodeStr := s!"{n.id} [label=\"{if n.label.isEmpty then "" else n.label ++ "\n"}({n.id}, {n.ty}, {n.createdIn}): {n.value}\n[height={n.height}, lastChangedAt={n.lastChangedAt}, lastRecomputedAt={n.lastRecomputedAt}]\"]"
  match n.ty with
  | .var => nodeStr
  | .map a _ => nodeStr ++ s!"\n  {n.id} -> {a} [constraint=\"true\"]"
  | .map2 a b _ => nodeStr ++ s!"\n  {n.id} -> {a} [constraint=\"true\"]\n  {n.id} -> {b} [constraint=\"true\"]"
  | .map3 a b c _ => nodeStr ++ s!"\n  {n.id} -> {a} [constraint=\"true\"]\n  {n.id} -> {b} [constraint=\"true\"]\n  {n.id} -> {c} [constraint=\"true\"]"
  | .bind a _ => nodeStr ++ s!"\n  {n.id} -> {a} [constraint=\"true\"]"

structure Graph where
  nodes : List (Node Graph)
  observers : Std.HashSet NodeId
  parents : Std.HashMap NodeId (List NodeId)
  varChanges : Std.HashMap NodeId Float
  stabilizeId : StabilizeId
  currentScope : Scope

def Graph.new : Graph :=
  ⟨[], {}, {}, {}, 0, .top⟩

instance : Inhabited Graph where
  default := Graph.new

def Graph.toGraphviz (g : Graph) : String :=
  "digraph {\n  " ++
  "\n  ".intercalate (Node.toGraphviz <$> g.nodes) ++
  "\n  " ++
  "\n  ".intercalate (g.parents.toList.flatMap fun (n, ps) =>
    ((s!"{n} -> {·} [color=\"red\", constraint=\"false\"]") <$> ps)) ++
  "\n}"

instance : ToString Graph where
  toString g := "\n".intercalate [
    s!"observers={g.observers.toList}",
    s!"varChanges={g.varChanges.toList}",
    s!"stabilizeId={g.stabilizeId}",
    s!"currentScope={g.currentScope}",
    s!"{g.toGraphviz}"]

abbrev Graph.numNodes (g : Graph) : Nat :=
  g.nodes.length

abbrev GraphChange := Graph × NodeId

def Graph.var (g : Graph) (init : Float) (label : String := "") : GraphChange :=
  let newId := g.numNodes
  let newVar := {
    id := newId
    ty := NodeTy.var
    label
    value := 0.0
    createdIn := g.currentScope
    height := 0
    lastChangedAt := g.stabilizeId
    lastRecomputedAt := none }

  let newG := { g with
    nodes := g.nodes.concat newVar
    varChanges := g.varChanges.insert newId init }

  (newG, newId)

def Graph.map (g : Graph) (a : NodeId) (f : Float → Float) (label : String := "") : GraphChange :=
  let newId := g.numNodes
  let newMap := {
    id := newId
    ty := NodeTy.map a f
    label
    value := 0.0
    createdIn := g.currentScope
    height := 1 + g.nodes[a]!.height
    lastChangedAt := g.stabilizeId
    lastRecomputedAt := none }

  let newG := { g with nodes := g.nodes.concat newMap }

  (newG, newId)

def Graph.map2 (g : Graph) (a b : NodeId) (f : Float → Float → Float) (label : String := "") : GraphChange :=
  let newId := g.numNodes
  let newMap2 := {
    id := newId
    ty := NodeTy.map2 a b f
    label
    value := 0.0
    createdIn := g.currentScope
    height := 1 + max g.nodes[a]!.height g.nodes[b]!.height
    lastChangedAt := g.stabilizeId
    lastRecomputedAt := none }

  let newG := { g with nodes := g.nodes.concat newMap2 }

  (newG, newId)

def Graph.map3 (g : Graph) (a b c : NodeId) (f : Float → Float → Float → Float) (label : String := "") : GraphChange :=
  let newId := g.numNodes
  let newMap3 := {
    id := newId
    ty := NodeTy.map3 a b c f
    label
    value := 0.0
    createdIn := g.currentScope
    height := 1 + max g.nodes[a]!.height (max g.nodes[b]!.height g.nodes[c]!.height)
    lastChangedAt := g.stabilizeId
    lastRecomputedAt := none }

  let newG := { g with nodes := g.nodes.concat newMap3 }

  (newG, newId)

def Graph.bind (g : Graph) (a : NodeId) (f : Float → GraphChange) (label : String := "") : GraphChange :=
  let newId := g.numNodes
  let newBind := {
    id := newId
    ty := NodeTy.bind a f
    label
    value := 0.0
    createdIn := g.currentScope
    height := 1 + g.nodes[a]!.height
    lastChangedAt := g.stabilizeId
    lastRecomputedAt := none }

  let newG := { g with nodes := g.nodes.concat newBind }
  (newG, newId)

def Graph.setVar (g : Graph) (v : NodeId) (value : Float) : Graph :=
  { g with varChanges := g.varChanges.insert v value }

namespace StaticIfElseTest

structure StaticIfElse where
  g : Graph
  a : NodeId
  b : NodeId
  c : NodeId
  d : NodeId
  result : NodeId

def makeStaticIfElse : StaticIfElse :=
  let g := Graph.new
  let (g, a) := g.var 1.0 "a"
  let (g, b) := g.var 2.0 "b"
  let (g, c) := g.var 3.0 "c"
  let (g, d) := g.var 4.0 "d"

  let (g, cond) := g.map a (fun x =>
    if x.toInt64 % 2 == 0 then 1.0 else 0.0)
    "cond"

  let (g, ifBranch) := g.map2 b c (fun x y =>
    x + y)
    "branch:cond=true"

  let (g, elseBranch) := g.map2 b d (fun x y =>
    x + y)
    "branch:cond=false"

  let (g, result) := g.map3 cond ifBranch elseBranch (fun x y z =>
    if x == 1.0 then y else z)
    "result"

  -- PICKUP: make necessary and parents happen
  let necessaryParents: Std.HashMap NodeId (List NodeId) := {
    (a, [cond]),
    (b, [ifBranch, elseBranch]),
    (c, [ifBranch]),
    (d, [elseBranch]),
    (cond, [result]),
    (ifBranch, [result]),
    (elseBranch, [result])
  }
  let g := { g with parents := necessaryParents }

  ⟨g, a, b, c, d, result⟩

def staticIfElse := makeStaticIfElse
-- #eval staticIfElse.g.stabilizeState.recomputeHeap
#eval IO.println staticIfElse.g

end StaticIfElseTest

namespace DynamicIfElseTest

structure DynamicIfElse where
  g : Graph
  a : NodeId
  b : NodeId
  c : NodeId
  d : NodeId
  result : NodeId

def makeDynamicIfElse : DynamicIfElse :=
  let g := Graph.new
  let (g, a) := g.var 0.0
  let (g, b) := g.var 2.0
  let (g, c) := g.var 3.0
  let (g, d) := g.var 4.0

  let (g, cond) := g.map a (fun x =>
    if x.toInt64 % 2 == 0 then 1.0 else 0.0)
    "cond"

  let (g, result) := g.bind cond (fun cond =>
    if cond == 1.0 then
      g.map2 b c fun x y =>
        x + y
    else
      g.map2 b d fun x y =>
        x + y)
    "result"

  ⟨g, a, b, c, d, result⟩

def dynamicIfElse := makeDynamicIfElse
#eval IO.println dynamicIfElse.g.toGraphviz

end DynamicIfElseTest
