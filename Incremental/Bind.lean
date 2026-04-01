import Std.Data.HashMap.Basic
import Std.Data.HashSet.Basic

abbrev NodeId := Nat

abbrev EdgeMap := Std.HashMap NodeId (List NodeId)

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
  | bind : NodeId → Option NodeId → (Float → γ × NodeId) → NodeTy γ

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
  | .bind a rhs _ => nodeStr ++
    s!"\n  {n.id} -> {a} [constraint=\"true\"]" ++
    if let some b := rhs then
      s!"\n  {n.id} -> {b} [constraint=\"true\"]"
    else ""

structure Graph where
  nodes : List (Node Graph)
  observers : Std.HashSet NodeId
  parents : EdgeMap
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
    ty := NodeTy.bind a none f
    label
    value := 0.0
    createdIn := g.currentScope
    height := 1 + g.nodes[a]!.height
    lastChangedAt := g.stabilizeId
    lastRecomputedAt := none }

  let newG := { g with nodes := g.nodes.concat newBind }
  (newG, newId)

/-- NOTE:
1. We can make this non-partial
2. Perf opportunities from building up a new EdgeMap from scratch vs mutating w/ one-reference
3. Initial EdgeMap is not initialized to parents' capacity, because abbrev's confound me
-/
partial def Graph.maintainParents (g : Graph) : Graph :=
  let addParent (parents : EdgeMap) (c : NodeId) (p : NodeId) : EdgeMap :=
    parents.alter c fun ps =>
      match ps with
      | none => some [p]
      | some ps => some (ps.concat p)

  let rec maintainParents (toVisit : List NodeId) (visited : List NodeId) (parents : EdgeMap) : EdgeMap :=
    match toVisit with
    | [] => parents
    | n :: remainingNodes =>
      if visited.contains n then
        panic! s!"Cycle detected to {n}"
      else
        let (children, newParents) := match g.nodes[n]!.ty with
        | .var => ([], parents)
        | .map a _ =>
          ([a], addParent parents a n)
        | .map2 a b _ =>
          ([a, b], addParent (addParent parents a n) b n)
        | .map3 a b c _ =>
          ([a, b, c], addParent (addParent (addParent parents a n) b n) c n)
        | .bind a rhs _ =>
          if let some b := rhs then
            ([a, b], addParent (addParent parents a n) b n)
          else
            ([a], addParent parents a n)

        let newToVisit := remainingNodes ++ children.filter (!remainingNodes.contains ·)
        maintainParents newToVisit (visited.concat n) newParents

  { g with parents := maintainParents g.observers.toList [] {} }

def Graph.observe (g : Graph) (n : NodeId) : Graph :=
  if !g.observers.contains n then
    { g with observers := g.observers.insert n }.maintainParents
  else g

def Graph.unobserve (g : Graph) (n : NodeId) : Graph :=
  if g.observers.contains n then
    { g with observers := g.observers.erase n }.maintainParents
  else g

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

  ⟨g, a, b, c, d, result⟩

def staticIfElse := makeStaticIfElse
#eval staticIfElse.g

def observingResult := staticIfElse.g.observe staticIfElse.result
#eval observingResult

def stopObservingResult := staticIfElse.g.unobserve staticIfElse.result
#eval stopObservingResult

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
#eval IO.println dynamicIfElse.g

end DynamicIfElseTest
