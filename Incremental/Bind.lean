import Std.Data.HashMap.Basic
import Std.Data.HashSet.Basic
import Batteries.Data.BinaryHeap

abbrev NodeId := Nat

abbrev EdgeMap := Std.HashMap NodeId (List NodeId)

abbrev StabilizeId := Nat

inductive Scope where
  | top
  | bind : NodeId → Scope
deriving BEq, Hashable

instance : ToString Scope where
  toString s := match s with
  | .top => "Top"
  | .bind n => s!"Bind {n}"

inductive NodeTy where
  | var : (val : Option Float) → NodeTy
  | map : (val : Option Float) → NodeId → (Float → Float) → NodeTy
  | map2 : (val : Option Float) → NodeId → NodeId → (Float → Float → Float) → NodeTy
  | map3 : (val : Option Float) → NodeId → NodeId → NodeId → (Float → Float → Float → Float) → NodeTy
  | bind : (val : Option NodeId) → (a : NodeId) → NodeTy
  | bindResult : (val : Option Float) → (lhs : NodeId) → (rhs : Option NodeId) → NodeTy

instance : ToString NodeTy where
  toString t := match t with
  | .var v => s!"({v} : var)"
  | .map v .. => s!"({v} : map)"
  | .map2 v .. => s!"({v} : map2)"
  | .map3 v .. => s!"({v} : map3)"
  | .bind v .. => s!"({v} : bind)"
  | .bindResult v .. => s!"({v} : bindResult)"

structure Node where
  id : NodeId
  ty : NodeTy
  label : String
  createdIn : Scope
  height : Nat
  lastChangedAt : StabilizeId
  lastRecomputedAt : Option StabilizeId

instance : Inhabited Node where
  default := ⟨0, .var none, "", Scope.top, 0, 0, none⟩

instance : BEq Node where
  beq a b := a.id == b.id

def Node.toGraphviz (n : Node) : String :=
  let nodeStr := fun ty val =>
    s!"{n.id} [label=\"{if n.label.isEmpty then "" else n.label ++ "\n"}({n.id}, {ty}, {n.createdIn}): {val}\n[height={n.height}, lastChangedAt={n.lastChangedAt}, lastRecomputedAt={(n.lastRecomputedAt.map toString).getD "none"}]\"]"
  match n.ty with
  | .var v => nodeStr "var" s!"{v}"
  | .map v a _ => nodeStr "map" s!"{v}"
    ++ s!"\n  {n.id} -> {a} [constraint=\"true\"]"
  | .map2 v a b _ => nodeStr "map2" s!"{v}"
    ++ s!"\n  {n.id} -> {a} [constraint=\"true\"]\n  {n.id} -> {b} [constraint=\"true\"]"
  | .map3 v a b c _ => nodeStr "map3" s!"{v}"
    ++ s!"\n  {n.id} -> {a} [constraint=\"true\"]\n  {n.id} -> {b} [constraint=\"true\"]\n  {n.id} -> {c} [constraint=\"true\"]"
  | .bind v a => nodeStr "bind" s!"{v}"
    ++ s!"\n  {n.id} -> {a} [constraint=\"true\"]"
  | .bindResult v lhs rhs => nodeStr "bindResult" s!"{v}"
    ++ s!"\n  {n.id} -> {lhs} [constraint=\"true\"]"
    ++ if let some rhs := rhs then
      s!"\n  {n.id} -> {rhs} [constraint=\"true\"]"
      else ""

def Node.floatVal! (n : Node) : Float :=
  match n.ty with
  | .var v => v.get!
  | .map v .. => v.get!
  | .map2 v .. => v.get!
  | .map3 v .. => v.get!
  | .bindResult v .. => v.get!
  | .bind .. => panic! "cannot get float val out of a bind"

def Node.floatVal? (n : Node) : Option Float :=
  match n.ty with
  | .var v => v
  | .map v .. => v
  | .map2 v .. => v
  | .map3 v .. => v
  | .bindResult v .. => v
  | .bind .. => none

def Node.ptrVal! (n : Node) : NodeId :=
  match n.ty with
  | .bind v .. => v.get!
  | _ => panic! s!"cannot get ptr val out of type {n.ty}"

def Node.ptrVal? (n : Node) : Option NodeId :=
  match n.ty with
  | .bind v .. => v
  | _ => none

structure Graph where
  nodes : List Node
  observers : Std.HashSet NodeId
  parents : EdgeMap
  varChanges : Std.HashMap NodeId Float
  stabilizeId : StabilizeId
  currentScope : Scope
  scopes : Std.HashMap Scope (List NodeId)

abbrev GraphChange := Graph × NodeId

abbrev BindGenerators := Std.HashMap NodeId (Graph → Float → GraphChange)

def Graph.new : Graph :=
  ⟨[], {}, {}, {}, 0, .top, {}⟩

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
        | .var _ => ([], parents)
        | .map _ a _ =>
          ([a], addParent parents a n)
        | .map2 _ a b _ =>
          ([a, b], addParent (addParent parents a n) b n)
        | .map3 _ a b c _ =>
          ([a, b, c], addParent (addParent (addParent parents a n) b n) c n)
        | .bind _ a =>
          ([a], addParent parents a n)
        | .bindResult _ lhs rhs =>
          if let some rhs := rhs then
            ([lhs, rhs], addParent (addParent parents lhs n) rhs n)
          else
            ([lhs], addParent parents lhs n)

        let newToVisit := remainingNodes ++ children.filter (!remainingNodes.contains ·)
        maintainParents newToVisit (visited.concat n) newParents

  { g with parents := maintainParents g.observers.toList [] {} }

abbrev Graph.numNodes (g : Graph) : Nat :=
  g.nodes.length

def Graph.var (g : Graph) (init : Float) (label : String := "") : GraphChange :=
  let newId := g.numNodes
  let newVar := {
    id := newId
    ty := NodeTy.var none
    label
    createdIn := g.currentScope
    height := 0
    lastChangedAt := g.stabilizeId
    lastRecomputedAt := none }

  let newG := { g with
    nodes := g.nodes.concat newVar
    varChanges := g.varChanges.insert newId init
    scopes := g.scopes.modify g.currentScope (·.concat newId)
   }.maintainParents

  (newG, newId)

def Graph.map (g : Graph) (a : NodeId) (f : Float → Float) (label : String := "") : GraphChange :=
  let newId := g.numNodes
  let newMap := {
    id := newId
    ty := NodeTy.map none a f
    label
    createdIn := g.currentScope
    height := 1 + g.nodes[a]!.height
    lastChangedAt := g.stabilizeId
    lastRecomputedAt := none }

  let newG := { g with
    nodes := g.nodes.concat newMap
    scopes := g.scopes.modify g.currentScope (·.concat newId)
   }.maintainParents

  (newG, newId)

def Graph.map2 (g : Graph) (a b : NodeId) (f : Float → Float → Float) (label : String := "") : GraphChange :=
  let newId := g.numNodes
  let newMap2 := {
    id := newId
    ty := NodeTy.map2 none a b f
    label
    createdIn := g.currentScope
    height := 1 + max g.nodes[a]!.height g.nodes[b]!.height
    lastChangedAt := g.stabilizeId
    lastRecomputedAt := none }

  let newG := { g with
    nodes := g.nodes.concat newMap2
    scopes := g.scopes.modify g.currentScope (·.concat newId)
   }.maintainParents

  (newG, newId)

def Graph.map3 (g : Graph) (a b c : NodeId) (f : Float → Float → Float → Float) (label : String := "") : GraphChange :=
  let newId := g.numNodes
  let newMap3 := {
    id := newId
    ty := NodeTy.map3 none a b c f
    label
    createdIn := g.currentScope
    height := 1 + max g.nodes[a]!.height (max g.nodes[b]!.height g.nodes[c]!.height)
    lastChangedAt := g.stabilizeId
    lastRecomputedAt := none }

  let newG := { g with
    nodes := g.nodes.concat newMap3
    scopes := g.scopes.modify g.currentScope (·.concat newId)
   }.maintainParents

  (newG, newId)

def Graph.bind (g : Graph) (a : NodeId) (f : Graph → Float → GraphChange) (bindGens : BindGenerators) (label : String := "") : GraphChange × BindGenerators :=
  let newBindId := g.numNodes
  let newBind := {
    id := newBindId
    ty := NodeTy.bind none a
    label
    createdIn := g.currentScope
    height := 1 + g.nodes[a]!.height
    lastChangedAt := g.stabilizeId
    lastRecomputedAt := none }

  let newBindGens := bindGens.insert newBindId f

  let newBindResId := g.numNodes + 1
  let newBindResult := {
    id := newBindResId
    ty := NodeTy.bindResult none newBindId none
    label
    createdIn := g.currentScope
    height := 1 + newBind.height
    lastChangedAt := g.stabilizeId
    lastRecomputedAt := none }

  let newG := { g with
    nodes := g.nodes ++ [newBind, newBindResult]
    scopes := g.scopes.modify g.currentScope (· ++ [newBindId, newBindResId])
   }.maintainParents

  ((newG, newBindResId), newBindGens)

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

partial def Graph.stabilize (g : Graph) (bindGens : BindGenerators) : Graph :=
  -- Batteries.BinaryHeap is a max heap, but we want a min heap, so we reverse the LT relation
  let heightsGT := fun (a b : NodeId × Nat) => b.snd.blt a.snd
  let initRH := (g.varChanges.keysArray.map (·, 0)).toBinaryHeap heightsGT

  let rec addNodes (ns : List (NodeId × Nat)) (rh : Batteries.BinaryHeap (NodeId × Nat) heightsGT) : Batteries.BinaryHeap (NodeId × Nat) heightsGT :=
    match ns with
    | [] => rh
    | n :: ns => addNodes ns (rh.insert n)

  -- 1. remove from the recompute heap a node with the smallest height
  -- 2. recompute that node
  -- 3. if the node's value changes, then add its parents to the heap.
  let rec walkRH (rh : Batteries.BinaryHeap (NodeId × Nat) heightsGT) (g : Graph) : Graph :=
    match rh.extractMax with
    | (none, _) => g
    | (some (n, _), rh) =>
      let node := g.nodes[n]!
      let (newG, newRh) :=
        match node.ty with
        | .var val =>
          if let some newVal := g.varChanges[n]? then
            if val != newVal then
              let newNode := { node with
                ty := .var newVal
                lastChangedAt := g.stabilizeId
                lastRecomputedAt := g.stabilizeId }
              let newG := { g with
                nodes := g.nodes.replace node newNode }
              let newRh := addNodes
                ((newG.parents.getD n []).map fun p =>
                  (p, newG.nodes[p]!.height))
                rh
              (newG, newRh)
            else
              let newNode := { node with
                lastRecomputedAt := g.stabilizeId }
              let newG := { g with
                nodes := g.nodes.replace node newNode }
              (newG, rh)
          else (g, rh)
        | .map val a f =>
          let aNode := g.nodes[a]!
          -- A node is NOT stale if:
          -- 1. It has been recomputed AND
          -- 2. Its recomputeID is greater than or equal to the changeId of ALL of its children
          let notStale := (node.lastRecomputedAt >>=
            Option.guard (aNode.lastChangedAt.blt ·)).isSome

          if notStale then (g, rh)
          else
            let newVal := f aNode.floatVal!
            if newVal == val then
              let newNode := { node with
                lastRecomputedAt := g.stabilizeId }
              let newG := { g with
                nodes := g.nodes.replace node newNode }
              (newG, rh)
            else
              let newNode := { node with
                ty := .map newVal a f
                lastChangedAt := g.stabilizeId
                lastRecomputedAt := g.stabilizeId }
              let newG := { g with
                nodes := g.nodes.replace node newNode }
              let newRh := addNodes
                ((newG.parents.getD n []).map fun p =>
                  (p, newG.nodes[p]!.height))
                rh
              (newG, newRh)
        | .map2 val a b f =>
          let aNode := g.nodes[a]!
          let bNode := g.nodes[b]!
          let notStale := (node.lastRecomputedAt >>=
            Option.guard (aNode.lastChangedAt.blt ·) >>=
            Option.guard (bNode.lastChangedAt.blt ·)).isSome

          if notStale then (g, rh)
          else
            let newVal := f aNode.floatVal! bNode.floatVal!
            if newVal == val then
              let newNode := { node with
                lastRecomputedAt := g.stabilizeId }
              let newG := { g with
                nodes := g.nodes.replace node newNode }
              (newG, rh)
            else
              let newNode := { node with
                ty := .map2 newVal a b f
                lastChangedAt := g.stabilizeId
                lastRecomputedAt := g.stabilizeId }
              let newG := { g with
                nodes := g.nodes.replace node newNode }
              let newRh := addNodes
                ((newG.parents.getD n []).map fun p =>
                  (p, newG.nodes[p]!.height))
                rh
              (newG, newRh)
        | .map3 val a b c f =>
          let aNode := g.nodes[a]!
          let bNode := g.nodes[b]!
          let cNode := g.nodes[c]!
          let notStale := (node.lastRecomputedAt >>=
            Option.guard (aNode.lastChangedAt.blt ·) >>=
            Option.guard (bNode.lastChangedAt.blt ·) >>=
            Option.guard (cNode.lastChangedAt.blt ·)).isSome

          if notStale then (g, rh)
          else
            let newVal := f aNode.floatVal! bNode.floatVal! cNode.floatVal!
            if newVal == val then
              let newNode := { node with
                lastRecomputedAt := g.stabilizeId }
              let newG := { g with
                nodes := g.nodes.replace node newNode }
              (newG, rh)
            else
              let newNode := { node with
                ty := .map3 newVal a b c f
                lastChangedAt := g.stabilizeId
                lastRecomputedAt := g.stabilizeId }
              let newG := { g with
                nodes := g.nodes.replace node newNode }
              let newRh := addNodes
                ((newG.parents.getD n []).map fun p =>
                  (p, newG.nodes[p]!.height))
                rh
              (newG, newRh)
        | .bind val a  =>
          let aNode := g.nodes[a]!
          -- A node is NOT stale if:
          -- 1. It has been recomputed AND
          -- 2. Its recomputeID is greater than or equal to the changeId of ALL of its children
          let notStale := (node.lastRecomputedAt >>=
            Option.guard (aNode.lastChangedAt.blt ·)).isSome

          if notStale then (g, rh)
          else
            -- If stale, assume a change occurred
            let f := bindGens[n]!
            -- let (newG, newRhs) := f g aNode.floatVal!
            let maybeAFloatVal := aNode.floatVal?
            if maybeAFloatVal.isNone then
              panic! "Failed unpacking the bind node's a value"
            else

            -- PICKUP: recursively invalidate all binds in this scope
            -- 1. Clear them from the g.scopes list
            -- 2. Clear them from the recomputeHeap
            -- `let (newScopeG, newScopeRh) := g.newScopeFor n rh`
            let newScopeG := { g with
              currentScope := .bind n
              scopes := g.scopes.insert (.bind n) [] }
            let newScopeRh := rh.vector.toList.filter fun (p, _) =>
              newScopeG.nodes[p]!.createdIn == Scope.bind n
            -- TODO: need to recur on scopes created in this bind
            let (newG, newRhs) := f newScopeG maybeAFloatVal.get!
            -- TODO: `let newG := newG.adjustHeights`
            -- TODO: `let newRh := addNodes newG.scopes[n].map heightsFn rh`

            let newNode := { node with
              ty := .bind newRhs a
              lastChangedAt := newG.stabilizeId
              lastRecomputedAt := newG.stabilizeId }
            let newG := { newG with
              nodes := newG.nodes.replace node newNode }
            let newRh := addNodes
              ((newG.parents.getD n []).map fun p =>
                (p, newG.nodes[p]!.height))
              rh -- TODO/NOTE: this should only be adding its one parent, the bindResult
            (newG, newRh)
        | .bindResult val lhs rhs =>
          -- let rhs := g.nodes[lhs]!.ptrVal!
          let opt := g.nodes[lhs]!.ptrVal?
          if opt.isNone then
            panic! "Failed at getting bindResult getting the ptrVal"
          else
          let rhs := opt.get!
          let rhsNode := g.nodes[rhs]!
          -- A node is NOT stale if:
          -- 1. It has been recomputed AND
          -- 2. Its recomputeID is greater than or equal to the changeId of ALL of its children
          let notStale := (node.lastRecomputedAt >>=
            Option.guard (rhsNode.lastChangedAt.blt ·)).isSome

          if notStale then (g, rh)
          else
            -- let newVal := rhsNode.floatVal!
            let opt := rhsNode.floatVal?
            if opt.isNone then
              panic! "Failed at getting bindResult's rhs floatVal"
            else
            let newVal := opt.get!
            if newVal == val then
              let newNode := { node with
                lastRecomputedAt := g.stabilizeId }
              let newG := { g with
                nodes := g.nodes.replace node newNode }
              (newG, rh)
            else
              let newNode := { node with
                ty := .bindResult newVal lhs rhs
                lastChangedAt := g.stabilizeId
                lastRecomputedAt := g.stabilizeId }
              let newG := { g with
                nodes := g.nodes.replace node newNode }
              let newRh := addNodes
                ((newG.parents.getD n []).map fun p =>
                  (p, newG.nodes[p]!.height))
                rh
              (newG, newRh)

      walkRH newRh newG

  let stableG := walkRH initRH { g with stabilizeId := g.stabilizeId + 1 }
  { stableG with varChanges := {} }

def l := [1,2,3,4,1].toArray
#eval l
def bh := l.toBinaryHeap (·>·)
partial def walkBH {lt : Nat → Nat → Bool} (bh : Batteries.BinaryHeap Nat lt) (s : String) : String :=
  match bh.max with
  | none => s
  | some e => walkBH bh.popMax s!"{s}, {e}"
#eval walkBH bh ""

namespace StaticIfElseTest

structure StaticIfElse where
  g : Graph
  a : NodeId
  b : NodeId
  c : NodeId
  d : NodeId
  result : NodeId

/-
def test (a b c d : Float) : Float :=
  if a % 2 == 0 then
    b + c
  else
    b + d

test 1.0 2.0 3.0 4.0 =
-/
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

def stabilized := observingResult.stabilize {}
#eval stabilized

def modified := stabilized.setVar staticIfElse.a 2.0
#eval modified.stabilize {}

end StaticIfElseTest

namespace DynamicIfElseTest

structure DynamicIfElse where
  g : Graph
  bindGens : BindGenerators
  a : NodeId
  b : NodeId
  c : NodeId
  d : NodeId
  result : NodeId

def makeDynamicIfElse : DynamicIfElse :=
  let g := Graph.new
  let bindGens := {}

  let (g, a) := g.var 1.0
  let (g, b) := g.var 2.0
  let (g, c) := g.var 3.0
  let (g, d) := g.var 4.0

  let (g, cond) := g.map a (fun x =>
    if x.toInt64 % 2 == 0 then 1.0 else 0.0)
    "cond"

  let ((g, result), bindGens) := g.bind cond (fun g cond =>
    if cond == 1.0 then
      g.map2 b c fun x y =>
        x + y
    else
      g.map2 b d fun x y =>
        x + y)
    bindGens
    "result"

  ⟨g, bindGens, a, b, c, d, result⟩

def dynamicIfElse := makeDynamicIfElse
#eval dynamicIfElse.g

def observingResult := dynamicIfElse.g.observe dynamicIfElse.result
#eval observingResult

#eval observingResult.stabilize dynamicIfElse.bindGens

end DynamicIfElseTest
