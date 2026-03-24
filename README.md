# Incremental

## Jane Street's Incremental

- Specify complex computations with changing input as dynamic dependency graph
- Library does minimal work necessary to update the output of the computation as inputs change
- Use cases at Jane Street:
  - Original: Trading systems send orders to markets based on some event that changes how a trading model assesses the fair value of a product.
  - Pricing and risk models for financial products
  - GUI construction
  - Dynamic web-applications

```ocaml
module Incremental : sig
    type 'a t (** 'a t is an incremental. 'a is the underlying data type of the incremental, such as an Int or a Float *)

    val return : 'a -> 'a t (** given a value of 'a, return an incremental that wraps this constant value *)

    val map : 'a t -> f: ('a -> 'b) -> 'b t (** given an 'a incremental and a function f that maps 'a to 'b values, return a 'b incremental ('b t). Thinking in terms of the computational dependency graph, map creates an edge from a leaf node containing 'a t to a new node containing 'b t with f as the edge property. *)

    val map2 : 'a t -> 'b t -> f:('a -> 'b -> 'c) -> 'c t (** given two incrementals, 'a t and 'b t, and a function that maps 'a and 'b values to 'c values, return a 'c incremental ('c t). In the context of the dependency graph, map2 creates an edge (two edges?) from two leaf nodes to a third node. *)

    (** map lets you "fan-out" your computation into different variables, and map2 lets you bring those variables back together. They both define static dependencies between computation. *)

    val bind : 'a t -> f:('a -> 'b t) -> 'b t (** bind gives the power to create dynamic dependencies between computations. Given an 'a incremental ('a t) and a function that takes an 'a and returns a 'b incremental ('b t), return a 'b t. In other words, given a new 'a value for the input 'a incremental, create an entirely new computation graph. *)

    (** map/map2 build static DAGs while bind builds dynamic DAGs. Dynamic DAGs can be used to implement efficient control-flow (if-then-else) logic that doesn't trigger re-computation of a branch that won't be used. *)

    val stabilize : unit -> unit (** execute all of the changes that have accrued to variables in the computation graph. Raise exceptions for pathological graphs (e.g. cycles produced by binds) *)

    (** these let you get values out of incrementals. *)
    val value : 'a t -> 'a
    val on_update : 'a t -> ('a -> unit) -> unit (** call a pure, no return function when the given incremental is updated. Returns nothing itself. Example use-case: logging. *)
end

module Variable : sig
    type 'a t
    val create  : 'a -> 'a t
    val set     : 'a t -> 'a -> unit
    val read    : 'a t -> 'a Incremental.t
end
```

### Example: Area of A Rectangle

This is an example of computation graph that is static relative to the inputs (doesn't use bind). In other words, it could be done by Excel.

```ocaml
let height = Variable.create 0.
let width = Variable.create 0.

let base_area = map2 (Variable.read height) (Variable.read width) (fun height width -> height *. width)

let () =
        on_update base_area (fun x -> printf "base_area = %.1f\n" x);
        Variable.set height 100.;
        Variable.set width 10.;
        stabilize ();
        (* "base_area = 1000.0" *)

        Variable.set height 10.;
        (* Nothing is printed *)

        Variable.set width 50.;
        stabilize ();
        (* "base_area = 500.0" *)
    ;;
```

### Bind

```lean
a := Var.create 0
b := Var.create 3
c := Var.create 4

is_even := Incr.map a fun a' => 'a % 2 == 0
result := Incr.bind is_even fun is_even' => if is_even' then Incr.return 0 else Incr.map2 b c fun (b', c') => b' * c'
```

#### Static if-else

Node {cond, fa} -e> result
Node {if_true, fb} -e> result
Node {if_false, fc} -e> result
Node {result, (a, b, c) -> if a then b else c}

Problem: library won't know that if the cond Node is true, then the if_false Node doesn't need to be recomputed. Therefore, the if_false Node could experience a downstream change and force a re-fire of itself despite that not being needed if cond is true.

#### Dynamic if-else

Recall: val bind : 'a t -> f:('a -> 'b t) -> 'b t
Node {cond, fa} -e> code
Bind {code, (a) -> if a then Node {if_true, fb} else Node {if_false, fb}} -e> result

### V1 Implementation

Stablization is the key algorithm. It is divided into two passes over the computation graph starting at the leaf nodes. The leaf nodes are the inputs (..?) to the computation graph. You know which ones have changed, because of calls to the Variable.set method:

1. Start at the leaf node (inputs?) of the graph and transitively mark all nodes as dirty. Additionally, each node keeps a counter of children that need to be recomputed before I (the node) can be recomputed.
2. Again starting at the leaf node, re-compute all the nodes that you need. "Propagate until all dirty nodes are clean."

### Problem: Memory Management

- Since calls to bind will change the computation graph, some nodes of that graph will be no longer needed. If they are not cleaned up, you will quickly run into memory problems, because you will have all these dead nodes lying around that aren't needed anymore.
- They solved this with ref-counting to track if no one is looking for a node anymore, it can be released.

### Problem: Cutoffs

- Broken

### No-closure Implementation

The data underlying incrementals are heterogeneous within a computation graph, so the data structure has to be a collection of heterogeneous types. In OCaml, this means using closures (Readers?) as the element of the computation graph collection. Closures are allocation-heavy which seriously hit performance.

They switched to algebraic data types (enums in Rust) and got 2-3x performance.

### Future Improvements

- Explicit memory management
- "Collapsing of nodes" "to avoid node overhead" "might need to know the contents of a closure" (??)
