Require Import Coq.FSets.FSetInterface.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Graph.
Require Import Forest.
Require Import Path.
Require Import Coq.Init.Nat.

Module Type DFSBase (O: UsualOrderedType)(S: FSetInterface.Sfun O)(G: Graph O S)(F: Forest O S).

  Module P := (Path.PathTheories O S G).

  Definition times_function := G.vertex -> nat.
  
  Parameter dfs : option G.vertex -> G.graph -> (F.forest *  times_function * times_function).

  Parameter state : option G.vertex -> G.graph -> Type.

  Definition d_time o g := match (dfs o g) with
                           | (_, f, _) => f
                           end.

  Definition f_time o g := match (dfs o g) with
                           | (_, _, f) => f
                           end.

  Definition dfs_forest o g := match (dfs o g) with
                           | (f, _, _) => f
                           end.

  (*

  Parameter f_time : G.graph -> G.vertex -> nat.

  Parameter d_time : G.graph -> G.vertex -> nat.*)

  Parameter time_of_state: forall o g, state o g -> nat. 

  (* States must exist*)
  Parameter discovery_exists: forall o g v,
    G.contains_vertex g v = true ->
    exists (s: state o g), time_of_state o g s = d_time o g v.

  Parameter finish_exists: forall o g v,
    G.contains_vertex g v = true ->
    exists (s: state o g), time_of_state o g s = f_time o g v.

  Parameter white: forall (o : option G.vertex) (g : G.graph), state o g -> G.vertex -> bool.

  Parameter white_def: forall o g s v,
    white o g s v = true <-> ltb (time_of_state o g s) (d_time o g v) = true.

  Parameter gray: forall (o : option G.vertex) (g : G.graph), state o g -> G.vertex -> bool.

  Parameter gray_def: forall o g s v,
    gray o g s v = true <-> ltb (time_of_state o g s) (f_time o g v) && leb (d_time o g v) (time_of_state o g s) = true.

  Parameter black:forall (o : option G.vertex) (g : G.graph), state o g -> G.vertex -> bool.

  Parameter black_def: forall o g s v,
    black o g s v = true <-> leb (f_time o g v) (time_of_state o g s) = true.

  Parameter state_time_unique: forall g o (s s': state o g),
    time_of_state o g s = time_of_state o g s' <-> s = s'.

  (* Some needed results about uniqueness of times *)
  Parameter d_times_unique: forall o g u v,
    G.contains_vertex g u = true ->
    G.contains_vertex g v = true ->
    d_time o g u = d_time o g v <-> u = v.

  Parameter f_times_unique: forall o g u v,
    G.contains_vertex g u = true ->
    G.contains_vertex g v = true ->
    f_time o g u = f_time o g v <-> u = v.

  Parameter all_times_unique:
    forall o g u v,
    G.contains_vertex g u = true ->
    G.contains_vertex g v = true ->
    f_time o g u <> d_time o g v.

  (*Major Results*)
  Parameter parentheses_theorem: forall o g u v,
    G.contains_vertex g u = true ->
    G.contains_vertex g v = true ->
    u <> v ->
    (d_time o g u < d_time o g v /\ d_time o g v < f_time o g v /\ f_time o g v < f_time o g u) \/
    (d_time o g v < d_time o g u /\ d_time o g u < f_time o g u /\ f_time o g u < f_time o g v) \/
    (d_time o g u < f_time o g u /\ f_time o g u < d_time o g v /\ d_time o g v < f_time o g v) \/
    (d_time o g v < f_time o g v /\ f_time o g v < d_time o g u /\ d_time o g u < f_time o g u).

  Parameter descendant_iff_interval: forall o g u v,
    G.contains_vertex g u = true ->
    G.contains_vertex g v = true ->
    F.desc (dfs_forest o g) u v <->
     (d_time o g u < d_time o g v /\ d_time o g v < f_time o g v /\ f_time o g v < f_time o g u).

  Parameter white_path_theorem: forall o g u v,
    G.contains_vertex g u = true ->
    F.desc (dfs_forest o g) u v <-> (forall s, time_of_state o g s = d_time o g u ->
    exists l, P.path_list_ind g u v (fun x => white o g s x) l).

  (* Basic results about vertices and edges *)
  Parameter same_vertices: forall o g v,
    G.contains_vertex g v = true <-> F.contains_vertex (dfs_forest o g) v = true.

  Parameter same_edges: forall o g u v,
    F.is_child (dfs_forest o g) u v = true -> G.contains_edge g u v = true.

  (*Why we care about starting from a specific vertex*)
  Parameter start_vertex: forall g v u,
    G.contains_vertex g v = true ->
    G.contains_vertex g u = true ->
    v <> u ->
    d_time (Some v) g v < d_time (Some v) g u.

  (*Definitions for applications of DFS*)

  Parameter back_edge : G.graph -> G.vertex -> G.vertex -> option G.vertex -> Prop.

  (*Gets around declaring definition in interface: see if better way*)
  Parameter back_edge_def: forall g u v o,
    back_edge g u v o <-> (G.contains_edge g u v = true /\ F.desc (dfs_forest o g) v u).

  Parameter rev_f_time: option G.vertex -> G.graph -> G.vertex -> G.vertex -> Prop.

  Parameter rev_f_time_def: forall o g u v,
    rev_f_time o g u v <-> f_time o g u > f_time o g v.

  (*(*The point of using an OrderedType*)
  Parameter root_smallest: forall v g s,
    time_of_state None g s = d_time None g v ->
    F.is_root (dfs_forest None g) v = true ->
    (forall u, G.contains_vertex g u = true -> white None g s u = true -> O.lt v u).*)

End DFSBase.
 

Module Type DFSWithCycleDetect(O: UsualOrderedType)(S: FSetInterface.Sfun O)(G: Graph O S)(F: Forest O S).
  Include (DFSBase O S G F).

  Parameter cycle_detect: option G.vertex -> G.graph -> bool.

  Parameter cycle_detect_back_edge: forall g o,
    cycle_detect o g = true <-> exists u v, back_edge g u v o.

End DFSWithCycleDetect.

Module Type DFSWithTopologicalSort(O: UsualOrderedType)(S: FSetInterface.Sfun O)(G: Graph O S)(F: Forest O S).
  Include (DFSBase O S G F).

  (*We have an additional function that produces a list of vertices reverse sorted by finish time*)
  Parameter rev_f_time_list: G.graph -> option G.vertex  -> list (G.vertex).

  Parameter topological_sort_condition: forall g o,
    (forall v, G.contains_vertex g v = true <-> In v (rev_f_time_list g o)) /\
    StronglySorted (rev_f_time o g) (rev_f_time_list g o).

End DFSWithTopologicalSort.

Module Type DFSCustomOrder (O: UsualOrderedType)(S: FSetInterface.Sfun O)(G: Graph O S)(F: Forest O S).

  Module P := (Path.PathTheories O S G).
  Module G' := (Graph.GraphOrder O S G).
  Section Whole.
    Context (g: G.graph) (lt' : O.t -> O.t -> bool) (Ho : G'.GraphOrdering g lt').

  Definition times_function := G.vertex -> nat.
  
  Parameter dfs:
       G'.GraphOrdering g lt' -> option G.vertex -> F.forest * times_function * times_function.


  Parameter state : G'.GraphOrdering g lt' ->
   option G.vertex -> Type.

  Definition d_time o := match (dfs Ho o) with
                           | (_, f, _) => f
                           end.

  Definition f_time o := match (dfs Ho o) with
                           | (_, _, f) => f
                           end.

  Definition dfs_forest o := match (dfs Ho o) with
                           | (f, _, _) => f
                           end.

  (*

  Parameter f_time : G.graph -> G.vertex -> nat.

  Parameter d_time : G.graph -> G.vertex -> nat.*)

  Parameter time_of_state: forall o, state Ho o  -> nat.

  (* States must exist*)
  Parameter discovery_exists: forall o v,
    G.contains_vertex g v = true ->
    exists (s: state Ho o), time_of_state o s = d_time o v.

  Parameter finish_exists: forall o v,
    G.contains_vertex g v = true ->
    exists (s: state Ho o), time_of_state o s = f_time o v.

  Parameter white: forall (o : option G.vertex), state Ho o -> G.vertex -> bool.

  Parameter white_def: forall o s v,
    white o s v = true <-> ltb (time_of_state o s) (d_time o v) = true.

  Parameter gray: forall (o : option G.vertex), state Ho o -> G.vertex -> bool.

  Parameter gray_def: forall o s v,
    gray o s v = true <-> ltb (time_of_state o s) (f_time o v) && leb (d_time o v) (time_of_state o s) = true.

  Parameter black:forall (o : option G.vertex), state Ho o -> G.vertex -> bool.

  Parameter black_def: forall o s v,
    black o s v = true <-> leb (f_time o v) (time_of_state o s) = true.

  Parameter state_time_unique: forall o (s s': state Ho o),
    time_of_state o s = time_of_state o s' <-> s = s'.

  (* Some needed results about uniqueness of times *)
  Parameter d_times_unique: forall o u v,
    G.contains_vertex g u = true ->
    G.contains_vertex g v = true ->
    d_time o u = d_time o v <-> u = v.

  Parameter f_times_unique: forall o u v,
    G.contains_vertex g u = true ->
    G.contains_vertex g v = true ->
    f_time o u = f_time o v <-> u = v.

  Parameter all_times_unique:
    forall o u v,
    G.contains_vertex g u = true ->
    G.contains_vertex g v = true ->
    f_time o u <> d_time o v.

  (*Major Results*)
  Parameter parentheses_theorem: forall o u v,
    G.contains_vertex g u = true ->
    G.contains_vertex g v = true ->
    u <> v ->
    (d_time o u < d_time o v /\ d_time o v < f_time o v /\ f_time o v < f_time o u) \/
    (d_time o v < d_time o u /\ d_time o u < f_time o u /\ f_time o u < f_time o v) \/
    (d_time o u < f_time o u /\ f_time o u < d_time o v /\ d_time o v < f_time o v) \/
    (d_time o v < f_time o v /\ f_time o v < d_time o u /\ d_time o u < f_time o u).

  Parameter descendant_iff_interval: forall o u v,
    G.contains_vertex g u = true ->
    G.contains_vertex g v = true ->
    F.desc (dfs_forest o) u v <->
     (d_time o u < d_time o v /\ d_time o v < f_time o v /\ f_time o v < f_time o u).

  Parameter white_path_theorem: forall o u v,
    G.contains_vertex g u = true ->
    F.desc (dfs_forest o) u v <-> (forall s, time_of_state o s = d_time o u ->
    exists l, P.path_list_ind g u v (fun x => white o s x) l).

  (* Basic results about vertices and edges *)
  Parameter same_vertices: forall o v,
    G.contains_vertex g v = true <-> F.contains_vertex (dfs_forest o) v = true.

  Parameter same_edges: forall o u v,
    F.is_child (dfs_forest o) u v = true -> G.contains_edge g u v = true.

  (*Why we care about starting from a specific vertex*)
  Parameter start_vertex: forall v u,
    G.contains_vertex g v = true ->
    G.contains_vertex g u = true ->
    v <> u ->
    d_time (Some v) v < d_time (Some v) u.

 (* (*Definitions for applications of DFS*)

  Parameter back_edge : G.graph -> G.vertex -> G.vertex -> option G.vertex -> Prop.

  (*Gets around declaring definition in interface: see if better way*)
  Parameter back_edge_def: forall u v o,
    back_edge g u v o <-> (G.contains_edge g u v = true /\ F.desc (dfs_forest o) v u).

  Parameter rev_f_time: option G.vertex -> G.graph -> G.vertex -> G.vertex -> Prop.

  Parameter rev_f_time_def: forall o u v,
    rev_f_time o g u v <-> f_time o u > f_time o v.*)

  (*The point of using a GraphOrdering*)
  Parameter root_smallest: forall v s,
    time_of_state None s = d_time None v ->
    F.is_root (dfs_forest None) v = true ->
    (forall u (H2: G.contains_vertex g u = true), white None s u = true -> lt' v u = true).
  End Whole.
End DFSCustomOrder.





