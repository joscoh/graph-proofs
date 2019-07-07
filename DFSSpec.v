Require Import Coq.FSets.FSetInterface.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Graph.
Require Import Forest.
Require Import Path.
Require Import Coq.Init.Nat.
 
Module Type DFSBase (O: UsualOrderedType)(S: FSetInterface.Sfun O)(G: Graph O S)(F: Forest O S G).

  Module P := (Path.PathTheories O S G).

  Definition times_function := G.vertex -> nat.
  
  Parameter dfs : option G.vertex -> G.graph -> (F.forest *  times_function * times_function).

  Parameter state : G.graph -> Type.

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

  Parameter time_of_state: forall g, state g -> nat. 

  (* States must exist*)
  Parameter discovery_exists: forall o g v,
    G.contains_vertex g v = true ->
    exists (s: state g), time_of_state g s = d_time o g v.

  Parameter finish_exists: forall o g v,
    G.contains_vertex g v = true ->
    exists (s: state g), time_of_state g s = d_time o g v.

  Definition white o g (s: state g)(v: G.vertex) : bool :=
    ltb (time_of_state g s) (d_time o g v).

  Definition gray o g (s: state g)(v: G.vertex): bool :=
    ltb (time_of_state g s) (f_time o g v) && leb (d_time o g v) (time_of_state g s).

  Definition black o g (s:state g)(v: G.vertex) : bool :=
    leb (f_time o g v) (time_of_state g s).

  Parameter state_time_unique: forall g (s s': state g),
    time_of_state g s = time_of_state g s' <-> s = s'.

  (* Some needed results about uniqueness of times *)
  Parameter d_times_unique: forall o g u v
    (Hu: G.contains_vertex g u = true)
    (Hv: G.contains_vertex g v = true),
    d_time o g u = d_time o g v <-> u = v.

  Parameter f_times_unique: forall o g u v
    (Hu: G.contains_vertex g u = true)
    (Hv: G.contains_vertex g v = true),
    f_time o g u = f_time o g v <-> u = v.

  Parameter all_times_unique:
    forall o g u v
    (Hu: G.contains_vertex g u = true)
    (Hv: G.contains_vertex g v = true),
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
    F.desc (dfs_forest o g) u v <-> (forall s, time_of_state g s = d_time o g u ->
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

End DFSBase.
(*
(*TODO: figure out how to not copy everything and fix types*)
Module Type DFSWithStart (O: UsualOrderedType)(S: FSetInterface.Sfun O)(G: Graph O S)(F: Forest O S G).

  Module P := (Path.PathTheories O S G).

  Section WithGraph.

  Variable (g: G.graph).
  
  Parameter dfs_start : G.vertex -> G.graph -> F.forest.

  Parameter state : G.graph -> Type.

  Parameter f_time : G.graph -> G.vertex -> nat.

  Parameter d_time : G.graph -> G.vertex -> nat.

  Notation "'d' x" := (d_time g x)(at level 40).
  Notation "'f' x" :=(f_time g x)(at level 40).

  Parameter time_of_state : state g -> nat.

  Definition white (s: state g)(v: G.vertex) : bool :=
    ltb (time_of_state s) (d v).

  Definition gray (s: state g)(v: G.vertex): bool :=
    ltb (time_of_state s) (f v) && leb (d v) (time_of_state s).

  Definition black (s:state g)(v: G.vertex) : bool :=
    leb (f v) (time_of_state s).

  Parameter state_time_unique: forall (s s': state g),
    time_of_state s = time_of_state s' <-> s = s'.

Section ValidVertex.

  Variable (u v: G.vertex).
  Variable (Hu: G.contains_vertex g u = true).
  Variable (Hv: G.contains_vertex g v = true).

  (* Some needed results about uniqueness of times *)
  Parameter d_times_unique: forall  u v,
    d u = d v <-> u = v.

  Parameter f_times_unique: forall u v,
    f u = f v <-> u = v.

  Parameter all_times_unique: forall u v,
    f u <> d v.

  (*Major Results*)
  Parameter parentheses_theorem: 
    u <> v ->
    (d u < d v /\ d v < f v /\ f v < f u) \/ (d v < d u /\ d u < f u /\ f u < f v) \/
    (d u < f u /\ f u < d v /\ d v < f v) \/ (d v < f v /\ f v < d u /\ d u < f u).

  Parameter descendant_iff_interval: forall a, 
    F.desc (dfs_start a g) u v <-> (d u < d v /\ d v < f v /\ f v < f u).

  Parameter white_path_theorem: forall s a,
    F.desc (dfs_start a g) u v <-> (time_of_state s = d u ->
    exists l, P.path_list_ind g u v (fun x => white s x) l).

End ValidVertex.
End WithGraph.

  (* Basic results about vertices and edges *)
  Parameter same_vertices: forall g v a,
    G.contains_vertex g v = true <-> F.contains_vertex (dfs_start a g) v = true.

  Parameter same_edges: forall g u v a,
    F.is_child (dfs_start a g) u v = true -> G.contains_edge g u v = true.

  (*Why we care about starting from a specific vertex*)
  Parameter start_vertex: forall g a u,
    G.contains_vertex g a = true ->
    G.contains_vertex g u = true ->
    a <> u ->
    d_time g a < d_time g u.
End DFSWithStart.
*)

  