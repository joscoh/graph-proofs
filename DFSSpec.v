Require Import Coq.FSets.FSetInterface.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Graph.
Require Import Forest.
Require Import Path.
Require Import Coq.Init.Nat.
 
Module Type DFSBase (O: UsualOrderedType)(S: FSetInterface.Sfun O)(G: Graph O S)(F: Forest O S G).

  Module P := (Path.PathTheories O S G).
  
  Parameter dfs : G.graph -> F.forest.

  Parameter state : G.graph -> Type.

  Parameter f_time : G.graph -> G.vertex -> nat.

  Parameter d_time : G.graph -> G.vertex -> nat.

  Parameter time_of_state: forall g, state g -> nat. 

  Definition white g (s: state g)(v: G.vertex) : bool :=
    ltb (time_of_state g s) (d_time g v).

  Definition gray g (s: state g)(v: G.vertex): bool :=
    ltb (time_of_state g s) (f_time g v) && leb (d_time g v) (time_of_state g s).

  Definition black g (s:state g)(v: G.vertex) : bool :=
    leb (f_time g v) (time_of_state g s).

  Parameter state_time_unique: forall g (s s': state g),
    time_of_state g s = time_of_state g s' <-> s = s'.

  (* Some needed results about uniqueness of times *)
  Parameter d_times_unique: forall g u v
    (Hu: G.contains_vertex g u = true)
    (Hv: G.contains_vertex g v = true),
    d_time g u = d_time g v <-> u = v.

  Parameter f_times_unique: forall g u v
    (Hu: G.contains_vertex g u = true)
    (Hv: G.contains_vertex g v = true),
    f_time g u = f_time g v <-> u = v.

  Parameter all_times_unique:
    forall g u v
    (Hu: G.contains_vertex g u = true)
    (Hv: G.contains_vertex g v = true),
    f_time g u <> d_time g v.

  (*Major Results*)
  Parameter parentheses_theorem: forall g u v,
    G.contains_vertex g u = true ->
    G.contains_vertex g v = true ->
    u <> v ->
    (d_time g u < d_time g v /\ d_time g v < f_time g v /\ f_time g v < f_time g u) \/
    (d_time g v < d_time g u /\ d_time g u < f_time g u /\ f_time g u < f_time g v) \/
    (d_time g u < f_time g u /\ f_time g u < d_time g v /\ d_time g v < f_time g v) \/
    (d_time g v < f_time g v /\ f_time g v < d_time g u /\ d_time g u < f_time g u).

  Parameter descendant_iff_interval: forall g u v,
    G.contains_vertex g u = true ->
    G.contains_vertex g v = true ->
    F.desc (dfs g) u v <-> (d_time g u < d_time g v /\ d_time g v < f_time g v /\ f_time g v < f_time g u).

  Parameter white_path_theorem: forall g u v,
    G.contains_vertex g u = true ->
    F.desc (dfs g) u v <-> (forall s, time_of_state g s = d_time g u ->
    exists l, P.path_list_ind g u v (fun x => white g s x) l).

  (* Basic results about vertices and edges *)
  Parameter same_vertices: forall g v,
    G.contains_vertex g v = true <-> F.contains_vertex (dfs g) v = true.

  Parameter same_edges: forall g u v,
    F.is_child (dfs g) u v = true -> G.contains_edge g u v = true.

End DFSBase.

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


  