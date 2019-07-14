Require Export Coq.Structures.OrderedTypeEx.

Require Export Coq.FSets.FSetInterface.

Module Type Graph (O: UsualOrderedType)(S: FSetInterface.Sfun O).

  Parameter graph: Type.

  Parameter empty : graph.

  Definition vertex := O.t.

  Parameter contains_vertex: graph -> vertex -> bool.

  Parameter contains_edge: graph -> vertex -> vertex -> bool.

  Parameter add_vertex: graph -> vertex -> graph.

  Parameter add_edge: graph -> vertex -> vertex -> graph.

  Parameter neighbors_list: graph -> vertex -> option (list vertex).

  Parameter neighbors_set: graph -> vertex -> option (S.t).

  Parameter list_of_graph: graph -> list vertex.

  Parameter set_of_graph: graph -> S.t.

  Parameter empty_1: forall v,
    contains_vertex empty v = false.

  Parameter empty_2: forall u v,
    contains_edge empty u v = false.
  
  Parameter add_vertex_1: forall g v,
    contains_vertex (add_vertex g v) v = true.

  Parameter contains_edge_1: forall g u v,
    contains_edge g u v = true ->
    contains_vertex g u = true.

  Parameter contains_edge_2: forall g u v,
    contains_edge g u v = true ->
    contains_vertex g v = true.

  Parameter add_edge_1: forall g u v,
    contains_vertex g v = true ->
    contains_vertex g u = true ->
    contains_edge (add_edge g u v) u v = true.

  Parameter add_edge_2: forall g u v a b,
    contains_edge g a b = true ->
    contains_edge (add_edge g u v) a b = true.

  Parameter add_edge_3: forall g u v a b,
    u <> a \/ v <> b ->
    (contains_edge g a b = contains_edge (add_edge g u v) a b).

  Parameter neighbors_list_1: forall g v,
    contains_vertex g v = false <-> neighbors_list g v = None.

  Parameter neighbors_list_2: forall g u v l,
    neighbors_list g u = Some l ->
    contains_edge g u v = true <-> In v l.

  Parameter neighbors_list_3: forall g v l,
    neighbors_list g v = Some l ->
    StronglySorted (O.lt) l.

  Parameter neighbors_set_1: forall g v,
    neighbors_set g v = None <-> neighbors_list g v = None.

  Parameter neighbors_set_2: forall g u v s,
    neighbors_set g u = Some s ->
    contains_edge g u v = true <-> S.In v s.

  Parameter list_of_graph_1: forall g v,
    contains_vertex g v = true <-> In v (list_of_graph g).

  Parameter list_of_graph_2: forall g,
    StronglySorted (O.lt) (list_of_graph g).

  Parameter set_of_graph_1: forall g v,
    contains_vertex g v = true <-> S.In v (set_of_graph g).

  (*TODO: see if better way to define in interface*)
  (*A topological ordering is one where there are no edges going backward in the list and every vertex in the 
  graph is in the list*)
  Parameter topological_sort: list vertex -> graph ->  Prop.

  Parameter topological_sort_def: forall l g,
    topological_sort l g <-> 
  (forall v, contains_vertex g v = true <-> In v l) /\ NoDup l /\
  (forall l1 l2 l3 u v, l = l1 ++ u :: l2 ++ v :: l3 -> contains_edge g v u = false).


End Graph.
(*
Module Transpose (O: UsualOrderedType)(S: FSetInterface.Sfun O) (G: Graph O S) <: Graph O S.

  Definition graph := G.graph.

  Definition empty : graph := G.empty.

  Definition vertex := O.t.

  Definition contains_vertex: graph -> vertex -> bool := G.contains_vertex.

  Definition contains_edge (g: graph )( u v : vertex) : bool :=
    G.contains_edge g v u.

  Definition add_vertex: graph -> vertex -> graph := G.add_vertex.

  Definition add_edge g u v := G.add_edge g v u.

  Definition neighbors_list: graph -> vertex -> option (list vertex) := G.neighbors_list.

  Definition neighbors_set: graph -> vertex -> option (S.t) := G.neighbors_set.

  Definition list_of_graph: graph -> list vertex := G.list_of_graph.

  Definition set_of_graph: graph -> S.t := G.set_of_graph.

  Lemma empty_1: forall v,
    contains_vertex empty v = false.
  Proof. intros. unfold contains_vertex. apply G.empty_1. Qed.

  Lemma empty_2: forall u v,
    contains_edge empty u v = false.
  Proof. intros. unfold contains_edge. apply G.empty_2. Qed.
  
  Lemma add_vertex_1: forall g v,
    contains_vertex (add_vertex g v) v = true.
  Proof. intros. unfold contains_vertex. unfold add_vertex. apply G.add_vertex_1. Qed.

  Lemma contains_edge_1: forall g u v,
    contains_edge g u v = true ->
    contains_vertex g u = true.
  Proof. 
    intros. unfold contains_vertex. unfold contains_edge in H. eapply G.contains_edge_2. apply H.
  Qed. 

  Lemma contains_edge_2: forall g u v,
    contains_edge g u v = true ->
    contains_vertex g v = true.
  Proof.
    intros. unfold contains_vertex. unfold contains_edge in H. eapply G.contains_edge_1. apply H.
  Qed.

  Lemma add_edge_1: forall g u v,
    contains_vertex g v = true ->
    contains_vertex g u = true ->
    contains_edge (add_edge g u v) u v = true.
  Proof.
    intros. unfold contains_edge. unfold add_edge. unfold contains_vertex in *. apply G.add_edge_1; assumption.
  Qed.

  Lemma add_edge_2: forall g u v a b,
    contains_edge g a b = true ->
    contains_edge (add_edge g u v) a b = true.
  Proof.
    intros. unfold contains_edge in *. unfold add_edge. apply G.add_edge_2. apply H.
  Qed.

  Lemma add_edge_3: forall g u v a b,
    u <> a \/ v <> b ->
    (contains_edge g a b = contains_edge (add_edge g u v) a b).
  Proof.
    intros. unfold contains_edge. unfold add_edge. apply G.add_edge_3. destruct H;
    try(right; assumption); try(left; assumption).
  Qed.

  Lemma neighbors_list_1: forall g v,
    contains_vertex g v = false <-> neighbors_list g v = None.
  Proof.
    intros. unfold contains_vertex. unfold neighbors_list. apply G.neighbors_list_1.
  Qed.

  Lemma neighbors_list_2: forall g u v l,
    neighbors_list g u = Some l ->
    contains_edge g u v = true <-> In v l.
  Proof.
    intros. unfold neighbors_list in H. unfold contains_edge. eapply G.neighbors_list_2.

  Parameter neighbors_list_3: forall g v l,
    neighbors_list g v = Some l ->
    StronglySorted (O.lt) l.

  Parameter neighbors_set_1: forall g v,
    neighbors_set g v = None <-> neighbors_list g v = None.

  Parameter neighbors_set_2: forall g u v s,
    neighbors_set g u = Some s ->
    contains_edge g u v = true <-> S.In v s.

  Parameter list_of_graph_1: forall g v,
    contains_vertex g v = true <-> In v (list_of_graph g).

  Parameter list_of_graph_2: forall g,
    StronglySorted (O.lt) (list_of_graph g).

  Parameter set_of_graph_1: forall g v,
    contains_vertex g v = true <-> S.In v (set_of_graph g).

  (*TODO: see if better way to define in interface*)
  (*A topological ordering is one where there are no edges going backward in the list and every vertex in the 
  graph is in the list*)
  Parameter topological_sort: list vertex -> graph ->  Prop.

  Parameter topological_sort_def: forall l g,
    topological_sort l g <-> 
  (forall v, contains_vertex g v = true <-> In v l) /\ NoDup l /\
  (forall l1 l2 l3 u v, l = l1 ++ u :: l2 ++ v :: l3 -> contains_edge g v u = false).

End Transpose.
*)
  

  