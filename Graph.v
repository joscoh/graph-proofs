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


End Graph.

  

  