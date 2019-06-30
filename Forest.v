Require Export Graph.

Require Export Path.
(*TODO: maybe extend graph instead of providing function*)

Module Type Forest(O: UsualOrderedType)(S Sg: FSetInterface.Sfun O)(G: Graph O Sg).

  Module P := (Path.PathTheories O Sg G).

  Parameter forest : Type.

  Definition vertex := O.t.
  
  Parameter empty : forest.

  Parameter is_empty: forest -> bool.

  Parameter add_root: forest -> vertex -> forest.

  Parameter contains_vertex: forest -> vertex -> bool.

  Parameter add_child : forest -> vertex -> vertex -> forest.

  Parameter is_child: forest -> vertex -> vertex -> bool.

  (*Parameter get_children: forest -> vertex -> option (list vertex).*)

  Parameter forest_to_graph: forest -> G.graph.

  Parameter is_descendent: forest -> vertex -> vertex -> bool.

  Definition is_parent f u v := is_child f v u.

  Definition is_ancestor f u v := is_descendent f v u.

  (*Parameter equal: tree -> tree -> bool.*)

  Parameter empty_1: is_empty empty = true.

  Parameter empty_2: forall f,
    is_empty f = true <-> (forall u, contains_vertex f u = false).

  Parameter add_child_1: forall t u v,
    contains_vertex t u = true ->
    contains_vertex t v = false ->
    is_child (add_child t u v) u v = true.

  Parameter add_child_2: forall t u v a b,
    is_child t u v = true ->
    is_child (add_child t a b) u v = true.

  Parameter add_child_3: forall t u v a,
    contains_vertex t a = true ->
    contains_vertex (add_child t u v) a = true.

  Parameter add_child_4: forall t u v,
    contains_vertex t v = true ->
    is_child (add_child t u v) u v = false.

  Parameter add_child_5: forall t u v,
    contains_vertex t u = true ->
    contains_vertex (add_child t u v) v = true.

  Parameter add_child_6: forall t u v a,
    contains_vertex (add_child t u v) a = true -> contains_vertex t a = true \/ a = v.

  Parameter add_root_1: forall f u,
    contains_vertex f u = false ->
    contains_vertex (add_root f u) u = true.

  Parameter add_root_2: forall f u v,
    contains_vertex f v = true ->
    contains_vertex (add_root f u) v = true.

(*
  Parameter singleton_1: forall v,
    root (singleton v) = Some v.

  Parameter singleton_2: forall v u,
    contains_vertex (singleton v) u = true <-> u = v.*)

  (*Parameter root_1: forall t u v r,
    root t = Some r <->
    root (add_child t u v) = Some r.

  Parameter root_2: forall t,
    root t = None <-> forall v, contains_vertex t v = false.*)

  (*Parameter empty_1: forall v,
    contains_vertex empty v = false.

  Parameter empty_2: forall u v,
    is_child empty u v = false.*)

  (*Parameter add_child_3: forall t u v,
    contains_vertex t v = true ->
    equal (add_child t u v) t = true.*)



  (*Parameter get_children_1: forall t u,
    contains_vertex t u = true <->
    exists l, get_children t u = Some l.

  Parameter get_children_2: forall t u v l,
    get_children t u = Some l ->
    (is_child t u v = true <-> In v l).*)

  Parameter tree_to_graph_1: forall t u,
    contains_vertex t u = true <-> G.contains_vertex (forest_to_graph t) u = true.

  Parameter tree_to_graph_2: forall t u v,
    is_child t u v = true <-> G.contains_edge (forest_to_graph t) u v = true.

  Parameter tree_to_graph_3: forall t,
    P.acyclic (forest_to_graph t).

  Parameter is_descendent_edge: forall t u v,
    is_child t u v = true ->
    is_descendent t u v = true.

  Parameter is_descendent_trans: forall t u v w,
    is_descendent t u v = true ->
    is_descendent t v w = true ->
    is_descendent t u w = true.
    
(*might need equal lemma to ensure it is acyclic but we will see*)
End Forest.
     
     
     