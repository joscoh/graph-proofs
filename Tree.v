Require Export Graph.

Require Export Path.


Module Type Tree(O: UsualOrderedType)(S: FSetInterface.Sfun O)(G: Graph O S).

  Module P := (Path.PathTheories O S G).

  Parameter tree : Type.

  Definition vertex := O.t.
  
  Parameter empty : tree.

  Parameter singleton: tree.

  Parameter root: tree -> option vertex.

  Parameter contains_vertex: tree -> vertex -> bool.

  Parameter add_child : tree -> vertex -> vertex -> tree.

  Parameter is_child: tree -> vertex -> vertex -> bool.

  Parameter get_children: tree -> vertex -> option (list vertex).

  Parameter tree_to_graph: tree -> G.graph.

  Parameter is_descendent: tree -> vertex -> vertex -> bool.

  Definition is_parent t u v := is_child t v u.

  Definition is_ancestor t u v := is_descendent t v u.

  Parameter equal: tree -> tree -> bool.

  
  Parameter add_child_1: forall t u v,
    contains_vertex t u = true ->
    contains_vertex t v = false ->
    is_child (add_child t u v) u v = true.

  Parameter add_child_2: forall t u v a b,
    is_child t u v = true ->
    is_child (add_child t a b) u v = true.

  Parameter add_child_3: forall t u v,
    contains_vertex t v = true ->
    equal (add_child t u v) t = true.

  Parameter add_child_4: forall t u v,
    contains_vertex t v = true ->
    is_child (add_child t u v) u v = false.

  Parameter get_children_1: forall t u,
    contains_vertex t u = true <->
    exists l, get_children t u = Some l.

  Parameter get_children_2: forall t u v l,
    get_children t u = Some l ->
    (is_child t u v = true <-> In v l).

  Parameter tree_to_graph_1: forall t u,
    contains_vertex t u = true <-> G.contains_vertex (tree_to_graph t) u = true.

  Parameter tree_to_graph_2: forall t u v,
    is_child t u v = true <-> G.contains_edge (tree_to_graph t) u v = true.

  Parameter tree_to_graph_3: forall t,
    P.acyclic (tree_to_graph t).

End Tree.
     
     
     