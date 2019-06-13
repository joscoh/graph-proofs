(*A rose tree-like implementation of the Tree interface*)
Require Import Tree.

Module RoseTree(O: UsualOrderedType)(S: FSetInterface.Sfun O)(G: Graph O S) <: (Tree O S G).

  Import G.

  Definition vertex := O.t.

  Inductive nempty_tree : Type :=
  | Node:  vertex -> list nempty_tree -> nempty_tree.

  Definition tree : Type := option nempty_tree.
(*
  Inductive tree : Type :=
  | TEmpty : forall (e: empty_tree),  tree
  | TNode: forall (n: nempty_tree),tree.
*)
(*From CPDT, better induction for non_empty_tree*)
Section All.
  Variable T : Type.
  Variable P : T -> Prop.


  Fixpoint all (ls : list T) : Prop :=
    match ls with
      | nil => True
      | cons h t => P h /\ all t
    end.
End All.


Section nempty_tree_ind'.
  Variable P : nempty_tree -> Prop.

  Hypothesis Node'_case : forall (v : vertex) (ls : list nempty_tree),
    all nempty_tree P ls -> P (Node v ls).

  Fixpoint nempty_tree_ind' (tr : nempty_tree) : P tr :=
    match tr with
      | Node n ls => Node'_case n ls
        ((fix list_nempty_tree_ind (ls : list nempty_tree) : all nempty_tree P ls :=
          match ls with
            | nil => I
            | cons tr' rest => conj (nempty_tree_ind' tr') (list_nempty_tree_ind rest)
          end) ls)
    end.
End nempty_tree_ind'.

(*End cpdt*)
  Definition empty : tree := None.

  Definition singleton (v:vertex) : tree := Some (Node v nil). 

  Definition root (t: tree) : option vertex :=
    match t with
    | None => None
    | Some (Node v l) => Some v
    end.

  Fixpoint contains_vertex_nempty (n: nempty_tree) (v: vertex) :=
  match n with
  | Node v' l => if O.eq_dec v v' then true else fold_right (fun x t => contains_vertex_nempty x v || t) false l
  end.

  Definition contains_vertex (t: tree) (v: vertex) :=
  match t with
  | None => false
  | Some n => contains_vertex_nempty n v
  end.

  Fixpoint add_child_nempty (n: nempty_tree) (p:vertex)(c: vertex) : nempty_tree :=
  match n with
  | Node v l => if O.eq_dec p v then Node v ((Node c nil) :: l) 
    else Node v (fold_right (fun x t => add_child_nempty x p c :: t) nil l)
  end.

  Definition add_child (t: tree) (p c : vertex) : tree :=
  match t with
  | None => None
  | Some n => Some (add_child_nempty n p c)
  end.

  Definition child_list (l : list nempty_tree) : list vertex :=
    fold_right (fun x t => match x with
                          | Node y l' => y
                          end :: t) nil l. 

  Fixpoint get_children_nempty (n: nempty_tree)(v: vertex) : option (list vertex) :=
  match n with
  | Node v' l => if O.eq_dec v v' then Some (child_list l)
                 else fold_right (fun x t => match (get_children_nempty x v) with
                                              | Some y => Some y
                                              | None => t
                                              end) None l
  end.

  Definition get_children (t: tree) (v: vertex) : option (list vertex) :=
  match t with
  | None => None
  | Some n => get_children_nempty n v
  end. 

  Fixpoint is_child_nempty (n : nempty_tree) (p c : vertex) : bool :=
  match n with
  | Node v l => if O.eq_dec p v then if in_dec O.eq_dec c (child_list l) then true else
    fold_right (fun x t => is_child_nempty x p c || t) false l else false
  end.

  Definition is_child (t: tree) (p c : vertex) : bool :=
  match t with
  | None => false
  | Some n => is_child_nempty n p c
  end.

  Fixpoint add_nempty_tree_to_graph (n : nempty_tree) (g: graph) : graph :=
    match n with
    | Node v l =>
      let new_g := (fold_right (fun x t => add_edge t v x) (add_vertex g v) (child_list l)) in
      fold_right (fun x t => add_nempty_tree_to_graph x t) new_g l
    end.

  Definition tree_to_graph (t: tree): graph :=
    match t with
    | None => G.empty
    | Some n => add_nempty_tree_to_graph n G.empty
  end.

  Fixpoint is_descendent_nempty (n: nempty_tree) (u v : vertex) : bool :=
    match n with
    | Node v' l => if O.eq_dec u v' then (fold_right (fun x t => contains_vertex_nempty x v || t) false l)
                   else (fold_right (fun x t => (is_descendent_nempty x u v) || t) false l) 
    end.

  Definition is_descendent (t: tree) (u v : vertex) : bool :=
  match t with
  | None => false
  | Some n => is_descendent_nempty n u v 
  end.

  (*Theories*)

  Lemma tree_to_graph_1: forall t u,
    contains_vertex t u = true <-> G.contains_vertex (tree_to_graph t) u = true.
  Proof.
    intros. destruct t.
    - simpl. split; intros.
      + eapply nempty_tree_ind'.
        * intros. unfold add_nempty_tree_to_graph. simpl.

  Lemma add_child_1: forall t u v,
    contains_vertex t u = true ->
    contains_vertex t v = false ->
    is_child (add_child t u v) u v = true.
  Proof.
    intros. destruct t.
    - simpl in *. eapply nempty_tree_ind'.
      + intros. unfold is_child_nempty.


