Require Export Graph.
Require Import Helper.

Require Export Path.
Require Import Coq.Lists.List.
(*TODO: maybe extend graph instead of providing function*)

Module Type Forest(O: UsualOrderedType)(Sg: FSetInterface.Sfun O)(G: Graph O Sg).

  Module P := (Path.PathTheories O Sg G).

  Parameter forest : Type.

  Definition vertex := O.t.
  
  Parameter empty : forest.

  Parameter is_empty: forest -> bool.

  Parameter add_root: forest -> vertex -> forest.

  Parameter contains_vertex: forest -> vertex -> bool.
  (*Input: forest, parent, child*)
  Parameter add_child : forest -> vertex -> vertex -> forest.

  Parameter is_child: forest -> vertex -> vertex -> bool.

  Parameter is_root: forest -> vertex -> bool.

  (*Parameter get_children: forest -> vertex -> option (list vertex).*)

  Parameter forest_to_graph: forest -> G.graph.
  (*Input: forest, ancestor, descendant*)
 (* Parameter is_descendant: forest -> vertex -> vertex -> bool.*)

  Definition is_parent f u v := is_child f v u.

 (* Definition is_ancestor f u v := is_descendant f v u.*)

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

  Parameter add_child_4: forall t u u' v,
    contains_vertex t v = true ->
    is_child (add_child t u' v) u v = is_child t u v.

  Parameter add_child_5: forall t u v,
    contains_vertex t u = true ->
    contains_vertex (add_child t u v) v = true.

  Parameter add_child_6: forall t u v a,
    contains_vertex (add_child t u v) a = true -> contains_vertex t a = true \/ a = v.

  Parameter add_child_7: forall f u v a b,
    is_child f u v = false ->
    a <> u \/ b <> v ->
    is_child (add_child f a b) u v = false.

  Parameter add_child_8: forall f u v r,
    is_child f u v = false ->
    is_child (add_root f r) u v = false.
    
Lemma add_child_9: forall f u v a b,
  is_child (add_child f u v) a b = true ->
  is_child f a b = true \/ (u = a /\ b = v).
Proof.
  intros. destruct (is_child f a b) eqn : ?.
  - left. reflexivity.
  - destruct (O.eq_dec u a). destruct (O.eq_dec v b). unfold O.eq in *. subst.
    right. split; reflexivity. all: right; eapply add_child_7 in Heqb0; try( rewrite Heqb0 in H; inversion H).
    right. apply n. left. apply n.
Qed. 

  Parameter add_root_1: forall f u,
    contains_vertex (add_root f u) u = true.

  Parameter add_root_2: forall f u v,
    contains_vertex f v = true ->
    contains_vertex (add_root f u) v = true.

  Parameter add_root_3: forall f u v,
    contains_vertex (add_root f u) v = true -> u = v \/ contains_vertex f v = true.

 

  (*Todo: see if I can prove 4 from this*)
  Parameter add_root_5: forall f u v r,
    is_child f u v = is_child (add_root f r) u v.

  Parameter is_root_1: forall f r,
    contains_vertex f r = false ->
    is_root (add_root f r) r = true.

  Parameter is_root_2: forall f r,
    contains_vertex f r = true ->
    is_root f r = false <-> (exists u, is_child f u r = true).
    

  Parameter is_root_3: forall f r u v,
    is_root f r = true ->
    is_root (add_child f u v) r = true.

  Parameter is_root_4: forall f r u,
    is_root f r = true ->
    is_root (add_root f u) r = true.

  Parameter is_child_1: forall f u v,
    is_child f u v = true -> contains_vertex f u = true /\ contains_vertex f v = true /\ is_root f v = false.

  Parameter is_child_2: forall f u u' v,
    is_child f u v = true -> is_child f u' v = true -> u = u'.

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
(*
  Parameter is_descendant_edge: forall t u v,
    is_child t u v = true ->
    is_descendant t u v = true.

  Parameter is_descendant_trans: forall t u v w,
    is_descendant t u v = true ->
    is_descendant t v w = true ->
    is_descendant t u w = true.

  Parameter is_descendant_1: forall t u v a b,
    is_descendant t u v = true ->
    is_descendant (add_child t a b)  u v = true.
*)
  (*Parameter is_descendant_iff: forall t u v,
    is_descendant t u v = true <-> is_child t u v = true \/ exists p, is_descendant t u p = true /\ is_child t p v = true.*)

  Inductive desc: forest -> vertex -> vertex -> Prop :=
  | parent: forall f u v, is_child f u v = true -> desc f u v
  | d_step: forall f u v p,
    desc f u p ->
    is_child f p v = true ->
    desc f u v.

  Lemma is_descendant_edge: forall t u v,
    is_child t u v = true ->
    desc t u v.
Proof.
  intros. apply parent. apply H.
Qed.

Lemma is_descendant_trans: forall t u v w,
    desc t u v ->
    desc t v w ->
    desc t u w.
Proof.
  intros. generalize dependent H. revert u. induction H0; intros.
  - eapply d_step. apply H0. apply H.
  - eapply d_step. apply IHdesc. apply H1. apply H.
Qed. 

Lemma is_descendant_1: forall t u v a b,
    desc t u v  ->
    desc (add_child t a b) u v.
Proof.
  intros. induction H.
  - apply parent. apply add_child_2. apply H.
  - eapply d_step. apply IHdesc. apply add_child_2. apply H0.
Qed.

Lemma desc_in_forest: forall f u v,
  desc f u v ->
  contains_vertex f u = true /\ contains_vertex f v = true.
Proof.
  intros. induction H; subst.
  - apply is_child_1 in H. destruct H. destruct H0. split; assumption.
  - apply is_child_1 in H0. repeat(match goal with | [H: _ /\ _ |- _ ] => destruct H end).
    split; assumption.
Qed. 

Lemma desc_depends_on_children: forall f f',
  (forall u v, is_child f u v = is_child f' u v) ->
  (forall u v, desc f u v <-> desc f' u v).
Proof.
  intros. split; intro H1; induction H1.
  - apply parent. rewrite <- H. apply H0.
  - eapply d_step. apply IHdesc. apply H. rewrite <- H. apply H0.
  - apply parent. rewrite H. apply H0.
  - eapply d_step. apply IHdesc. apply H. rewrite H. apply H0.
Qed.

Lemma add_child_equiv: forall f v u',
  contains_vertex f v = true ->
  (forall a b, is_child f a b = true <-> is_child (add_child f u' v) a b = true).
Proof.
  intros. split; intros.
  - apply add_child_2. apply H0.
  - destruct (O.eq_dec v b).
    + unfold O.eq in e. subst.  eapply add_child_4 in H. rewrite H0 in H. symmetry. apply H.
    + apply add_child_9 in H0. destruct H0. apply H0. destruct H0; subst. exfalso. apply n.
      reflexivity.
Qed.

Lemma is_descendant_contain: forall f u u' v' v,
  contains_vertex f v = true ->
  desc (add_child f u' v) u v' <->
  desc f u v'.
Proof.
  intros. eapply desc_depends_on_children. intros. rewrite bool_prop. intros; split; intros.
  eapply add_child_equiv. 
  apply H. apply H0. apply add_child_2. apply H0.
Qed. 

Lemma is_descendant_2: forall f u v a b,
  contains_vertex f u = true ->
  desc (add_child f u v) a b ->
  b = v \/ desc f a b.
Proof.
  intros.


 remember (add_child f u v) as f'. induction H0; subst.
  - apply add_child_9 in H0. destruct H0. right. apply parent. assumption. left. destruct H0; subst; split; reflexivity.
  - 
 destruct IHdesc. reflexivity. destruct H2; subst. destruct (O.eq_dec p v0). unfold O.eq in e.
    subst. left. reflexivity.
    assert (is_child f p v0 = true). destruct (contains_vertex f p) eqn : ?.
    rewrite <- add_child_equiv in H1. apply H1. apply Heqb.
    apply add_child_9 in H1. destruct H1. apply H1. destruct H1; subst. exfalso. apply n; reflexivity.
    assert (contains_vertex f p = true). apply is_child_1 in H2. destruct H2; assumption.
    rewrite is_descendant_contain in H0. right. eapply d_step. apply H0. apply H2. apply H3.
    assert (A:= H1).
    apply add_child_9 in H1. destruct H1. right. eapply d_step. apply H2. apply H1. destruct H1. subst.
    left. reflexivity.
Qed.


 Lemma add_root_4: forall f u v r,
    desc f u v <-> desc (add_root f r) u v.
Proof.
  intros. split; intros.
  - induction H.
  + apply parent. rewrite <- add_root_5. apply H.
  + eapply d_step. apply IHdesc. rewrite <- add_root_5. apply H0.
  - remember (add_root f r) as f'. induction H; subst.
    + eapply parent. erewrite add_root_5. apply H.
    + eapply d_step. apply IHdesc. reflexivity. erewrite add_root_5. apply H0.
Qed. 


Lemma child_is_leaf: forall f u v,
  contains_vertex f u = true ->
  contains_vertex f v = false ->
  (forall x, is_child (add_child f u v) v x = false).
Proof.
  intros. eapply add_child_7. destruct (is_child f v x) eqn : ?.
  apply is_child_1 in Heqb. destruct Heqb. rewrite H1 in H0. inversion H0. reflexivity.
  assert (u <> v). intro. subst. rewrite H0 in H. inversion H. left. apply H1.
Qed.

Lemma desc_is_leaf: forall f u v,
  contains_vertex f u = true ->
  contains_vertex f v = false ->
  (forall x, ~desc (add_child f u v) v x).
Proof.
  intros. intro. remember (add_child f u v) as f'. induction H1; subst.
  - rewrite child_is_leaf in H1. inversion H1. apply H. apply H0.
  - apply IHdesc. apply H0. reflexivity.
Qed.

Lemma path_iff_desc: forall f u v,
  P.path (forest_to_graph f) u v <-> desc f u v.
Proof.
  intros. split; intro H. remember (forest_to_graph f) as g. induction H; subst.
  - rewrite <- tree_to_graph_2 in H. apply parent. apply H.
  - rewrite <- tree_to_graph_2 in H0. eapply d_step. apply IHpath. reflexivity. apply H0.
  - induction H.
    + apply P.p_start. rewrite <- tree_to_graph_2. apply H.
    + eapply P.p_continue. apply IHdesc. rewrite <- tree_to_graph_2. apply H0.
Qed.

Import ListNotations.

Fixpoint desc_list (f: forest) (u v: vertex) (l : list vertex) : bool :=
  match l with
  | nil => is_child f u v
  | x :: tl => is_child f x v && desc_list f u x tl
  end.

(*Easier to prove for lists*)
  Inductive desc': forest -> vertex -> vertex -> Prop :=
  | parent': forall f u v, is_child f u v = true -> desc' f u v
  | d_step': forall f u v p,
    is_child f u p = true ->
    desc' f p v ->
    desc' f u v.

Lemma desc'_trans: forall f u v w,
  desc' f u v ->
  desc' f v w ->
  desc' f u w.
Proof.
  intros. induction H.
  - eapply d_step'. apply H. apply H0.
  - eapply d_step'. apply H. apply IHdesc'. apply H0.
Qed.

Lemma desc_desc': forall f u v,
  desc f u v <-> desc' f u v.
Proof.
  intros. split; intros; induction H.
  - apply parent'. apply H.
  - eapply desc'_trans. apply IHdesc. apply parent'. apply H0.
  - apply parent. apply H.
  - eapply is_descendant_trans. apply parent. apply H. apply IHdesc'.
Qed.

  Lemma desc_list_iff_desc: forall f u v,
    (exists l, desc_list f u v l = true) <->
    desc f u v.
  Proof.
    intros. split; intros. destruct H. generalize dependent v. induction x; intros.
    - simpl in H. apply parent. apply H.
    - simpl in H. rewrite andb_true_iff in H. destruct H.
      eapply is_descendant_trans. apply (IHx a). apply H0. apply parent. apply H. 
    -  induction H.
      + exists nil. simpl. apply H.
      + destruct IHdesc. exists (p :: x). simpl. rewrite andb_true_iff. split; assumption.
  Qed. 

  Lemma desc_list_all_desc: forall f u v l,
    desc_list f u v l = true ->
    (forall x, In x l -> desc f u x).
  Proof.
    intros. generalize dependent v. induction l; intros.
    - inversion H0.
    - simpl in *. rewrite andb_true_iff in H. destruct H. destruct H0. subst.
      rewrite <- desc_list_iff_desc. exists l. apply H1.
      eapply IHl. apply H0. apply H1.
  Qed. 
    
    
(*might need equal lemma to ensure it is acyclic but we 
will see*)
End Forest.
     
     
     