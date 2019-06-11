Require Import Graph.

Module PathTheories  (O: UsualOrderedType)(S: FSetInterface.Sfun O)(G: Graph O S).

  Module G := Graph.

  Import G.

  Inductive path : graph -> vertex -> vertex -> Prop :=
  | p_start : forall g u v,
    contains_edge g u v = true -> path g u v
  | p_continue: forall g u v w,
    contains_edge g u w = true ->
    path g w v ->
    path g u v.

  Fixpoint path_list (g: graph) (u v : vertex) (l: list vertex) : bool :=
    match l with
    | nil => contains_edge g u v
    | w :: t => contains_edge g u w && path_list g w v t
    end.

  Definition eq_bool (a b : O.t) :=
    if O.eq_dec a b then true else false.

  Lemma path_iff_list: forall g u v,
    path g u v <-> exists l, path_list g u v l = true.
  Proof.
    intros. split; intros.
    - induction H.
      + exists nil. simpl. apply H.
      + destruct IHpath. exists (w :: x). simpl. rewrite H. rewrite H1. reflexivity.
    - destruct H. generalize dependent u. induction x; intros. 
      + simpl in H. apply p_start. apply H.
      + simpl in H. rewrite andb_true_iff in H. destruct H.  eapply p_continue.  apply H.
        apply IHx. apply H0.
  Qed.

  Definition cycle_exists (g: graph) := exists v, path g v v.
 
  (*Is there a way to do this better without using law of excluded middle?*)
  Definition acyclic (g: graph) := forall v, ~path g v v.

  Lemma alt_acyclic: forall g,
    acyclic g <-> (forall u v, path g u v -> u <> v).
  Proof.
    intros. split; intros.
    - intro. subst. unfold acyclic in H. specialize (H v). contradiction.
    - unfold acyclic. intros. intro. apply H in H0. contradiction.
  Qed.


(*Let's see what we need later*)

End PathTheories.