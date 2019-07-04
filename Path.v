Require Import Graph.

Module PathTheories  (O: UsualOrderedType)(S: FSetInterface.Sfun O)(G: Graph O S).

  Module G := Graph.

  Import G.
  

  Inductive path : graph -> vertex -> vertex -> Prop :=
  | p_start : forall g u v,
    contains_edge g u v = true -> path g u v
  | p_continue: forall g u v w,
    path g u w ->
    contains_edge g w v = true ->
    path g u v.

  Inductive path' : graph -> vertex -> vertex -> Prop :=
  | p_start' : forall g u v,
    contains_edge g u v = true -> path' g u v
  | p_continue': forall g u v w,
    contains_edge g u w = true ->
    path' g w v ->
    path' g u v.

  Lemma path_trans: forall g u v w,
    path g u v ->
    path g v w ->
    path g u w.
  Proof.
    intros. induction H0.
    - eapply p_continue. apply H. apply H0.
    - eapply p_continue. apply IHpath. apply H. apply H1.
  Qed.

  Lemma path'_trans: forall g u v w,
    path' g u v ->
    path' g v w ->
    path' g u w.
  Proof.
    intros. induction H. 
    - eapply p_continue'. apply H. apply H0.
    - eapply p_continue'. apply H. apply IHpath'. apply H0. 
  Qed.

  Lemma path_path': forall g v u,
    path g u v <-> path' g u v.
  Proof.
    intros. split; intros H; induction H.
    - apply p_start'. apply H.
    - eapply path'_trans. apply IHpath. apply p_start'. apply H0.
    - apply p_start. apply H.
    - eapply path_trans. apply p_start. apply H. apply IHpath'.
Qed.

 (* Fixpoint path_list (g: graph) (u v : vertex) (l: list vertex) : bool :=
    match l with
    | nil => contains_edge g u v
    | w :: t => contains_edge g u w && path_list g w v t
    end.

  Definition eq_bool (a b : O.t) :=
    if O.eq_dec a b then true else false.

  Lemma path_iff_list: forall g u v,
    path g u v <-> exists l, path_list g u v l = true.
  Proof.
    intros. rewrite path_path'. split; intros.
    - induction H.
      + exists nil. simpl. apply H.
      + destruct IHpath'. exists (w :: x). simpl. rewrite H. rewrite H1. reflexivity.
    - destruct H. generalize dependent u. induction x; intros. 
      + simpl in H. apply p_start'. apply H.
      + simpl in H. rewrite andb_true_iff in H. destruct H.  eapply p_continue'.  apply H.
        apply IHx. apply H0.
  Qed.*)

  Inductive path_with: graph -> vertex -> vertex -> (vertex -> bool) -> Prop :=
    |  pw_start : forall g u v f,
      contains_edge g u v = true ->
      f v = true ->
      path_with g u v f
    | pw_continue: forall g u v w f,
      path_with g u w f ->
      f v = true ->
      contains_edge g w v = true ->
      path_with g u v f.

  Inductive path_list_ind: graph -> vertex -> vertex -> (vertex -> bool) -> list vertex -> Prop :=
    | pl_start : forall g u v f,
      contains_edge g u v = true ->
      f v = true ->
      path_list_ind g u v f nil
    | pl_continue: forall g u v w f l,
      path_list_ind g u w f l ->
      f v = true ->
      contains_edge g w v = true ->
      path_list_ind g u v f (w :: l).

Fixpoint path_list_rev (g: graph) (u v: vertex) (l: list vertex) : bool :=
  match l with
  | nil => G.contains_edge g u v
  | x :: tl => G.contains_edge g x v && path_list_rev g u x tl
  end.

Lemma path_list_ind_rev: forall g u v l f,
  path_list_ind g u v f l <-> (path_list_rev g u v l = true /\ (forall y, In y l -> f y = true) /\ f v = true).
Proof.
  intros. split; intros. induction H.
  - simpl in *. split. apply H. split. intros. destruct H1. apply H0.
  - simpl. destruct IHpath_list_ind. destruct H3. split. rewrite H1. rewrite H2. reflexivity.
    split. intros. destruct H5. subst. apply H4. apply H3. apply H5. apply H0.
  - generalize dependent v. induction l; intros.
    + destruct H. destruct H0. simpl in *. apply pl_start. apply H. apply H1.
    + simpl in *. apply pl_continue. apply IHl. destruct H. destruct H0. split. rewrite andb_true_iff in H.
      apply H. split. intros. apply H0. right. apply H2. apply H0. left. reflexivity. destruct H.
      destruct H0. apply H1. destruct H. rewrite andb_true_iff in H. destruct H. apply H.
Qed. 

  Lemma path_with_implies_path: forall g u v f,
    path_with g u v f ->
    path g u v.
  Proof.
    intros. induction H.
    - apply p_start. apply H.
    - eapply p_continue. apply IHpath_with. apply H1.
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