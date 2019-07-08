Require Import Graph.
Require Import Helper.
Require Import Wellfounded.
Require Import Coq.Lists.ListDec.
Require Import Omega.


Module PathTheories  (O: UsualOrderedType)(S: FSetInterface.Sfun O)(G: Graph O S).

  Module G := Graph.

  Import G.

(*There are a lot of essentially equivalent definitions of being a path in here. The only ones I use
  are [path_list_ind] and [path_list_rev], which are also the most general, so we can get rid of the others*)
  

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

  Lemma path_path_list_rev: forall g u v,
    path g u v <-> (exists l, path_list_rev g u v l = true).
  Proof.
    intros. split; intros. induction H.
    - exists nil. simpl. apply H.
    - destruct_all. exists (w :: x). simpl. simplify.
    - destruct H. generalize dependent v. induction x; intros.
      + simpl in H. constructor. apply H.
      + simpl in H. simplify. eapply p_continue. apply IHx. apply H1. apply H0.
  Qed.

  Definition cyclic (g: graph) := exists v, path g v v.

  (*There is a cycle that does not consist only of a single vertex*)
  Definition nontrivial_cyclic (g: graph) := exists v l, (exists x, x <> v /\ In x l)
   /\ path_list_rev g v v l = true.

  Definition acyclic (g: graph):= ~ exists v, path g v v.

  Definition acyclic' (g: graph) := forall v, ~path g v v.

  Lemma acylic_no_nontrivial: forall g,
    acyclic g ->
    ~nontrivial_cyclic g.
  Proof.
   intros. intro.  unfold acyclic in H. unfold nontrivial_cyclic in H0. destruct_all.
    apply H. exists x. rewrite path_path_list_rev. exists x0. apply H1.
  Qed.

  Lemma acyclic_equiv: forall g,
    acyclic' g <-> acyclic g.
  Proof.
    intros. split; intros; unfold acyclic in *; unfold acyclic' in *. intro. destruct H0. apply (H x). apply H0.
    intros. intro. apply H. exists v. apply H0.
  Qed.

  Lemma alt_acyclic: forall g,
    acyclic g <-> (forall u v, path g u v -> u <> v).
  Proof.
    intros. split; intros.
    - intro. subst. unfold acyclic in H. apply H. exists v. apply H0.
    - unfold acyclic. intro. destruct H0. apply H in H0. contradiction.
  Qed.

(** ** Some results about paths **)
  Lemma path_app: forall g u v a l1 l2,
    path_list_rev g u v (l1 ++ a :: l2) = true <->
    path_list_rev g a v l1 = true /\ path_list_rev g u a l2 = true.
  Proof.
    intros. split; intros. generalize dependent v. generalize dependent l2. induction l1; intros.
    - simpl in H. simpl. rewrite andb_true_iff in H. apply H.
    - simpl in *. simplify; apply IHl1 in H1; destruct H1; assumption.
    - destruct_all. generalize dependent v. generalize dependent a. revert l2. induction l1; intros.
      + simpl in *. simplify.
      + simpl in *. simplify.
  Qed.

  (*If there is a path from u to v, then there is a path from u to v that does not contain u as an intermediate
    vertex*)
  Lemma path_start_unique: forall g u v l,
    path_list_rev g u v l = true ->
    exists l1, path_list_rev g u v l1 = true /\ ~In u l1.
  Proof.
    intros. destruct (in_dec O.eq_dec u l).
    - apply in_split_app_fst in i. destruct_all. rewrite H0 in H.
      apply path_app in H. destruct H. exists x. split. apply H.
      intro. apply H1 in H3. contradiction. apply O.eq_dec.
    - exists l. split; assumption.
  Qed. 
    
  Lemma path_implies_in_graph: forall g u v l,
    path_list_rev g u v l = true ->
    G.contains_vertex g u = true /\ G.contains_vertex g v = true /\ (forall x, In x l -> G.contains_vertex g x = true).
  Proof.
    intros. generalize dependent v. induction l; intros.
    - simpl in H. split. eapply G.contains_edge_1. apply H. split. eapply G.contains_edge_2. apply H.
      intros. inversion H0.
    - simpl in H. simplify. apply IHl in H1. simplify. eapply G.contains_edge_2. apply H0.
      simpl in H. destruct H. subst. eapply G.contains_edge_1. apply H0. apply IHl in H1.
      destruct_all. apply H3. apply H.
  Qed.


(* Results about cycle *)
Lemma any_cycle: forall g u v l,
  path_list_rev g u u l = true ->
  In v l ->
  exists l1, path_list_rev g v v l1 = true /\ In u l1 /\ (forall x, x <> u -> x <> v -> In x l <-> In x l1).
Proof.
  intros. apply in_split_app_fst in H0. destruct_all.
  rewrite H0 in H. apply path_app in H. destruct_all.
  exists (x0 ++ u :: x). split. eapply path_app; simplify.
  intros. split. solve_in. split; intros.  subst. apply in_app_or in H5. destruct H5. solve_in.
  simpl in H0. destruct H0. subst. contradiction. solve_in.
  subst. apply in_app_or in H5. destruct H5. solve_in. simpl in H0. destruct H0.
  subst. contradiction. solve_in.
  apply O.eq_dec.
Qed.

Lemma path_remove_cycle: forall g u v w l1 l2 l3,
  path_list_rev g u v (l1 ++ w :: l2 ++ w :: l3) = true ->
  path_list_rev g u v (l1 ++ w :: l3) = true.
Proof.
  intros. apply path_app in H. destruct_all. apply path_app in H0. destruct_all.
  apply path_app. simplify.
Qed.


Lemma path_no_end: forall g u v l,
  path_list_rev g u v l = true ->
  exists l, path_list_rev g u v l = true /\ ~In v l.
Proof.
  intros. destruct (in_dec O.eq_dec v l).
    - apply in_split_app_snd in i. destruct_all. rewrite H0 in H.
      apply path_app in H. destruct H. exists x0. split. apply H2.
      intro. apply H1 in H3. contradiction. apply O.eq_dec.
    - exists l. split; assumption.
Qed.




(*A crucial lemma for proving the correctness of cycle detection: If there is a cycle that does not
  consist solely of the same vertex, then there is a cycle with no duplicates*)
Lemma cycle_no_dups_strong: forall g u l,
  path_list_rev g u u l = true ->
  (exists w, In w l /\ w <> u) ->
  exists l1, path_list_rev g u u l1 = true /\ NoDup l1 /\ ~In u l1 /\ l1 <> nil /\ (forall x, In x l1 -> In x l).
Proof.
  intros. induction l using (well_founded_induction
                     (wf_inverse_image _ nat _ (@length _)
                        PeanoNat.Nat.lt_wf_0)). destruct_all. destruct l.
  inversion H0. destruct (In_dec O.eq_dec u (v ::l)).
  apply in_split_app_fst in i. destruct_all.
  rewrite H3 in H. apply path_app in H. destruct_all. rewrite H3 in H0.
  apply in_app_or in H0. destruct H0. 
  assert (exists l1 : list vertex,
       path_list_rev g u u l1 = true /\
       NoDup l1 /\ ~ In u l1 /\ l1 <> nil /\ (forall x : vertex, In x l1 -> In x x0)).
  apply H1. rewrite H3. rewrite app_length. simpl.
  assert (forall n m, n < n + S(m)). intros. omega. apply H6.
  apply H. exists x. split; assumption.
  destruct_all. exists x2. repeat(split; try(assumption)). intros. rewrite H3.
  apply H10 in H11. solve_in.
  simpl in H0. destruct H0. subst. contradiction. 
  assert ( exists l1 : list vertex,
       path_list_rev g u u l1 = true /\
       NoDup l1 /\ ~ In u l1 /\ l1 <> nil /\ (forall x : vertex, In x l1 -> In x x1)).
  apply (H1 x1). rewrite H3. rewrite app_length. simpl.
  assert (forall n m, n < m + S(n)). intros. omega. apply H6.
  apply H5. exists x. split; assumption. destruct_all.
  exists x2. repeat(split; try(assumption)). intros.
  apply H10 in H11. rewrite H3. solve_in. apply O.eq_dec.
  destruct (NoDup_dec (O.eq_dec) (v :: l)).
  exists (v :: l). split; try(split); try(assumption). split. apply n. split.
  intro. inversion H3. intros. apply H3.
  rewrite no_no_dup in n0. destruct_all. rewrite H3 in H.
  apply path_remove_cycle in H. rewrite H3 in H0. 
  rewrite H3 in n. assert (exists l1 : list vertex,
       path_list_rev g u u l1 = true /\
       NoDup l1 /\ ~ In u l1 /\ l1 <> nil /\ (forall x : vertex, In x l1 -> In x (x1 ++ x0 :: x3))).
  apply H1.  rewrite H3.
  repeat(rewrite app_length; simpl). omega. apply H. exists x0.
  split. solve_in. intro. subst. apply n. solve_in. destruct_all. exists x4.
  repeat(split; try(assumption)). intros. rewrite H3. apply H8 in H9.
  apply in_app_or in H9. simpl in H9. destruct H9. apply in_or_app. left. apply H9.
  destruct H9. subst. solve_in. solve_in.  apply O.eq_dec.
Qed. 
  


End PathTheories.