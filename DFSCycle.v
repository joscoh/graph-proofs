Require Import Graph.
Require Import Forest.
Require Import Coq.FSets.FMapInterface.
Require Import Coq.Lists.List.
Require Import Coq.FSets.FSetInterface.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.FSets.FSetProperties.
Require Import Omega.
Require Import Path.
Require Import Helper.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Program.Wf.
Require Import DFSSpec.
Require Import Coq.Init.Nat.
Require Import Coq.Logic.EqdepFacts.
Require Import DFS.
Require Import DerivedProofs.

(*In order to perform DFS, we need a lawful Graph (the input), Tree (the output), Set (for keeping
  track of the vertices not yet seen), Map (for storing discover/finish times), and UsualOrderedType
  (for the vertices). Also, we could use different sets for the Graph and Tree instances.*)
Module DFSCycle (O: UsualOrderedType)(M: FMapInterface.Sfun O) (S St: FSetInterface.Sfun O) (G: Graph O S)
            (F: Forest O S G).

Module P := FMapFacts.WProperties_fun O M.
Module P2 := FSetProperties.WProperties_fun O S.
Module O2 := OrderedTypeFacts O.
Module Pa := (Path.PathTheories O S G).
Module D := (DFS.DFS O M S St G F ).

Import D.

Definition state': Type := graph * forest * times_map * times_map * nat * S.t * S.t * stack * bool.

Definition get_state (s: state') : state :=
  match s with
    |(g, f, f_times, d_times, n, remain_d, remain_f, st, b) => (g, f, f_times, d_times, n, remain_d, remain_f, st)
  end.

  Definition check_back_edge (v : vertex) (g: graph) (remain_d remain_f: S.t) : bool :=
    match G.neighbors_set g v with
    | None => false
    | Some s => fold_right (fun x t => if O.eq_dec x v then t else 
                          if negb (S.mem x remain_d) && (S.mem x remain_f) then true else t) false (S.elements s)
    end.

Inductive dfs_step': state' -> state' -> Prop :=
  | dfs_discover_root' : forall g f f_times d_times time remain_d remain_f st x tl b,
    S.mem x remain_d = true ->
    (x, None) :: tl = start_new (pop_stack st remain_f) remain_d ->
    dfs_step' (g, f, f_times, d_times, time, remain_d, remain_f, st, b)
    (g, F.add_root f x, f_times, (M.add x (time + 1) d_times), (time + 1), (S.remove x remain_d), 
    remain_f, (add_to_stack x g remain_d) ++  ((x, None) :: tl), b || (check_back_edge x g remain_d remain_f))
    (*Discover a vertex: add all of its neighbors who have not been discovered to the stack,
      add it to the stack, add it to the discover times with the current time, and remove it from
      remain_d. We also add it to the forest as a new singleton tree*)
  | dfs_discover_child' : forall g f f_times d_times time remain_d remain_f st x y tl b,
    S.mem x remain_d = true ->
    (x, Some y) :: tl = start_new (pop_stack st remain_f) remain_d ->
    dfs_step' (g, f, f_times, d_times, time, remain_d, remain_f, st, b)
    (g, F.add_child f y x, f_times, (M.add x (time + 1) d_times), (time + 1), (S.remove x remain_d), 
    remain_f, (add_to_stack x g remain_d) ++  ((x, Some y) :: tl), b || (check_back_edge x g remain_d remain_f))
    (*The same as the previous except we add the vertex as a child of its parent in the tree*)
  | dfs_finish': forall g f f_times d_times time remain_d remain_f x o tl st b,
    S.mem x remain_d = false ->
    S.mem x remain_f = true ->
    (x, o) :: tl = start_new (pop_stack st remain_f) remain_d ->
    dfs_step' (g, f, f_times, d_times, time, remain_d, remain_f, st, b)
    (g,  f, (M.add x (time + 1) f_times), d_times, (time + 1), remain_d, (S.remove x remain_f), tl, b)
    (*Finish a vertex by adding it to finish_times whileremoving it from remain_f and the stack*).

(*If we ignore the cycle detection part, this is the same algorithm as before*)
Lemma dfs_step_equiv: forall s s',
  dfs_step' s s' -> 
  dfs_step (get_state s) (get_state s').
Proof.
  intros. inversion H; simpl in *.
  - apply dfs_discover_root; assumption. 
  - apply dfs_discover_child; assumption.
  - eapply dfs_finish; eassumption.
Qed. 

Definition start_state' (g: graph) (o: option vertex) : state' :=
  let init_stack := match o with
                    | None => nil
                    | Some v => if G.contains_vertex g v then (v, None) :: nil else nil
                    end in
  (g, F.empty, M.empty nat, M.empty nat, 0, (G.set_of_graph g), (G.set_of_graph g), init_stack, false).

Lemma start_state_equiv: forall g o,
  get_state (start_state' g o) = start_state g o.
Proof.
  intros. unfold start_state'. unfold start_state. simpl. reflexivity.
Qed.

Inductive valid_cycle_state: state' -> graph -> option vertex -> Prop :=
  | start': forall g o, valid_cycle_state (start_state' g o) g o
  | step': forall s1 s2 g o,
    valid_cycle_state s1 g o ->
    dfs_step' s1 s2 ->
    valid_cycle_state s2 g o.

Lemma valid_state_equiv: forall s g o,
  valid_cycle_state s g o ->
  valid_dfs_state (get_state s) g o.
Proof.
  intros. induction H.
  - rewrite start_state_equiv. apply start. 
  - eapply step. apply IHvalid_cycle_state. apply dfs_step_equiv. apply H0.
Qed.

Definition done' (s: state') :=
  S.is_empty (get_remain_d (get_state s)) && S.is_empty (get_remain_f (get_state s)).

Lemma done_equiv: forall s,
  done' s = done (get_state s).
Proof.
  intros. unfold done'. unfold done. reflexivity.
Qed.

Definition next_state' (s: state') : state' :=
  match s with
  | (g, f, f_times, d_times, time, remain_d, remain_f, st, b) =>
    match (start_new (pop_stack st remain_f) remain_d) with
    (*Impossible*)
    | nil => s
    | (x,o) :: tl =>
      if S.mem x remain_d then match o with
      | None => (g, F.add_root f x, f_times, M.add x (time + 1) d_times, time + 1,
                 S.remove x remain_d, remain_f, (add_to_stack x g remain_d ++ (x,None) :: tl),
                  b || (check_back_edge x g remain_d remain_f))
      | Some y => (g, F.add_child f y x, f_times, M.add x (time+1) d_times,
                                 time + 1, S.remove x remain_d, remain_f, (add_to_stack x g remain_d ++
                                  (x, Some y) :: tl), b || (check_back_edge x g remain_d remain_f))
                    
      end
      else if S.mem x remain_f then (g, f, M.add x (time + 1) f_times, d_times, time+1, remain_d, 
                                    S.remove x remain_f, tl, b)
      (*Impossible*)
      else s
    end
  end.

(*This function is equivalent to dfs_step for a valid state - basically the same proof as before*)
Lemma step_next_state': forall s g o,
  valid_cycle_state s g o ->
  done' s = false ->
  dfs_step' s (next_state' s).
Proof.
  intros. destruct s. destruct p. destruct p. destruct p. destruct p. destruct p. destruct p. destruct p.
  remember (g0, f, t2, t1, n, t0, t, s, b) as st. 
  destruct (start_new (pop_stack s t) t0) eqn : ?.
  - assert ( t=get_remain_f (get_state st)) by (subst; reflexivity). rewrite H1 in Heqs0.
    assert (t0 = get_remain_d (get_state st)) by (subst; reflexivity). rewrite H2 in Heqs0.
    assert (s = get_stack (get_state st)) by (subst; reflexivity). rewrite H3 in Heqs0.
    rewrite <- done_condition in Heqs0. rewrite <- done_equiv in Heqs0. rewrite Heqs0 in H0. inversion H0.
    apply valid_state_equiv. apply H.
  - unfold next_state'. rewrite Heqst. simpl. rewrite Heqs0. destruct p.
    destruct (S.mem t3 t0) eqn : ?.
    + destruct o0. apply dfs_discover_child'. assumption. symmetry. assumption.
      apply dfs_discover_root'. assumption. symmetry. apply Heqs0.
    + destruct (S.mem t3 t) eqn : ?.
      * eapply dfs_finish'. apply Heqb0. apply Heqb1. rewrite Heqs0. reflexivity.
      * destruct (pop_stack s t) eqn : ?.
        -- simpl in Heqs0. destruct (S.min_elt t0) eqn : ?.
          ++ inversion Heqs0; subst. apply S.min_elt_1 in Heqo1. apply S.mem_1 in Heqo1. 
             rewrite Heqo1 in Heqb0. inversion Heqb0.
          ++ inversion Heqs0.
        -- simpl in Heqs0; subst. inversion Heqs0; subst. apply pop_stack_cons in Heqs1.
           rewrite Heqs1 in Heqb1. inversion Heqb1.
Qed.

Definition dfs_multi' := multi dfs_step'.

Program Fixpoint cycle_exec (s: state') g o (H: valid_cycle_state s g o) {measure (measure_dfs (get_state s))} :
 {s' : state' | dfs_multi' s s' /\ done' s' = true}  :=
  if bool_dec (done' s) true then exist _ s _ else exist _ (proj1_sig (cycle_exec (next_state' s) g o _)) _.
Next Obligation.
split. apply multi_refl. apply H0.
Defined.
Next Obligation.
eapply step'. apply H. eapply step_next_state'. apply H. destruct (done' s). contradiction. reflexivity.
Defined.
Next Obligation.
apply step_measure_lt. apply dfs_step_equiv. eapply step_next_state'. apply H.
destruct (done' s). contradiction. reflexivity.
Defined.
Next Obligation.
destruct (  (cycle_exec (next_state' s) g o (cycle_exec_func_obligation_2 s g o H H0)
        (cycle_exec_func_obligation_3 s g o H H0))). destruct a; simpl in *.
split. eapply multi_trans. apply multi_R. eapply step_next_state'. apply H.
destruct (done' s). contradiction. reflexivity. apply d. apply e. 
Defined.

(*Now we need to prove the actual cycle detection*)
Definition back_edge' g u v o := exists s, valid_cycle_state s g o /\ u <> v /\
  M.find u (get_d_times (get_state s)) = Some (get_time (get_state s)) /\ 
   G.contains_edge g u v = true
   /\ gray (get_state s) v = true.

Definition get_bool (s: state') :=
  match s with
  |(_, _, _, _, _, _, _, _, b) => b
  end.

Lemma bool_stays_true: forall s s',
  get_bool s = true ->
  dfs_multi' s s' ->
  get_bool s' = true.
Proof.
  intros. induction H0.
  - apply H.
  - inversion H0; subst; simpl in *; subst; simplify.
Qed.

Lemma check_back_edge_find_back_edge: forall g v remain_d remain_f,
  check_back_edge v g remain_d remain_f = true <->
  exists x, G.contains_edge g v x = true /\ S.mem x remain_d = false /\ S.mem x remain_f = true /\ x <> v.
Proof.
  intros. unfold check_back_edge. assert (forall v s, fold_right
      (fun (x : O.t) (t : bool) =>
       if P2.FM.eq_dec x v then t else if negb (S.mem x remain_d) && S.mem x remain_f then true else t) false
      s = true <-> exists x, In x s /\ S.mem x remain_d = false /\ S.mem x remain_f = true /\ x <> v). {
      - intros; split; intros.
        + induction s; simpl in *.
          * inversion H.
          * destruct (P2.FM.eq_dec a v0).
            -- apply IHs in H. destruct_all. exists x. simplify. 
            -- destruct (negb (S.mem a remain_d) && S.mem a remain_f) eqn : ?.
               ++ simplify. exists a. simplify.
               ++ apply IHs in H. destruct_all. exists x. simplify.
         + induction s; simpl in *; destruct_all.
            * destruct H. 
            * destruct (P2.FM.eq_dec a v0).
              -- unfold O.eq in e. subst. destruct H. subst. contradiction.
                  apply IHs. exists x. simplify.
              -- destruct (negb (S.mem a remain_d) && S.mem a remain_f) eqn : ?. reflexivity.
                 destruct H; subst. rewrite H0 in Heqb. rewrite H1 in Heqb. inversion Heqb.
                 apply IHs. exists x. simplify. }
  split; intros.
  - destruct (G.neighbors_set g v) eqn : ?.
    + apply H in H0. destruct_all. exists x. simplify. apply In_InA_equiv in H0. apply S.elements_2 in H0.
      rewrite <- G.neighbors_set_2 in H0. apply H0. apply Heqo.
    + inversion H0.
  - destruct (G.neighbors_set g v) eqn : ?.
    + rewrite H. destruct_all. exists x. split. rewrite In_InA_equiv. apply S.elements_1.
      rewrite G.neighbors_set_2 in H0. apply H0. apply Heqo. simplify.
    + destruct_all. apply G.neighbors_set_1 in Heqo. apply G.neighbors_list_1 in Heqo.
      apply G.contains_edge_1 in H0. rewrite Heqo in H0. inversion H0.
Qed.

Lemma bool_becomes_true: forall s g o s',
  valid_cycle_state s g o ->
  get_bool s = false ->
  dfs_step' s s' ->
  get_bool s' = true ->
  exists u v, back_edge' g u v o.
Proof.
  intros. unfold back_edge'. inversion H1; subst; simpl in *; subst; simpl in H2.
  - apply check_back_edge_find_back_edge in H2. destruct_all. exists x. exists x0.
    remember (g0, F.add_root f x, f_times, M.add x (time + 1) d_times, time + 1, S.remove x remain_d, remain_f,
       add_to_stack x g0 remain_d ++ (x, None) :: tl, false || check_back_edge x g0 remain_d remain_f) as s.
    exists s. simplify. eapply step'. apply H. apply H1. subst. simpl. simplify. assert (g = g0).
    assert (g0 = get_graph (get_state s)) by (subst; reflexivity). rewrite H7. symmetry. eapply graph_constant.
    apply valid_state_equiv. eapply step'. apply H. apply H1. subst. apply H0.
    unfold gray. subst; simpl. simplify. rewrite P2.Dec.F.remove_b. simplify.
  - apply check_back_edge_find_back_edge in H2. destruct_all. exists x. exists x0.
    remember (g0, F.add_child f y x, f_times, M.add x (time + 1) d_times, time + 1, S.remove x remain_d, remain_f,
       add_to_stack x g0 remain_d ++ (x, Some y) :: tl, false || check_back_edge x g0 remain_d remain_f) as s.
    exists s. simplify. eapply step'. apply H. apply H1. subst. simpl. simplify. assert (g = g0).
    assert (g0 = get_graph (get_state s)) by (subst; reflexivity). rewrite H7. symmetry. eapply graph_constant.
    apply valid_state_equiv. eapply step'. apply H. apply H1. subst. apply H0.
    unfold gray. subst; simpl. simplify. rewrite P2.Dec.F.remove_b. simplify.
  - inversion H2.
Qed.

Lemma bool_true_multi: forall s g o s',
  valid_cycle_state s g o ->
  get_bool s = false ->
  dfs_multi' s s' ->
  get_bool s' = true ->
  exists u v, back_edge' g u v o.
Proof.
  intros. induction H1.
  - rewrite H0 in H2. inversion H2.
  - destruct (get_bool y) eqn : ?.
    eapply bool_becomes_true. apply H. apply H0. apply H1. apply Heqb.
    apply IHmulti. eapply step'. apply H. apply H1. reflexivity. apply H2.
Qed.

Lemma valid_begins_with_start': forall s g o,
  valid_cycle_state s g o ->
  dfs_multi' (start_state' g o) s.
Proof.
  intros. induction H.
  - constructor.
  - eapply multi_trans. apply IHvalid_cycle_state. eapply multi_step. apply H0. apply multi_refl.
Qed.

Lemma true_implies_back_edge: forall s g o,
  valid_cycle_state s g o ->
  get_bool s = true ->
  exists u v, back_edge' g u v o.
Proof.
  intros. apply valid_begins_with_start' in H.
  eapply bool_true_multi. apply start'. simpl. reflexivity. apply H. apply H0.
Qed.

(*TODO: see: might not need all of this*)
Lemma time_plus_one': forall s s',
  dfs_step' s s' ->
  get_time (get_state s) + 1 = get_time (get_state s').
Proof.
  intros. inversion H; subst; simpl in *; try(omega).
Qed.

Lemma time_incr_step': forall s s',
  dfs_step' s s' ->
  get_time (get_state s) < get_time (get_state s').
Proof.
  intros. rewrite <- (time_plus_one' _ _ H). omega.
Qed.

Lemma time_incr_multi': forall s s',
  dfs_multi' s s' ->
  s = s' \/ get_time (get_state s) < get_time (get_state s').
Proof.
  intros. induction H.
  - left. reflexivity.
  - destruct IHmulti. inversion H1; subst. right. apply time_incr_step'. apply H.
    right. apply time_incr_step' in H. omega.
Qed. 

Lemma dfs_step_deterministic' : forall s1 s2 s,
  dfs_step' s s1 -> dfs_step' s s2 -> s1 = s2.
Proof.
  intros. inversion H; subst; simpl in *.
  - inversion H0; subst; simpl in *.
    + rewrite <- H14 in H2. inversion H2; subst. reflexivity.
    + rewrite <- H14 in H2. inversion H2.
    + rewrite <- H15 in H2. inversion H2; subst. rewrite H13 in H1. inversion H1.
  - inversion H0; subst; simpl in *.
    + rewrite <- H14 in H2. inversion H2.
    + rewrite <- H14 in H2. inversion H2; subst. reflexivity.
    + rewrite <- H15 in H2. inversion H2; subst. rewrite H13 in H1. inversion H1.
  - inversion H0; subst; simpl in *.
    + rewrite <- H15 in H3. inversion H3; subst. rewrite H14 in H1. inversion H1.
    + rewrite <- H15 in H3. inversion H3; subst. rewrite H14 in H1. inversion H1.
    + rewrite <- H16 in H3. inversion H3; subst. reflexivity.
Qed.

Lemma multi_from_start': forall s s' s'',
  dfs_multi' s s'' ->
  dfs_multi' s s' ->
  (dfs_multi' s' s'' \/ dfs_multi' s'' s').
Proof.
  intros. generalize dependent s'. induction H; intros.
  - right. apply H0.
  - inversion H1; subst.
    + left. eapply multi_step. apply H. apply H0.
    + assert (y=y0). eapply dfs_step_deterministic'.
      apply H. apply H2. subst. apply IHmulti. apply H3.
Qed.

Lemma times_unique': forall s s' g o,
  valid_cycle_state s g o ->
  valid_cycle_state s' g o ->
  get_time (get_state s) = get_time (get_state s') ->
  s = s'.
Proof.
  intros. assert (A:=H0). assert (B:=H).  apply valid_begins_with_start' in A.
   apply valid_begins_with_start' in B. pose proof (multi_from_start' _ _ _ A B).
  destruct H2; apply time_incr_multi' in H2; destruct H2; try(subst; reflexivity); try(omega).
Qed.

Lemma multi_equiv: forall s s',
  dfs_multi' s s' ->
  dfs_multi (get_state s) (get_state s').
Proof.
  intros. induction H.
  - apply multi_refl.
  - eapply multi_step. eapply dfs_step_equiv. apply H. apply IHmulti.
Qed.

Lemma multistep_preserves_valid': forall s s' g o,
  valid_cycle_state s g o ->
  dfs_multi' s s' ->
  valid_cycle_state s' g o.
Proof.
  intros. induction H0.
  - assumption.
  - apply IHmulti. eapply step'. apply H. apply H0.
Qed.

(*If there is a back edge, then when we discover that vertex, the boolean will be true*)
Lemma visit_at_time_back_edge_gives_true: forall u v s g o,
  back_edge' g u v o ->
  valid_cycle_state s g o ->
  M.find u (get_d_times (get_state s)) = Some (get_time (get_state s)) ->
  get_bool s = true.
Proof.
  intros. induction H0; subst; simpl in *; subst.
  - rewrite P.F.empty_o in H1. inversion H1.
  - inversion H2; subst; simpl in *; subst.
    + destruct b. reflexivity. simpl.
      destruct (O.eq_dec u x).
      * unfold O.eq in e. subst. unfold back_edge' in H.
        destruct_all. remember (g0, F.add_root f x, f_times, M.add x (time + 1) d_times, time + 1, S.remove x remain_d, remain_f,
       add_to_stack x g0 remain_d ++ (x, None) :: tl, false || check_back_edge x g0 remain_d remain_f) as s.
        assert (time + 1 = get_time (get_state x0)). { 
        assert (M.find x (get_d_times (get_state s)) = Some (time + 1)) by (subst; simpl; assumption).
        pose proof (multi_from_start' (start_state' g o) s x0).
        assert (dfs_multi' s x0 \/ dfs_multi' x0 s). apply H10. apply valid_begins_with_start'. apply H.
        apply valid_begins_with_start'. eapply step'. apply H0. apply H2. destruct H11.
        eapply discovery_time_constant in H9. rewrite H9 in H6. inversion H6; subst. reflexivity.
        apply valid_state_equiv. eapply step'. apply H0. apply H2. apply multi_equiv. apply H11.
        eapply discovery_time_constant in H6. rewrite H6 in H9. inversion H9; subst; reflexivity.
        apply valid_state_equiv. apply H. apply multi_equiv. apply H11. }
        assert (s = x0). eapply times_unique'. eapply step'. apply H0. apply H2. apply H. subst. simpl. apply H9.
        subst. simpl in *. rewrite check_back_edge_find_back_edge. exists v. unfold gray in H8; simpl in *.
        simplify. remember (g0, f, f_times, d_times, time, remain_d, remain_f, st, false) as s.
         assert (g0 = get_graph (get_state s)) by (subst; reflexivity). assert (g = g0). rewrite H8. symmetry.
        eapply graph_constant. apply valid_state_equiv. apply H0. subst. apply H7.
        rewrite P2.FM.remove_neq_b in H10. apply H10. auto. 
      * rewrite P.F.add_neq_o in H1. remember (g0, f, f_times, d_times, time, remain_d, remain_f, st, false) as s.
        assert (M.find u (get_d_times (get_state s)) = Some (time + 1)) by (subst; simpl; assumption).
        eapply d_times_leq_current_time in H5. subst; simpl in *. omega. apply valid_state_equiv. apply H0.
        auto.
    + destruct b. reflexivity. simpl.
      destruct (O.eq_dec u x).
      * unfold O.eq in e. subst. unfold back_edge' in H.
        destruct_all. remember (g0, F.add_child f y x, f_times, M.add x (time + 1) d_times, time + 1, S.remove x remain_d, remain_f,
       add_to_stack x g0 remain_d ++ (x, Some y) :: tl, false || check_back_edge x g0 remain_d remain_f) as s.
        assert (time + 1 = get_time (get_state x0)). { 
        assert (M.find x (get_d_times (get_state s)) = Some (time + 1)) by (subst; simpl; assumption).
        pose proof (multi_from_start' (start_state' g o) s x0).
        assert (dfs_multi' s x0 \/ dfs_multi' x0 s). apply H10. apply valid_begins_with_start'. apply H.
        apply valid_begins_with_start'. eapply step'. apply H0. apply H2. destruct H11.
        eapply discovery_time_constant in H9. rewrite H9 in H6. inversion H6; subst. reflexivity.
        apply valid_state_equiv. eapply step'. apply H0. apply H2. apply multi_equiv. apply H11.
        eapply discovery_time_constant in H6. rewrite H6 in H9. inversion H9; subst; reflexivity.
        apply valid_state_equiv. apply H. apply multi_equiv. apply H11. }
        assert (s = x0). eapply times_unique'. eapply step'. apply H0. apply H2. apply H. subst. simpl. apply H9.
        subst. simpl in *. rewrite check_back_edge_find_back_edge. exists v. unfold gray in H8; simpl in *.
        simplify. remember (g0, f, f_times, d_times, time, remain_d, remain_f, st, false) as s.
         assert (g0 = get_graph (get_state s)) by (subst; reflexivity). assert (g = g0). rewrite H8. symmetry.
        eapply graph_constant. apply valid_state_equiv. apply H0. subst. apply H7.
        rewrite P2.FM.remove_neq_b in H10. apply H10. auto. 
      * rewrite P.F.add_neq_o in H1. remember (g0, f, f_times, d_times, time, remain_d, remain_f, st, false) as s.
        assert (M.find u (get_d_times (get_state s)) = Some (time + 1)) by (subst; simpl; assumption).
        eapply d_times_leq_current_time in H5. subst; simpl in *. omega. apply valid_state_equiv. apply H0.
        auto.
    + remember (g0, f, f_times, d_times, time, remain_d, remain_f, st, b) as s.
        assert (M.find u (get_d_times (get_state s)) = Some (time + 1)) by (subst; simpl; assumption).
        eapply d_times_leq_current_time in H6. subst; simpl in *. omega. apply valid_state_equiv. apply H0.
Qed.

Lemma discovery_time_means_discovered': forall s g o v n,
  valid_cycle_state s g o->
  M.find v (get_d_times (get_state s)) = Some n ->
  (exists s', dfs_multi' s' s /\ n = get_time (get_state s') /\ valid_cycle_state s' g o /\
   M.find v (get_d_times (get_state s')) = Some n).
Proof.
  intros. induction H; subst; simpl in *. 
  - rewrite P.F.empty_o in H0. inversion H0.
  - inversion H1; subst; simpl in *.
     + destruct (O.eq_dec v x).
      * unfold O.eq in e. subst. rewrite P.F.add_eq_o in H0. inversion H0; subst. 
        exists (g0, F.add_root f x, f_times, M.add x (time + 1) d_times, time + 1, S.remove x remain_d, remain_f,
       add_to_stack x g0 remain_d ++ (x, None) :: tl, b || check_back_edge x g0 remain_d remain_f).
        split. apply multi_refl. simpl. split. reflexivity. split. eapply step'. apply H. apply H1.
        rewrite P.F.add_eq_o. reflexivity. reflexivity. reflexivity.
      * rewrite P.F.add_neq_o in H0. apply IHvalid_cycle_state in H0. destruct_all. exists x0.
        split. eapply multi_trans. apply H0. apply multi_R. apply H1. split. apply H4. split. apply H5.
         apply H6. intuition. 
    + destruct (O.eq_dec v x).
      * unfold O.eq in e. subst. rewrite P.F.add_eq_o in H0. inversion H0; subst. 
        exists (g0, F.add_child f y x, f_times, M.add x (time + 1) d_times, time + 1, S.remove x remain_d, remain_f,
       add_to_stack x g0 remain_d ++ (x, Some y) :: tl, b || check_back_edge x g0 remain_d remain_f).
        split. apply multi_refl. simpl. split. reflexivity. split. eapply step'. apply H. apply H1.
        rewrite P.F.add_eq_o. reflexivity. reflexivity. reflexivity.
      * rewrite P.F.add_neq_o in H0. apply IHvalid_cycle_state in H0. destruct_all. exists x0.
        split. eapply multi_trans. apply H0. apply multi_R. apply H1. split. apply H4. split. apply H5.
         apply H6. intuition. 
    + apply IHvalid_cycle_state in H0. destruct_all. exists x0. split. eapply multi_trans.
      apply H0. apply multi_R. apply H1. split. apply H5. split. apply H6. apply H7.
Qed.

Lemma back_edge_implies_true: forall s g o,
  (exists u v, back_edge' g u v o) ->
  done' s = true ->
  valid_cycle_state s g o ->
  get_bool s = true.
Proof.
  intros. destruct_all. assert (A:= H). unfold back_edge' in H. destruct_all.
  assert (dfs_multi' x1 s \/ dfs_multi' s x1). eapply multi_from_start'. apply valid_begins_with_start'.
  apply H1. apply valid_begins_with_start'. apply H. destruct H6.
  eapply bool_stays_true. eapply visit_at_time_back_edge_gives_true. apply A.
  apply H. apply H3. apply H6. rewrite done_equiv in H0. apply multi_equiv in H6.
  inversion H6. subst. pose proof (all_times_when_done (get_state x1) g o x).
   assert (valid_dfs_state (get_state x1) g o). apply valid_state_equiv. apply H.
  assert (G.contains_vertex g x = true). eapply discovered_vertices_in_graph. 
  apply H8. apply H3. rewrite H9 in H0. specialize (H7 H8 H0 H10). destruct_all.
  rewrite H7 in H3. inversion H3; subst. 
  assert ((get_time (get_state x1)) < x2). eapply discover_before_finish.
  apply valid_state_equiv. apply H. apply H7. apply H11.
  eapply f_times_leq_current_time in H11. omega. apply valid_state_equiv. apply H.
  subst. pose proof (done_cannot_step (get_state s) g o ). exfalso. apply H9.
  apply valid_state_equiv. apply H1. apply H0. exists y. apply H7.
Qed.

Lemma back_edge_iff_true: forall s g o,
  valid_cycle_state s g o ->
  done' s = true ->
  (exists u v, back_edge' g u v o) <-> get_bool s = true.
Proof.
  intros. split; intros. eapply back_edge_implies_true; eassumption.
  eapply true_implies_back_edge; eassumption.
Qed.
(** ** Instantiating the [DFSBase] interface **)

Module DFSWithCycleDetectBase <: (DFSSpec.DFSBase O S G F).

  Module P := D.Pa.

  (*TODO: come up with ways of not copying this*)
Definition times_function := G.vertex -> nat.

  Definition end_state (g: G.graph) o := cycle_exec (start_state' g o) g o (start' g o).

  Definition dfs_forest o (g: G.graph) : F.forest := 
    get_forest (get_state (proj1_sig (end_state g o))).

  Definition state o (g: graph) := {s : state' | valid_cycle_state s g o} .

  Definition f_time o (g: graph) (v: vertex) : nat :=
    match M.find v (get_f_times (get_state (proj1_sig (end_state g o)))) with
    | Some n => n
    | None => 0
    end.

  Definition d_time o (g: graph) (v: vertex) : nat :=
    match M.find v (get_d_times ( get_state (proj1_sig (end_state g o)))) with
    | Some n => n
    | None => 0
    end.

  Definition dfs : option G.vertex -> G.graph -> (F.forest *  times_function * times_function)
   := fun  (o: option vertex)(g: G.graph) => ((dfs_forest o g) , (d_time o g) , (f_time o g)).

  Definition time_of_state o (g: graph) (s: state o g) := get_time (get_state (proj1_sig s)).

  Lemma discovery_exists: forall o g v,
    G.contains_vertex g v = true ->
    exists (s: state o g), time_of_state o g s = d_time o g v.
  Proof.
    intros. unfold d_time. unfold time_of_state. destruct (end_state g o).
    destruct_all; simpl in *. 
    assert (valid_cycle_state x g o). eapply multistep_preserves_valid'. apply start'.
    apply d. assert (valid_dfs_state (get_state x) g o). eapply valid_state_equiv. apply H0.
    pose proof (all_times_when_done (get_state x) g o v H1 e H). destruct_all.
    pose proof (discovery_time_means_discovered' x g o v x1 H0 H2). destruct_all.
    exists (exist _ x2 H6). simpl. rewrite H2. symmetry. apply H5.
  Qed.

  Definition white o g (s: state o g)(v: G.vertex) : bool :=
    ltb (time_of_state o g s) (d_time o g v).

  Lemma white_def: forall o g s v,
    white o g s v = true <-> ltb (time_of_state o g s) (d_time o g v) = true.
  Proof.
    intros. unfold white. reflexivity.
  Qed.

  Definition gray o g (s: state o g)(v: G.vertex): bool :=
    ltb (time_of_state o g s) (f_time o g v) && leb (d_time o g v) (time_of_state o g s).

  Lemma gray_def: forall o g s v,
    gray o g s v = true <-> 
    ltb (time_of_state o g s) (f_time o g v) && leb (d_time o g v) (time_of_state o g s) = true.
  Proof. unfold gray. reflexivity. Qed.

  Definition black o g (s:state o g)(v: G.vertex) : bool :=
    leb (f_time o g v) (time_of_state o g s).

  Lemma black_def: forall o g s v,
    black o g s v = true <-> leb (f_time o g v) (time_of_state o g s) = true.
  Proof. unfold black. reflexivity. Qed.

  Lemma state_time_unique: forall g o (s s': state o g),
    time_of_state o g s = time_of_state o g s' <-> s = s'.
  Proof. 
    intros. unfold state in *. destruct s. destruct s'. simpl in *. unfold time_of_state; simpl in *.
    split; intros. eapply times_unique' in H. subst. apply ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat.
    reflexivity. apply v. apply v0. apply EqdepFacts.eq_sig_eq_dep in H. rewrite <- eq_sigT_iff_eq_dep in H.
    apply eq_sigT_fst in H. subst. reflexivity.
  Qed.
 
  Lemma d_time_equiv: forall o g u,
    G.contains_vertex g u = true ->
    M.find u (get_d_times (get_state (proj1_sig (end_state g o)))) = Some (d_time o g u).
  Proof.
    intros.
    unfold d_time. destruct (end_state g o); destruct_all; simpl in *. 
    destruct (M.find u (get_d_times (get_state x))) eqn : ?.
    - reflexivity.
    - assert (valid_dfs_state (get_state x) g o). eapply valid_state_equiv. eapply multistep_preserves_valid'.
      apply start'. apply d.  pose proof (all_times_when_done _ _ _ _ H0 e H).
      destruct_all. rewrite H1 in Heqo0. inversion Heqo0.
  Qed.

  Lemma f_time_equiv: forall o g u,
    G.contains_vertex g u = true ->
    M.find u (get_f_times (get_state (proj1_sig (end_state g o)))) = Some (f_time o g u).
  Proof.
    intros.
    unfold f_time. destruct (end_state g o); destruct_all; simpl in *. 
    destruct (M.find u (get_f_times (get_state x))) eqn : ?.
    - reflexivity.
    - assert (valid_dfs_state (get_state x) g o). eapply valid_state_equiv. eapply multistep_preserves_valid'.
      apply start'. apply d.  pose proof (all_times_when_done _ _ _ _ H0 e H).
      destruct_all. rewrite H2 in Heqo0. inversion Heqo0.
  Qed.

  (* Some needed results about uniqueness of times *)
  Lemma d_times_unique: forall o g u v,
    G.contains_vertex g u = true ->
    G.contains_vertex g v = true ->
    d_time o g u = d_time o g v <-> u = v.
  Proof.
    split; intros. pose proof (d_time_equiv o g u H). pose proof (d_time_equiv o g v H0).
    destruct (end_state g o); destruct_all; simpl in *. eapply d_times_unique. apply valid_state_equiv.
    eapply multistep_preserves_valid'. apply start'. apply d. apply H3. apply H2.
    omega. subst. reflexivity.
  Qed.

  Lemma f_times_unique: forall o g u v,
    G.contains_vertex g u = true ->
    G.contains_vertex g v = true ->
    f_time o g u = f_time o g v <-> u = v.
  Proof.
    split; intros. pose proof (f_time_equiv o g u H). pose proof (f_time_equiv o g v H0).
    destruct (end_state g o); destruct_all; simpl in *. eapply f_times_unique. apply valid_state_equiv.
    eapply multistep_preserves_valid'. apply start'. apply d. apply H3. apply H2.
    omega. subst. reflexivity.
  Qed.

  Lemma all_times_unique:
    forall o g u v,
    G.contains_vertex g u = true ->
    G.contains_vertex g v = true ->
    f_time o g u <> d_time o g v.
  Proof.
    intros. intro. unfold f_time in *. unfold d_time in *. 
    destruct_all. eapply (f_time_equiv o g u) in H. apply (d_time_equiv o g v) in H0.
    remember end_state as e. destruct e; simpl in *. rewrite H in H1.
    rewrite H0 in H1. subst. rewrite H1 in H. eapply all_times_unique. apply valid_state_equiv.
    eapply multistep_preserves_valid'.
    apply start'. apply a. apply H0. apply H. 
  Qed. 

  (*Major Results*)
  Theorem parentheses_theorem: forall o g u v,
    G.contains_vertex g u = true ->
    G.contains_vertex g v = true ->
    u <> v ->
    (d_time o g u < d_time o g v /\ d_time o g v < f_time o g v /\ f_time o g v < f_time o g u) \/
    (d_time o g v < d_time o g u /\ d_time o g u < f_time o g u /\ f_time o g u < f_time o g v) \/
    (d_time o g u < f_time o g u /\ f_time o g u < d_time o g v /\ d_time o g v < f_time o g v) \/
    (d_time o g v < f_time o g v /\ f_time o g v < d_time o g u /\ d_time o g u < f_time o g u).
  Proof.
    intros. unfold d_time. unfold f_time. destruct (end_state g o); destruct_all; simpl in *. 
    assert (valid_dfs_state (get_state x) g o). eapply valid_state_equiv. eapply multistep_preserves_valid'.
    apply start'. apply d. pose proof (all_times_when_done _ _ _ _ H2 e H).
    pose proof (all_times_when_done _ _ _ _ H2 e H0). destruct_all. rewrite H3.
    rewrite H4. rewrite H5. rewrite H6. pose proof (parentheses_theorem
    _ _ _ _ _ _ _ _ _ H2 H1 H3 H4 H6 H5). omega.
  Qed.
  

  Lemma descendant_iff_interval: forall o g u v,
    G.contains_vertex g u = true ->
    G.contains_vertex g v = true ->
    F.desc (dfs_forest o g) u v <->
     (d_time o g u < d_time o g v /\ d_time o g v < f_time o g v /\ f_time o g v < f_time o g u).
  Proof.
    intros. unfold dfs_forest. unfold d_time. unfold f_time. destruct (end_state g o). simpl in *.
    destruct_all. assert (valid_dfs_state (get_state x) g o). eapply valid_state_equiv.
     eapply multistep_preserves_valid'.
    apply start'. apply H1. pose proof (all_times_when_done _ _ _ _ H3 H2 H).
    pose proof (all_times_when_done _ _ _ _ H3 H2 H0). destruct_all. rewrite H4.
    rewrite H5. rewrite H6. rewrite H7. eapply desc_iff_time_interval; try(eassumption).
  Qed.

  (*Proves that the version of white in the interface (referencing only finish times) is equivalent to
    the other set based definition*)
  Lemma white_equiv: forall o g (s: state o g) v,
    G.contains_vertex g v = true ->
    white o g s v = true <-> D.white (get_state (proj1_sig s)) v = true.
  Proof.
    intros. assert (A:= H). apply (d_time_equiv o) in A. split; intros.
    - unfold white in H0. unfold time_of_state in H0. unfold d_time in H0.
      destruct s; simpl in *. destruct (end_state g o); simpl in *. destruct_all.
      rewrite A in H0. rewrite Nat.ltb_lt in H0. unfold D.white.
      assert (S.mem v (get_remain_d (get_state x)) = true). destruct (S.mem v (get_remain_d (get_state x))) eqn : ?.
      reflexivity. rewrite v_discovered_iff_not_remain in Heqb. destruct Heqb.
      assert (dfs_multi (get_state x) (get_state x0)). assert (B:= v0). assert (valid_dfs_state (get_state x0) g o).
      apply valid_state_equiv. eapply multistep_preserves_valid'. apply start'. apply H1.
      assert (C:= H4). apply valid_begins_with_start in H4.
      apply valid_state_equiv in v0.  apply valid_begins_with_start in v0.
      pose proof (multi_from_start _ _ _ v0 H4). destruct H5. 
      inversion H5. subst. apply multi_refl. subst. 
      exfalso. eapply done_cannot_step. apply C. apply H2. exists y. apply H6. apply H5.
      assert (B:= H3). eapply discovery_time_constant in H3. rewrite H3 in A. inversion A; subst.
      assert (C:= B). eapply d_times_leq_current_time in B.  omega. apply valid_state_equiv.
      apply v0. apply valid_state_equiv. apply v0. apply H4. apply valid_state_equiv. apply v0. apply H.
      rewrite H3. eapply not_f_if_not_d in H3. rewrite H3. reflexivity. apply valid_state_equiv. apply v0.
    - unfold white. destruct s; simpl in *. destruct (end_state g o); simpl in *. unfold time_of_state. simpl.
      destruct_all. assert (valid_dfs_state (get_state x0) g o). apply valid_state_equiv.
       eapply multistep_preserves_valid'. apply start'.
      apply H1. unfold D.white in H0. destruct (get_time (get_state x) <? d_time o g v) eqn : ?.
      reflexivity. rewrite Nat.ltb_antisym in Heqb. simplify.
      assert (M.find v (get_d_times (get_state x)) = None). apply valid_state_equiv in v0. pose proof (v_discovered_iff_not_remain
      _ _ _ _ v0 H). destruct H0. apply contrapositive in H6. 
      destruct (M.find v (get_d_times (get_state x))) eqn : ?. exfalso. apply H6.
      exists n. reflexivity. reflexivity. rewrite H4. intro. inversion H7.
      rewrite Nat.leb_le in Heqb. 
      pose proof (discovery_time_means_discovered _ _ _ _ _ H3 A). destruct_all.
      rewrite H7 in Heqb. rewrite H7 in H9. 
      assert (get_time x1 = get_time (get_state x) \/ get_time x1 < get_time (get_state x)) by omega.
      destruct H10. assert (x1 = get_state x). eapply times_unique; try(eassumption). apply valid_state_equiv.
      apply v0. subst.
      rewrite H9 in H0. inversion H0. 
      assert (dfs_multi x1 (get_state x)). assert (J:= H8). assert (K:= v0). eapply valid_begins_with_start in J.
      apply valid_state_equiv in K.
      eapply valid_begins_with_start in K. pose proof (multi_from_start _ _ _ J K). destruct H11.
      apply time_incr_multi in H11. destruct H11; subst; omega. apply H11.
      eapply discovery_time_constant in H9. rewrite H9 in H0. inversion H0. apply H8.
      apply H11.
  Qed.

  Theorem white_path_equiv: forall o u v l g s,
    Pa.path_list_ind g u v (fun x => white o g s x) l <->
    Pa.path_list_ind g u v (fun x => D.white (get_state(proj1_sig s)) x) l.
  Proof.
    intros. split; intros. 
    - remember (fun x : G.vertex => white o g s x) as f.  induction H; subst.
      + constructor. apply H. rewrite <- white_equiv. apply H0. eapply G.contains_edge_2. apply H.
      + constructor. apply IHpath_list_ind. reflexivity. rewrite <- white_equiv. apply H0. 
        eapply G.contains_edge_2. apply H1. apply H1.
    - remember (fun x : G.vertex => D.white (get_state (proj1_sig s)) x) as f. induction H; subst.
      + constructor. apply H. rewrite white_equiv. apply H0. eapply G.contains_edge_2. apply H.
      + constructor. apply IHpath_list_ind. reflexivity. rewrite white_equiv. apply H0. 
        eapply G.contains_edge_2. apply H1. apply H1.
  Qed.

  Theorem white_path_theorem: forall o g u v,
    G.contains_vertex g u = true ->
    F.desc (dfs_forest o g) u v <-> (forall s, time_of_state o g s = d_time o g u ->
    exists l, P.path_list_ind g u v (fun x => white o g s x) l).
  Proof.
    intros. setoid_rewrite white_path_equiv. unfold dfs_forest. unfold d_time. destruct (end_state g o); simpl in *.
    destruct_all. assert (valid_dfs_state (get_state x) g o). apply valid_state_equiv. eapply multistep_preserves_valid'.
    apply start'. apply H0. unfold time_of_state. simpl. split; intros. destruct s; simpl in *.
    - apply (d_time_equiv o) in H.
      destruct (end_state g o); simpl in *. destruct_all. assert (get_state x1 = get_state x).
      eapply done_unique. eapply valid_state_equiv. eapply multistep_preserves_valid'. apply start'.
      apply H5. apply H2. rewrite <- done_equiv. apply H6. rewrite <- done_equiv. apply H1.
      subst. rewrite <- H7 in H4. rewrite H in H4. rewrite H7 in H. pose proof (discovery_time_means_discovered _ _ _ _ _ H2 H).
      destruct_all. rewrite H9 in H. rewrite H9 in H11. 
      assert (x2 = get_state x0). eapply times_unique. apply H10. apply valid_state_equiv. apply v0.
      rewrite H4. symmetry. apply H9. subst.
      assert (done (get_state x) = true). rewrite <- done_equiv. apply H1.
      pose proof (D.white_path_theorem  _ _ _ _ v _ H2 H10 H12 H11). destruct H13. apply H14. apply H3.
    - apply (d_time_equiv o) in H. destruct (end_state g o); simpl in *. destruct_all.
      assert (get_state x = get_state x0). eapply done_unique. apply H2. apply valid_state_equiv.
      eapply multistep_preserves_valid'. apply start'. apply H4. all: try(rewrite <- done_equiv; assumption).
      rewrite H6 in H3. rewrite H in H3. rewrite <- H6 in H.
      assert (valid_cycle_state x g o). eapply multistep_preserves_valid'. apply start'. apply H0.
      pose proof (discovery_time_means_discovered' _ _ _ _ _ H7 H). destruct_all.
      eapply D.white_path_theorem. apply H2. apply valid_state_equiv. apply H10. rewrite <- done_equiv. apply H1. rewrite H9 in H11.
      apply H11.
      specialize (H3 (exist (fun s => valid_cycle_state s g o) x1 H10)).
      simpl in H3. apply H3. rewrite H9. reflexivity.
  Qed. 

  (* Basic results about vertices and edges *)
  Lemma same_vertices: forall o g v,
    G.contains_vertex g v = true <-> F.contains_vertex (dfs_forest o g) v = true.
  Proof.
    intros. unfold dfs_forest. destruct (end_state g o); simpl in *; destruct_all.
    eapply same_vertices. apply valid_state_equiv. eapply multistep_preserves_valid'. apply start'.
    apply H. apply H0.
  Qed.

  Lemma same_edges: forall o g u v,
    F.is_child (dfs_forest o g) u v = true -> G.contains_edge g u v = true.
  Proof.
    intros. unfold dfs_forest in *.  destruct (end_state g o); simpl in *; destruct_all. 
    eapply edges_in_forest_in_graph. apply valid_state_equiv. eapply multistep_preserves_valid'. apply start'.
    apply H0. apply H.
  Qed. 

  Lemma start_vertex: forall g v u,
    G.contains_vertex g v = true ->
    G.contains_vertex g u = true ->
    v <> u ->
    d_time (Some v) g v < d_time (Some v) g u.
  Proof.
    intros. unfold d_time. destruct (end_state g (Some v)); destruct_all; simpl in *.
    assert (valid_dfs_state (get_state x) g (Some v)). apply valid_state_equiv.
    eapply multistep_preserves_valid'. apply start'.
    apply d.
    pose proof (all_times_when_done (get_state x) g (Some v) u H2 e H0).
    pose proof (all_times_when_done (get_state x) g (Some v) v H2 e H). destruct_all.
    rewrite H3. rewrite H4. eapply first_vertex_smallest. apply H2. apply H.
    assert (u <> v) by auto. apply H7. apply H4. apply H3.
  Qed.

  Definition back_edge g u v o := (G.contains_edge g u v = true /\ F.desc (dfs_forest o g) v u).

  (*Gets around declaring definition in interface: see if better way*)
  Lemma back_edge_def: forall g u v o,
    back_edge g u v o <-> (G.contains_edge g u v = true /\ F.desc (dfs_forest o g) v u).
  Proof. unfold back_edge. reflexivity. Qed.

  Definition rev_f_time o g u v :=
    f_time o g u > f_time o g v.

  Lemma rev_f_time_def: forall o g u v,
    rev_f_time o g u v <-> f_time o g u > f_time o g v.
  Proof. unfold rev_f_time. reflexivity. Qed.

End DFSWithCycleDetectBase.

Module A := DerivedProofs.DerivedProofs O S G F DFSWithCycleDetectBase.

Module DFSWithCycleDetectImpl <: (DFSSpec.DFSWithCycleDetect O S G F).

  Include DFSWithCycleDetectBase.

  Import DFSWithCycleDetectBase.

  Definition cycle_detect o (g: G.graph) := get_bool (proj1_sig (end_state g o)).

  (*Proves that the version of gray in the interface (referencing only finish times) is equivalent to
    the other set based definition *)
  Lemma gray_equiv: forall o g (s: state o g) v,
    G.contains_vertex g v = true ->
    gray o g s v = true <-> D.gray (get_state (proj1_sig s)) v = true.
  Proof.
    intros. assert (A:= H). assert (B:= H). apply (d_time_equiv o) in A. apply (f_time_equiv o) in B. 
    split; intros.
    - unfold gray in H0. unfold time_of_state in H0. unfold d_time in H0.
      destruct s; simpl in *. destruct (end_state g o); simpl in *. destruct_all.
      rewrite A in H3. rewrite Nat.ltb_lt in H0. unfold D.gray.
      assert (V: valid_dfs_state (get_state x) g o) by (apply valid_state_equiv; assumption).
      assert (V1: valid_dfs_state (get_state x0) g o). apply valid_state_equiv. eapply multistep_preserves_valid'.
      apply start'. apply H1.
      pose proof (discovery_time_means_discovered _ _ _ _ _ V1 A). destruct_all.
      assert (dfs_multi x1 (get_state x)). assert (dfs_multi x1 (get_state x) \/ dfs_multi (get_state x) x1).
      eapply multi_from_start. apply valid_begins_with_start. apply V. apply valid_begins_with_start.
      apply H6. destruct H8. apply H8. apply time_incr_multi in H8. destruct H8. subst.
      apply multi_refl. rewrite Nat.leb_le in H3. omega. 
      assert (S.mem v (get_remain_d (get_state x)) = false). destruct (S.mem v (get_remain_d (get_state x))) eqn : ?.
      pose proof (v_discovered_iff_not_remain _ _ _ _ V H). destruct H9. apply contrapositive in H10.
      exfalso. apply H10. eapply discovery_time_constant in H7. exists (d_time o g v). apply H7.
      apply H6. apply H8. rewrite Heqb. intro. inversion H11. reflexivity. rewrite H9. split. reflexivity.
      pose proof (finish_time_means_finished _ _ _ _ _ V1 B). destruct_all.
      assert (dfs_multi (get_state x) x2). assert (dfs_multi x2 (get_state x) \/ dfs_multi (get_state x) x2).
       eapply multi_from_start. apply valid_begins_with_start. apply V. apply valid_begins_with_start.
      apply H12. destruct H14. apply time_incr_multi in H14. destruct H14. subst. apply multi_refl.
      omega. apply H14. destruct (S.mem v (get_remain_f (get_state x))) eqn : ?. reflexivity.
      rewrite (v_finished_iff_not_remain) in Heqb. destruct Heqb. assert (x3 <= get_time (get_state x)).
      eapply f_times_leq_current_time. eassumption. apply H15. eapply finish_time_constant in H15.
      rewrite H15 in H13. inversion H13; subst. omega. eassumption. apply H14. apply V. apply H.
    - unfold D.gray in H0. unfold gray. unfold time_of_state. destruct s. destruct (end_state g o).
      simpl in *. destruct_all. simplify. 
      + assert (V: valid_dfs_state (get_state x0) g o). apply valid_state_equiv. eapply multistep_preserves_valid'.
        apply start'. apply H1. pose proof (finish_time_means_finished _ _ _ _ _ V B). destruct_all.
        assert (dfs_multi (get_state x) x1). assert (dfs_multi x1 (get_state x) \/ dfs_multi (get_state x) x1).
        eapply multi_from_start. apply valid_begins_with_start. apply valid_state_equiv. apply v0.
        apply valid_begins_with_start. apply H6. destruct H8.
        assert (M.find v (get_f_times (get_state x)) = Some (f_time o g v)). eapply finish_time_constant.
        apply H6. apply H7. apply H8. assert (exists n, M.find v (get_f_times (get_state x)) = Some n).
        exists (f_time o g v). apply H9. rewrite <- v_finished_iff_not_remain in H10. rewrite H10 in H3. inversion H3.
        apply valid_state_equiv. apply v0. apply H. apply H8. apply time_incr_multi in H8. destruct H8.
        subst. assert (exists n, M.find v (get_f_times (get_state x)) = Some n). exists (f_time o g v); assumption.
        rewrite <- v_finished_iff_not_remain in H8. rewrite H8 in H3. inversion H3. apply valid_state_equiv.
        apply v0. apply H. rewrite Nat.ltb_lt. omega.
      + assert (V: valid_dfs_state (get_state x0) g o). apply valid_state_equiv. eapply multistep_preserves_valid'.
        apply start'. apply H1. pose proof (discovery_time_means_discovered _ _ _ _ _ V A). destruct_all.
        assert (dfs_multi x1 (get_state x)). assert (dfs_multi x1 (get_state x) \/ dfs_multi (get_state x) x1).
        eapply multi_from_start. apply valid_begins_with_start. apply valid_state_equiv. apply v0.
        apply valid_begins_with_start. apply H6. destruct H8. apply H8.
        rewrite v_discovered_iff_not_remain in H0. destruct H0. assert (T:= H8). apply time_incr_multi in H8.
        destruct H8. subst. apply multi_refl.  
        assert (M.find v (get_d_times x1) = Some x2). eapply discovery_time_constant. apply valid_state_equiv.
        apply v0. apply H0. apply T. rewrite H9 in H7. inversion H7; subst. eapply d_times_leq_current_time in H9.
        eapply d_times_leq_current_time in H0. omega. apply valid_state_equiv. apply v0. apply H6.
        eapply valid_state_equiv. apply v0. apply H. assert (M:= H8). apply time_incr_multi in H8. destruct H8.
        subst. rewrite H5. rewrite Nat.leb_le. omega. rewrite Nat.leb_le. omega.
Qed. 

  Lemma back_edge_equiv: forall g u v o,
    back_edge g u v o <-> back_edge' g u v o.
  Proof.
    intros. rewrite A.back_edge_equiv. unfold back_edge'. unfold A.back_edge'.
    unfold state. unfold time_of_state.
    unfold d_time. split; intros.
    - destruct_all. assert (C: G.contains_vertex g u = true). eapply G.contains_edge_1. apply H1.
      apply (d_time_equiv o) in C.  destruct x. simpl in *.  
      destruct (end_state g o). simpl in *. destruct_all. rewrite C in H0. rewrite <- H0 in C.
      exists x. split. apply v0. split.
      apply H. split. assert (V: valid_dfs_state (get_state x0) g o). apply valid_state_equiv.
      eapply multistep_preserves_valid'. apply start'. apply H3.
      pose proof (discovery_time_means_discovered _ _ _ _ _ V C). destruct_all.
      assert (x1 = get_state x). eapply times_unique. apply H7. eapply valid_state_equiv. apply v0.
      omega. subst. apply H8. split. apply H1. 
      rewrite gray_equiv in H2. simpl in *. apply H2. eapply G.contains_edge_2. apply H1.
    - destruct_all. exists (exist _ x H). split. apply H0. simpl in *.
      assert (G.contains_vertex g u = true). eapply G.contains_edge_1.
      apply H2. apply (d_time_equiv o) in H4. destruct (end_state g o).
      destruct_all; simpl in *. split. rewrite H4. 
      assert (dfs_multi (get_state x) (get_state x0) \/ dfs_multi (get_state x0) (get_state x) ).
      eapply multi_from_start. apply valid_begins_with_start. eapply valid_state_equiv. 
      eapply multistep_preserves_valid'. apply start'. apply d. 
      eapply valid_begins_with_start. apply valid_state_equiv. apply H. destruct H5.
      eapply discovery_time_constant in H1. rewrite H1 in H4. inversion H4; subst. reflexivity.
      apply valid_state_equiv. apply H. apply H5. eapply discovery_time_constant in H4.
      rewrite H4 in H1. inversion H1; subst. reflexivity. eapply valid_state_equiv.
      eapply multistep_preserves_valid'. apply start'. apply d. apply H5. split. apply H2.
      rewrite gray_equiv. simpl. apply H3. eapply G.contains_edge_2. apply H2.
Qed.

   Lemma cycle_detect_back_edge: forall g o,
    cycle_detect o g = true <-> exists u v, back_edge g u v o.
  Proof.
    intros. unfold cycle_detect. setoid_rewrite back_edge_equiv.  rewrite back_edge_iff_true. reflexivity.
    destruct (end_state g o); simpl. destruct a. eapply multistep_preserves_valid'. apply start'. apply H.
    destruct (end_state g o); simpl; destruct_all; assumption.
  Qed.
End DFSWithCycleDetectImpl.

End DFSCycle.
