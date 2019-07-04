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

(*In order to perform DFS, we need a lawful Graph (the input), Tree (the output), Set (for keeping
  track of the vertices not yet seen), Map (for storing discover/finish times), and UsualOrderedType
  (for the vertices). Also, we could use different sets for the Graph and Tree instances.*)
Module DFS (O: UsualOrderedType)(M: FMapInterface.Sfun O) (S St: FSetInterface.Sfun O) (G: Graph O S)
            (F: Forest O St S G).

Module P := FMapFacts.WProperties_fun O M.
Module F := P.F.
Module P2 := FSetProperties.WProperties_fun O S.
Module O2 := OrderedTypeFacts O.
Module Pa := (Path.PathTheories O S G).

(*First, we define the types we will need*)
Definition vertex := O.t.
Definition graph := G.graph.
Definition forest := F.forest.
Definition times_map := M.t nat.
(*Each vertex on the stack is pushed along with its parent if it has one*)
Definition stack := list (O.t * (option O.t)).
(*The state of the program at any given iteration: contains the input graph, the current output forest,
  the map of discovery times, the map of finish times, the current timestamp, the set of vertices
  yet to be discovered, the set of vertices yet to be finished, and the stack*)
Definition state : Type := graph * forest * times_map * times_map * nat * S.t * S.t * stack.

(*A preliminary function: add all neighbors of a vertex to a stack unless they have already been
  discovered*)
Definition add_to_stack (vertex: O.t) (g: graph) (remaining: S.t) : stack :=
  match G.neighbors_set g vertex with
    |None => nil
    |Some s => fold_right (fun v t => if S.mem v (S.remove vertex remaining) then (v, Some vertex) :: t else t) nil (S.elements s)
  end.

Fixpoint pop_stack (s: stack) (remaining: S.t) : stack :=
  match s with
  | nil => nil
  | (v,p) :: t => if (negb (S.mem v remaining)) then pop_stack t remaining
                  else s
  end.

Definition start_new (s: stack) (r: S.t) : stack :=
  match s with
  | nil => match (S.min_elt r) with
            | Some x => (x, None) :: nil
            (*Impossible*)
            | None => nil
            end
  | _ => s
  end.

Inductive dfs_step: state -> state -> Prop :=
  | dfs_discover_root : forall g f f_times d_times time remain_d remain_f st x tl,
    S.mem x remain_d = true ->
    (x, None) :: tl = start_new (pop_stack st remain_f) remain_d ->
    dfs_step (g, f, f_times, d_times, time, remain_d, remain_f, st)
    (g, F.add_root f x, f_times, (M.add x (time + 1) d_times), (time + 1), (S.remove x remain_d), 
    remain_f, (add_to_stack x g remain_d) ++  ((x, None) :: tl))
    (*Discover a vertex: add all of its neighbors who have not been discovered to the stack,
      add it to the stack, add it to the discover times with the current time, and remove it from
      remain_d. We also add it to the forest as a new singleton tree*)
  | dfs_discover_child : forall g f f_times d_times time remain_d remain_f st x y tl,
    S.mem x remain_d = true ->
    (x, Some y) :: tl = start_new (pop_stack st remain_f) remain_d ->
    dfs_step (g, f, f_times, d_times, time, remain_d, remain_f, st)
    (g, F.add_child f y x, f_times, (M.add x (time + 1) d_times), (time + 1), (S.remove x remain_d), 
    remain_f, (add_to_stack x g remain_d) ++  ((x, Some y) :: tl))
    (*The same as the previous except we add the vertex as a child of its parent in the tree*)
  | dfs_finish: forall g f f_times d_times time remain_d remain_f x o tl st,
    S.mem x remain_d = false ->
    S.mem x remain_f = true ->
    (x, o) :: tl = start_new (pop_stack st remain_f) remain_d ->
    dfs_step (g, f, f_times, d_times, time, remain_d, remain_f, st)
    (g,  f, (M.add x (time + 1) f_times), d_times, (time + 1), remain_d, (S.remove x remain_f), tl)
    (*Finish a vertex by adding it to finish_times whileremoving it from remain_f and the stack*).

(*A few state-related definitions to make the proofs simpler*)

Definition get_time (s : state) : nat :=
  match s with
  | (_, _, _, _, n, _, _, _) => n
  end.

Definition get_remain_d (s: state) : S.t :=
  match s with
  | (_, _, _, _, _, r, _, _) => r
  end.

Definition get_remain_f (s: state) : S.t :=
  match s with
  | (_, _, _, _, _, _, f, _) => f
  end.

Definition get_d_times (s: state) :=
  match s with
  | (_, _, _, d, _, _, _, _) => d
  end.

Definition get_f_times (s : state) :=
  match s with
  | (_, _, f, _, _, _, _, _) => f
  end.

Definition get_stack (s: state) :=
  match s with
  | (_, _, _, _, _, _, _, s') => s'
  end.

Definition get_forest (s: state) :=
  match s with
  | (_, f, _, _, _, _, _, _) => f
  end.

(* A useful property of dfs_step: it is determinstic *)
Lemma dfs_step_deterministic : forall s1 s2 s,
  dfs_step s s1 -> dfs_step s s2 -> s1 = s2.
Proof.
  intros. inversion H; subst; simpl in *.
  - inversion H0; subst; simpl in *.
    + rewrite <- H13 in H2. inversion H2; subst. reflexivity.
    + rewrite <- H13 in H2. inversion H2.
    + rewrite <- H14 in H2. inversion H2; subst. rewrite H12 in H1. inversion H1.
  - inversion H0; subst; simpl in *.
    + rewrite <- H13 in H2. inversion H2.
    + rewrite <- H13 in H2. inversion H2; subst. reflexivity.
    + rewrite <- H14 in H2. inversion H2; subst. rewrite H12 in H1. inversion H1.
  - inversion H0; subst; simpl in *.
    + rewrite <- H14 in H3. inversion H3; subst. rewrite H13 in H1. inversion H1.
    + rewrite <- H14 in H3. inversion H3; subst. rewrite H13 in H1. inversion H1.
    + rewrite <- H15 in H3. inversion H3; subst. reflexivity.
Qed.

(** ** Valid DFS states **)

(*Now we want to define a valid DFS state based on this definition. A state where, for example, 
  there are vertices in the yet-to-finish set that are not in the graph is not valid. We will define
  valid states inductively, either as the start state or a dfs_step from another valid state*)

(*The valid start state of DFS. We take in a graph and vertex option, representing starting DFS 
  from a specific vertex *)
Definition start_state (g: graph) (o: option vertex) : state :=
  let init_stack := match o with
                    | None => nil
                    | Some v => if G.contains_vertex g v then (v, None) :: nil else nil
                    end in
  (g, F.empty, M.empty nat, M.empty nat, 0, (G.set_of_graph g), (G.set_of_graph g), init_stack).

(*A state for a given graph is valid if is is the start state or can be reached in 1 step from
  another valid state. This allows us to work only with correct dfs states in proofs (not, for example,
  in the case where the vertices that must be finished is empty but there are vertices to discover*)
Inductive valid_dfs_state: state -> graph -> option vertex -> Prop :=
  | start: forall g o, valid_dfs_state (start_state g o) g o
  | step: forall s1 s2 g o,
    valid_dfs_state s1 g o ->
    dfs_step s1 s2 ->
    valid_dfs_state s2 g o.

(*We can give an alternate definition using the multistep relation from [Smallstep.v] in Software Foundations*)
Section Multi.
Definition relation (X : Type) := X -> X -> Prop.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Theorem multi_R : forall (X : Type) (R : relation X) (x y : X),
    R x y -> (multi R) x y.
Proof.
  intros X R x y H.
  apply multi_step with y. apply H. apply multi_refl.
Qed.

Theorem multi_trans :
  forall (X : Type) (R : relation X) (x y z : X),
      multi R x y ->
      multi R y z ->
      multi R x z.
Proof.
  intros X R x y z G H.
  induction G.
    - (* multi_refl *) assumption.
    - (* multi_step *)
      apply multi_step with y. assumption.
      apply IHG. assumption.
Qed.
End Multi.

Definition dfs_multi (s1 s2 : state):= multi (dfs_step) s1 s2.

Lemma multistep_preserves_valid: forall s s' g o,
  valid_dfs_state s g o ->
  dfs_multi s s' ->
  valid_dfs_state s' g o.
Proof.
  intros. induction H0.
  - assumption.
  - apply IHmulti. eapply step. apply H. apply H0.
Qed.

Lemma valid_begins_with_start: forall s g o,
  valid_dfs_state s g o ->
  dfs_multi (start_state g o) s.
Proof.
  intros. induction H.
  - constructor.
  - eapply multi_trans. apply IHvalid_dfs_state. eapply multi_step. apply H0. apply multi_refl.
Qed.

(*This uses the above 2 helper lemmas to prove that the two definitions of valid dfs states are equivalent. 
(I think) the inductive definition will be much more useful in proofs*)
Lemma valid_dfs_multistep: forall s g o,
  dfs_multi (start_state g o) s <-> valid_dfs_state s g o.
Proof.
  intros. split; intros.
  - eapply multistep_preserves_valid. apply start. assumption.
  - apply valid_begins_with_start. assumption.
Qed. 

(*Measure decreasing*)
Definition measure_dfs (s: state) :=
  S.cardinal (get_remain_d s) + S.cardinal (get_remain_f s).

(*Tactics for proving that a set that we remove something from is smaller than the original set*)
Ltac prove_in_set x s :=
  match goal with
  | [H : S.min_elt s = Some x |- _] => apply S.min_elt_1; apply H
  | [H: S.mem x s = true |- _ ] => apply S.mem_2; apply H
  | [H: S.In x s |- _] => apply H
  | [H: _ |- _] => auto
  end. 

Ltac assert_remove_size x s :=
  assert (Hremove : S(S.cardinal (S.remove x s)) = S.cardinal s) by 
  (apply P2.remove_cardinal_1; prove_in_set x s); try(omega).

Ltac size_of_remove :=
  match goal with
  | [H :_ |- (?y + S.cardinal (S.remove ?x ?s)) < ?y + (S.cardinal ?s)] =>
    assert (S(S.cardinal (S.remove x s)) = S.cardinal s) by ( 
    apply P2.remove_cardinal_1; prove_in_set x s); omega
  | [H : _ |- (S.cardinal (S.remove ?x ?s)) + ?y < (S.cardinal ?s) + ?y] =>
    assert (S(S.cardinal (S.remove x s)) = S.cardinal s) by ( 
    apply P2.remove_cardinal_1; prove_in_set x s); omega
  | [H : _ |- (S.cardinal (S.remove ?x (S.remove ?z ?s))) + ?y < (S.cardinal ?s) + ?y] =>
    assert (S(S(S.cardinal (S.remove x (S.remove z s)))) = S.cardinal s) by ( 
    rewrite P2.remove_cardinal_1; [apply P2.remove_cardinal_1| prove_in_set x (S.remove z s)]; prove_in_set z s; omega)
  | [H : _ |- (?y + S.cardinal (S.remove ?x (S.remove ?z ?s))) <  ?y + (S.cardinal ?s)] =>
    assert (S(S(S.cardinal (S.remove x (S.remove z s)))) = S.cardinal s) by ( 
    rewrite P2.remove_cardinal_1; [apply P2.remove_cardinal_1| prove_in_set x (S.remove z s)]; prove_in_set z s; omega)
  | [H : _ |- S.cardinal (S.remove ?x ?s) + S.cardinal (S.remove ?y ?t) < S.cardinal ?s + S.cardinal ?t] =>
    assert (S.cardinal (S.remove x s) + 0 < S.cardinal s + 0) by size_of_remove;
    assert (S.cardinal (S.remove y t) + 0 < S.cardinal t + 0) by size_of_remove;
    omega
end; try(omega).

(*Each step has strictly smaller measure*)

(*See, prove stronger claim*)
Lemma step_measure_decr: forall s s',
  dfs_step s s' ->
  measure_dfs s' + 1 = measure_dfs s.
Proof.
  intros. unfold measure_dfs. induction H; subst; simpl in *; try(assert_remove_size x remain_d);
  try(assert_remove_size x remain_f); try(apply IHdfs_step).
Qed.

Lemma step_measure_lt: forall s s',
  dfs_step s s' ->
  measure_dfs s' < measure_dfs s.
Proof.
  intros. rewrite <- (step_measure_decr _ _ H). omega.
Qed. 

Lemma multistep_measure_lt: forall s s',
  dfs_multi s s' ->
  s = s' \/ measure_dfs s' < measure_dfs s.
Proof.
  intros. induction H.
  - left. reflexivity.
  - destruct IHmulti. subst. right. apply step_measure_lt.
    apply H. right. eapply lt_trans. apply H1. apply step_measure_lt. apply H.
Qed.

Lemma multistep_neq_measure_lt: forall s s',
  dfs_multi s s' ->
  (s <> s') <-> (measure_dfs s' < measure_dfs s).
Proof.
  intros. split; intros; subst.
  - apply multistep_measure_lt in H. destruct H. contradiction. apply H.
  - intro. subst. omega.
Qed.

Lemma multistep_eq_measure: forall s s',
  dfs_multi s s' ->
  (s = s') <-> (measure_dfs s' = measure_dfs s).
Proof.
  intros. split; intros; subst.
  - reflexivity.
  - apply multistep_measure_lt in H.
    destruct H. assumption. omega.
Qed.

Lemma multistep_no_cycle: forall s s',
  dfs_multi s s' ->
  dfs_multi s' s ->
  s = s'.
Proof.
  intros. apply multistep_measure_lt in H. apply multistep_measure_lt in H0.
  destruct H; try(assumption). destruct H0; try(subst; reflexivity).
  omega.
Qed.

Lemma multi_from_start: forall s s' s'',
  dfs_multi s s'' ->
  dfs_multi s s' ->
  (dfs_multi s' s'' \/ dfs_multi s'' s').
Proof.
  intros. generalize dependent s'. induction H; intros.
  - right. apply H0.
  - inversion H1; subst.
    + left. eapply multi_step. apply H. apply H0.
    + assert (y=y0). eapply dfs_step_deterministic.
      apply H. apply H2. subst. apply IHmulti. apply H3.
Qed.

Lemma valid_determ: forall s g o s' x,
  valid_dfs_state s g o ->
  valid_dfs_state s' g o ->
  dfs_step s x ->
  dfs_step s' x ->
  s = s'.
Proof.
  intros. assert (S:=H). assert (S':= H0). apply valid_begins_with_start in S.
  apply valid_begins_with_start in S'. pose proof multi_from_start.
  specialize (H3 (start_state g o) s s' S' S). destruct H3.
  - apply multistep_eq_measure. apply H3.
    apply multistep_measure_lt in H3. destruct H3. subst; reflexivity.
    apply step_measure_decr in H1. apply step_measure_decr in H2. omega.
  - symmetry. apply multistep_eq_measure. apply H3.
    apply multistep_measure_lt in H3. destruct H3. subst; reflexivity.
    apply step_measure_decr in H1. apply step_measure_decr in H2. omega.
Qed.

Definition white (s: state) (v: vertex) :=
  S.mem v (get_remain_d s) && S.mem v (get_remain_f s).

Definition gray s v :=
  negb (S.mem v (get_remain_d s)) && S.mem v (get_remain_f s).

Definition black s v :=
  negb (S.mem v (get_remain_d s)) && negb (S.mem v (get_remain_f s)).

Lemma v_discovered_iff_not_remain: forall s g o v,
  valid_dfs_state s g o ->
  G.contains_vertex g v = true ->
  S.mem v (get_remain_d s) = false <-> (exists n, M.find v (get_d_times s) = Some n).
Proof.
  intros. induction H.
  - simpl. split; intros. 
    + apply G.set_of_graph_1 in H0. apply S.mem_1 in H0. rewrite H in H0. inversion H0.
    + destruct H. rewrite P.F.empty_o in H. inversion H.
  - inversion H1; subst; simpl in *; split; intros.
    + destruct (O.eq_dec x v).
      * rewrite e. exists (time + 1). apply P.F.add_eq_o. reflexivity.
      * rewrite P.F.add_neq_o. rewrite P2.Dec.F.remove_neq_b in H4. apply IHvalid_dfs_state.
        apply H0. apply H4. apply n. apply n.
    + destruct (O.eq_dec x v).
      * rewrite P2.FM.remove_b. rewrite andb_false_iff. right. unfold P2.FM.eqb.
        destruct (O.eq_dec x v). reflexivity. contradiction.
      * rewrite P.F.add_neq_o in H4. apply IHvalid_dfs_state in H4. 
        rewrite P2.Dec.F.remove_neq_b. apply H4. apply n. apply H0. apply n.
    + destruct (O.eq_dec x v).
      * rewrite e. exists (time + 1). apply P.F.add_eq_o. reflexivity.
      * rewrite P.F.add_neq_o. rewrite P2.Dec.F.remove_neq_b in H4. apply IHvalid_dfs_state.
        apply H0. apply H4. apply n. apply n.
    + destruct (O.eq_dec x v).
      * rewrite P2.FM.remove_b. rewrite andb_false_iff. right. unfold P2.FM.eqb.
        destruct (O.eq_dec x v). reflexivity. contradiction.
      * rewrite P.F.add_neq_o in H4. apply IHvalid_dfs_state in H4. 
        rewrite P2.Dec.F.remove_neq_b. apply H4. apply n. apply H0. apply n.
    + apply IHvalid_dfs_state. apply H0. apply H5.
    + apply IHvalid_dfs_state. apply H0. apply H5.
Qed.

Lemma v_finished_iff_not_remain: forall s g o v,
  valid_dfs_state s g o ->
  G.contains_vertex g v = true ->
  S.mem v (get_remain_f s) = false <-> (exists n, M.find v (get_f_times s) = Some n).
Proof.
  intros. induction H.
  - simpl. split; intros. 
    + apply G.set_of_graph_1 in H0. apply S.mem_1 in H0. rewrite H in H0. inversion H0.
    + destruct H. rewrite P.F.empty_o in H. inversion H.
  - inversion H1; subst; simpl in *; split; intros.
    + apply IHvalid_dfs_state. apply H0. apply H4.
    + apply IHvalid_dfs_state. apply H0. apply H4.
    + apply IHvalid_dfs_state. apply H0. apply H4.
    + apply IHvalid_dfs_state. apply H0. apply H4.
    +  destruct (O.eq_dec x v).
      * rewrite e. exists (time + 1). apply P.F.add_eq_o. reflexivity.
      * rewrite P.F.add_neq_o. rewrite P2.Dec.F.remove_neq_b in H5. apply IHvalid_dfs_state.
        apply H0. apply H5. apply n. apply n.
    + destruct (O.eq_dec x v).
      * rewrite P2.FM.remove_b. rewrite andb_false_iff. right. unfold P2.FM.eqb.
        destruct (O.eq_dec x v). reflexivity. contradiction.
      * rewrite P.F.add_neq_o in H5. apply IHvalid_dfs_state in H5. 
        rewrite P2.Dec.F.remove_neq_b. apply H5. apply n. apply H0. apply n.
Qed.


(*General facts about times*)
Lemma time_plus_one: forall s s',
  dfs_step s s' ->
  get_time s + 1 = get_time s'.
Proof.
  intros. inversion H; subst; simpl in *; try(omega).
Qed.

Lemma time_incr_step: forall s s',
  dfs_step s s' ->
  get_time s < get_time s'.
Proof.
  intros. rewrite <- (time_plus_one _ _ H). omega.
Qed.

Lemma time_incr_multi: forall s s',
  dfs_multi s s' ->
  s = s' \/ get_time s < get_time s'.
Proof.
  intros. induction H.
  - left. reflexivity.
  - destruct IHmulti. inversion H1; subst. right. apply time_incr_step. apply H.
    right. apply time_incr_step in H. omega.
Qed. 

Lemma times_unique: forall s s' g o,
  valid_dfs_state s g o ->
  valid_dfs_state s' g o ->
  get_time s = get_time s' ->
  s = s'.
Proof.
  intros. assert (A:=H0). assert (B:=H). apply valid_begins_with_start in A.
  apply valid_begins_with_start in B. pose proof (multi_from_start _ _ _ A B).
  destruct H2; apply time_incr_multi in H2; destruct H2; try(subst; reflexivity); try(omega).
Qed.


Definition done (s: state) :=
  S.is_empty (get_remain_d s) && S.is_empty (get_remain_f s).

Ltac simplify := try(rewrite andb_diag in *); try(rewrite andb_true_iff in *); try(rewrite negb_true_iff in *);
  try(rewrite andb_false_iff in *); try(rewrite negb_false_iff in *); intuition.

Ltac solve_empty :=
  simplify; match goal with
  |[H: S.is_empty ?s = true, H1: S.mem ?x ?s = true |- _] =>
    apply S.is_empty_2 in H; apply P2.empty_is_empty_1 in H; rewrite H in H1; rewrite P2.FM.empty_b in H1;
    inversion H1
  end.

Lemma done_cannot_step: forall s g o,
  valid_dfs_state s g o ->
  done s = true ->
  ~(exists s', dfs_step s s').
Proof.
  intros. intro. destruct H1. unfold done in H0; inversion H1; subst; simpl in *; solve_empty.
Qed. 

Lemma pop_stack_nil: forall l r,
  pop_stack l r = nil <-> (forall (x: O.t * option O.t), let (a,b):= x in
   In x l -> (S.mem a r = false)).
Proof.
  intros. induction l; split; intros.
  - destruct x. intro. inversion H0.
  - simpl. reflexivity.
  - destruct x. intros. simpl in *. destruct a.
    destruct H0. inversion H0; subst. 
    destruct (S.mem t r) eqn :?; simpl in H. inversion H. reflexivity.
    destruct (S.mem t0 r) eqn : ?; simpl in H. inversion H. 
    rewrite IHl in H. specialize (H (t, o)).
    apply H. apply H0.
  - simpl in *. destruct a. destruct (S.mem t r) eqn : ?.
    + simpl. specialize (H (t, o)). simpl in H. rewrite H in Heqb. inversion Heqb. left. reflexivity.
    + simpl. apply IHl. intros. destruct x. intros. specialize (H (t0, o0)). simpl in H.
      apply H. right. apply H0.
Qed.

Lemma not_f_if_not_d: forall s g o v,
  valid_dfs_state s g o ->
  S.mem v (get_remain_d s) = true ->
  S.mem v (get_remain_f s) = true.
Proof.
  intros. generalize dependent v. induction H; intros; subst; simpl in *.
  - apply H0.
  - inversion H0; subst; simpl in *.
    + destruct (O.eq_dec x v).
      * rewrite e in H2. apply IHvalid_dfs_state. apply H2.
      * rewrite P2.Dec.F.remove_neq_b in H1. apply IHvalid_dfs_state. apply H1. apply n.
   + destruct (O.eq_dec x v).
      * rewrite e in H2. apply IHvalid_dfs_state. apply H2.
      * rewrite P2.Dec.F.remove_neq_b in H1. apply IHvalid_dfs_state. apply H1. apply n.
    + destruct (O.eq_dec x v).
      * rewrite <- e in H1. rewrite H1 in H2. inversion H2.
      * rewrite P2.Dec.F.remove_neq_b. apply IHvalid_dfs_state. apply H1. apply n.
Qed.

Lemma f_empty_implies_d_empty: forall s g o,
  valid_dfs_state s g o ->
  S.is_empty (get_remain_f s) = true ->
  S.is_empty (get_remain_d s) = true.
Proof.
  intros. destruct (S.min_elt (get_remain_d s)) eqn : ?.
  + apply S.min_elt_1 in Heqo0. apply S.mem_1 in Heqo0. eapply not_f_if_not_d in Heqo0.
    solve_empty. apply H.
  + apply S.min_elt_3 in Heqo0. apply S.is_empty_1 in Heqo0. apply Heqo0.
Qed.

Lemma start_new_nil: forall l r r',
  start_new (pop_stack l r') r = nil -> S.is_empty r = true.
Proof.
  intros. unfold start_new in *. destruct (pop_stack l r').
  + destruct (S.min_elt r) eqn : ?.
    * inversion H.
    * apply S.min_elt_3 in Heqo. apply S.is_empty_1 in Heqo. apply Heqo.
  + inversion H.
Qed. 

Lemma pop_stack_cons: forall l r h o t,
  pop_stack l r = (h, o) :: t -> S.mem h r = true.
Proof.
  intros. induction l.
  - simpl in H. inversion H.
  - simpl in H. destruct a. destruct (S.mem t0 r) eqn : ?; simpl in H.
    + inversion H; subst. apply Heqb.
    + apply IHl. apply H.
Qed. 

Lemma color_total: forall s g o v,
  valid_dfs_state s g o ->
  G.contains_vertex g v = true ->
  white s v = true \/ gray s v = true \/ black s v = true.
Proof.
  intros. unfold white. unfold gray. unfold black. 
  destruct (S.mem v (get_remain_d s)) eqn : ?.
  - left. eapply not_f_if_not_d in Heqb. rewrite Heqb. reflexivity. apply H.
  - destruct (S.mem v (get_remain_f s)) eqn : ?.
    + right. left. reflexivity.
    + right. right. reflexivity.
Qed.

(*Lemmas for dealing with [pop_stack]*)

Lemma in_pop: forall l a b r,
  In (a,b) l ->
  S.mem a r = true ->
  In (a,b) (pop_stack l r).
Proof.
  intros. induction l.
  - inversion H.
  - simpl in *. destruct H. inversion H; subst. 
    rewrite H0. simpl. left. reflexivity.
    destruct a0. destruct (S.mem e r) eqn : ?; simpl.
    + right. apply H.
    + apply IHl. apply H.
Qed.

Lemma in_pop_rev: forall l x r,
  In x (pop_stack l r) ->
  In x l.
Proof.
  intros. induction l.
  - simpl in H. inversion H.
  - simpl in *. destruct a. destruct (S.mem t r) eqn : ?; simpl in H.
    + apply H.
    + right. apply IHl. apply H.
Qed.

Lemma remove_eq: forall x s, 
  S.mem x (S.remove x s) = true -> False.
Proof.
  intros. rewrite P2.FM.remove_b in H. rewrite andb_true_iff in H.
  destruct H. unfold P2.FM.eqb in H0. destruct (O.eq_dec x x). inversion H0.
  exfalso. apply n. reflexivity.
Qed.

(** Reasoning about color of vertices **)

(*Gray vertices are on the stack*)
Lemma gray_on_stack: forall s g o v,
  valid_dfs_state s g o ->
  gray s v = true ->
  exists o, In (v,o) (get_stack s).
Proof.
  intros. unfold gray in H0. induction H; subst; simpl in *; simplify.
  - rewrite H in H1. inversion H1.
  - inversion H1; subst; simpl in *.
    + destruct (O.eq_dec v x).
      * exists None. apply in_or_app. right. rewrite e. left. reflexivity.
      * rewrite P2.Dec.F.remove_neq_b in H2. specialize (H0 H2 H3). destruct H0.
        assert (In (v, x0) (pop_stack st remain_f)). eapply in_pop. apply H0. apply H3.
        destruct (pop_stack st remain_f) eqn : ?. 
        -- inversion H6.
        -- simpl in *. inversion H5; subst. destruct H6.
            ++ inversion H6; subst. exists None. apply in_or_app. right. left. reflexivity.
            ++ exists x0. apply in_or_app. right. right. apply H6.
        -- intuition.
    + destruct (O.eq_dec v x).
      * exists (Some y). apply in_or_app. right. rewrite e. left. reflexivity.
      * rewrite P2.Dec.F.remove_neq_b in H2. specialize (H0 H2 H3). destruct H0.
        assert (In (v, x0) (pop_stack st remain_f)). eapply in_pop. apply H0. apply H3.
        destruct (pop_stack st remain_f) eqn : ?. 
        -- inversion H6.
        -- simpl in *. inversion H5; subst. destruct H6.
            ++ inversion H6; subst. exists (Some y). apply in_or_app. right. left. reflexivity.
            ++ exists x0. apply in_or_app. right. right. apply H6.
        -- intuition.
    + destruct (O.eq_dec v x).
      * rewrite e in H3. apply remove_eq in H3. destruct H3.
      * rewrite P2.Dec.F.remove_neq_b in H3. specialize (H0 H2 H3). destruct H0.
        assert (In (v, x0) (pop_stack st remain_f)). eapply in_pop. apply H0. apply H3.
        destruct (pop_stack st remain_f) eqn : ?. 
        -- inversion H7.
        -- simpl in *. inversion H7; subst. inversion H6; subst. exfalso. apply n. reflexivity.
           inversion H6; subst. exists x0. apply H8.
        -- intuition.
Qed. 

Lemma pop_only_removes_black: forall s g o v o',
  valid_dfs_state s g o ->
  black s v = false ->
  In (v,o') (get_stack s) ->
  In (v,o') (pop_stack (get_stack s) (get_remain_f s)).
Proof.
  intros. unfold black in H0. eapply in_pop. apply H1. simplify. eapply not_f_if_not_d. apply H.
  apply H2. rewrite negb_false_iff in H2. apply H2.
Qed.

(** ** Dealing with set inequality **)

(*It turns out to be surprisingly involved to prove that if two sets are not equal, then there
  is an element in one but not the other. I prove this by proving an analogous result for sorted lists
  and using S.elements to relate the two*)

(*List inequality as a function, since it gives us the element in one list but not the other
  directly*)
Fixpoint list_neq (l1 l2: list O.t) :=
  match l1, l2 with
  | x1 :: t1, x2 :: t2 => if O.eq_dec x1 x2 then list_neq t1 t2 else true
  | nil, nil => false
  | _, _ => true
  end.

(*The above function actually defines list inequality*)
Lemma list_eq_neq: forall l1 l2,
  l1 <> l2 <-> list_neq l1 l2 = true.
Proof.
  intros. split; intros.
  - generalize dependent l2. induction l1; intros.
    + simpl. destruct l2. contradiction. reflexivity.
    + simpl. destruct l2 eqn : ?. reflexivity.
      destruct (O.eq_dec a t).
      * setoid_rewrite e in H. assert (l1 <> l). intro. subst. contradiction.
        apply IHl1. apply H0.
      * reflexivity.
  - intro. subst. induction l2. simpl in H. inversion H. simpl in H.
    destruct (O.eq_dec a a). apply IHl2. apply H. apply n. apply eq_refl.
Qed. 

(*The result for lists: if two sorted lists are unequal, then there is an element in
  one but not the other*)
Lemma list_neq_has_diff_elements: forall (l1 l2: list O.t),
  StronglySorted O.lt l1 ->
  StronglySorted O.lt l2 ->
  l1 <> l2 ->
  (exists x, In x l1 /\ ~In x l2) \/ (exists x, ~In x l1 /\ In x l2).
Proof.
  intros. rewrite list_eq_neq in H1. generalize dependent l2; induction l1; intros.
  - simpl in H1. destruct l2 eqn : ?. inversion H1. right. exists t.
    split. auto. simpl. left. reflexivity.
  - simpl in H1. destruct l2 eqn : ?.
    + left. exists a. split. simpl. left. reflexivity. auto.
    + inversion H0; subst. inversion H; subst. destruct (O.eq_dec a t) eqn : ?. 
      * setoid_rewrite e. apply IHl1 in H4. destruct H4.
        -- destruct H2. destruct H2. assert (O.lt t x). rewrite Forall_forall in H7.
           setoid_rewrite <- e. eapply H7. apply H2. left. exists x. split. simpl.
           right. apply H2. simpl. intro. destruct H8. subst. apply O.lt_not_eq in H4.
           apply H4. apply eq_refl. contradiction.
        -- destruct H2. destruct H2. assert (O.lt t x). rewrite Forall_forall in H5.
           eapply H5. apply H3. right. exists x. split.  simpl. intro. destruct H8.
           subst. apply O.lt_not_eq in H4. apply H4. apply eq_refl. contradiction.
           simpl. right. apply H3.
        -- apply H6.
        -- apply H1.
      * pose proof (O2.lt_total a t). destruct H2.
        -- left. exists a. split. simpl. left. reflexivity. rewrite Forall_forall in H5.
           simpl. intro. destruct H3. subst. apply n. apply eq_refl. apply H5 in H3.
           apply O2.lt_le in H3. contradiction.
        -- destruct H2.
            ** subst. exfalso. apply n. apply eq_refl.
            ** right. exists t. split. simpl. intro. destruct H3. subst. apply n. apply eq_refl.
               rewrite Forall_forall in H7. apply H7 in H3. apply O2.lt_le in H3.
               contradiction. simpl. left. reflexivity.
Qed. 

(*The analogous result for sets*)
Lemma unequal_sets: forall s1 s2,
  S.equal s1 s2 = false ->
  (exists v, S.In v s1 /\ ~S.In v s2) \/ (exists v, ~S.In v s1 /\ S.In v s2).
Proof.
  intros. destruct (list_neq (S.elements s1) (S.elements s2)) eqn : ?.
  - rewrite <- list_eq_neq in Heqb. apply list_neq_has_diff_elements in Heqb.
    destruct Heqb.
    + destruct H0. destruct H0. rewrite In_InA_equiv in *. apply S.elements_2 in H0.
      assert (~S.In x s2). intro. apply S.elements_1 in H2. contradiction.
      left. exists x. split; assumption.
    + destruct H0. destruct H0. rewrite In_InA_equiv in *. apply S.elements_2 in H1.
      assert (~S.In x s1). intro. apply S.elements_1 in H2. contradiction.
      right. exists x. split; assumption.
    + apply Sorted_StronglySorted. unfold Relations_1.Transitive. intros.
      eapply O.lt_trans. apply H0. apply H1. apply S.elements_3.
    + apply Sorted_StronglySorted. unfold Relations_1.Transitive. intros.
      eapply O.lt_trans. apply H0. apply H1. apply S.elements_3.
  - destruct (list_eq_dec O.eq_dec (S.elements s1) (S.elements s2)).
    + assert (forall x, S.In x s1 <-> S.In x s2). { intros.
      split; intros; apply S.elements_1 in H0.  all: apply S.elements_2.
      rewrite <- e. assumption. rewrite e. assumption. }
      assert (~S.Equal s1 s2). intro. apply S.equal_1 in H1. rewrite H1 in H. inversion H.
      assert (S.Equal s1 s2). unfold S.Equal. apply H0. contradiction.
    + rewrite list_eq_neq in n. rewrite n in Heqb. inversion Heqb.
Qed.

(*What we wanted to prove: if pop_stack returns nil, then the remain_d and remain_f sets are equal.
  In particular, this is true when we finish*)
Lemma pop_stack_nil_finished: forall s g o,
  valid_dfs_state s g o ->
  pop_stack (get_stack s) (get_remain_f s) = nil ->
  S.equal (get_remain_d s) (get_remain_f s) = true.
Proof.
  intros. destruct (S.equal (get_remain_d s) (get_remain_f s)) eqn : ?. reflexivity.
  apply unequal_sets in Heqb. destruct Heqb; destruct H1.
  - destruct H1. apply S.mem_1 in H1. eapply not_f_if_not_d in H1. apply S.mem_2 in H1.
    contradiction. apply H.
  - destruct H1. assert (gray s x = true). unfold gray. simplify.
    destruct (S.mem x(get_remain_d s)) eqn : ?. apply S.mem_2 in Heqb.
    apply H1 in Heqb. inversion Heqb. reflexivity. 
    pose proof (gray_on_stack _ _ _ _ H H3). destruct H4. eapply in_pop in H4.
    rewrite H0 in H4. inversion H4. apply S.mem_1. apply H2.
Qed.

(** Executable DFS Algorithm **)

(*We do not just give an inductive relation, we also want a provably terminating, correct algorithm that
  can be run on an actual graph. To that end, we have a few helper lemmas and definitions first*)

(*We are done iff after we pop the stack and attempt to start a new connected component, there is nothing left*)
Lemma done_condition: forall s g o,
  valid_dfs_state s g o ->
  done s = true <-> start_new(pop_stack (get_stack s) (get_remain_f s)) (get_remain_d s) = nil.
Proof.
  intros. unfold done. induction H; split; intros; subst; simpl in *.
  - simplify. destruct o. destruct (G.contains_vertex g v) eqn : ?.
    + apply G.set_of_graph_1 in Heqb. apply S.mem_1 in Heqb. solve_empty.
    + simpl. destruct (S.min_elt (G.set_of_graph g)) eqn : ?.
      * apply S.min_elt_1 in Heqo. apply S.mem_1 in Heqo. solve_empty.
      * reflexivity.
    + simpl. destruct (S.min_elt (G.set_of_graph g)) eqn : ?.
      * apply S.min_elt_1 in Heqo. apply S.mem_1 in Heqo. solve_empty.
      * reflexivity.
  - rewrite andb_diag. destruct o. destruct (G.contains_vertex g v) eqn : ?.
    + simpl in H. destruct (S.mem v (G.set_of_graph g)) eqn : ?; simpl in H.
      * inversion H.
      * destruct (S.min_elt (G.set_of_graph g)) eqn : ?.
        -- inversion H.
        -- apply S.min_elt_3 in Heqo. apply S.is_empty_1. apply Heqo.
    + simpl in H. destruct (S.min_elt (G.set_of_graph g)) eqn : ?.
      * inversion H.
      * apply S.min_elt_3 in Heqo. apply S.is_empty_1. apply Heqo.
    + simpl in H. destruct (S.min_elt (G.set_of_graph g)) eqn : ?.
      * inversion H.
      * apply S.min_elt_3 in Heqo. apply S.is_empty_1. apply Heqo.
  - inversion H0; subst; simpl in *; simplify.
    + remember (g0, f, f_times, d_times, time, remain_d, remain_f, st) as s.
      assert (S.is_empty (get_remain_f s) = true) by (subst; simpl; assumption).
      eapply f_empty_implies_d_empty in H1. subst; simpl in *. solve_empty. apply H.
    + remember (g0, f, f_times, d_times, time, remain_d, remain_f, st)as s.
      assert (S.is_empty (get_remain_f s) = true) by (subst; simpl; assumption).
      eapply f_empty_implies_d_empty in H1. subst; simpl in *. solve_empty. apply H.
    + destruct (start_new (pop_stack tl (S.remove x remain_f)) remain_d) eqn : ?.
      * reflexivity.
      * destruct p. destruct (pop_stack tl (S.remove x remain_f)) eqn : ?; simpl in Heqs.
        -- destruct (S.min_elt remain_d) eqn : ?. apply S.min_elt_1 in Heqo2. apply S.mem_1 in Heqo2.
           solve_empty. inversion Heqs.
        -- inversion Heqs; subst. apply pop_stack_cons in Heqs0. solve_empty.
  - destruct (pop_stack (get_stack s2) (get_remain_f s2)) eqn : ?.
    + simpl in H1. destruct (S.min_elt (get_remain_d s2)) eqn : ?.
      * inversion H1.
      * apply S.min_elt_3 in Heqo0. apply S.is_empty_1 in Heqo0.
        assert (S.equal (get_remain_d s2) (get_remain_f s2) = true). eapply pop_stack_nil_finished.
        eapply step. apply H. apply H0. apply Heqs. rewrite Heqo0. apply S.equal_2 in H2.
        rewrite <- H2. apply Heqo0.
    + simpl in H1. inversion H1.
Qed.

(*The core of the algorithm: a function that takes a state and returns the next valid state. The actual
  algorithm is basically repeatedly calling this function*)
(*Note that certain states are impossible for a valid starting state that is not finished (which
  we will prove)*)
Definition next_state (s: state) : state :=
  match s with
  | (g, f, f_times, d_times, time, remain_d, remain_f, st) =>
    match (start_new (pop_stack st remain_f) remain_d) with
    (*Impossible*)
    | nil => s
    | (x,o) :: tl =>
      if S.mem x remain_d then match o with
      | None => (g, F.add_root f x, f_times, M.add x (time + 1) d_times, time + 1,
                 S.remove x remain_d, remain_f, (add_to_stack x g remain_d ++ (x,None) :: tl))
      | Some y => (g, F.add_child f y x, f_times, M.add x (time+1) d_times,
                                 time + 1, S.remove x remain_d, remain_f, (add_to_stack x g remain_d ++
                                  (x, Some y) :: tl))
                    
      end
      else if S.mem x remain_f then (g, f, M.add x (time + 1) f_times, d_times, time+1, remain_d, 
                                    S.remove x remain_f, tl)
      (*Impossible*)
      else s
    end
  end.

(*This function is equivalent to dfs_step for a valid state*)
Lemma step_next_state: forall s g o,
  valid_dfs_state s g o ->
  done s = false ->
  dfs_step s (next_state s).
Proof.
  intros. destruct s. destruct p. destruct p. destruct p. destruct p. destruct p. destruct p.
  remember (g0, f, t2, t1, n, t0, t, s) as st. 
  destruct (start_new (pop_stack s t) t0) eqn : ?.
  - assert ( t=get_remain_f st) by (subst; reflexivity). rewrite H1 in Heqs0.
    assert (t0 = get_remain_d st) by (subst; reflexivity). rewrite H2 in Heqs0.
    assert (s = get_stack st) by (subst; reflexivity). rewrite H3 in Heqs0.
    rewrite <- done_condition in Heqs0. rewrite Heqs0 in H0. inversion H0. apply H.
  - unfold next_state. rewrite Heqst. simpl. rewrite Heqs0. destruct p.
    destruct (S.mem t3 t0) eqn : ?.
    + destruct o0. apply dfs_discover_child. assumption. symmetry. assumption.
      apply dfs_discover_root. assumption. symmetry. apply Heqs0.
    + destruct (S.mem t3 t) eqn : ?.
      * eapply dfs_finish. apply Heqb. apply Heqb0. rewrite Heqs0. reflexivity.
      * destruct (pop_stack s t) eqn : ?.
        -- simpl in Heqs0. destruct (S.min_elt t0) eqn : ?.
          ++ inversion Heqs0; subst. apply S.min_elt_1 in Heqo1. apply S.mem_1 in Heqo1. 
             rewrite Heqo1 in Heqb. inversion Heqb.
          ++ inversion Heqs0.
        -- simpl in Heqs0; subst. inversion Heqs0; subst. apply pop_stack_cons in Heqs1.
           rewrite Heqs1 in Heqb0. inversion Heqb0.
Qed.

(*The actual executable. Note that we return a proof that the resulting state is done and that the original
  step multisteps to it. This allows us to use all the theorems that we have (and will) proved about valid, done
  states without having to prove it from the [dfs_exec] function directly*)
Program Fixpoint dfs_exec (s: state) g o (H: valid_dfs_state s g o) {measure (measure_dfs s)} :
 {s' : state | dfs_multi s s' /\ done s' = true}  :=
  if bool_dec (done s) true then exist _ s _ else exist _ (proj1_sig (dfs_exec (next_state s) g o _)) _.
Next Obligation.
split. apply multi_refl. apply H0.
Defined.
Next Obligation.
eapply step. apply H. eapply step_next_state. apply H. destruct (done s). contradiction. reflexivity.
Defined.
Next Obligation.
apply step_measure_lt. eapply step_next_state. apply H. destruct (done s). contradiction. reflexivity.
Defined.
Next Obligation.  
remember
     (dfs_exec (next_state s) g o (dfs_exec_func_obligation_2 s g o H H0) (dfs_exec_func_obligation_3 s g o H H0))
as p. destruct Heqp. destruct p. simpl. destruct a. split. eapply multi_trans. apply multi_R. eapply step_next_state.
apply H. destruct (done s). contradiction. reflexivity. apply H1. apply H2.
Defined. 

(*Falls out as a simple corollary of the above. This succests that our choice of [done] was a 
  reasinable one*)
Lemma progress: forall s g o,
  valid_dfs_state s g o ->
  (exists s', dfs_step s s') <-> done s = false.
Proof.
  intros. split; intros.
  - destruct (done s) eqn : ?. eapply done_cannot_step in Heqb. contradiction.
    apply H. reflexivity.
  - exists (next_state s). eapply step_next_state. apply H. apply H0.
Qed.

(*Any valid dfs state multisteps to a finished state*)
Lemma all_finish: forall s g o,
  valid_dfs_state s g o ->
  exists s', dfs_multi s s' /\ done s' = true.
Proof.
  intros. pose proof dfs_exec. specialize (X s g o H). destruct X. exists x. apply a.
Qed.

(** Reasoning about the stack **)

(*Helper lemmas for dealing with [app], since we will be using it a lot when reaonsing about
  where vertices are on the stack in relation to each other*)
Lemma pop_stack_app: forall l r,
  exists l1 l2, 
  l = l1 ++ l2 /\ pop_stack l r = l2.
Proof.
  intros. induction l; simpl.
  - exists nil. exists nil. split; reflexivity.
  - destruct a. destruct (S.mem t r) eqn : ?; simpl.
    + exists nil. exists ((t,o)::l). split; reflexivity.
    + destruct IHl. destruct H. exists ((t,o) :: x). exists x0.
      split. simpl. destruct H; rewrite H; reflexivity. destruct H; assumption.
Qed.

Lemma one_none_in_list: forall (x1: stack) x t o0 s x0,
(x1 ++ (x, None) :: (t, o0) :: s = x0 ++ (x, None) :: nil /\ forall y : O.t, ~ In (y, None) x0) -> False.
Proof.
  intros. destruct H. generalize dependent x1. induction x0; intros; simpl in *.
  - destruct x1. inversion H. inversion H. destruct x1; inversion H3.
  - destruct x1; simpl in *. 
    + inversion H; subst. apply (H0 x). left. reflexivity.
    + inversion H; subst. eapply IHx0. intros. intro. eapply H0. right. apply H1.
      apply H3.
Qed.

Lemma app_inversion: forall (A: Type) (x: A) y l1 l2,
  l1 ++ (x :: nil) = l2 ++ (y :: nil) ->
  l1 = l2 /\ x = y.
Proof.
  intros. generalize dependent l2. induction l1; intros; subst; simpl in *.
  - destruct l2. split. reflexivity. inversion H. reflexivity.
    inversion H. destruct l2; inversion H2.
  - destruct l2; simpl in H.
    + inversion H. destruct l1; inversion H2.
    + inversion H. apply IHl1 in H2. destruct H2; subst; split; reflexivity.
Qed. 

Lemma app_inversion_2: forall (A: Type) (x:A) l l1 l2,
  l2 <> nil ->
  l1 ++ l2 = l ++ (x:: nil) ->
  exists l3, l2 = l3 ++ (x:: nil).
Proof.
  intros. generalize dependent l1. revert l. induction l2; intros; simpl in *.
  - contradiction.
  - destruct l1; simpl in *. destruct l; simpl in *. inversion H0; subst. 
    exists nil. reflexivity. inversion H0; subst. exists (a0 :: l). reflexivity.
    destruct l; simpl in *. inversion H0; subst.
     pose proof (app_cons_not_nil l1 l2 a). rewrite H3 in H1. contradiction. inversion H0; subst.
    destruct l2; simpl in *. apply app_inversion in H3. destruct H3; subst. exists nil. reflexivity.
    assert (a0 :: l2 <> nil). intro. inversion H1.
    destruct (IHl2 H1 l ( l1 ++ a ::  nil)). simpl. rewrite <- H3.
    rewrite <- app_assoc. simpl. reflexivity. exists (a :: x0). rewrite H2. reflexivity.
Qed.  

Lemma app_inversion_3: forall (A: Type) l1 l2 l3 x (y: A),
  l1 ++ x :: nil = l2 ++ y :: l3 ->
  (exists l4, l4 ++ x :: nil = y :: l3).
Proof.
  intros. generalize dependent l1. revert l3. induction l2; intros; subst; simpl in *.
  - exists l1. apply H.
  - destruct l1; simpl in *.
    + inversion H. destruct l2; inversion H2.
    + inversion H; subst. eapply IHl2. apply H2.
Qed.

(*Random helper lemmas about [add_to_stack] and [pop_stack] TODO: move these*)

Lemma add_to_stack_adds_parent: forall v g r x y,
  In (x,y) (add_to_stack v g r) ->
  y = Some v.
Proof.
  intros. unfold add_to_stack in H. destruct (G.neighbors_set g v).
  assert (forall x y l, In (x,y)(fold_right (fun (v0 : S.elt) (t : list (S.elt * option O.t)) => 
        if S.mem v0 (S.remove v r) then (v0, Some v) :: t else t)
         nil l) -> y = Some v). { intros. induction l; simpl in H0. destruct H0.
        destruct (S.mem a (S.remove v r)). simpl in H0. destruct H0. inversion H0. reflexivity. apply IHl.
        apply H0. apply IHl. apply H0. }
  eapply H0. apply H. inversion H.
Qed.


Lemma pop_stack_inversion: forall l1 l2 x r y,
  pop_stack (l1 ++ x :: nil) r = l2 ++ x :: nil ->
  In y l2 -> In y (pop_stack l1 r).
Proof.
  intros. generalize dependent l2. induction l1; intros; simpl in *.
  - destruct x. destruct (S.mem t r) eqn : ?; simpl in H.
    + destruct l2. inversion H0. inversion H. destruct l2; inversion H3.
    + destruct l2; inversion H.
  - destruct a. destruct (S.mem t r) eqn : ?; simpl in *.
    + apply (app_inversion _ x x ((t,o) :: l1) l2) in H. destruct H; inversion H; subst.
      simpl in H0. apply H0.
    + eapply IHl1. apply H. apply H0.
Qed.

(*There is only 1 root, namely, there is a single vertex on the stack (at the very end)
  without a parent; everyone else has a parent*)
Lemma only_1_root: forall s g o x,
  valid_dfs_state s g o ->
  In (x, None) (get_stack s) ->
  exists l, get_stack s = l ++ (x, None) :: nil /\ forall y, ~In (y, None) l.
Proof.
  intros. generalize dependent x. induction H; intros; simpl in *.
  - destruct o. destruct (G.contains_vertex g v).
    + simpl in H0. destruct H0. inversion H; subst. exists nil. split. reflexivity.
      intros. intro. inversion H0. destruct H.
    + inversion H0.
    + inversion H0.
  - inversion H0; subst; simpl in *.
    + destruct (add_to_stack x0 g0 remain_d) eqn : ?.
      * simpl in H1. destruct H1. 
        -- inversion H1; subst. destruct (pop_stack st remain_f) eqn : ?.
           ++ simpl in H3. destruct (S.min_elt remain_d) eqn : ?.
              ** inversion H3; subst. exists nil. split. reflexivity. intros. intro. inversion H4.
              ** inversion H3.
           ++ simpl in H3. assert (In (x, None) st). eapply in_pop_rev. rewrite Heqs0. inversion H3; subst.
              left. reflexivity. apply IHvalid_dfs_state in H4. destruct H4. simpl in *.
              inversion H3; subst. destruct s. exists nil. split. reflexivity. intros. intro. inversion H5.
              destruct p.
              pose proof (pop_stack_app st remain_f). destruct H5. destruct H5. destruct H5.
              rewrite Heqs0 in H6. inversion H6; subst. destruct H4. exfalso. eapply one_none_in_list.
              split. apply H4. apply H5.
        -- simpl in *. 
           destruct (pop_stack st remain_f) eqn : ?; simpl in H3.
           ++ destruct (S.min_elt remain_d). inversion H3; subst. inversion H1. subst. inversion H3.
           ++ pose proof (pop_stack_app st remain_f). destruct H4. destruct H4. destruct H4.
              rewrite Heqs0 in H5. inversion H5; subst. inversion H3; subst. destruct (IHvalid_dfs_state x).
              apply in_or_app. right. right. apply H1. destruct H4. destruct s; simpl in *.
              apply app_inversion in H4. destruct H4. inversion H7; subst. exists nil. split.
              reflexivity. intros. intro. inversion H4. destruct p. destruct H1. inversion H1; subst.
              destruct s; simpl in *. pose proof (app_inversion _ (x, None) (x, None) (x1 ++ (x0, None) :: nil) (x2)).
              assert ((x1 ++ (x0, None) :: nil) ++ (x, None) :: nil = x1 ++ (x0, None) :: (x, None) :: nil ).
              rewrite <- app_assoc. simpl. reflexivity. rewrite H8 in H7. apply H7 in H4. destruct H4.
              clear H7. clear H8. rewrite <- H4 in H5. exfalso. apply (H5 x0). apply in_or_app.
              right. left. reflexivity. pose proof app_inversion_2. specialize (H7 _ (x, None) x2
              (x1 ++ (x0, None) ::(x, None) :: nil) (p::s)). destruct H7.
              intro. inversion H7. rewrite <- H4. rewrite  <- app_assoc. reflexivity.
              rewrite H7 in H4. 
              assert ((x1 ++ (x0, None) :: (x, None) :: x3) ++ (x, None) :: nil = 
              x1 ++ (x0, None) :: (x, None) :: x3 ++ (x, None) :: nil). rewrite <- app_assoc. reflexivity.  
                pose proof (app_inversion _ (x, None) (x, None) 
              (x1 ++ (x0, None) :: (x, None) :: x3) x2). destruct H9. rewrite H8. apply H4. 
              rewrite <- H9 in H5. exfalso. apply (H5 x0). apply in_or_app. right. left. reflexivity.
              destruct s; simpl in *. pose proof (app_inversion _ (t, o0) (x, None) (x1 ++ (x0, None) :: nil)
              x2). destruct H7. rewrite <- app_assoc. rewrite <- H4. reflexivity. 
              rewrite <- H7 in H5. exfalso. apply (H5 x0). apply in_or_app. right. left. reflexivity.
              pose proof (app_inversion_2 _ (x, None) x2 (x1 ++ (x0, None) :: (t, o0) :: nil) (p ::s)).
              destruct H7. intro. inversion H7. rewrite <- H4. rewrite <- app_assoc. reflexivity.
              rewrite H7 in H4. pose proof (app_inversion _ (x, None) (x, None) (x1 ++ (x0, None) :: (t, o0) :: x3)
              x2). destruct H8. rewrite <- H4. rewrite <- app_assoc. reflexivity. rewrite <- H8 in H5.
              exfalso. apply (H5 x0). apply in_or_app. right. left. reflexivity.
      * simpl in H1. destruct H1. assert (None = Some x0). eapply add_to_stack_adds_parent.
        rewrite Heqs. rewrite H1. left. reflexivity. inversion H4.
        apply in_app_or in H1. destruct H1. assert (None = Some x0). eapply add_to_stack_adds_parent.
        rewrite Heqs. right. apply H1. inversion H4. destruct (pop_stack st remain_f) eqn : ?.
        -- simpl in H3. destruct (S.min_elt remain_d). inversion H3; subst. simpl in H1.
           destruct H1. inversion H1; subst. exists (p :: s). split. reflexivity.
           intros. intro. rewrite <- Heqs in H4. assert (None = Some x). eapply add_to_stack_adds_parent.
           apply H4. inversion H5. destruct H1. inversion H3.
        -- simpl in H3. rewrite <- Heqs0 in H3. assert (In (x, None) st). eapply in_pop_rev.
           rewrite <- H3. apply H1. apply IHvalid_dfs_state in H4. destruct H4. destruct H4.
           pose proof (pop_stack_app st remain_f). destruct H6. destruct H6. destruct H6.
           rewrite H4 in H6. subst. rewrite <- H3 in H6. 
           destruct tl; simpl in *. apply app_inversion in H6. destruct H6. inversion H6; subst.
           exists (p :: s). split. reflexivity. intros. intro. assert (None = Some x0). eapply
           add_to_stack_adds_parent. rewrite Heqs. apply H4. inversion H7.
           pose proof (app_inversion_2 _ (x, None) x1 (x2 ++ (x0, None) :: nil) (p1 :: tl)).
           destruct H4. intro. inversion H4. rewrite H6. rewrite <- app_assoc. reflexivity.
           rewrite H4 in H6. pose proof (app_inversion  _ (x, None) (x, None) x1 (x2 ++ (x0, None) :: x3)).
            destruct H7. rewrite H6. rewrite <- app_assoc. reflexivity. 
           rewrite H7 in H5. exfalso. apply (H5 x0). apply in_or_app. right. left. reflexivity.
    + destruct (pop_stack st remain_f) eqn : ?.
      * simpl in H3. destruct (S.min_elt remain_d); inversion H3.
      * simpl in H3. rewrite <- H3 in Heqs. apply in_app_or in H1. destruct H1.
        apply add_to_stack_adds_parent in H1. inversion H1.
        assert (In (x, None) st). eapply in_pop_rev. rewrite Heqs. apply H1. apply IHvalid_dfs_state in H4.
        destruct H4. destruct H4. pose proof (pop_stack_app st remain_f). destruct H6. destruct H6.
        destruct H6. subst. rewrite Heqs in H6. apply app_inversion_3 in H6.
        destruct H6. exists (add_to_stack x0 g0 remain_d ++ x3). split. rewrite <- app_assoc. rewrite <- H4.
        reflexivity. intros. intro. apply in_app_or in H6. destruct H6.
        apply add_to_stack_adds_parent in H6. inversion H6. assert (In (y0, None) x1).
        rewrite <- H4 in Heqs. 
        eapply in_pop_rev. eapply pop_stack_inversion in Heqs. apply Heqs. apply H6. 
        apply (H5 y0). apply H7.
    + destruct (pop_stack st remain_f) eqn : ?.
      * simpl in H4. destruct (S.min_elt remain_d). inversion H4; subst. 
        inversion H1. inversion H4.
      * simpl in H4. inversion H4; subst. 
        assert (In (x, None) st). eapply in_pop_rev. rewrite Heqs. simpl. right. apply H1.
        apply IHvalid_dfs_state in H5. destruct H5. destruct H5. 
        pose proof (pop_stack_app st remain_f). destruct H7. destruct H7. destruct H7. subst.
        rewrite Heqs in H7. destruct s; simpl in *. inversion H1.  symmetry in H7.
        pose proof (app_inversion_2 _ (x, None) x1 (x2 ++ (x0, o0) :: nil) (p :: s)).
        destruct H5. intro. inversion H5. rewrite <- H7. rewrite <- app_assoc. reflexivity.
        exists x3. split. apply H5. rewrite H5 in H7. pose proof (app_inversion _ (x, None)
        (x, None) x1 (x2 ++ (x0, o0) :: x3)). destruct H8. rewrite <- H7. rewrite <- app_assoc.
        reflexivity. intros. intro. rewrite H8 in H6. apply (H6 y). apply in_or_app. right. right.
        apply H10.
Qed. 

Lemma stack_elt_dec: forall (x y: O.t * option O.t),
  {x = y} + {x <> y}.
Proof.
decide equality.  subst. destruct b. destruct o.
destruct (O.eq_dec t0 t1). rewrite e. left. reflexivity.
right. intro. inversion H; subst. apply n. reflexivity.
right. intro. inversion H.
destruct o. right. intro. inversion H.
left. reflexivity. simpl in *.
apply O.eq_dec.
Qed.

Lemma in_split_list: forall (l: stack) x,
  (exists y, In (x, y) l) ->
  exists l1 l2 y, l1 ++ (x, y) :: l2 = l /\ forall y', ~In (x, y') l1.
Proof.
  intros. induction l.
  - destruct H. inversion H.
  - simpl in H. destruct H.  destruct a. destruct (O.eq_dec t x).
    + unfold O.eq in e. subst. destruct H.
      * inversion H; subst. exists nil. exists l. exists x0. split. reflexivity.
        intros. intro. inversion H0.
      * exists nil. exists l. exists o. split. reflexivity. intros. intro. inversion H0.
    + destruct H. inversion H; subst. exfalso. apply n. reflexivity. destruct IHl.
      exists x0. apply H. destruct H0. destruct H0. destruct H0. rewrite <- H0.
      exists ((t, o) :: x1). exists x2. exists x3. split. reflexivity. intros. intro.
      destruct H2. inversion H2; subst. apply n. reflexivity. apply (H1 y'). apply H2.
Qed.


Lemma gray_list: forall s g o v,
  valid_dfs_state s g o ->
  gray s v = true ->
  exists l1 l2 p, l1 ++ (v, p) :: l2 = get_stack s /\ forall p', ~In (v, p') l1.
Proof.
  intros. eapply gray_on_stack in H0. destruct H0. destruct (in_split_list (get_stack s) v).
  exists x. apply H0. exists x0. apply H1. apply H.
Qed. 

(*More helper lemmas about [add_to_stack]*)
Lemma only_add_yet_to_be_discovered: forall v g r x y,
  In (x,y) (add_to_stack v g r) ->
  S.mem x r = true.
Proof.
  intros. unfold add_to_stack in H. destruct (G.neighbors_set g v).
  assert (forall x y l, In (x, y)
      (fold_right
         (fun (v0 : S.elt) (t : list (S.elt * option O.t)) =>
          if S.mem v0 (S.remove v r) then (v0, Some v) :: t else t) nil l) -> S.mem x r = true). { 
  intros. induction l; simpl in H0. destruct H0. destruct (S.mem a (S.remove v r) )eqn : ?.
        simpl in H0. destruct H0. inversion H0; subst. rewrite P2.Dec.F.remove_b in Heqb.
        rewrite andb_true_iff in Heqb. destruct Heqb. apply H1.
 all: apply IHl; apply H0. }
  eapply H0. apply H. inversion H.
Qed.

Lemma add_to_stack_neq: forall v g r x y,
  In (x,y) (add_to_stack v g r) ->
  x <> v.
Proof.
  intros. unfold add_to_stack in H. destruct (G.neighbors_set g v) eqn : ?.
  - assert (forall x y l, In (x,y)(fold_right
         (fun (v0 : S.elt) (t : list (S.elt * option O.t)) =>
          if S.mem v0 (S.remove v r) then (v0, Some v) :: t else t) nil l) -> x <> v). {
  intros. induction l. simpl in H0. destruct H0. simpl in H0.
  destruct (S.mem a (S.remove v r)) eqn : ?. simpl in H0. destruct H0.
  inversion H0; subst. intro; subst. rewrite P2.Dec.F.remove_b in Heqb.
  rewrite andb_true_iff in Heqb. destruct Heqb. unfold P2.Dec.F.eqb in H2.
  destruct (O.eq_dec v v ). inversion H2. apply n. apply eq_refl.
  apply IHl. apply H0. apply IHl. apply H0. } eapply H0.
  apply H.
  - inversion H.
Qed.
(*Parents of vertices are not white. Later I prove that parents are gray, but I'm not sure if I use either
  of these*)
Lemma parents_not_white: forall s g o x y,
  valid_dfs_state s g o ->
  In (x, Some y) (get_stack s) ->
  white s y = false.
Proof.
  intros. unfold white. induction H; subst; simpl in *.
  - destruct o. destruct (G.contains_vertex g v). inversion H0. inversion H. inversion H. inversion H0.
    inversion H0.
  - inversion H1; subst; simpl in *.
    + simplify. apply in_app_or in H0. destruct H0.
      * apply add_to_stack_adds_parent in H0. inversion H0; subst. left. 
        destruct (S.mem x0 (S.remove x0 remain_d)) eqn : ?. exfalso. eapply remove_eq. apply Heqb. reflexivity.
      * destruct (pop_stack st remain_f) eqn : ?.
        -- simpl in H3. destruct (S.min_elt remain_d); inversion H3; subst. simpl in H0.
           destruct H0; inversion H0.
        -- simpl in H3. rewrite <-  H3 in Heqs. destruct IHvalid_dfs_state. eapply in_pop_rev. rewrite Heqs. apply H0.
           left. rewrite P2.FM.remove_b. simplify. right. apply H4.
   + simplify. apply in_app_or in H0. destruct H0.
      * apply add_to_stack_adds_parent in H0. inversion H0; subst. left. 
        destruct (S.mem x0 (S.remove x0 remain_d)) eqn : ?. exfalso. eapply remove_eq. apply Heqb. reflexivity.
      * destruct (pop_stack st remain_f) eqn : ?.
        -- simpl in H3. destruct (S.min_elt remain_d); inversion H3; subst. 
        -- simpl in H3. rewrite <-  H3 in Heqs. destruct IHvalid_dfs_state. eapply in_pop_rev. rewrite Heqs. apply H0.
           destruct (O.eq_dec x0 y). rewrite e in H2. rewrite H2 in H4. inversion H4. 
           left. rewrite P2.FM.remove_b. simplify. right. apply H4.
    + simplify. destruct (pop_stack st remain_f) eqn : ?.
      * simpl in H4. destruct (S.min_elt remain_d); inversion H4; subst. inversion H0.
      * simpl in H4. rewrite <- H4 in Heqs. destruct IHvalid_dfs_state.
        eapply in_pop_rev. rewrite Heqs. right. apply H0.
        left. apply H5. right. rewrite P2.FM.remove_b. simplify.
Qed.

Lemma root_nil: forall s g o v l tl,
  valid_dfs_state s g o ->
  get_stack s = l ++ (v, None) :: tl ->
  tl = nil.
Proof.
  intros. pose proof only_1_root. specialize (H1 s g o v H). destruct H1.
  - rewrite H0. apply in_or_app. right. left. reflexivity.
  - destruct tl. reflexivity. destruct H1. rewrite H1 in H0.
    pose proof (app_inversion_2 _ (v, None) x (l ++ (v, None) :: nil) (p :: tl)). destruct H3.
    intro. inversion H3. rewrite H0. rewrite <- app_assoc. reflexivity. rewrite H3 in H0.
    pose proof (app_inversion _ (v, None) (v, None) x (l ++ (v, None) :: x0)). destruct H4.
    rewrite H0. rewrite <- app_assoc. reflexivity. rewrite H4 in H2. exfalso. apply (H2 v).
    apply in_or_app. right. left. reflexivity.
Qed. 
(*more helpers*)
Lemma pair_neq_add_to_stack: forall v g r x y,
  In (x, Some y) (add_to_stack v g r) ->
  x <> y.
Proof.
  intros. unfold add_to_stack in H. assert (forall x y l,
  In (x, Some y) (fold_right
            (fun (v0 : S.elt) (t : list (S.elt * option O.t)) =>
             if S.mem v0 (S.remove v r) then (v0, Some v) :: t else t) nil l )->  x <> y).
{ intros. induction l. simpl in H0. destruct H0. simpl in H0. destruct (S.mem a (S.remove v r)) eqn : ?.
  simpl in H0. destruct H0. inversion H0; subst. intro. subst. eapply remove_eq. apply Heqb.
  apply IHl; assumption. apply IHl; assumption. }
  destruct (G.neighbors_set g v). eapply H0. apply H. inversion H.
Qed.

Lemma neq_parent: forall s g o x y,
  valid_dfs_state s g o ->
  In (x, Some y) (get_stack s) ->
  x <> y.
Proof.
  intros. induction H; subst; simpl in *.
  - destruct o. destruct (G.contains_vertex g v). inversion H0. inversion H. inversion H.
    inversion H0. inversion H0. 
  - inversion H1; subst; simpl in *.
    + apply in_app_or in H0. destruct H0.
      * apply pair_neq_add_to_stack in H0. assumption.
      * destruct (pop_stack st remain_f) eqn : ?; simpl in H3. destruct (S.min_elt remain_d); inversion H3; subst.
        simpl in H0. destruct H0; inversion H0. apply IHvalid_dfs_state. eapply in_pop_rev. rewrite Heqs.
        rewrite <- H3. apply H0.
    + apply in_app_or in H0. destruct H0.
      * apply pair_neq_add_to_stack in H0. assumption.
      * destruct (pop_stack st remain_f) eqn : ?; simpl in H3. destruct (S.min_elt remain_d); inversion H3; subst.
         apply IHvalid_dfs_state. eapply in_pop_rev. rewrite Heqs.
        rewrite <- H3. apply H0.
    + destruct (pop_stack st remain_f) eqn : ?; simpl in H4. destruct (S.min_elt remain_d); inversion H4; subst.
      destruct H0. apply IHvalid_dfs_state. eapply in_pop_rev. rewrite Heqs. rewrite <- H4. right. apply H0.
Qed.

(*Ltac for solving statements of the form: In x l, where l may be many lists appended together*) 
Ltac solve_in :=
  match goal with
  | [ H : _ |- In ?x (?l ++ ?r)] => apply in_or_app; solve_in
  | [ H : _ |- In ?x ?s \/ In ?x ?s'] => (right; solve_in) + (left; solve_in) 
  | [ H : _ |- In ?x (?x :: ?l)] => simpl; left; reflexivity
  | [H : _ |- In ?x (?a :: ?l)] => simpl; right; solve_in
  | [ H : _ |- _ ] => try(reflexivity); assumption
end. 

Ltac destruct_all :=
repeat(match goal with
            |[H: (exists _, _) |- _] => destruct H
            |[H: _ /\ _ |- _] => destruct H 
            end; try(rewrite andb_true_iff in *)).

(*More helpers about [app] and [pop_stack]*)
Lemma app_match: forall (A: Type) (l1: list A) l2 l3 l4,
  l1 ++ l2 = l3 ++ l4 ->
  (exists x, l1 = l3 ++ x) \/ (exists x, l3 = l1 ++ x).
Proof.
  intros. revert H. revert l3. induction l1; intros; subst.
  - right. exists l3. reflexivity.
  - simpl in H. destruct l3; simpl in H.
    left. exists (a :: l1). reflexivity. inversion H; subst.
    apply IHl1 in H2. destruct H2.
    + left. destruct H0. rewrite H0. exists x. reflexivity.
    + right. destruct_all. exists x. rewrite H0. reflexivity.
Qed.

Lemma pop_stack_delete: forall s r a b,
  In (a,b) s ->
  S.mem a r = false \/ In (a,b) (pop_stack s r).
Proof.
  intros. induction s.
  - inversion H.
  - simpl in *. destruct a0. destruct H.
    + inversion H; subst. destruct (S.mem a r) eqn : ?.
      * simpl. right. left. reflexivity.
      * simpl. left. reflexivity.
    + destruct (S.mem a r) eqn : ?; simpl.
      * right. destruct (S.mem e r) eqn : ?; simpl.
        -- right. apply H.
        -- apply IHs in H. destruct H. inversion H. apply H.
      * left. reflexivity.
Qed.

Lemma pop_stack_app_distr: forall l1 l2 a b r,
   S.mem a r = true -> pop_stack (l1 ++ (a,b) :: l2) r = (pop_stack l1 r) ++ ((a,b) :: l2).
Proof.
  intros. generalize dependent l2. induction l1; subst; intros.
    + simpl. rewrite H. simpl. reflexivity.
    + simpl in *. destruct a0. destruct (S.mem e r) eqn : ?; simpl. reflexivity.
      apply IHl1.
Qed. 

(*Proving that what we add to the stack is sorted is overkill but useful for proving that there
  are no duplicates inside this list*)

(*Predicate for proving the result of add_to_stack is sorted*)
Definition pair_lt (x y : vertex * option vertex) : Prop :=
  match x,y with
  | (a,b), (c,d) => O.lt a c
  end.

(*The result of add_to_stack is sorted by vertex. This obviously proves the claim for
  the part of the stack added by [add_to_stack]*)
Lemma add_to_stack_sorted: forall v g r,
  StronglySorted pair_lt (add_to_stack v g r).
Proof.
  intros. unfold add_to_stack.
  assert (forall (l: list vertex) (a: vertex) (y: option vertex), Forall (O.lt a) l ->
  Forall (pair_lt (a,y))  (fold_right (fun (v0 : S.elt) (t : list (S.elt * option O.t)) => 
    if S.mem v0 (S.remove v r) then (v0, Some v) :: t else t) nil l)).
  { intros. induction l.
    - simpl. constructor.
    - simpl. inversion H; subst. destruct (S.mem a0 (S.remove v r)). constructor. unfold pair_lt. apply H2.
      apply IHl. apply H3. apply IHl. apply H3. }
 assert (forall l, StronglySorted O.lt l ->
  StronglySorted pair_lt (fold_right (fun (v0 : S.elt) (t : list (S.elt * option O.t)) => 
    if S.mem v0 (S.remove v r) then (v0, Some v) :: t else t) nil l)).
  { intros. induction l.
    - simpl. constructor.
    - simpl. inversion H0; subst. destruct (S.mem a (S.remove v r)). constructor.
      + apply IHl. apply H3.
      + apply H. apply H4.
      + apply IHl. apply H3. }
 destruct (G.neighbors_set) eqn : ?.
  - apply H0. apply Sorted_StronglySorted.  unfold Relations_1.Transitive. apply O.lt_trans.
    apply S.elements_3.
  - constructor.
Qed. 

(*Probably proved somewhere*)
Lemma Forall_all: forall A (l1: list A) l2 R,
  Forall R (l1 ++ l2) ->
  Forall R l1 /\ Forall R l2.
Proof.
  intros. generalize dependent l2. induction l1; intros.
  - simpl in H. split. constructor. apply H.
  - simpl in H. inversion H; subst. split.
    constructor. apply H2. apply (IHl1 l2). apply H3. apply (IHl1 l2). apply H3.
Qed.

(*Same as above, if concatenation of lists is sorted, so are both of the lists*)
Lemma sort_app: forall A (l1: list A) l2 R,
  StronglySorted R (l1 ++ l2) ->
  StronglySorted R l1 /\ StronglySorted R l2.
Proof.
  intros. generalize dependent l2. induction l1; intros.
  - simpl in H. split. constructor. apply H.
  - simpl in H. inversion H; subst.
    split. constructor. apply (IHl1 l2). apply H2.
    apply (Forall_all _ _ _ _ H3). apply IHl1. apply H2.
Qed.

(** Results about times **)

(*The discovery time of any vertex cannot occur in the future*)
Lemma d_times_leq_current_time: forall s g o v n,
  valid_dfs_state s g o ->
  M.find v (get_d_times s) = Some n ->
  n <= get_time s.
Proof.
  intros. induction H; subst; simpl in *.
  - rewrite F.empty_o in H0. inversion H0.
  - inversion H1; subst; simpl in *.
    + destruct (O.eq_dec v x).
      * unfold O.eq in e. subst. rewrite F.add_eq_o in H0. inversion H0; subst. omega.
        reflexivity.
      * rewrite P.F.add_neq_o in H0. apply IHvalid_dfs_state in H0. omega. intuition.
    + destruct (O.eq_dec v x).
      * unfold O.eq in e. subst. rewrite F.add_eq_o in H0. inversion H0; subst. omega.
        reflexivity.
      * rewrite P.F.add_neq_o in H0. apply IHvalid_dfs_state in H0. omega. intuition.
    + apply IHvalid_dfs_state in H0. omega.
Qed.

(*Two vertices share a discovery time iff they are the same vertex*)
Lemma d_times_unique: forall s g o v u n m,
  valid_dfs_state s g o ->
  M.find v (get_d_times s) = Some n ->
  M.find u (get_d_times s) = Some m ->
  (n = m) <-> (u = v).
Proof.
  intros. split; intros; subst. induction H; subst; simpl in *.
  - rewrite F.empty_o in H0. inversion H0.
  - inversion H2; subst; simpl in *.
    + destruct (O.eq_dec u x).
      * unfold O.eq in e. subst. rewrite F.add_eq_o in H1. inversion H1; subst.
        destruct (O.eq_dec v x). unfold O.eq in e. subst. reflexivity.
        rewrite P.F.add_neq_o in H0. remember (g0, f, f_times, d_times, time, remain_d, remain_f, st) as s.
        assert (M.find v (get_d_times s) = Some (time + 1)) by (subst; simpl; assumption).
        eapply d_times_leq_current_time in H5. subst; simpl in *. omega. apply H. intuition. reflexivity.
      * rewrite P.F.add_neq_o in H1. destruct (O.eq_dec v x). unfold O.eq in e. subst.
        rewrite F.add_eq_o in H0. inversion H0; subst. 
        remember (g0, f, f_times, d_times, time, remain_d, remain_f, st) as s'.
        assert (M.find u (get_d_times s') = Some (time + 1)) by (subst; simpl; assumption).
        eapply d_times_leq_current_time in H5. subst; simpl in *. omega. apply H. reflexivity.
        rewrite P.F.add_neq_o in H0. apply IHvalid_dfs_state; assumption. intuition. intuition.
    + destruct (O.eq_dec u x).
      * unfold O.eq in e. subst. rewrite F.add_eq_o in H1. inversion H1; subst.
        destruct (O.eq_dec v x). unfold O.eq in e. subst. reflexivity.
        rewrite P.F.add_neq_o in H0. remember (g0, f, f_times, d_times, time, remain_d, remain_f, st) as s.
        assert (M.find v (get_d_times s) = Some (time + 1)) by (subst; simpl; assumption).
        eapply d_times_leq_current_time in H5. subst; simpl in *. omega. apply H. intuition. reflexivity.
      * rewrite P.F.add_neq_o in H1. destruct (O.eq_dec v x). unfold O.eq in e. subst.
        rewrite F.add_eq_o in H0. inversion H0; subst. 
        remember (g0, f, f_times, d_times, time, remain_d, remain_f, st)as s'.
        assert (M.find u (get_d_times s') = Some (time + 1)) by (subst; simpl; assumption).
        eapply d_times_leq_current_time in H5. subst; simpl in *. omega. apply H. reflexivity.
        rewrite P.F.add_neq_o in H0. apply IHvalid_dfs_state; assumption. intuition. intuition.
    + apply IHvalid_dfs_state; assumption.
  - rewrite H1 in H0. inversion H0; subst; reflexivity.
Qed.

(*Analogous results for finish times*)
Lemma f_times_leq_current_time: forall s g o v n,
  valid_dfs_state s g o ->
  M.find v (get_f_times s) = Some n ->
  n <= get_time s.
Proof.
  intros. induction H; subst; simpl in *.
  - rewrite F.empty_o in H0. inversion H0.
  - inversion H1; subst; simpl in *.
    + apply IHvalid_dfs_state in H0. omega.
    + apply IHvalid_dfs_state in H0. omega.
    + destruct (O.eq_dec v x).
      * unfold O.eq in e. subst. rewrite F.add_eq_o in H0. inversion H0; subst. omega.
        reflexivity.
      * rewrite P.F.add_neq_o in H0. apply IHvalid_dfs_state in H0. omega. intuition.
Qed.

(*Two vertices share a discovery time iff they are the same vertex*)
Lemma f_times_unique: forall s g o v u n m,
  valid_dfs_state s g o ->
  M.find v (get_f_times s) = Some n ->
  M.find u (get_f_times s) = Some m ->
  (n = m) <-> (u = v).
Proof.
  intros. split; intros; subst. induction H; subst; simpl in *.
  - rewrite F.empty_o in H0. inversion H0.
  - inversion H2; subst; simpl in *.
    + apply IHvalid_dfs_state; assumption.
    + apply IHvalid_dfs_state; assumption.
    + destruct (O.eq_dec u x).
      * unfold O.eq in e. subst. rewrite F.add_eq_o in H1. inversion H1; subst.
        destruct (O.eq_dec v x). unfold O.eq in e. subst. reflexivity.
        rewrite P.F.add_neq_o in H0. remember (g0, f, f_times, d_times, time, remain_d, remain_f, st) as s.
        assert (M.find v (get_f_times s) = Some (time + 1)) by (subst; simpl; assumption).
        eapply f_times_leq_current_time in H6. subst; simpl in *. omega. apply H. intuition. reflexivity.
      * rewrite P.F.add_neq_o in H1. destruct (O.eq_dec v x). unfold O.eq in e. subst.
        rewrite F.add_eq_o in H0. inversion H0; subst. 
        remember (g0, f, f_times, d_times, time, remain_d, remain_f, st) as s'.
        assert (M.find u (get_f_times s') = Some (time + 1)) by (subst; simpl; assumption).
        eapply f_times_leq_current_time in H6. subst; simpl in *. omega. apply H. reflexivity.
        rewrite P.F.add_neq_o in H0. apply IHvalid_dfs_state; assumption. intuition. intuition.
  - rewrite H1 in H0. inversion H0; subst; reflexivity.
Qed.

Lemma remove_eq_false: forall s x,
  S.mem x (S.remove x s) = false.
Proof.
  intros. destruct (S.mem x (S.remove x s)) eqn : ?.
  - exfalso. eapply remove_eq. apply Heqb.
  - reflexivity.
Qed.

(*results about the forest*)
Lemma white_not_in_forest: forall s g o v,
  valid_dfs_state s g o ->
  white s v = true ->
  F.contains_vertex (get_forest s) v = false.
Proof.
  intros. unfold white in *. induction H; subst; simpl in *.
  - pose proof F.empty_1. rewrite F.empty_2 in H. apply H.
  - inversion H1; subst; simpl in *; simplify.
    + destruct (O.eq_dec x v).
      * unfold O.eq in e. subst. rewrite remove_eq_false in H4. inversion H4.
      * rewrite P2.FM.remove_neq_b in H4. destruct (F.contains_vertex (F.add_root f x) v ) eqn : ?.
        -- apply F.add_root_3 in Heqb. destruct Heqb. subst. exfalso. apply n. reflexivity. 
            rewrite H0 in H6. inversion H6. assumption. assumption.
        -- reflexivity.
        -- apply n.
    + destruct (O.eq_dec x v).
      * unfold O.eq in e. subst. rewrite remove_eq_false in H4. inversion H4.
      * rewrite P2.FM.remove_neq_b in H4. destruct (F.contains_vertex (F.add_child f y x) v ) eqn : ?.
        -- apply F.add_child_6 in Heqb. destruct Heqb. rewrite H0 in H6. inversion H6. assumption.
           assumption. subst. exfalso. apply n. reflexivity. 
        -- reflexivity.
        -- apply n.
     + destruct (O.eq_dec x v).
      * unfold O.eq in e. subst. rewrite remove_eq_false in H6. inversion H6.
      * rewrite P2.FM.remove_neq_b in H6. apply H7. apply H6. apply n.
Qed.

(*More helper lemmas: move*)
Lemma remain_d_contains_valid_vertices: forall s g o v,
  valid_dfs_state s g o ->
  S.mem v (get_remain_d s) = true ->
  G.contains_vertex g v = true.
Proof.
  intros. generalize dependent v. induction H; intros.
  - simpl in H0. rewrite G.set_of_graph_1. apply S.mem_2. apply H0.
  - inversion H0; subst; simpl in *; try (apply IHvalid_dfs_state; assumption).
    + rewrite P2.Dec.F.remove_b in H1. rewrite andb_true_iff in H1. destruct H1.
      unfold P2.Dec.F.eqb in H4. destruct (O.eq_dec x v). inversion H4.
      apply IHvalid_dfs_state. apply H1.
    + rewrite P2.Dec.F.remove_b in H1. rewrite andb_true_iff in H1. destruct H1.
      unfold P2.Dec.F.eqb in H4. destruct (O.eq_dec x v). inversion H4.
      apply IHvalid_dfs_state. apply H1.
Qed.

Lemma remain_f_contains_valid_vertices: forall s g o v,
  valid_dfs_state s g o ->
  S.mem v (get_remain_f s) = true ->
  G.contains_vertex g v = true.
Proof.
  intros. generalize dependent v. induction H; intros.
  - simpl in H0. rewrite G.set_of_graph_1. apply S.mem_2. apply H0.
  - inversion H0; subst; simpl in *; try (apply IHvalid_dfs_state; assumption).
    rewrite P2.Dec.F.remove_b in H1. rewrite andb_true_iff in H1. destruct H1.
      unfold P2.Dec.F.eqb in H5. destruct (O.eq_dec x v). inversion H5.
      apply IHvalid_dfs_state. apply H1.
Qed.

Lemma discovered_vertices_in_graph: forall s g o v n,
  valid_dfs_state s g o ->
  M.find v (get_d_times s) = Some n ->
  G.contains_vertex g v = true.
Proof.
  intros. generalize dependent n. induction H; intros.
  - simpl in H0. rewrite F.empty_o in H0. inversion H0.
  - inversion H0; subst; simpl in *.
    + destruct (O.eq_dec x v).
      * setoid_rewrite <- e. eapply remain_d_contains_valid_vertices.
        apply H. simpl. apply H2.
      * rewrite P.F.add_neq_o in H1. eapply IHvalid_dfs_state. apply H1.
        auto.
    + destruct (O.eq_dec x v).
      * setoid_rewrite <- e. eapply remain_d_contains_valid_vertices.
        apply H. simpl. apply H2. 
      * rewrite P.F.add_neq_o in H1. eapply IHvalid_dfs_state. apply H1.
        auto.
    + eapply IHvalid_dfs_state. apply H1.
Qed.

Lemma finished_vertices_in_graph: forall s g o v n,
  valid_dfs_state s g o ->
  M.find v (get_f_times s) = Some n ->
  G.contains_vertex g v = true.
Proof.
  intros. generalize dependent n. induction H; intros.
  - simpl in H0. rewrite F.empty_o in H0. inversion H0.
  - inversion H0; subst; simpl in *; try(eapply IHvalid_dfs_state; apply H1).
    destruct (O.eq_dec x v).
      * setoid_rewrite <- e. eapply remain_f_contains_valid_vertices.
        apply H. simpl. apply H3.
      * rewrite P.F.add_neq_o in H1. eapply IHvalid_dfs_state. apply H1.
        auto.
Qed.

Lemma stack_valid: forall s g o x o',
  valid_dfs_state s g o ->
  In (x, o') (get_stack s) ->
  G.contains_vertex g x = true.
Proof.
  intros. induction H; subst; simpl in *.
  - destruct o.  destruct (G.contains_vertex g v) eqn : ?.
    + simpl in H0. destruct H0. inversion H; subst. apply Heqb. destruct H.
    + inversion H0.
    + inversion H0. 
  - inversion H1; subst; simpl in *.
    + apply in_app_or in H0. destruct H0. apply only_add_yet_to_be_discovered in H0.
      eapply remain_d_contains_valid_vertices. apply H. simpl. apply H0. 
      assert (tl = nil). eapply root_nil. eapply step. apply H. apply H1. simpl. reflexivity.
      subst. simpl in H0. destruct H0. inversion H0; subst. eapply remain_d_contains_valid_vertices.
      apply H. simpl. apply H2. destruct H0.
    + apply in_app_or in H0. destruct H0. apply only_add_yet_to_be_discovered in H0.
      eapply remain_d_contains_valid_vertices. apply H. simpl. apply H0.
      destruct ((pop_stack st remain_f)) eqn : ?; simpl in H3. destruct (S.min_elt remain_d); inversion H3.
      rewrite <- H3 in Heqs. apply IHvalid_dfs_state. eapply in_pop_rev. rewrite Heqs. solve_in.
    + destruct (pop_stack st remain_f)  eqn : ?; simpl in H4.
      * destruct (S.min_elt remain_d); inversion H4; subst. inversion H0.
      * rewrite <- H4 in Heqs. apply IHvalid_dfs_state. eapply in_pop_rev. rewrite Heqs. solve_in.
Qed. 

Lemma parents_valid: forall s g o x y,
  valid_dfs_state s g o ->
  In (x, Some y) (get_stack s) ->
  G.contains_vertex g y = true.
Proof.
  intros. induction H; subst; simpl in *.
  - destruct o. destruct (G.contains_vertex). inversion H0. inversion H. inversion H. inversion H0. inversion H0.
  - inversion H1; subst; simpl in *.
    + assert (tl = nil). eapply root_nil. eapply step. apply H. apply H1. simpl. reflexivity. subst.
      apply in_app_or in H0. destruct H0. apply add_to_stack_adds_parent in H0. inversion H0; subst.
      eapply remain_d_contains_valid_vertices. apply H. simpl. apply H2. simpl in H0. destruct H0; inversion H0.
    + destruct (pop_stack st remain_f) eqn : ?; simpl in H3.
      * destruct (S.min_elt remain_d); inversion H3.
      * rewrite <- H3 in Heqs; clear H3. apply in_app_or in H0. destruct H0. apply add_to_stack_adds_parent in H0.
        inversion H0; subst. eapply stack_valid. apply H. simpl. eapply in_pop_rev.
        rewrite Heqs. left. reflexivity. apply IHvalid_dfs_state. eapply in_pop_rev. rewrite Heqs. apply H0.
    + destruct (pop_stack st remain_f) eqn : ?; simpl in H4.
      * destruct (S.min_elt remain_d); inversion H4; subst. inversion H0.
      * rewrite <- H4 in Heqs; clear H4. apply IHvalid_dfs_state. eapply in_pop_rev. rewrite Heqs. right.
        assumption.
Qed.

Lemma gray_in_forest: forall s g o v,
  valid_dfs_state s g o ->
  G.contains_vertex g v = true ->
  white s v = false ->
  F.contains_vertex (get_forest s) v = true.
Proof.
  intros. generalize dependent v. unfold white in *. induction H; intros; subst; simpl in *.
  - rewrite G.set_of_graph_1 in H0. apply S.mem_1 in H0. simplify. rewrite H1 in H0. inversion H0.
  - inversion H0; subst; simpl in *.
    + destruct (O.eq_dec x v).
      * unfold O.eq in e. subst. apply F.add_root_1. 
      * rewrite P2.FM.remove_neq_b in H2. apply F.add_root_2. eapply IHvalid_dfs_state. apply H1.
        simplify. intuition.
    + destruct (O.eq_dec x v).
      * unfold O.eq in e. subst. remember (g0, f, f_times, d_times, time, remain_d, remain_f, st) as s.
        assert (white s y = false). eapply parents_not_white. apply H.
        destruct ((pop_stack st remain_f)) eqn : ?; simpl in H4. destruct (S.min_elt remain_d); inversion H4.
        rewrite <- H4 in Heqs0; clear H4. eapply in_pop_rev. subst; simpl. rewrite Heqs0. left. reflexivity.
        apply F.add_child_5. apply IHvalid_dfs_state. destruct (pop_stack st remain_f) eqn : ?; simpl in H4.
        -- destruct (S.min_elt remain_d); inversion H4; subst.
        -- rewrite <- H4 in Heqs0; clear H4. eapply parents_valid. apply H.
        subst; simpl. eapply in_pop_rev. rewrite Heqs0. left. reflexivity.
        -- unfold white in H5. subst; simpl in *. apply H5.
      * apply F.add_child_3. apply IHvalid_dfs_state. apply H1. rewrite P2.FM.remove_neq_b in H2.
        rewrite H2. reflexivity. apply n.
    + destruct (O.eq_dec x v).
      * unfold O.eq in e. subst. apply IHvalid_dfs_state. apply H1. rewrite H3. reflexivity.
      * rewrite P2.FM.remove_neq_b in H2. apply IHvalid_dfs_state. apply H1. apply H2. apply n.
Qed. 

(*An important lemma: If a vertex is gray, we can split the stack into two parts: the
  left does not have v as a child anywhere, and the right does not have v as a parent anywhere.
  This will helper prove many other lemmas about the stack.*)
Lemma right_left_stacks: forall s g o v,
  valid_dfs_state s g o ->
  exists tl o',
  gray s v = true ->
  (exists l1, get_stack s = l1 ++ (v,o') :: tl /\ (forall o'', ~In (v, o'') l1) /\
  (forall y, ~In (y, Some v) tl) /\ 
  (forall x y, In (x, Some y) l1 -> F.desc (get_forest s) v y \/ y = v)).
Proof.
  intros. unfold gray in *. induction H; subst; simpl in *.
  - destruct o. destruct (G.contains_vertex g v0) eqn : ?.
    + exists nil. exists None. intros. simplify. rewrite H1 in H0. inversion H0.
    + exists nil. exists None. intros. simplify. rewrite H1 in H0. inversion H0.
    + exists nil. exists None. intros. simplify. rewrite H1 in H0. inversion H0.
  - inversion H0; subst; simpl in *; destruct IHvalid_dfs_state.
    + destruct H3. assert (tl = nil). eapply root_nil. eapply step. apply H. apply H0. simpl. reflexivity.
    subst. destruct (O.eq_dec x v). 
      * unfold O.eq in e. subst. exists nil. exists None. intros. exists (add_to_stack v g0 remain_d).
        split. reflexivity. intros. split. intros. intro. apply add_to_stack_neq in H5. contradiction.
        split. intros. intro. inversion H5. intros. apply add_to_stack_adds_parent in H5. inversion H5; subst.
        right. reflexivity.
      * (*doesn't matter, this is impossible*)
        exists nil. exists None. intros. remember (g0, f, f_times, d_times, time, remain_d, remain_f, st) as s.
       assert (exists o, In (v, o) (get_stack s)). eapply gray_on_stack. apply H.
       unfold gray; subst; simpl in *. simplify. rewrite P2.FM.remove_neq_b in H5. apply H5. intuition.
       subst; simpl in *. destruct H5. destruct (pop_stack st remain_f) eqn : ?.
       -- simpl in H2. rewrite pop_stack_nil in Heqs. specialize (Heqs (v, x2)).
          simpl in Heqs. apply Heqs in H5. simplify. rewrite H5 in H7. inversion H7.
       -- simpl in H2. inversion H2; subst. eapply (pop_stack_delete _ remain_f) in H5.
          destruct H5. simplify. rewrite H7 in H5. inversion H5.
          rewrite Heqs in H5. simpl in H5. destruct H5. inversion H5. subst. simplify. exfalso. apply n.
          reflexivity. destruct H5.
    + destruct H3. destruct (O.eq_dec x v).
      * exists tl. exists (Some y). intros. exists (add_to_stack x g0 remain_d). split. 
        rewrite e. reflexivity. intros. split. intros. intro. apply add_to_stack_neq in H5. rewrite e in H5.
        contradiction. split. intros. intro. rewrite e in H1. 
        remember (g0, f, f_times, d_times, time, remain_d, remain_f, st) as s.
        assert (white s v = true). unfold white; subst; simpl; simplify.
        pose proof parents_not_white. specialize (H7 s g o y0 v). apply H7 in H. rewrite H in H6. inversion H6.
         subst; simpl. destruct (pop_stack st remain_f) eqn : ?.
        -- simpl in H2. destruct (S.min_elt remain_d). inversion H2; subst. inversion H2.
        -- simpl in H2. rewrite <- H2 in Heqs. eapply in_pop_rev. rewrite Heqs. solve_in.
        -- intros. unfold O.eq in e. subst. apply add_to_stack_adds_parent in H5. inversion H5; subst.
           right. reflexivity.
      * exists x0. exists x1. intros. destruct H3.
        rewrite P2.FM.remove_neq_b in H4. apply H4. apply n.
        destruct (pop_stack st) eqn : ?.
        -- simpl in H2. destruct (S.min_elt remain_d); inversion H2.
        -- simpl in H2. exists (add_to_stack x g0 remain_d ++ (pop_stack (x2) remain_f)).
        split. destruct H3. rewrite H2. rewrite <- Heqs. rewrite H3. rewrite pop_stack_app_distr.
        rewrite app_assoc. reflexivity. simplify. split. intros. intro. apply in_app_or in H5.
        destruct H5. apply only_add_yet_to_be_discovered in H5. simplify.
        rewrite P2.FM.remove_neq_b in H6. rewrite H6 in H5. inversion H5. intuition. 
        destruct H3. destruct H6. apply (H6 o''). eapply in_pop_rev. apply H5. split.
        intros. intro. destruct_all.  apply (H7 y0). apply H5. intros.
        destruct_all. rewrite H3 in Heqs. rewrite pop_stack_app_distr in Heqs. rewrite <- H2 in Heqs; clear H2.
        destruct (pop_stack x2 remain_f) eqn : ?. inversion Heqs; subst. exfalso. apply n. reflexivity.
        inversion Heqs; subst. assert (In (x, Some y) x2). eapply in_pop_rev. rewrite Heqs0. solve_in.
        apply in_app_or in H5. destruct H5. apply add_to_stack_adds_parent in H3. inversion H3; subst.
        apply H8 in H2. destruct H2. left. apply (F.is_descendant_trans _ _ y). apply F.is_descendant_1.
        apply H2. apply F.is_descendant_edge. apply F.add_child_1.
        remember (g0, F.add_child f y x, f_times, M.add x (time + 1) d_times, time + 1, 
        S.remove x remain_d, remain_f,add_to_stack x g0 remain_d ++ (x, Some y) :: s0 ++ (v, x1) :: x0) as s'.
        assert (white s' y = false). apply (parents_not_white _ g o x). eapply step. apply H. apply H0.
        subst. simpl. apply in_or_app. right. left. reflexivity. eapply gray_in_forest in H5.
        subst. simpl in *. apply F.add_child_6 in H5. destruct H5. apply H5. subst.
        exfalso. eapply neq_parent. eapply step. apply H. apply H0. simpl. apply in_or_app. right. left. reflexivity.
        reflexivity. eapply step. apply H. apply H0. eapply parents_valid. eapply step. apply H. apply H0.
        subst; simpl. apply in_or_app. right. left. reflexivity.
        remember (g0, f, f_times, d_times, time, remain_d, remain_f, x2 ++ (v, x1) :: x0)  as s'.
        assert (white s' x = true). unfold white. assert (S.mem x (get_remain_d s') = true) by
        (subst; simpl; assumption). rewrite H5. eapply not_f_if_not_d in H5. rewrite H5.
        reflexivity. subst. apply H. eapply white_not_in_forest in H5. subst; simpl in *. apply H5.
        subst; apply H. subst. left. apply F.is_descendant_edge. 
        remember (g0, f, f_times, d_times, time, remain_d, remain_f, x2 ++ (v, x1) :: x0) as s'.
        rewrite P2.FM.remove_neq_b in H4. simplify. assert (get_forest s' = f) by (subst; simpl; reflexivity).
        rewrite <- H2. clear H2. apply F.add_child_1. eapply gray_in_forest. subst; apply H.
        eapply remain_f_contains_valid_vertices. apply H. simpl. apply H9. unfold white.
        subst; simpl in *. rewrite H4. reflexivity. eapply white_not_in_forest. subst. apply H.
        unfold white. assert (S.mem x (get_remain_d s') = true) by (subst; simpl; apply H1).
        rewrite H2. eapply not_f_if_not_d in H2. rewrite H2. reflexivity.  subst; apply H.
        apply n. assert (In (x3, Some y0) x2). eapply in_pop_rev. rewrite Heqs0. apply H3.
        apply H8 in H5. destruct H5. left. apply F.is_descendant_1. apply H5. right. apply H5.
        apply H9.
    + destruct H4. destruct (O.eq_dec x v).
      * unfold O.eq in e. subst. destruct H4. simplify. destruct H4.
        exists x0. exists x1. intros. simplify. exfalso. eapply remove_eq. apply H9.
      * exists x0. exists x1. intros. simplify.
        rewrite P2.FM.remove_neq_b in H7. destruct H4. assumption.
        destruct (pop_stack st remain_f) eqn : ?.
        -- simpl in H3. destruct (S.min_elt remain_d) eqn : ?; inversion H3; subst.
           remember (g0, f, M.add e (time + 1) f_times, d_times, time + 1, remain_d, S.remove e remain_f, nil) as s.
           assert (exists o, In (v,o) (get_stack s)). eapply gray_on_stack. eapply step. apply H.
           apply H0. unfold gray. subst; simpl; simplify. subst; simpl in *. destruct H5. destruct H5.
        -- simpl in H3. rewrite <- H3 in Heqs.
            destruct H4. rewrite H4 in Heqs. rewrite pop_stack_app_distr in Heqs.
            destruct (pop_stack x2 remain_f) eqn : ?.
            ++ inversion Heqs; subst. exfalso. apply n. reflexivity.
            ++ inversion Heqs; subst. exists s0. split. reflexivity. split. intros.
               destruct H5.
               apply (H5 o''). eapply in_pop_rev. rewrite Heqs0. right. apply H4. split.
                destruct H5.  apply H5. intros. destruct_all. eapply H9.
                eapply in_pop_rev. rewrite Heqs0. right. apply H4.
            ++ apply H7.
       -- intuition.
Qed. 

(** ** Lemmas for Parentheses Theorem **)

(*the stack before a gray vertex is constant when we step, as long as that vertex stays gray*)
Lemma left_stack_constant_step: forall s g o v l1 l2 o' s',
  valid_dfs_state s g o ->
  get_stack s = l1 ++ (v, o') :: l2 ->
  gray s v = true ->
  (forall o, ~In (v, o) l1) ->
  dfs_step s s' ->
  gray s' v = true ->
  exists l1, get_stack s' = l1 ++ (v, o') :: l2 /\ (forall o, ~In (v, o) l1).
Proof.
  intros. unfold gray in *. inversion H3; subst; simpl in *; simplify.
  - assert (tl = nil). eapply root_nil. eapply step. apply H. apply H3. simpl. reflexivity.
    subst. destruct (pop_stack (l1 ++ (v, o') :: l2) remain_f) eqn : ?.
    + simpl in H6. destruct (S.min_elt remain_d) eqn : ?; inversion H6; subst.
      rewrite pop_stack_nil in Heqs. specialize (Heqs (v, o')). simpl in *.
      assert (S.mem v remain_f = false). apply Heqs. solve_in. rewrite H0 in H9. inversion H9.
    + simpl in H6. rewrite <- H6 in Heqs. rewrite pop_stack_app_distr in Heqs.
      destruct (pop_stack l1 remain_f) eqn : ?. inversion Heqs; subst.
      exists (add_to_stack x g0 remain_d). split. reflexivity. intros. apply add_to_stack_neq in H0.
      contradiction. inversion Heqs; subst. destruct s0; inversion H10. apply H9.
  - destruct (pop_stack st remain_f) eqn : ?; simpl in H6.
    + destruct (S.min_elt remain_d); inversion H6.
    + rewrite <- H6 in Heqs. clear H6. rewrite H0 in Heqs. rewrite pop_stack_app_distr in Heqs.
      destruct (pop_stack l1 remain_f) eqn : ?. inversion Heqs; subst. rewrite H7 in H5.  inversion H5. 
      inversion Heqs; subst. exists (add_to_stack x g0 remain_d ++ (x, Some y) :: s0).
      split. rewrite <- app_assoc. simpl. reflexivity. intros.
      apply in_app_or in H0. destruct H0. apply only_add_yet_to_be_discovered in H0.
      rewrite H0 in H7. inversion H7. assert (In (v, o0) l1). eapply in_pop_rev. rewrite Heqs0.
      apply H0. apply (H2 o0). apply H4. apply H9.
  - destruct (O.eq_dec x v). unfold O.eq in e. subst. rewrite remove_eq_false in H10. inversion H10.
    destruct (pop_stack st remain_f) eqn : ?; simpl in H7. destruct (S.min_elt remain_d) eqn : ?; inversion H7; subst.
    rewrite pop_stack_nil in Heqs. specialize (Heqs (v, o')). simpl in Heqs. assert (S.mem v remain_f = false).
    apply Heqs; solve_in. rewrite H0 in H9. inversion H9. rewrite <- H7 in Heqs. clear H7.
    rewrite H0 in Heqs. rewrite pop_stack_app_distr in Heqs. destruct (pop_stack l1 remain_f) eqn : ?.
    inversion Heqs; subst. exfalso. apply n. reflexivity. inversion Heqs; subst.
    exists s0. split. reflexivity. intros. assert (In (v, o1) l1). eapply in_pop_rev. rewrite Heqs0.
    solve_in. apply (H2 o1). apply H4. apply H9.
Qed.

(*Black vertices remain black*)
Lemma black_stays_black: forall s g o v s',
  valid_dfs_state s g o ->
  black s v = true ->
  dfs_multi s s' ->
  black s' v = true.
Proof.
  intros. induction H1.
  - apply H0.
  - inversion H1; subst; unfold black in *; simpl in *.
    + apply IHmulti. eapply step. apply H. apply H1. simplify. rewrite P2.Dec.F.remove_b.
      simplify.
    + apply IHmulti. eapply step. apply H. apply H1. simplify. rewrite P2.Dec.F.remove_b.
      simplify.
    + apply IHmulti. eapply step. apply H. apply H1. simplify. rewrite P2.Dec.F.remove_b.
      simplify.
Qed.

(*Gray vertices are always gray or black in the future*)
Lemma gray_to_gray_black: forall s g o v s',
  valid_dfs_state s g o ->
  gray s v = true ->
  dfs_multi s s' ->
  gray s' v = true \/ black s' v = true.
Proof.
  intros. induction H1.
  - left. apply H0.
  - inversion H1; subst; unfold gray in *; unfold black in *; simpl in *; simplify; simplify.
    + destruct (O.eq_dec v x0).
      * unfold O.eq in e. subst. rewrite H5 in H3. inversion H3.
      * rewrite P2.FM.remove_neq_b in IHmulti. simplify. simplify. apply IHmulti. 
        eapply step. apply H. apply H1. simplify. intuition.
    + simplify. simplify. apply IHmulti. eapply step. apply H. apply H1. simplify.
      rewrite P2.Dec.F.remove_b. simplify.
    + destruct (O.eq_dec x0 v).
      * unfold O.eq in e. subst. simplify. simplify. right.  
        assert (black z v = true). eapply black_stays_black. eapply step. apply H.
        apply H1. unfold black; simpl. simplify. simplify. apply remove_eq_false. apply H2.
        unfold black in H0. simplify. simplify.
      * simplify. simplify. apply IHmulti. eapply step. apply H. apply H1. simplify.
Qed.

(*The stack to the left of a gray vertex is constant whenever it is gray*)
Lemma left_stack_constant: forall s g o v l1 l2 o' s',
  valid_dfs_state s g o ->
  get_stack s = l1 ++ (v, o') :: l2 ->
  gray s v = true ->
  (forall o, ~In (v, o) l1) ->
  dfs_multi s s' ->
  gray s' v = true ->
  exists l1, get_stack s' = l1 ++ (v, o') :: l2.
Proof.
  intros. generalize dependent l1. induction H3; intros; simpl in *.
  - exists l1. apply H0.
  - assert (A:=H1). eapply gray_to_gray_black in H1.
    + destruct H1. pose proof (left_stack_constant_step x g o v l1 l2 o' y H H2 A H5).
      specialize (H6 H0 H1). destruct H6.
      eapply IHmulti. eapply step. apply H. apply H0. apply H1. apply H4. destruct H6. apply e. 
      destruct H6. apply H7. eapply black_stays_black in H1. 
      assert (black z v = true) by (apply H1). unfold gray in *; unfold black in *; simplify.
      simplify. rewrite H8 in H12. inversion H12. eapply step. apply H. apply H0. apply H3.
    + apply H.
    + eapply multi_R. apply H0.
Qed.

(*A vertex occurring later on the stack must turn black before an earlier vertex (step version)*)
Lemma later_vertices_finish_first_step: forall u v p o' l1 l2 l3 s s' g o,
  valid_dfs_state s g o ->
  get_stack s = l1 ++ (u, Some p) :: nil ++ l2 ++ (v, o') :: l3 ->
  (forall o, ~In (v, o) (l1 ++ (u, Some p) :: l2)) ->
  gray s u = true ->
  gray s v = true ->
  dfs_step s s' ->
  black s' v = true -> black s' u = true.
Proof.
  intros. unfold black in *. unfold gray in *. inversion H4; subst; simpl in *; simplify.
  - rewrite P2.FM.remove_b. simplify.
  - destruct ((pop_stack st remain_f)) eqn : ?.
    + simpl in H7. destruct (S.min_elt remain_d); inversion H7; subst.
      rewrite pop_stack_nil in Heqs. specialize (Heqs (u, Some p)). simpl in *.
      rewrite Heqs. reflexivity. solve_in.
    + simpl in H7. rewrite <- H7 in Heqs. rewrite H0 in Heqs.
      remember (g0, f, f_times, d_times, time, remain_d, remain_f, st) as s'.
      assert (A:=H). eapply right_left_stacks in A. destruct_all.
      assert (gray s' v = true) by (unfold gray; subst; simplify).
      specialize (H5 H12). destruct_all. rewrite Heqs' in H5; simpl in H5.
      rewrite H5 in H0. assert (A:=H0). apply app_match in H0. destruct H0.
      * destruct H0. rewrite H0 in A. rewrite <- app_assoc in A. apply app_inv_head in A.
        destruct x3. inversion A; subst. rewrite H9 in H11. inversion H11.
        inversion A; subst. simplify. rewrite H11 in H9. inversion H9.
      * destruct H0. rewrite H0 in A. rewrite <- app_assoc in A. apply app_inv_head in A.
        inversion A; subst. simplify. rewrite H11 in H9. inversion H9.
  - destruct ((pop_stack st remain_f)) eqn : ?; simpl in H7.
    + destruct (S.min_elt remain_d); inversion H7.
    + rewrite <-H7 in Heqs. assert (B:=Heqs). rewrite H0 in Heqs. rewrite pop_stack_app_distr in Heqs.
      destruct (pop_stack l1 remain_f ) eqn : ?.
      * inversion Heqs; subst. rewrite H6 in H3. inversion H3.
      * rewrite H9 in H11. inversion H11.
      * simplify.
  - destruct ((pop_stack st remain_f)) eqn : ?; simpl in H7.
    + destruct (S.min_elt remain_d); inversion H7.
    + rewrite <-H7 in Heqs. assert (B:=Heqs). rewrite H0 in Heqs. rewrite pop_stack_app_distr in Heqs.
      destruct (pop_stack l1 remain_f ) eqn : ?.
      * inversion Heqs; subst. rewrite H6 in H3. inversion H3.
      * rewrite H9 in H11. inversion H11.
      * simplify.
  - simplify. destruct (pop_stack st remain_f) eqn : ?; simpl in H8.
    + destruct (S.min_elt remain_d) eqn : ?; inversion H8; subst.
      * apply S.min_elt_1 in Heqo1. apply S.mem_1 in Heqo1. rewrite Heqo1 in H6. inversion H6.
    + rewrite <- H8 in Heqs. remember (g0, f, f_times, d_times, time, remain_d, remain_f, st) as s'.
      assert (gray s' v = true) by (unfold gray; subst; simplify). assert (A:=H). eapply right_left_stacks in A.
      destruct_all. specialize (H13 H5). destruct_all. rewrite Heqs' in H13; simpl in H13.
      assert (B:= H0). rewrite H13 in H0. destruct (O.eq_dec u v). unfold O.eq in e. subst.
      apply H12. assert (C:=H0). apply app_match in H0; destruct H0; destruct H0.
      * rewrite H0 in C. rewrite <- app_assoc in C. apply app_inv_head in C. destruct x3; inversion C; subst.
        exfalso. apply n. reflexivity. rewrite pop_stack_app_distr in Heqs.
        rewrite pop_stack_app_distr in Heqs. destruct (pop_stack l1 remain_f) eqn : ?. inversion Heqs; subst.
        apply remove_eq_false. inversion Heqs; subst. assert (x <> v). destruct (O.eq_dec x v).
        unfold O.eq in e. subst. exfalso. apply (H14 o0). assert (In (v, o0) l1). eapply in_pop_rev. rewrite Heqs0.
        left. reflexivity. solve_in. apply n0. rewrite P2.FM.remove_neq_b in H12. rewrite H12 in H10. inversion H10.
        apply H0. simplify. simplify.
      * rewrite H0 in C. rewrite <- app_assoc in C. apply app_inv_head in C. destruct x3. inversion C; subst.
        exfalso. apply n. reflexivity. inversion C; subst. exfalso. apply (H1 x1). (*figure out ltac*)
        apply in_or_app. left. apply in_or_app. right. left. reflexivity.
Qed.

(*If 2 gray vertices are on the stack, 1 in front of the other, that order is preserved
  as long as they are both gray*)
Lemma gray_stack_structure:  forall u v p o' l1 l2 l3 s s' g o,
  valid_dfs_state s g o ->
  get_stack s = l1 ++ (u, Some p) :: nil ++ l2 ++ (v, o') :: l3 ->
  (forall o, ~In (v, o) (l1 ++ (u, Some p) :: l2)) ->
  (forall o, ~In(u, o) l1) ->
  gray s u = true ->
  gray s v = true ->
  dfs_step s s' ->
  gray s' u = true ->
  exists l1, get_stack s' = l1 ++ (u, Some p) :: nil ++ l2 ++ (v, o') :: l3 /\ 
  (forall o, ~In (v, o) (l1 ++ (u, Some p) :: l2)) /\ (forall o, ~In(u, o) l1).
Proof.
  intros. pose proof (left_stack_constant_step s g o u l1 (l2 ++ (v, o') :: l3) (Some p) s' H H0 H3 H2 H5 H6).
  destruct_all. exists x. split. apply H7.
  assert (forall o, ~In (v,o) x). { unfold gray in *. intros. intro. inversion H5; subst; simpl in *; simplify.
  - assert (tl = nil). eapply root_nil. eapply step. eapply H. apply H5. simpl. reflexivity. subst.
    destruct (pop_stack (l1 ++ (u, Some p) :: l2 ++ (v, o') :: l3) remain_f) eqn : ?.
    + simpl in H11. destruct (S.min_elt remain_d) eqn : ?; inversion H11; subst.
      rewrite pop_stack_nil in Heqs. specialize (Heqs (v, o')). simpl in *. 
      assert (S.mem v remain_f = false). apply Heqs. solve_in. rewrite H0 in H13. inversion H13.
    + rewrite pop_stack_app_distr in Heqs. simpl in H11. rewrite <- H11 in Heqs. 
      destruct (pop_stack l1 remain_f); inversion Heqs; subst. destruct s0; inversion H16. apply H15.
  - destruct (pop_stack st remain_f) eqn : ?; simpl in H11.
    + destruct (S.min_elt remain_d); inversion H11.
    + rewrite H0 in Heqs. rewrite pop_stack_app_distr in Heqs. rewrite <- H11 in Heqs. clear H11.
       destruct (pop_stack l1 remain_f )eqn : ?.
      * simpl in Heqs. inversion Heqs; subst. rewrite H4 in H10. inversion H10.
      * inversion Heqs; subst; simpl in *. assert (A:=H7). apply app_match in H7. destruct H7; destruct_all; subst.
        rewrite H0 in A. rewrite <- app_assoc in A. apply app_inv_head in A.
        assert (In (v, o0) (add_to_stack x0 g0 remain_d)). rewrite H0. solve_in. apply only_add_yet_to_be_discovered in H6.
        rewrite H6 in H12. inversion H12. rewrite <- app_assoc in A. apply app_inv_head in A.
        destruct x1. inversion A; subst. rewrite H10 in H4. inversion H4. inversion A; subst.
        assert (B:=H7). apply app_match in H7; destruct H7; destruct_all; subst. 
        rewrite <- app_assoc in B. apply app_inv_head in B. 
        apply in_app_or in H9. destruct H9. apply only_add_yet_to_be_discovered in H0. rewrite H0 in H12. inversion H12.
        assert (In (v, o0) l1). eapply in_pop_rev. rewrite Heqs0. simpl in H0; destruct H0.
        simpl. left. apply H0. solve_in. apply (H1 o0). solve_in.
        rewrite <- app_assoc in B. apply app_inv_head in B. destruct x. 
        apply in_app_or in H9. destruct H9. apply only_add_yet_to_be_discovered in H0. rewrite H0 in H12.
        inversion H12. rewrite app_nil_r in H0. assert (In (v, o0) l1). eapply in_pop_rev.
        rewrite Heqs0. apply H0. apply (H1 o0). solve_in. inversion B; subst.
        apply (H8 (Some p)). apply in_or_app. right. simpl. right. apply in_or_app. right. left. reflexivity.
      * assumption.
  - destruct (pop_stack st remain_f) eqn : ?; simpl in H12.
    + destruct (S.min_elt remain_d); inversion H12; subst. rewrite pop_stack_nil in Heqs.
      specialize (Heqs (u, Some p)). simpl in *. assert (S.mem u remain_f = false). apply Heqs.
      solve_in. rewrite H0 in H15. inversion H15.
    + rewrite H0 in Heqs. rewrite pop_stack_app_distr in Heqs. rewrite <- H12 in Heqs. clear H12.
      destruct (pop_stack l1 remain_f) eqn : ?. inversion Heqs; subst. rewrite remove_eq_false in H16. inversion H16.
      rewrite H7 in Heqs. inversion Heqs; subst. assert (A:=H17). apply app_match in H17. destruct H17; destruct_all;subst.
      rewrite <- app_assoc in A. apply app_inv_head in A. assert (In (v, o0) l1). eapply in_pop_rev.
      rewrite Heqs0. solve_in. apply (H1 o0). solve_in. rewrite <- app_assoc in A. apply app_inv_head in A.
      destruct x1. assert (In (v, o0) l1). eapply in_pop_rev.
      rewrite Heqs0. rewrite app_nil_r in H9. solve_in. apply (H1 o0). solve_in.
      inversion A; subst. apply (H8 (Some p)). apply in_or_app. right. left. reflexivity.
      assumption. }
      intros. split. intros. intro. apply in_app_or in H10. destruct H10. apply (H9 o0). apply H10.
      apply (H1 o0). solve_in. apply H8.
Qed.

(*A vertex occurring later on the stack must turn black before an earlier vertex (multistep version)*)
Lemma later_vertices_finish_first: forall u v p o' l1 l2 l3 s s' g o,
  valid_dfs_state s g o ->
  get_stack s = l1 ++ (u, Some p) :: nil ++ l2 ++ (v, o') :: l3 ->
  (forall o, ~In (v, o) (l1 ++ (u, Some p) :: l2)) ->
  (forall o, ~In(u, o) l1) ->
  gray s u = true ->
  gray s v = true ->
  dfs_multi s s' ->
  black s' v = true -> black s' u = true.
Proof.
  intros. generalize dependent l1. induction H5; intros.
  - unfold gray in *; unfold black in *; simplify. simplify. rewrite H9 in H8. inversion H8.
  - pose proof (later_vertices_finish_first_step u v p o' l1 l2 l3 x y g o H H1 H2 H3 H4 H0).
    simpl in H1.
    pose proof ( left_stack_constant x g o v (l1 ++ (u, Some p) :: l2) l3 o' y H).
    assert (get_stack x = (l1 ++ (u, Some p) :: l2) ++ (v, o') :: l3). rewrite H1.
    rewrite <- app_assoc. simpl. reflexivity. specialize (H9 H10). clear H10. specialize (H9 H4 H2).
    assert (dfs_multi x y). apply multi_R; assumption. 
    assert (A:= H3). apply (gray_to_gray_black _ g o _ y) in H3. destruct H3.
    assert (B:=H4). apply (gray_to_gray_black _ g o _ y) in H4. destruct H4.
    assert (valid_dfs_state y g o). eapply step. apply H. apply H0. 
    specialize (IHmulti H11 H3 H4 H6).
    pose proof (gray_stack_structure u v p o' l1 l2 l3 x y g o H H1 H2 H7 A B H0 H3). destruct_all.
    specialize (IHmulti x0). apply IHmulti. apply H12. apply H13. apply H14.
    eapply black_stays_black. eapply step. apply H. apply H0. 
    eapply later_vertices_finish_first_step. apply H. apply H1. apply H2. apply A. apply B.
    apply H0. apply H4. apply H5. apply H. apply multi_R. apply H0. 
    eapply black_stays_black. eapply step. apply H. apply H0. apply H3. apply H5. apply H.
    apply multi_R. apply H0.
Qed.

(*At discovery time of v, the stack contains v, and everything after v is white*)
Lemma stack_at_discovery_time: forall s g o v,
  valid_dfs_state s g o ->
  M.find v (get_d_times s) = Some (get_time s) ->
  gray s v = true /\ (exists l1 l2 p, get_stack s = l1 ++ (v, p) :: l2 /\ (forall o, ~In(v,o) l1) /\
  (forall u o, In (u, o) l1 -> white s u = true)).
Proof.
  intros. inversion H; subst; simpl in *.
  - rewrite F.empty_o in H0. inversion H0.
  - unfold gray. unfold white. inversion H2; subst; simpl in *.
    +  assert (tl = nil). eapply root_nil. apply H. simpl. reflexivity. subst.
      destruct (O.eq_dec x v).
      * unfold O.eq in e. subst. split. simplify. apply remove_eq_false. 
        remember (g0, f, f_times, d_times, time, remain_d, remain_f, st) as s.
        assert (S.mem v (get_remain_d s) = true) by (subst; simpl in *; assumption).
        eapply not_f_if_not_d in H5. subst; simpl in *; assumption. apply H1.
        exists (add_to_stack v g0 remain_d). exists nil. exists (None).
        split. reflexivity. intros. split. intros. intro. apply add_to_stack_neq in H5. contradiction.
        intros. assert (A:=H5). apply add_to_stack_neq in H5. rewrite P2.FM.remove_neq_b.
        apply only_add_yet_to_be_discovered in A. rewrite A.
        remember (g0, f, f_times, d_times, time, remain_d, remain_f, st) as s.
        assert (S.mem u (get_remain_d s) = true) by (subst; simpl; assumption).
        eapply not_f_if_not_d in H6. subst; simpl in *. assumption. apply H1. intuition. 
      * rewrite P.F.add_neq_o in H0. remember (g0, f, f_times, d_times, time, remain_d, remain_f, st) as s.
        assert (M.find v (get_d_times s) = Some (time +1)) by (subst; simpl in *; assumption).
        eapply d_times_leq_current_time in H5. subst; simpl in *; omega. apply H1. apply n.
    + destruct (O.eq_dec x v).
      * unfold O.eq in e. subst. split. simplify. apply remove_eq_false. 
        remember (g0, f, f_times, d_times, time, remain_d, remain_f, st) as s.
        assert (S.mem v (get_remain_d s) = true) by (subst; simpl; assumption).
        eapply not_f_if_not_d in H5. subst; simpl in *. assumption. apply H1.
        exists (add_to_stack v g0 remain_d). exists tl. exists (Some y). split.
        reflexivity. split. intros. intro. apply add_to_stack_neq in H5. contradiction.
        intros. assert (A:=H5). apply add_to_stack_neq in H5. rewrite P2.FM.remove_neq_b.
        apply only_add_yet_to_be_discovered in A. rewrite A.
        remember (g0, f, f_times, d_times, time, remain_d, remain_f, st) as s.
        assert (S.mem u (get_remain_d s) = true) by (subst; simpl; assumption).
        eapply not_f_if_not_d in H6. subst; simpl in *. assumption. apply H1. intuition. 
      * rewrite P.F.add_neq_o in H0. remember (g0, f, f_times, d_times, time, remain_d, remain_f, st) as s.
        assert (M.find v (get_d_times s) = Some (time +1)) by (subst; simpl in *; assumption).
        eapply d_times_leq_current_time in H5. subst; simpl in *; omega. apply H1. apply n.
    + remember (g0, f, f_times, d_times, time, remain_d, remain_f, st) as s.
        assert (M.find v (get_d_times s) = Some (time +1)) by (subst; simpl in *; assumption).
        eapply d_times_leq_current_time in H6. subst; simpl in *; omega. apply H1.
Qed. 

(*If a vertex p is gray when v is discovered, then p cannot turn black before v*)
Lemma gray_at_discovery_time_finishes_after: forall s g o v p s',
  valid_dfs_state s g o ->
  Some (get_time s) = M.find v (get_d_times s) ->
  p <> v ->
  gray s p = true ->
  dfs_multi s s' ->
  black s' p = true -> black s' v = true.
Proof.
  intros. symmetry in H0. pose proof (stack_at_discovery_time s g o v H H0).
  destruct_all;destruct_all.
  pose proof (right_left_stacks s g o p H). destruct_all. specialize (H9 H2).
  destruct_all. rewrite H9 in H6. assert (A:=H6). apply app_match in A; destruct A; destruct_all; subst.
  rewrite <- app_assoc in H6. apply app_inv_head in H6. destruct x5. inversion H6; subst. contradiction.
  inversion H6; subst. destruct x1. eapply later_vertices_finish_first. apply H. rewrite <- app_assoc in H9. apply H9.
  apply H10. apply H7. apply H5. apply H2. apply H3. apply H4. 
  rewrite <- app_assoc in H9. simpl in H9. assert (x5 ++ (p, x3) :: x2 = nil). eapply root_nil.
  apply H. apply H9. destruct x5; inversion H13. rewrite <- app_assoc in H6. apply app_inv_head in H6.
  destruct x5; inversion H6; subst. contradiction. assert (white s p = true).
  apply (H8 _ x3). apply in_or_app. right. left. reflexivity. unfold gray in *; unfold white in *; simplify. 
  rewrite H5 in H14. inversion H14.
Qed. 

Lemma contrapositive: forall (P Q: Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros. intro. apply H in H1. contradiction.
Qed.

(*Vertex is black iff it has a finish time*)
Lemma black_iff_finished: forall s g o v,
  valid_dfs_state s g o ->
  G.contains_vertex g v = true ->
  black s v = true <-> (exists n, M.find v (get_f_times s) = Some n).
Proof.
  intros. unfold black in *. pose proof (v_finished_iff_not_remain s g o v H H0).
  rewrite <- H1. split; intros.
  - simplify. simplify.
  - pose proof (not_f_if_not_d s g o v H). apply contrapositive in H3.
    destruct (S.mem v (get_remain_d s)). contradiction. simpl. simplify.
    rewrite H2. intro. inversion H4.
Qed.

Lemma all_finished_at_end: forall s g o v,
  valid_dfs_state s g o ->
  G.contains_vertex g v = true ->
  done s = true ->
  exists n, M.find v (get_f_times s ) = Some n.
Proof.
  intros. unfold done in H1. pose proof v_finished_iff_not_remain. eapply H2.
  apply H. apply H0. simplify. destruct (S.mem v (get_remain_f s)) eqn : ?. solve_empty. reflexivity.
Qed.

(*If a vertex has a finish time, then there is a valid state before where it was finished*)
Lemma finish_time_means_finished: forall s g o v n,
  valid_dfs_state s g o->
  M.find v (get_f_times s) = Some n ->
  (exists s', dfs_multi s' s /\ n = get_time s' /\ valid_dfs_state s' g o /\ M.find v (get_f_times s') = Some n).
Proof.
  intros. induction H; subst; simpl in *. 
  - rewrite F.empty_o in H0. inversion H0.
  - inversion H1; subst; simpl in *.
    + apply IHvalid_dfs_state in H0. destruct_all. exists x0. split. eapply multi_trans.
      apply H0. apply multi_R. apply H1. split. apply H4. split. apply H5. apply H6.
    + apply IHvalid_dfs_state in H0. destruct_all. exists x0. split. eapply multi_trans.
      apply H0. apply multi_R. apply H1. split. apply H4. split. apply H5. apply H6.
    + destruct (O.eq_dec v x).
      * unfold O.eq in e. subst. rewrite F.add_eq_o in H0. inversion H0; subst. 
        exists (g0, f, M.add x (time + 1) f_times, d_times, time + 1, remain_d, S.remove x remain_f, tl).
        split. apply multi_refl. simpl. split. reflexivity. split. eapply step. apply H. apply H1.
        rewrite F.add_eq_o. reflexivity. reflexivity. reflexivity.
      * rewrite F.add_neq_o in H0. apply IHvalid_dfs_state in H0. destruct_all. exists x0.
        split. eapply multi_trans. apply H0. apply multi_R. apply H1. split. apply H5. split. apply H6.
         apply H7. intuition. 
Qed.

Lemma finish_time_constant: forall s g o v n s',
  valid_dfs_state s g o ->
  M.find v (get_f_times s) = Some n ->
  dfs_multi s s' ->
  M.find v (get_f_times s') = Some n.
Proof.
  intros. induction H1.
  - apply H0.
  - inversion H1; subst; simpl in *.
    + apply IHmulti. eapply step. apply H. apply H1. apply H0.
    + apply IHmulti. eapply step. apply H. apply H1. apply H0.
    + destruct (O.eq_dec v x0).
      * unfold O.eq in e. subst. remember (g0, f, f_times, d_times, time, remain_d, remain_f, st) as s.
        assert (exists n, M.find x0 (get_f_times s) = Some n) by (exists n; subst; simpl; assumption).
        rewrite <- v_finished_iff_not_remain in H6. subst; simpl in *. rewrite H6 in H4. inversion H4.
        apply H. eapply remain_f_contains_valid_vertices. apply H. subst; simpl; assumption.
      * apply IHmulti. eapply step. apply H. apply H1. rewrite P.F.add_neq_o. apply H0.
        intuition.
Qed. 

(*If a vertex is not finished, then there is some state in the future where it will be finished*)
Lemma multistep_to_finish: forall s g o v,
  valid_dfs_state s g o ->
  G.contains_vertex g v = true ->
  black s v = false ->
  exists s',
  dfs_multi s s' /\ M.find v (get_f_times s') = Some (get_time s').
Proof.
  intros. assert (exists s', dfs_multi s s' /\ done s' = true ) by (eapply all_finish; eassumption).
  destruct_all. assert (valid_dfs_state x g o). eapply multistep_preserves_valid.
  apply H. apply H2. pose proof (all_finished_at_end x g o v H4 H0 H3). destruct_all.
  pose proof (finish_time_means_finished x g o v x0 H4 H5). destruct_all.
  assert (A:= H). assert (B:=H8). eapply valid_begins_with_start in H8. apply valid_begins_with_start in H.
  pose proof ((multi_from_start)(start_state g o) x1 s H H8). destruct H10.
  + assert (M.find v (get_f_times s) = Some x0). eapply finish_time_constant. apply B. apply H9. apply H10.
    assert (exists x, M.find v (get_f_times s) = Some x) by (exists x0; subst; simpl; assumption).
    rewrite <- black_iff_finished in H12. rewrite H12 in H1. inversion H1. apply A. apply H0.
  + exists x1. split. apply H10. subst. apply H9.
Qed. 

Lemma finish_time_constant': forall s g o s' v n m,
  valid_dfs_state s g o ->
  valid_dfs_state s' g o ->
  M.find v (get_f_times s) = Some n ->
  M.find v (get_f_times s') = Some m ->
  n = m.
Proof.
  intros. assert (A:=H). assert (B:=H0). apply valid_begins_with_start in H.
  apply valid_begins_with_start in H0. pose proof (multi_from_start (start_state g o) s s' H0 H).
  destruct H3.
  - pose proof (finish_time_constant s g o v n s' A H1 H3). rewrite H4 in H2. inversion H2; subst; reflexivity.
  - pose proof (finish_time_constant s' g o v m s B H2 H3). rewrite H4 in H1. inversion H1; subst; reflexivity.
Qed.

(*Another key lemma for Parentheses Theorem: If a vertex p is gray when v is discovered, then it finishes
  after*)
Lemma gray_at_discovery_time_later_f_time: forall s g o v p s' n m,
  valid_dfs_state s g o ->
  Some (get_time s) = M.find v (get_d_times s) ->
  p <> v ->
  gray s p = true ->
  dfs_multi s s' ->
  M.find v (get_f_times s') = Some n ->
  M.find p (get_f_times s') = Some m ->
  n < m.
Proof.
  intros. pose proof (gray_at_discovery_time_finishes_after s g o v p).
  pose proof (multistep_to_finish s g o p H). assert (G.contains_vertex g p = true).
  eapply finished_vertices_in_graph. eapply multistep_preserves_valid. apply H. apply H3.
  apply H5. assert (black s p = false). unfold black in *; unfold gray in *; simplify. simplify.
  specialize (H7 H8 H9). destruct_all. specialize (H6 x H H0 H1 H2 H7).
  assert (valid_dfs_state x g o). eapply multistep_preserves_valid. apply H. apply H7. 
  assert (valid_dfs_state s' g o). eapply multistep_preserves_valid. apply H. apply H3.
  assert (black x p = true). eapply black_iff_finished. apply H11. 
  apply H8. exists (get_time x). apply H10.
  specialize (H6 H13). 
  eapply black_iff_finished in H6. destruct H6. assert (A:=H6). eapply f_times_leq_current_time in H6.
  assert (x0 < get_time x \/ x0 = get_time x) by omega. destruct H14.
  + assert (m = (get_time x)). eapply finish_time_constant'. apply H12. apply H11. apply H5. apply H10.
    assert (n = x0). eapply finish_time_constant'. apply H12. apply H11. apply H4. apply A. subst. assumption.
  + pose proof (f_times_unique x g o v p x0 (get_time x) H11 A H10). apply H15 in H14. contradiction.
  + apply H11.
  + apply H11.
  + eapply finished_vertices_in_graph. apply H12. apply H4.
Qed.

(*Similar results as finish times for discovery times*)
(*If a vertex has a discovery time, then there is a valid state before where it was discovered*)
Lemma discovery_time_means_discovered: forall s g o v n,
  valid_dfs_state s g o->
  M.find v (get_d_times s) = Some n ->
  (exists s', dfs_multi s' s /\ n = get_time s' /\ valid_dfs_state s' g o /\ M.find v (get_d_times s') = Some n).
Proof.
  intros. induction H; subst; simpl in *. 
  - rewrite F.empty_o in H0. inversion H0.
  - inversion H1; subst; simpl in *.
     + destruct (O.eq_dec v x).
      * unfold O.eq in e. subst. rewrite F.add_eq_o in H0. inversion H0; subst. 
        exists (g0, F.add_root f x, f_times, M.add x (time + 1) d_times, time + 1, S.remove x remain_d, remain_f,
       add_to_stack x g0 remain_d ++ (x, None) :: tl).
        split. apply multi_refl. simpl. split. reflexivity. split. eapply step. apply H. apply H1.
        rewrite F.add_eq_o. reflexivity. reflexivity. reflexivity.
      * rewrite F.add_neq_o in H0. apply IHvalid_dfs_state in H0. destruct_all. exists x0.
        split. eapply multi_trans. apply H0. apply multi_R. apply H1. split. apply H4. split. apply H5.
         apply H6. intuition. 
    + destruct (O.eq_dec v x).
      * unfold O.eq in e. subst. rewrite F.add_eq_o in H0. inversion H0; subst. 
        exists (g0, F.add_child f y x, f_times, M.add x (time + 1) d_times, time + 1, S.remove x remain_d, remain_f,
       add_to_stack x g0 remain_d ++ (x, Some y) :: tl).
        split. apply multi_refl. simpl. split. reflexivity. split. eapply step. apply H. apply H1.
        rewrite F.add_eq_o. reflexivity. reflexivity. reflexivity.
      * rewrite F.add_neq_o in H0. apply IHvalid_dfs_state in H0. destruct_all. exists x0.
        split. eapply multi_trans. apply H0. apply multi_R. apply H1. split. apply H4. split. apply H5.
         apply H6. intuition. 
    + apply IHvalid_dfs_state in H0. destruct_all. exists x0. split. eapply multi_trans.
      apply H0. apply multi_R. apply H1. split. apply H5. split. apply H6. apply H7.
Qed.

Lemma discovery_time_constant: forall s g o v n s',
  valid_dfs_state s g o ->
  M.find v (get_d_times s) = Some n ->
  dfs_multi s s' ->
  M.find v (get_d_times s') = Some n.
Proof.
  intros. induction H1.
  - apply H0.
  - inversion H1; subst; simpl in *.
    + destruct (O.eq_dec v x0).
      * unfold O.eq in e. subst. remember (g0, f, f_times, d_times, time, remain_d, remain_f, st) as s.
        assert (exists n, M.find x0 (get_d_times s) = Some n) by (exists n; subst; simpl; assumption).
        rewrite <- v_discovered_iff_not_remain in H5. subst; simpl in *. rewrite H5 in H3. inversion H3.
        apply H. eapply remain_d_contains_valid_vertices. apply H. subst; simpl; assumption.
      * apply IHmulti. eapply step. apply H. apply H1. rewrite P.F.add_neq_o. apply H0.
        intuition.
    + destruct (O.eq_dec v x0).
      * unfold O.eq in e. subst. remember (g0, f, f_times, d_times, time, remain_d, remain_f, st) as s.
        assert (exists n, M.find x0 (get_d_times s) = Some n) by (exists n; subst; simpl; assumption).
        rewrite <- v_discovered_iff_not_remain in H5. subst; simpl in *. rewrite H5 in H3. inversion H3.
        apply H. eapply remain_d_contains_valid_vertices. apply H. subst; simpl; assumption.
      * apply IHmulti. eapply step. apply H. apply H1. rewrite P.F.add_neq_o. apply H0.
        intuition.
    + apply IHmulti. eapply step. apply H. apply H1. apply H0.
Qed. 

(*Every vertex is discovered before it is finished*)
Lemma discover_before_finish: forall s g o v n m,
  valid_dfs_state s g o ->
  M.find v (get_d_times s) = Some n ->
  M.find v (get_f_times s) = Some m ->
  n < m.
Proof.
  intros. induction H; subst; simpl in *.
  - rewrite F.empty_o in H0. inversion H0.
  - assert (G.contains_vertex g v = true). eapply finished_vertices_in_graph.
    eapply step. apply H. apply H2. apply H1. inversion H2; subst; simpl in *.
    + destruct (O.eq_dec x v).
      * unfold O.eq in e. subst. remember (g0, f, f_times, d_times, time, remain_d, remain_f, st) as s.
        pose proof (v_finished_iff_not_remain s g o v H H3). destruct H6. assert (S.mem v (get_remain_f s) = false).
        apply H7. exists m. subst; simpl; assumption. assert (A:=H8).
        pose proof (not_f_if_not_d s g o v H). apply contrapositive in H9. subst; simpl in *.
        contradiction. rewrite H8. intro. inversion H10.
      * rewrite F.add_neq_o in H0. apply IHvalid_dfs_state. apply H0. apply H1. apply n0.
    + destruct (O.eq_dec x v).
      * unfold O.eq in e. subst. remember (g0, f, f_times, d_times, time, remain_d, remain_f, st) as s.
        pose proof (v_finished_iff_not_remain s g o v H H3). destruct H6. assert (S.mem v (get_remain_f s) = false).
        apply H7. exists m. subst; simpl; assumption. assert (A:=H8).
        pose proof (not_f_if_not_d s g o v H). apply contrapositive in H9. subst; simpl in *.
        contradiction. rewrite H8. intro. inversion H10.
      * rewrite F.add_neq_o in H0. apply IHvalid_dfs_state. apply H0. apply H1. apply n0.
    + destruct (O.eq_dec x v).
      * unfold O.eq in e. subst. rewrite F.add_eq_o in H1. inversion H1; subst.
        remember (g0, f, f_times, d_times, time, remain_d, remain_f, st) as s.
        assert (M.find v (get_d_times s) = Some n) by (subst; simpl; assumption).
        eapply d_times_leq_current_time in H7. subst; simpl in *; omega. apply H. reflexivity.
      * rewrite F.add_neq_o in H1. apply IHvalid_dfs_state. apply H0. apply H1. apply n0.
Qed.

(*The last lemma before Parentheses Theorem: if v starts after u and u finishes after v, then v finishes
  before u*)
Lemma times_ordering: forall s g o u v du dv fu fv,
  valid_dfs_state s g o ->
  u <> v ->
  M.find u (get_d_times s) = Some du ->
  M.find v (get_d_times s) = Some dv ->
  M.find u (get_f_times s ) = Some fu ->
  M.find v (get_f_times s) = Some fv ->
  du < dv /\ dv < fu ->
  dv < fv /\ fv < fu.
Proof.
  intros. pose proof (discovery_time_means_discovered  s g o v _ H H2). destruct_all.
  subst. assert (M.find u (get_d_times x) = Some du). { 
  pose proof (discovery_time_means_discovered s g o u _ H H1). destruct_all.
  subst. assert (A:=H12). assert (B:= H8). apply valid_begins_with_start in A.
  apply valid_begins_with_start in B. pose proof (multi_from_start (start_state g o) x0 x B A).
  destruct H11. eapply discovery_time_constant. apply H12. apply H13. apply H11.
  apply time_incr_multi in H11. destruct H11. subst. omega. omega. }
  assert (M.find u (get_f_times x) = None). { destruct (M.find u (get_f_times x)) eqn : ?.
  assert (A:=Heqo0). eapply f_times_leq_current_time in Heqo0. pose proof
  (finish_time_constant' s g o x u fu n H H8 H3 A). subst. omega. apply H8. reflexivity. }
  assert (gray x u = true). assert (G.contains_vertex g u = true). 
  eapply discovered_vertices_in_graph. apply H8. apply H7. pose proof (v_discovered_iff_not_remain x g o u H8 H12).
  destruct H13. assert (S.mem u (get_remain_d x) = false). apply H14. exists du. apply H7.
  clear H13. clear H14. pose proof (v_finished_iff_not_remain x g o u H8 H12). destruct H13.
  apply contrapositive in H13. unfold gray; simplify. destruct (S.mem u (get_remain_f x)).
  reflexivity. exfalso. apply H13. reflexivity. intro. destruct H16. rewrite H16 in H11. inversion H11.
  split. eapply discover_before_finish. apply H. apply H2. apply H4.
  eapply gray_at_discovery_time_later_f_time. apply H8. symmetry. apply H9. apply H0.
  apply H12. apply H6. apply H4. apply H3.
Qed.

(*No vertex is discovered at the same time another one is finished*)
Theorem all_times_unique: forall s g o u v n,
  valid_dfs_state s g o ->
  M.find v (get_d_times s) = Some n ->
  M.find u (get_f_times s) = Some n ->
  False.
Proof.
  intros. induction H; subst; simpl in *.
  - rewrite F.empty_o in H0. inversion H0.
  - inversion H2; subst; simpl in *.
    + destruct (O.eq_dec x v).
      * unfold O.eq in e. subst. rewrite F.add_eq_o in H0. inversion H0; subst.
        remember (g0, f, f_times, d_times, time, remain_d, remain_f, st) as s.
        assert (M.find u (get_f_times s) = Some (time + 1)) by (subst; simpl; assumption).
        eapply f_times_leq_current_time in H5. subst; simpl in *. omega. apply H. reflexivity.
      * rewrite F.add_neq_o in H0. apply IHvalid_dfs_state; assumption. apply n0.
    + destruct (O.eq_dec x v).
      * unfold O.eq in e. subst. rewrite F.add_eq_o in H0. inversion H0; subst.
        remember (g0, f, f_times, d_times, time, remain_d, remain_f, st) as s.
        assert (M.find u (get_f_times s) = Some (time + 1)) by (subst; simpl; assumption).
        eapply f_times_leq_current_time in H5. subst; simpl in *. omega. apply H. reflexivity.
      * rewrite F.add_neq_o in H0. apply IHvalid_dfs_state; assumption. apply n0.
    + destruct (O.eq_dec x u).
      * unfold O.eq in e. subst. rewrite F.add_eq_o in H1. inversion H1; subst.
        remember (g0, f, f_times, d_times, time, remain_d, remain_f, st) as s.
        assert (M.find v (get_d_times s) = Some (time + 1)) by (subst; simpl; assumption).
        eapply d_times_leq_current_time in H6. subst; simpl in *. omega. apply H. reflexivity.
      * rewrite F.add_neq_o in H1. apply IHvalid_dfs_state; assumption. apply n0.
Qed.

(** ** Parentheses Theorem **)

Theorem parentheses_theorem: forall s g o u v du dv fu fv,
  valid_dfs_state s g o ->
  u <> v ->
  M.find u (get_d_times s) = Some du ->
  M.find v (get_d_times s) = Some dv ->
  M.find u (get_f_times s ) = Some fu ->
  M.find v (get_f_times s) = Some fv ->
  (du < dv /\ dv < fv /\ fv < fu) \/ (dv < du /\ du < fu /\ fu < fv)
   \/ (dv < fv /\ fv < du /\ du < fu) \/ (du < fu /\ fu < dv /\ dv < fv).
Proof.
  intros. assert (du < dv \/ dv < du \/ du = dv) by omega. destruct H5.
  - assert (dv < fu \/ fu < dv \/ dv = fu) by omega. destruct H6.
    + left. pose proof (times_ordering s g o u v du dv fu fv H H0 H1 H2 H3 H4).
      destruct H7. omega. omega.
    + destruct H6.
      * right. right. right. assert (du < fu). eapply discover_before_finish.
        apply H. apply H1. apply H3. assert (dv < fv). eapply discover_before_finish.
        apply H. apply H2. apply H4. omega.
      * subst. exfalso. eapply all_times_unique. apply H. apply H2. apply H3.
  - destruct H5.
    + assert (du < fv \/ fv < du \/ du = fv) by omega. destruct H6.
      * right. left. assert (v <> u) by auto. pose proof (times_ordering s g o v u dv du fv fu H H7 H2 H1 H4 H3).
        omega.
      * destruct H6.
        -- right. right. left. assert (dv < fv) by (eapply discover_before_finish; eassumption).
           assert (du < fu) by (eapply discover_before_finish; eassumption). omega.
        -- subst. exfalso. eapply all_times_unique. apply H. apply H1. apply H4.
    + subst. assert (u = v). eapply d_times_unique. apply H. apply H2. apply H1. reflexivity. contradiction.
Qed. 

(** ** Lemmas for Corollary 22.8 of CLRS (u is a descendant of v iff du < dv < fv < fu) **)

(*If a vertex u is gray when v is discovered, then v is a descendant of u in the DFS forest*)
Lemma gray_at_discovery_time_implies_descedant: forall s g o u v,
  valid_dfs_state s g o ->
  u <> v ->
  gray s u = true ->
  M.find v (get_d_times s) = Some (get_time s) ->
  F.desc (get_forest s) u v.
Proof. 
  intros. induction H; subst; simpl in *.
  - rewrite F.empty_o in H2. inversion H2.
  - inversion H3; subst; simpl in *.
    + assert (tl = nil). eapply root_nil. eapply step. apply H. apply H3. reflexivity.
      subst. destruct (O.eq_dec x v).
      * unfold O.eq in e. subst. 
 remember (g0, F.add_root f v, f_times, M.add v (time + 1) d_times, time + 1, S.remove v remain_d, remain_f,
       add_to_stack v g0 remain_d ++ (v, None) :: nil) as s'. pose proof (gray_on_stack s' g o u).
       assert (A:=H1). apply H6 in H1. destruct_all. unfold gray in *; subst; simpl in *.
       rewrite P2.FM.remove_neq_b in A. simplify. apply in_app_or in H1. destruct H1.
       eapply only_add_yet_to_be_discovered in H1. rewrite H1 in H7. inversion H7.
       destruct H1; inversion H1; subst. exfalso. apply H0. reflexivity. auto. eapply step. apply H.
       apply H3.
      * rewrite P.F.add_neq_o in H2. remember (g0, f, f_times, d_times, time, remain_d, remain_f, st) as s.
        assert (M.find v (get_d_times s) = Some (time + 1)) by (subst; simpl; assumption).
        eapply d_times_leq_current_time in H6. subst; simpl in *. omega. apply H. apply n.
    + destruct (O.eq_dec x v).
      * unfold O.eq in e. subst. remember (g0, F.add_child f y v, f_times, M.add v (time + 1) d_times, time + 1, S.remove v remain_d, remain_f,
       add_to_stack v g0 remain_d ++ (v, Some y) :: tl) as s.
        assert (valid_dfs_state s g o) by (eapply step; [apply H | apply H3]). 
       pose proof (right_left_stacks s g o u H6). destruct_all. specialize (H7 H1). destruct_all.
       rewrite Heqs in H7. simpl in H7. assert (A:=H7). apply app_match in H7. destruct H7; destruct_all.
       rewrite H7 in A. rewrite <- app_assoc in A. apply app_inv_head in A. 
       destruct x2. inversion A; subst. contradiction. inversion A; subst.
       assert (In (u, x0) (add_to_stack v g0 remain_d)) by (rewrite H7; solve_in).
       apply only_add_yet_to_be_discovered in H11. unfold gray in *; simpl in *; simplify.
       rewrite P2.FM.remove_neq_b in H12. rewrite H12 in H11. inversion H11. auto.
       rewrite H7 in A. rewrite <- app_assoc in A. apply app_inv_head in A.
       destruct x2. inversion A; subst. contradiction. inversion A; subst.
        simpl in *. specialize (H10 v y). destruct H10. solve_in.
        eapply F.is_descendant_trans. apply H7. apply F.is_descendant_edge.
        remember (g0, f, f_times, d_times, time, remain_d, remain_f, st) as s.
        assert (f = get_forest s) by (subst; reflexivity). rewrite H10.
        apply F.add_child_1. destruct (pop_stack st remain_f) eqn : ?; simpl in H5.
        destruct (S.min_elt remain_d); inversion H5. rewrite <- H5 in Heqs0. clear H5.
         eapply gray_in_forest. apply H. eapply parents_valid. apply H. subst; simpl. eapply in_pop_rev.
        rewrite Heqs0. left. reflexivity. eapply parents_not_white. apply H. subst. simpl. eapply in_pop_rev.
        rewrite Heqs0. left. reflexivity. eapply white_not_in_forest. apply H. unfold white.
        assert (S.mem v (get_remain_d s) = true) by (subst; simpl; assumption). rewrite H11.
        eapply not_f_if_not_d in H11. apply H11. apply H. subst.
        apply F.is_descendant_edge. remember (g0, f, f_times, d_times, time, remain_d, remain_f, st) as s.
        assert (f = get_forest s) by (subst; reflexivity). apply F.add_child_1.
         rewrite H7. 
        unfold gray in H1; simpl in H1. rewrite P2.FM.remove_neq_b in H1. simplify.
        eapply gray_in_forest. apply H. eapply remain_f_contains_valid_vertices. apply H. subst; simpl. apply H11.
        unfold white. replace (get_remain_d s) with remain_d by (subst; reflexivity).
        rewrite H10. reflexivity. auto. rewrite H7. eapply white_not_in_forest. apply H.
        unfold white. assert (S.mem v (get_remain_d s) = true) by (subst; simpl; assumption).
        rewrite H10. eapply not_f_if_not_d in H10. rewrite H10. reflexivity. apply H.
       * rewrite P.F.add_neq_o in H2. remember (g0, f, f_times, d_times, time, remain_d, remain_f, st) as s.
        assert (M.find v (get_d_times s) = Some (time + 1)) by (subst; simpl; assumption).
        eapply d_times_leq_current_time in H6. subst; simpl in *. omega. apply H. apply n.
      + remember (g0, f, f_times, d_times, time, remain_d, remain_f, st) as s.
        assert (M.find v (get_d_times s) = Some (time + 1)) by (subst; simpl; assumption).
        eapply d_times_leq_current_time in H7. subst; simpl in *. omega. apply H.
Qed. 

(*Descendants do not change as the algorithm steps*)
Lemma descendant_constant: forall s g o u v,
  valid_dfs_state s g o ->
  F.desc (get_forest s) u v ->
  forall s',
  dfs_multi s s' ->
  F.desc (get_forest s') u v.
Proof.
  intros. induction H1; subst; simpl in *.
  - apply H0.
  - inversion H1; subst; simpl in *.
    + apply IHmulti. eapply step. apply H. apply H1. rewrite <- F.add_root_4. apply H0.
    + apply IHmulti. eapply step. apply H. apply H1. apply F.is_descendant_1. apply H0.
    + apply IHmulti. eapply step. apply H. apply H1. apply H0.
Qed.

(*Part 1 (<=) of the corollary: If du < dv < dv < fu, then v is a descendant of u*)
Lemma time_interval_implies_descendant: forall s g o u v du dv fu fv,
  valid_dfs_state s g o ->
  u <> v ->
  M.find u (get_d_times s) = Some du ->
  M.find u (get_f_times s) = Some fu ->
  M.find v (get_d_times s) = Some dv ->
  M.find v (get_f_times s) = Some fv ->
  (du < dv) /\ (dv < fv) /\ (fv < fu) ->
  F.desc (get_forest s) u v.
Proof.
  intros. pose proof (discovery_time_means_discovered s g o v dv H H3). destruct_all.
  assert (gray x u = true). { assert (G.contains_vertex g u = true). eapply finished_vertices_in_graph.
  apply H. apply H2. assert (M.find u (get_d_times x) = Some du). { 
  pose proof (discovery_time_means_discovered s g o u du H H1). destruct_all. 
  assert (A:=H8). assert (B:=H15). apply valid_begins_with_start in H8. apply valid_begins_with_start in H15.
  pose proof (multi_from_start (start_state g o) x x0 H15 H8). destruct H17. subst.
  apply time_incr_multi in H17. destruct H17. subst. apply H16. omega.
  eapply discovery_time_constant. apply B. apply H16. apply H17. }
  assert (M.find u (get_f_times x) = None). {
  destruct (M.find u (get_f_times x)) eqn : ?. assert (A:=Heqo0).
  eapply finish_time_constant in Heqo0. rewrite Heqo0 in H2. inversion H2; subst.
  eapply f_times_leq_current_time in A. omega. apply H8. apply H8. apply H6. reflexivity. }
  unfold gray. pose proof (v_discovered_iff_not_remain x g o u H8 H12).
  pose proof (v_finished_iff_not_remain x g o u H8 H12). destruct H15. destruct H16.
  apply contrapositive in H16. destruct (S.mem u (get_remain_f x)).
  rewrite H17. reflexivity. exists du. apply H13. contradiction. intro. destruct_all.
  rewrite H19 in H14. inversion H14. }
  eapply descendant_constant. apply H8.
  eapply gray_at_discovery_time_implies_descedant. apply H8. apply H0. apply H12. subst.
  apply H9. apply H6.
Qed. 

(*Older proof, try to make shorter/use other theorems. I'm sure there is a better proof that the parent
  is gray at this point.*)
Lemma destruct_app: forall (l1: stack) x l2 y  l3,
  l1 ++ x :: l2 = y :: l3 ->
  (l1 = nil /\ x = y /\ l2 = l3) \/ In y l1.
Proof.
  intros. induction l1.
  - simpl in H. inversion H; subst. left. split; try(split); reflexivity.
  - destruct (stack_elt_dec y a).
    + subst. right. simpl. left. reflexivity.
    + inversion H; subst. contradiction.
Qed.  

(*If a vertex has a child on the stack, then it is gray*)
Lemma parent_gray: forall s g o y,
  valid_dfs_state s g o ->
  (exists x, In (x, Some y) (get_stack s)) ->
  gray s y = true.
Proof.
  intros. unfold gray. induction H; subst; simpl in *.
  - destruct o. destruct (G.contains_vertex g v). all: repeat(try(inversion H); try(inversion H0); try(inversion H1)).
  - inversion H1; subst; simpl in *.
    + assert (tl = nil). remember (g0, F.add_root f x, f_times, M.add x (time + 1) d_times, time + 1, S.remove x remain_d, remain_f,
       add_to_stack x g0 remain_d ++ (x, None) :: tl)as s.
      eapply root_nil. eapply step. apply H. apply H1. subst; simpl. reflexivity. subst.
      destruct H0. apply in_app_or in H0. destruct H0.
      * apply add_to_stack_adds_parent in H0. inversion H0; subst. simplify.
        destruct (S.mem x (S.remove x remain_d)) eqn : ?. exfalso. eapply remove_eq. apply Heqb.
        reflexivity. remember (g0, f, f_times, d_times, time, remain_d, remain_f, st) as s.
        assert (S.mem x (get_remain_d s ) = true) by (subst; simpl; assumption). 
        eapply not_f_if_not_d in H4. subst; simpl in *; assumption. apply H.
      * simpl in H0; destruct H0; inversion H0.
    + destruct H0. apply in_app_or in H0. destruct H0. apply add_to_stack_adds_parent in H0. inversion H0; subst.
      simplify. destruct (S.mem x (S.remove x remain_d)) eqn : ?. exfalso. eapply remove_eq. apply Heqb. reflexivity.
      remember (g0, f, f_times, d_times, time, remain_d, remain_f, st) as s.
      assert (S.mem x (get_remain_d s) = true) by (subst; simpl; assumption). eapply not_f_if_not_d in H4.
      subst; simpl in *; assumption. apply H. destruct (pop_stack st remain_f) eqn : ?; simpl in H3.
      * destruct (S.min_elt remain_d); inversion H3; subst.
      * rewrite andb_true_iff. assert (exists x, In (x, Some y) st). exists x0. eapply in_pop_rev.
        rewrite Heqs. rewrite <- H3. apply H0. apply IHvalid_dfs_state in H4. split. simplify.
        rewrite P2.Dec.F.remove_b. simplify. simplify.
    + destruct H0.
      destruct (O.eq_dec x y).
      * remember (g0, f, f_times, d_times, time, remain_d, remain_f, st) as s.
        assert (gray s x = true). subst; unfold gray; simpl in *; simplify.
        pose proof (right_left_stacks  s g o x H). destruct H6. destruct H6. 
        apply H6 in H5. clear H6. destruct H5. destruct H5. subst; simpl in *.
        destruct (pop_stack st remain_f) eqn : ?.
        -- simpl in H4. destruct (S.min_elt remain_d). inversion H4; subst. destruct H0.
            inversion H4.
        -- simpl in H4. rewrite <- H4 in Heqs. rewrite H5 in Heqs. 
           rewrite pop_stack_app_distr in Heqs. destruct H6. 
           pose proof destruct_app. specialize (H8 (pop_stack x3 remain_f) (x, x2) x1 (x, o0) tl).
           apply H8 in Heqs. assert (In (x0, Some y) x1). { destruct Heqs.
           ++ destruct H9. destruct H10. inversion H10; subst. apply H0.
           ++ assert (In (x, o0) x3). eapply in_pop_rev. apply H9. exfalso. apply (H6 o0).
              apply H10. } exfalso. destruct H7. apply (H7 x0). rewrite e. apply H9. apply H3.
      * destruct (pop_stack st remain_f) eqn : ?.
        ++ simpl in H4. destruct (S.min_elt remain_d); inversion H4; subst. destruct H0.
        ++ simpl in H4. rewrite <- H4 in Heqs. assert (exists x, In (x, Some y) st). exists x0. eapply in_pop_rev.
           rewrite Heqs. right. apply H0. apply IHvalid_dfs_state in H5. simplify.
Qed.

(*get rid of exists in hypothesis*)
Lemma parent_on_stack_is_gray: forall s g o u v,
  valid_dfs_state s g o ->
  In (u, Some v) (get_stack s) ->
  gray s v = true.
Proof.
 intros. eapply parent_gray. apply H. exists u. apply H0.
Qed.

(*If u , v is an edge in DFS forest, then v is gray at time du*)
Lemma parent_in_forest_gray_at_discovery_time: forall s g o u v,
  valid_dfs_state s g o ->
  F.is_child (get_forest s) u v = true ->
  M.find v (get_d_times s) = Some (get_time s) ->
  gray s u = true.
Proof.
  intros. inversion H; subst.
  - apply F.is_child_1 in H0. destruct_all. simpl in *.
    pose proof F.empty_1. rewrite F.empty_2 in H4. rewrite H4 in H0. inversion H0.
  - inversion H3; subst; simpl in *.
    + unfold gray in *; simpl in *. destruct (O.eq_dec x v).
      * unfold O.eq in e. subst. assert (F.is_root (F.add_root f v) v = true).
        apply F.is_root_1. remember (g0, f, f_times, d_times, time, remain_d, remain_f, st) as s.
        replace f with (get_forest s) by (subst; reflexivity). eapply white_not_in_forest.
        apply H2. unfold white. replace remain_d with (get_remain_d s) in H4 by (subst; simpl; reflexivity).
        rewrite H4. eapply not_f_if_not_d in H4. rewrite H4. reflexivity. apply H2. 
        pose proof (F.is_root_2 (F.add_root f v) v). destruct H7. apply F.add_root_1. 
        apply contrapositive in H8. exfalso. apply H8. exists u. apply H0. rewrite H6. intro. inversion H9.
      * rewrite P.F.add_neq_o in H1. remember (g0, f, f_times, d_times, time, remain_d, remain_f, st) as s.
        replace d_times with (get_d_times s) in H1 by (subst; reflexivity). eapply d_times_leq_current_time in H1.
        subst; simpl in *. omega. apply H2. apply n.
    + destruct (O.eq_dec x v). 
      * unfold O.eq in e. subst. destruct (pop_stack st remain_f) eqn : ?; simpl in H5. destruct (S.min_elt remain_d); inversion H5.
        rewrite <- H5 in Heqs. clear H5. remember (g0, f, f_times, d_times, time, remain_d, remain_f, st) as s'.
        assert (f = (get_forest s')) by (subst; reflexivity). assert (F.is_child (F.add_child f y v) y v = true).
        rewrite H5. apply F.add_child_1. eapply gray_in_forest. apply H2. eapply parents_valid.
        apply H. simpl. apply in_or_app. right. left. reflexivity. eapply parents_not_white.
        apply H2. eapply in_pop_rev.  subst; simpl. rewrite Heqs. left. reflexivity.
        eapply white_not_in_forest. apply H2. unfold white. replace (remain_d) with (get_remain_d s') in H4
        by (subst; reflexivity). rewrite H4. eapply not_f_if_not_d in H4. rewrite H4. reflexivity.
        apply H2. pose proof (F.is_child_2 _ _ _ _ H6 H0). subst. eapply parent_on_stack_is_gray.
        apply H. simpl. apply in_or_app. right. left. reflexivity.
      * rewrite P.F.add_neq_o in H1. remember (g0, f, f_times, d_times, time, remain_d, remain_f, st) as s.
        replace d_times with (get_d_times s) in H1 by (subst; reflexivity). eapply d_times_leq_current_time in H1.
        subst; simpl in *. omega. apply H2. apply n.
    + remember (g0, f, f_times, d_times, time, remain_d, remain_f, st) as s.
        replace d_times with (get_d_times s) in H1 by (subst; reflexivity). eapply d_times_leq_current_time in H1.
        subst; simpl in *. omega. apply H2.
Qed. 

(*If a vertex is a root (has no parent) in the DFS forest at one point in the algorithm, then
  it is a root in all future steps*)
Lemma root_preserved: forall s g o v,
  valid_dfs_state s g o ->
  F.is_root (get_forest s) v = true ->
  forall s', dfs_multi s s' ->
  F.is_root (get_forest s') v = true.
Proof.
  intros. induction H1.
  - apply H0.
  - assert (valid_dfs_state y g o). eapply step. apply H. apply H1. specialize (IHmulti H3).
    clear H3. inversion H1; subst; simpl in *.
    + apply IHmulti. apply F.is_root_4. apply H0.
    + apply IHmulti. apply F.is_root_3. apply H0.
    + apply IHmulti. apply H0.
Qed. 

(*Likewise, edges in the DFS forest are preserved*)
Lemma child_preserved: forall s g o u v,
  valid_dfs_state s g o ->
  F.is_child (get_forest s) u v = true ->
  forall s', dfs_multi s s' ->
  F.is_child (get_forest s') u v = true.
Proof.
  intros. induction H1.
  - apply H0.
  - assert (valid_dfs_state y g o). eapply step. apply H. apply H1. specialize (IHmulti H3). clear H3.
    inversion H1; subst; simpl in *; apply IHmulti.
    + rewrite <- F.add_root_5. apply H0.
    + apply F.add_child_2. apply H0.
    + apply H0.
Qed.

(*Every vertex is either a root it has a parent in the forest at its discovery time
  (TODO: might be able to prove in general that every vertex is either a root or has a parent
  and then it will be trivial*)
Lemma parent_or_root_at_discovery: forall s g o v,
  valid_dfs_state s g o ->
  M.find v (get_d_times s) = Some (get_time s) ->
  (exists u, F.is_child (get_forest s) u v = true) \/ F.is_root (get_forest s) v = true.
Proof.
  intros. assert (F.contains_vertex (get_forest s) v = true). eapply gray_in_forest.
  apply H. eapply discovered_vertices_in_graph. apply H. apply H0. unfold white.
  assert (exists n, M.find v (get_d_times s) = Some n) by (exists (get_time s); apply H0).
  rewrite <- v_discovered_iff_not_remain in H1. rewrite H1. reflexivity.
  apply H. eapply discovered_vertices_in_graph. apply H. apply H0.  
  destruct (F.is_root (get_forest s) v) eqn : ?.
  + right. reflexivity.
  + apply F.is_root_2 in Heqb. left. apply Heqb. apply H1.
Qed.

(*An edge in the DFS forest between (u,v) exists iff it exists at time du (so 
  the only time we add an edge is when v is discovered)*)
Lemma child_iff_at_discovery: forall s g o u v x,
  valid_dfs_state s g o ->
  valid_dfs_state x g o ->
  M.find v (get_d_times x) = Some (get_time x) ->
  (exists n, M.find v (get_d_times s) = Some n) ->
  F.is_child (get_forest s) u v = true <-> F.is_child (get_forest x) u v = true.
Proof.
  intros. assert (dfs_multi x s). { assert (A:= H). assert (B:= H0). apply valid_begins_with_start 
  in H. apply valid_begins_with_start in H0. pose proof (multi_from_start _ _ _ H H0). destruct H3. apply H3.
  destruct_all. assert (x0 = get_time x). eapply discovery_time_constant in H2. rewrite H2 in H1. inversion H1; subst.
  reflexivity. apply A. apply H3. subst. 
  apply time_incr_multi in H3. destruct H3. subst. apply multi_refl. eapply d_times_leq_current_time in H2.
   omega. apply A. } split; intros.
  - pose proof (parent_or_root_at_discovery x g o v H0 H1). destruct H5. destruct_all.
    assert (F.is_child (get_forest s) x0 v = true). eapply child_preserved. apply H0. apply H5.
    apply H3. assert (x0 = u). eapply F.is_child_2. apply H6. apply H4. subst.
    apply H5. assert (F.is_root (get_forest s) v = true). eapply root_preserved. apply H0.
    apply H5. apply H3. pose proof (F.is_root_2 (get_forest s) v). destruct H7.
    eapply gray_in_forest. apply H. eapply discovered_vertices_in_graph. apply H0.
    apply H1. rewrite <- v_discovered_iff_not_remain in H2. unfold white. rewrite H2. reflexivity.
    apply H. eapply discovered_vertices_in_graph. apply H0.
    apply H1. apply contrapositive in H8. exfalso. apply H8. exists u. apply H4. rewrite H6.
    intro. inversion H9.
  - eapply child_preserved. apply H0. apply H4. apply H3.
Qed.

(*If v is a child of u in the DFS forest (not yet a descendant in general), then
  du < dv < fv < fu*)
Lemma parent_implies_time_interval: forall s g o u v du dv fu fv,
  valid_dfs_state s g o ->
  u <> v ->
  F.is_child (get_forest s) u v = true ->
  M.find u (get_d_times s) = Some du ->
  M.find u (get_f_times s) = Some fu ->
  M.find v (get_d_times s) = Some dv ->
  M.find v (get_f_times s) = Some fv ->
  (du < dv) /\ (dv < fv) /\ (fv < fu).
Proof.
  intros. pose proof (discovery_time_means_discovered s g o v dv H H4). destruct_all.
   assert (F.is_child (get_forest x) u v = true). erewrite <- child_iff_at_discovery.
   apply H1. apply H. apply H8. subst. apply H9. exists dv. apply H4.
  assert (gray x u = true). 
 eapply parent_in_forest_gray_at_discovery_time. apply H8.
   apply H10. subst. apply H9. subst. pose proof (times_ordering _ _ _ _ _ _ _ _ _ H H0 H2 H4 H3 H5) as T.
    pose proof (discovery_time_means_discovered s g o u du H H2). destruct_all; subst.
    assert (A:= H8). assert (B:= H13). 
    apply valid_begins_with_start in H8. apply valid_begins_with_start in H13.
    pose proof (multi_from_start _ _ _ H8 H13). destruct H12.
    assert (C:= H12). eapply time_incr_multi in H12. destruct H12.
    subst. assert (u = v). eapply d_times_unique. apply H. apply H4. apply H2.
    reflexivity. subst. contradiction. split. apply H12. 
    assert (M.find u (get_f_times x) = None). unfold gray in *. simplify.
    destruct (M.find u (get_f_times x)) eqn : ?. 
    assert (exists n, M.find u (get_f_times x) = Some n) by (exists n; assumption).
    rewrite <- v_finished_iff_not_remain in H11. rewrite H11 in H16. inversion H16.
    apply A. eapply remain_f_contains_valid_vertices. apply A. apply H16. reflexivity.
    pose proof (finish_time_means_finished s g o u fu H H3). destruct_all;subst. 
    assert (D:= H18). apply valid_begins_with_start in H18.
    pose proof (multi_from_start _ _ _ H18 H8). destruct H17.
    apply time_incr_multi in H17. destruct H17. subst.
    exfalso. eapply all_times_unique. apply H. apply H4. apply H3. 
    apply T. split. apply H12. apply H17. 
    eapply finish_time_constant in H19. rewrite H19 in H15. inversion H15. apply D. apply H17.
    assert (exists n, M.find u (get_d_times x) = Some n). { rewrite <- v_discovered_iff_not_remain.
    unfold gray in *; simpl in *; simplify. apply A. eapply discovered_vertices_in_graph.
    apply H. apply H2. } destruct_all.
    assert (C:=H15).
    eapply discovery_time_constant in H15. rewrite H15 in H14. inversion H14; subst.
    assert (x <> x0). intro. subst. assert (u = v). eapply d_times_unique. apply H.
    apply H4. apply H2. reflexivity. subst. contradiction.
    eapply time_incr_multi in H12. destruct H12. subst. contradiction.
    eapply d_times_leq_current_time in C. omega. apply A. apply A. apply H12.
Qed.

(** ** Proof that DFS forest and original graph have same vertices **)

(*Every vertex in the DFS forest was in the original graph*)
Lemma vertices_in_forest_in_graph: forall s g o u,
  valid_dfs_state s g o ->
  F.contains_vertex (get_forest s) u = true ->
  G.contains_vertex g u = true.
Proof.
  intros. induction H; subst; simpl in *.
  - pose proof F.empty_2. pose proof F.empty_1. rewrite H in H1. rewrite H1 in H0. inversion H0.
  - inversion H1; subst; simpl in *. 
    + apply F.add_root_3 in H0. destruct H0.
      * subst. eapply remain_d_contains_valid_vertices. apply H. simpl. apply H2.
      * apply IHvalid_dfs_state. apply H0.
    + apply F.add_child_6 in H0. destruct H0.
      * apply IHvalid_dfs_state. apply H0.
      * subst. eapply remain_d_contains_valid_vertices. apply H. simpl. apply H2.
    + apply IHvalid_dfs_state. apply H0.
Qed.

(*Every vertex in the original forest iff it is not white (has been discovered)*)
Lemma in_forest_iff_not_white: forall s g o u,
  valid_dfs_state s g o ->
  G.contains_vertex g u = true ->
  (white s u = false) <-> F.contains_vertex (get_forest s) u = true.
Proof.
  intros. split; intros. eapply gray_in_forest. apply H. apply H0. apply H1.
  induction H; subst; simpl in *.
  - pose proof F.empty_1. pose proof F.empty_2. rewrite H2 in H. rewrite H in H1. inversion H1.
  - specialize (IHvalid_dfs_state H0). unfold white in *. inversion H2; subst; simpl in *.
    + destruct (O.eq_dec x u).
      * unfold O.eq in e. subst. rewrite remove_eq_false. reflexivity.
      * apply F.add_root_3 in H1. destruct H1. subst. exfalso. apply n. reflexivity.
        rewrite P2.FM.remove_neq_b. apply IHvalid_dfs_state. apply H1. apply n.
    + destruct (O.eq_dec x u).
      * unfold O.eq in e. subst. rewrite remove_eq_false. reflexivity.
      * apply F.add_child_6 in H1. destruct H1. rewrite P2.FM.remove_neq_b. apply IHvalid_dfs_state.
        apply H1. apply n. subst. exfalso. apply n. reflexivity.
    + simplify. rewrite P2.Dec.F.remove_b. simplify.
Qed.

(*There are no white vertices when we finish*)
Lemma no_white_vertices_at_end: forall s g o u,
  valid_dfs_state s g o ->
  done s = true ->
  white s u = false.
Proof.
  intros. pose proof (all_finished_at_end s g o u H). destruct (G.contains_vertex g u) eqn : ?.
  - assert (exists n : nat, M.find u (get_f_times s) = Some n) by (apply H1; [reflexivity|assumption]).
    rewrite <- v_finished_iff_not_remain in H2. unfold white. rewrite H2. apply andb_false_r.
    apply H. apply Heqb.
  - destruct (white s u) eqn : ?. unfold white in Heqb0. simplify.
    assert (G.contains_vertex g u = true). eapply remain_d_contains_valid_vertices. apply H.
    apply H2. rewrite H4 in Heqb. inversion Heqb. reflexivity.
Qed. 

(*The DFS forest has the same vertices as the original graph*)
Lemma same_vertices: forall s g o u,
  valid_dfs_state s g o ->
  done s = true ->
  (G.contains_vertex g u = true <-> F.contains_vertex (get_forest s) u = true).
Proof.
  intros. eapply no_white_vertices_at_end in H0. split; intros.
  rewrite <- in_forest_iff_not_white. apply H0. apply H. apply H1. 
  eapply vertices_in_forest_in_graph. apply H. apply H1. apply H.
Qed.

(*If v is a descendant of v, then u <> v. Note that this is equivalent to proving that the
  DFS forest is acyclic, once I defined that formally. It is also very likely that
  this follows immediately from acyclicty, so I may change it TODO: come back*)
Lemma desc_in_forest_neq: forall s g o u v,
  valid_dfs_state s g o ->
  F.desc (get_forest s) u v ->
  u <> v.
Proof.
  intros. induction H; subst; simpl in *.
  - pose proof F.empty_1. pose proof F.empty_2. inversion H0; subst. 
    apply F.is_child_1 in H2. destruct_all. rewrite H1 in H. rewrite H in H2. inversion H2.
    apply F.is_child_1 in H3. destruct_all. rewrite H1 in H. rewrite H in H3. inversion H3.
  - inversion H1; subst; simpl in *. 
    + rewrite <- F.add_root_4 in H0. apply IHvalid_dfs_state. apply H0.
    + assert (F.contains_vertex f y = true). { 
      remember (g0, f, f_times, d_times, time, remain_d, remain_f, st) as s.
      replace f with (get_forest s) by (subst; reflexivity).
      destruct (pop_stack st remain_f) eqn : ?; simpl in H3.
      destruct (S.min_elt remain_d); inversion H3. rewrite <- H3 in Heqs0; clear H3. eapply gray_in_forest.
      apply H. eapply parents_valid. apply H. subst; simpl. eapply in_pop_rev. rewrite Heqs0.
      left. reflexivity. eapply parents_not_white. apply H. subst; simpl. eapply in_pop_rev.
      rewrite Heqs0. left. reflexivity. } assert (F.contains_vertex f x = false). {
      remember (g0, f, f_times, d_times, time, remain_d, remain_f, st) as s.
      replace f with (get_forest s) by (subst; reflexivity).
      eapply white_not_in_forest. apply H. unfold white. replace remain_d with (get_remain_d s) in H2
      by (subst; reflexivity). rewrite H2. eapply not_f_if_not_d in H2. apply H2. apply H. }
      destruct (O.eq_dec u x). 
      * unfold O.eq in e. subst. eapply F.desc_is_leaf in H4. exfalso. apply H4.
        apply H0. apply H5.
      * apply F.is_descendant_2 in H0. destruct H0. subst. apply n. apply IHvalid_dfs_state.
        apply H0. apply H4.
    + apply IHvalid_dfs_state. apply H0.
Qed.

(*Every vertex has a discovery and finish time when the algorithm terminates*)
Lemma all_times_when_done: forall s g o u,
  valid_dfs_state s g o ->
  done s = true ->
  G.contains_vertex g u = true ->
  (exists n, M.find u (get_d_times s) = Some n) /\
  (exists n, M.find u (get_f_times s) = Some n).
Proof.
  intros. assert (black s u = true). unfold black. unfold done in *. simplify. 
  destruct (S.mem u (get_remain_d s)) eqn : ?. solve_empty. reflexivity.
  simplify. destruct (S.mem u (get_remain_f s)) eqn : ?. solve_empty. reflexivity.
  unfold black in H2. simplify. simplify. rewrite <- v_discovered_iff_not_remain.
  apply H3. apply H. apply H1. rewrite <- v_finished_iff_not_remain. simplify.
  apply H. apply H1.
Qed.

(*The other side of the corollary: If v is a descendant of u in the DFS forest,
  du < dv < fv < fv*)
Lemma desc_implies_time_interval: forall s g o u v du dv fu fv,
  valid_dfs_state s g o ->
  u <> v ->
  done s = true ->
  F.desc (get_forest s) u v ->
  M.find u (get_d_times s) = Some du ->
  M.find u (get_f_times s) = Some fu ->
  M.find v (get_d_times s) = Some dv ->
  M.find v (get_f_times s) = Some fv ->
  (du < dv) /\ (dv < fv) /\ (fv < fu). 
Proof.
  intros. generalize dependent du. generalize dependent fu. generalize dependent dv. generalize dependent fv.
  remember (get_forest s) as f. induction H2; subst; intros; subst.
  - eapply parent_implies_time_interval; try(eassumption).
  - assert (u <> p). eapply desc_in_forest_neq. apply H. apply H2. 
    specialize (IHdesc H8).
    assert (white s p = false). eapply no_white_vertices_at_end. apply H. apply H1.
    assert (G.contains_vertex g p = true). rewrite same_vertices. apply F.is_child_1 in H3.
    destruct H3. apply H3. apply H. apply H1. pose proof (all_times_when_done _ _ _ _ H H1 H10).
    destruct_all. edestruct IHdesc. reflexivity. apply H12. apply H11. apply H4. apply H7.
    assert (p <> v). eapply desc_in_forest_neq. apply H. apply F.parent. apply H3. 
    pose proof (parent_implies_time_interval _ _ _ _ _ _ _ _ _ H H15 H3 H11 H12 H5 H6). omega.
Qed.

(*The second major theorem of DFS: Corollary 22.8 in CLRS: v is a descendant of u in the DFS forest
  iff du < dv < fv < fu*)
Theorem desc_iff_time_interval: forall s g o u v du dv fu fv,
  valid_dfs_state s g o ->
  done s = true ->
  M.find u (get_d_times s) = Some du ->
  M.find u (get_f_times s) = Some fu ->
  M.find v (get_d_times s) = Some dv ->
  M.find v (get_f_times s) = Some fv ->
  F.desc (get_forest s) u v <->(du < dv) /\ (dv < fv) /\ (fv < fu). 
Proof.
  intros. split; intros.
  - eapply desc_implies_time_interval; try(eassumption). eapply desc_in_forest_neq in H5. apply H5. apply H.
  - eapply time_interval_implies_descendant; try(eassumption). intro. subst. rewrite H2 in H4. inversion H4; omega.
Qed.

(** ** Lemmas for White Path Theorem **)

(*[add_to_stack] only adds neighbors in the original graph*)
Lemma add_to_stack_neighbors: forall v g r u p,
  In (u, Some p) (add_to_stack v g r) ->
  G.contains_edge g p u = true.
Proof.
  intros. assert (p = v). eapply add_to_stack_adds_parent in H. inversion H; subst. reflexivity.
  subst. unfold add_to_stack in H.
  assert (forall s x y, In (x, y) (fold_right
            (fun (v0 : S.elt) (t : list (S.elt * option O.t)) =>
             if S.mem v0 (S.remove v r) then (v0, Some v) :: t else t) nil s) -> In x s).
  { intros. induction s. simpl in H0. destruct H0. simpl in H0.
    destruct (S.mem a (S.remove v r)) eqn : ?.
    simpl in H0. destruct H0. inversion H0; subst. left. reflexivity.
    right. apply IHs. apply H0. right. apply IHs. apply H0. }
    destruct (G.neighbors_set g v) eqn : ?.
    - assert (In u (S.elements t)). eapply H0. apply H. clear H. clear H0.
      rewrite In_InA_equiv in H1. apply S.elements_2 in H1.
      rewrite G.neighbors_set_2. apply H1. apply Heqo.
    - inversion H.
Qed.

Definition get_graph (s: state) :=
  match s with
  | (g, _, _, _, _, _, _, _) => g
  end.

Lemma graph_constant: forall s g o,
  valid_dfs_state s g o ->
  get_graph s = g.
Proof.
  intros. induction H.
  - simpl. reflexivity.
  - inversion H0; subst; simpl in *; reflexivity.
Qed.

(*If (u, Some v) is on the stack, then the edge (v, u) exists in the graph*)
Lemma stack_elts_neighbors: forall s g o u v,
  valid_dfs_state s g o ->
  In (u, Some v) (get_stack s) ->
  G.contains_edge g v u = true.
Proof.
  intros. induction H; subst; simpl in *.
  - destruct o. destruct (G.contains_vertex g v0). inversion H0. inversion H. inversion H. inversion H0.
    inversion H0.
  - inversion H1; assert (A: g0 = g) by ((replace g0 with (get_graph s1) by (subst; reflexivity)); apply (graph_constant _ _ _ H));
    subst; simpl in *.
    + assert (tl = nil). eapply root_nil. eapply step. apply H. apply H1. reflexivity. subst.
      apply in_app_or in H0. destruct H0. eapply add_to_stack_neighbors.  apply H0. destruct H0; inversion H0.
    + destruct (pop_stack st remain_f) eqn : ?; simpl in H3.
      * destruct (S.min_elt remain_d); inversion H3.
      * rewrite <- H3 in Heqs. clear H3. apply in_app_or in H0. destruct H0. eapply add_to_stack_neighbors.
        apply H0. apply IHvalid_dfs_state. eapply in_pop_rev. rewrite Heqs. apply H0.
    + destruct ((pop_stack st remain_f)) eqn : ?; simpl in H4.
      * destruct (S.min_elt remain_d); inversion H4; subst. inversion H0.
      * rewrite <- H4 in Heqs. clear H4. apply IHvalid_dfs_state. eapply in_pop_rev. rewrite Heqs. solve_in.
Qed.  

(*Every edge in the DFS forest is also in the original graph*)
Lemma edges_in_forest_in_graph: forall s g o u v,
  valid_dfs_state s g o ->
  F.is_child (get_forest s) u v = true ->
  G.contains_edge g u v = true.
Proof.
  intros. induction H; subst; simpl in *.
  - pose proof F.empty_1. pose proof F.empty_2. rewrite H1 in H. apply F.is_child_1 in H0. destruct_all.
     rewrite H in H0. inversion H0.
  - inversion H1; subst; simpl in *.
    + rewrite <- F.add_root_5 in H0. apply IHvalid_dfs_state. apply H0.
    + apply F.add_child_9 in H0. destruct H0. apply IHvalid_dfs_state. apply H0.
      destruct_all; subst. destruct (pop_stack st remain_f) eqn : ?; simpl in H3.
      destruct (S.min_elt remain_d); inversion H3. rewrite <- H3 in Heqs; clear H3.
      eapply stack_elts_neighbors. apply H. simpl. eapply in_pop_rev. rewrite Heqs. left. reflexivity.
    + apply IHvalid_dfs_state. apply H0.
Qed.

(*If there is a path from one vertex to another in the DFS forest, then that same path exists
  in the graph*)
Lemma desc_implies_path: forall s g o u v l,
  valid_dfs_state s g o ->
  F.desc_list (get_forest s) u v l = true ->
  Pa.path_list_rev g u v l = true.
Proof.
  intros. generalize dependent v. induction l; intros.
  - simpl in *. eapply edges_in_forest_in_graph. apply H. apply H0.
  - simpl in *. simplify. eapply edges_in_forest_in_graph. apply H. apply H1. 
Qed. 

(*Every descendant of u is white when u is discovered*)
Lemma descendants_white_at_time_du: forall s g o u v x,
  valid_dfs_state s g o ->
  done s = true ->
  F.desc (get_forest s) u v ->
  valid_dfs_state x g o ->
  M.find u (get_d_times x) = Some (get_time x) ->
  white x v = true.
Proof.
  intros. pose proof (F.desc_in_forest _ _ _ H1). destruct_all.  rewrite <- (same_vertices _ _ _ _ H H0) in H5.
  rewrite <- (same_vertices _ _ _ _ H H0) in H4. pose proof (all_times_when_done s g o u H H0 H4).
  destruct_all. pose proof (all_times_when_done s g o v H H0 H5). destruct_all.
  assert (dfs_multi x s). assert (A:= H). assert (B:= H2). apply valid_begins_with_start in H.
  apply valid_begins_with_start in H2. pose proof (multi_from_start _ _ _ H H2). destruct H10.
  apply H10. inversion H10. subst. apply multi_refl. subst. eapply done_cannot_step in H0.
  exfalso. apply H0. exists y. apply H11. apply A.
  assert (A:=H3). eapply discovery_time_constant in H3. rewrite H3 in H6. inversion H6; subst.
  pose proof (desc_iff_time_interval
  s g o u v (get_time x) x3 x0 x2 H H0 H3 H7 H8 H9). destruct H11. apply H11 in H1.
  destruct (white x v) eqn : ?. reflexivity. unfold white in *.
  assert (S.mem v(get_remain_d x) = false). simplify. pose proof (not_f_if_not_d
  x g o v H2). apply contrapositive in H17. destruct (S.mem v (get_remain_d x)).
  contradiction. reflexivity. rewrite H14. intro. inversion H19.
  rewrite v_discovered_iff_not_remain in H13. destruct_all. 
  assert (B:= H13). eapply d_times_leq_current_time in H13.
  eapply discovery_time_constant in B. rewrite B in H8. inversion H8; subst. omega.
  apply H2. apply H10. apply H2. apply H2. apply H5. apply H2. apply H10.
Qed.

(*The first half of the white path theorem: If v is a descendant of u when DFS finishes, then at time du,
  there is a path in the original graph from u to v such that all vertices (except for u) are white*)
Lemma desc_implies_white_path: forall s g o u v x,
  valid_dfs_state s g o ->
  done s = true ->
  F.desc (get_forest s) u v ->
  valid_dfs_state x g o ->
  M.find u (get_d_times x) = Some (get_time x) ->
  (exists l, Pa.path_list_rev g u v l = true /\ (forall y, In y l -> white x y = true) /\ white x v = true).
Proof.
  intros. assert (A:=H1). rewrite <- F.desc_list_iff_desc in H1. destruct_all. exists x0.
  split. eapply desc_implies_path. apply H. apply H1. split. intros.
  eapply F.desc_list_all_desc in H1. eapply descendants_white_at_time_du. apply H.
  apply H0. apply H1. apply H2. apply H3. apply H4. eapply descendants_white_at_time_du.
  apply H. apply H0. apply A. apply H2. apply H3.
Qed. 

(* We want to prove that if the edge (p, u) is in the graph and if u is white at time dp, then u is a 
  descendant of p. We will do this in the following steps:
1. Prove that if (u, Some p) is on the stack, then it is on the stack when u is discovered
2. Therefore, p is gray when u is discovered
3. Therefore, u is a descendant of p
4. Thus, at time dp, (p, u) will be included in the add_to_stack portion (because u is white), 
  so (u, Some p) is on the stack, so u is a descendant of p *)

(*Alternative DFS multi that takes the step last. This helps ensure that the discovery time in the next
  proof does not change when we do induction*)
Inductive dfs_multi': state -> state -> Prop :=
  | multi_refl' : forall s, dfs_multi' s s
  | multi_step': forall s1 s2 s3,
    dfs_multi' s1 s2 ->
    dfs_step s2 s3 ->
    dfs_multi' s1 s3.

Lemma dfs_multi'_trans: forall s1 s2 s3,
  dfs_multi' s1 s2 ->
  dfs_multi' s2 s3 ->
  dfs_multi' s1 s3.
Proof.
  intros. induction H0.
  - apply H.
  - eapply multi_step'. apply IHdfs_multi'. apply H. apply H1.
Qed.

Lemma dfs_multi'_R: forall s1 s2,
  dfs_step s1 s2 ->
  dfs_multi' s1 s2.
Proof.
  intros. eapply multi_step'. apply multi_refl'. apply H.
Qed.

(*Equivalence with original definition*)
Lemma dfs_multi_equiv: forall s s',
  dfs_multi s s' <-> dfs_multi' s s'.
Proof.
  intros. split; intro H; induction H.
  - constructor.
  - eapply dfs_multi'_trans. apply dfs_multi'_R. apply H. apply IHmulti.
  - constructor.
  - eapply multi_trans. apply IHdfs_multi'. apply multi_R. apply H0.
Qed. 

Lemma list_app_neq: forall (A: Type) (l l1: list A),
  l1 <> nil ->
  l <> l1 ++ l.
Proof.
  intros. generalize dependent l1. induction l; intros; simpl in *.
  - destruct l1. contradiction. intro. inversion H0.
  - intro. destruct l1. contradiction. inversion H0; subst. eapply IHl. 
    assert (l1 ++ (a0:: nil) <> nil). intro. destruct l1; inversion H1. apply H1.
    rewrite H3 at 1. rewrite <- app_assoc. reflexivity.
Qed.

(*Part 1: If (u, Some p) is on the stack, then it is on the stack at time du*)
Lemma on_stack_discover: forall s g o u p x,
  valid_dfs_state s g o ->
  In (u, Some p) (get_stack s) ->
  valid_dfs_state x g o ->
  M.find u (get_d_times x) = Some (get_time x) ->
  In (u, Some p) (get_stack x).
Proof.
  intros. assert (A:= H). assert (B:=H1). apply valid_begins_with_start in A. apply valid_begins_with_start in B.
  pose proof (multi_from_start _ _ _ A B). destruct H3. clear A. clear B. rewrite dfs_multi_equiv in H3.
  assert (M: M.find u (get_d_times s) = Some (get_time x)). eapply discovery_time_constant. apply H1. apply H2.
  rewrite dfs_multi_equiv. apply H3.
  induction H3.
  - apply H0.
  - assert (valid_dfs_state s2 g o). eapply multistep_preserves_valid. apply H1. rewrite dfs_multi_equiv.
    apply H3. specialize (IHdfs_multi' H5). inversion H4; subst; simpl in *.
    + assert (tl = nil). eapply root_nil. eapply step. apply H5. apply H4. reflexivity. subst.
      apply in_app_or in H0. destruct H0.
      * assert (A:=H0). apply add_to_stack_neq in H0. rewrite F.add_neq_o in M.
        apply only_add_yet_to_be_discovered in A. remember (g0, f, f_times, d_times, time, remain_d, remain_f, st) as s.
        assert (S.mem u (get_remain_d s) = false). rewrite v_discovered_iff_not_remain. exists (get_time s1).
        subst; simpl; apply M. apply H5. eapply discovered_vertices_in_graph. apply H5. subst; simpl; apply M.
        subst; simpl in *. rewrite H8 in A. inversion A. auto.
      * destruct H0; inversion H0.
    + destruct (O.eq_dec u x).
      * unfold O.eq in e. subst. rewrite F.add_eq_o in M. inversion M; subst.
        rewrite <- dfs_multi_equiv in H3. apply time_incr_multi in H3. simpl in *. destruct H3.
        subst; simpl in *. omega. omega. reflexivity.
      * rewrite F.add_neq_o in M. destruct (pop_stack st remain_f) eqn : ?; simpl in H7.
        destruct (S.min_elt remain_d); inversion H7. rewrite <- H7 in Heqs; clear H7.
        remember (g0, f, f_times, d_times, time, remain_d, remain_f, st)  as s'.
        assert (S.mem u (get_remain_d s') = false). rewrite v_discovered_iff_not_remain.
        exists (get_time s1). subst; simpl; assumption. apply H5. 
        eapply discovered_vertices_in_graph. apply H5. subst; simpl; apply M.
        subst; simpl in *. apply in_app_or in H0. destruct H0.
        apply only_add_yet_to_be_discovered in H0. rewrite H0 in H7. inversion H7.
        apply IHdfs_multi'. eapply in_pop_rev. rewrite Heqs. apply H0. apply H1. apply H2. auto. auto.
    + destruct (pop_stack st remain_f) eqn : ?; simpl in H8. destruct (S.min_elt remain_d); inversion H8; subst.
      inversion H0. rewrite <- H8 in Heqs; clear H8. apply IHdfs_multi'. eapply in_pop_rev. rewrite Heqs. right. apply H0.
      apply H1. apply H2. auto.
  - clear A. clear B. induction H3; subst; simpl in *.
    + apply H0.
    + assert (S.mem u (get_remain_d x) = true). destruct (S.mem u (get_remain_d x)) eqn : ?. reflexivity.
       rewrite v_discovered_iff_not_remain in Heqb. destruct_all. assert (A:=H5). eapply d_times_leq_current_time in H5.
      eapply discovery_time_constant in A. rewrite A in H2. inversion H2; subst.
      apply time_incr_step in H3. apply time_incr_multi in H4. destruct H4. subst. omega. omega.
      apply H. eapply multi_step. apply H3. apply H4. apply H. apply H. 
      eapply stack_valid. apply H. apply H0.
      assert (S.mem u (get_remain_f x) = true) by (eapply not_f_if_not_d; eassumption).
      assert (valid_dfs_state y g o). eapply step. apply H. apply H3.
      specialize (IHmulti H7). inversion H3; subst; simpl in *.
      * assert (tl = nil). eapply root_nil. eapply step. apply H. apply H3. reflexivity. subst.
        destruct (pop_stack st remain_f) eqn : ?; simpl in H9. destruct (S.min_elt remain_d) eqn : ?.
        inversion H9; subst. rewrite pop_stack_nil in Heqs. specialize (Heqs (u, Some p)). simpl in Heqs.
        rewrite Heqs in H6. inversion H6. apply H0. inversion H9. 
        rewrite <- H9 in Heqs. 
        pose proof (pop_stack_app st remain_f). destruct_all; subst. apply in_app_or in H0. destruct H0.
        rewrite H11 in Heqs. subst. rewrite pop_stack_app_distr in H11. assert (pop_stack x remain_f = nil).
        destruct (pop_stack x remain_f) eqn : ?. reflexivity. inversion H11. destruct s0; inversion H13.
        rewrite pop_stack_nil in H10. specialize (H10 (u, Some p)). simpl in H10. rewrite H10 in H6.
        inversion H6. apply H0. remember (g0, f, f_times, d_times, time, remain_d, remain_f, x ++ (x0, None) :: nil) as s'.
        replace remain_f with (get_remain_f s') by (subst; reflexivity).
        eapply not_f_if_not_d. subst. apply H. subst; simpl; assumption. rewrite H11 in Heqs. subst.
        destruct H0; inversion H0.
      * destruct ((pop_stack st remain_f)) eqn : ?; simpl in H9.
        -- destruct (S.min_elt remain_d) eqn : ?; inversion H9.
        -- rewrite <- H9 in Heqs. pose proof (pop_stack_app st remain_f). destruct_all; subst.
           rewrite H11 in Heqs; subst. rewrite pop_stack_app_distr in H11.
           assert (pop_stack x remain_f = nil). destruct (pop_stack x remain_f) eqn : ?. reflexivity.
           pose proof (list_app_neq _ ((x0, Some y0) :: tl)(p1 :: s0)). rewrite <- H11 in H10 at 1.
          assert ( (p1 :: s0) ++ (x0, Some y0) :: tl <> (p1 :: s0) ++ (x0, Some y0) :: tl).
          apply H10. intro. inversion H12. contradiction. rewrite pop_stack_nil in H10.
          specialize (H10 (u, Some p)). simpl in H10. apply in_app_or in H0. destruct H0.
          rewrite H10 in H6. inversion H6. apply H0. apply IHmulti. solve_in. apply H1. apply H2.
          remember (g0, f, f_times, d_times, time, remain_d, remain_f, x ++ (x0, Some y0) :: tl) as s'.
          replace remain_f with (get_remain_f s') by (subst; reflexivity). eapply not_f_if_not_d. subst.
          apply H. subst; simpl; assumption.
      * destruct ((pop_stack st remain_f)) eqn : ?; simpl in H10.
        -- rewrite pop_stack_nil in Heqs. specialize (Heqs (u, Some p)). rewrite Heqs in H6. inversion H6.
            apply H0.
        -- rewrite <- H10 in Heqs. clear H10. pose proof (pop_stack_app st remain_f). destruct_all; subst.
           rewrite H11 in Heqs; subst. rewrite pop_stack_app_distr in H11.
           assert (pop_stack x remain_f = nil). destruct (pop_stack x remain_f) eqn : ?. reflexivity.
           pose proof (list_app_neq _ ((x0, o0) :: tl)(p1 :: s0)). rewrite <- H11 in H10 at 1.
          assert ( (p1 :: s0) ++ (x0, o0) :: tl <> (p1 :: s0) ++ (x0, o0) :: tl).
          apply H10. intro. inversion H12. contradiction. rewrite pop_stack_nil in H10.
          specialize (H10 (u, Some p)). simpl in H10. apply in_app_or in H0. destruct H0.
          rewrite H10 in H6. inversion H6. apply H0. simpl in H0. destruct H0. inversion H0; subst.
          rewrite H8 in H5. inversion H5. apply IHmulti. solve_in. apply H1. apply H2. apply H9.
Qed.
 
(*Part 2: if (u, Some p) is on the stack, then p is gray when u is discovered*)
Lemma on_stack_parent_gray_when_discovered: forall s g o u p x,
  valid_dfs_state s g o ->
  In (u, Some p) (get_stack s) ->
  valid_dfs_state x g o ->
  M.find u (get_d_times x) = Some (get_time x) ->
  gray x p = true.
Proof.
  intros. eapply parent_on_stack_is_gray. apply H1. eapply on_stack_discover. apply H. apply H0. apply H1.
  apply H2.
Qed.

(*Part 3: If (u, Some p) is on the stack at any point, then u is a descendant of p when we are done*)
Lemma on_stack_descendant: forall s s' g o u p,
  valid_dfs_state s g o ->
  done s = true ->
  valid_dfs_state s' g o ->
  In (u, Some p) (get_stack s') ->
  F.desc (get_forest s) p u.
Proof.
  intros. assert (G.contains_vertex g u = true). eapply stack_valid. apply H1. apply H2.
  pose proof (all_times_when_done s g o u H H0 H3). destruct_all.
  pose proof (discovery_time_means_discovered s g o u x0 H H4). destruct_all; subst.
  assert (gray x1 p = true). eapply on_stack_parent_gray_when_discovered. apply H1.
  apply H2. apply H8. apply H9. assert (G.contains_vertex g p = true). eapply parents_valid.
  apply H1. apply H2.
  pose proof (all_times_when_done s g o p H H0 H10). destruct_all.
  assert (A:=H7). unfold gray in H7. simplify. 
  rewrite v_discovered_iff_not_remain in H13. destruct_all. 
  assert (x3 = x2). eapply discovery_time_constant in H7. rewrite H7 in H11. inversion H11; subst.
  reflexivity. apply H8. apply H6. subst. 
  assert (x2 < (get_time x1)). eapply d_times_leq_current_time in H7. 
  assert (x2 = get_time x1 \/ x2 < get_time x1) by omega. destruct H13. subst.
  pose proof (d_times_unique _ _ _ _ _ _ _ H H4 H11). assert (p = u). apply H13. reflexivity.
  subst. exfalso. eapply neq_parent. apply H1. apply H2. reflexivity. apply H13. apply H8.
  pose proof (finish_time_means_finished s g o p x0 H H12). destruct_all.
  assert (dfs_multi x1 x3). { assert (B:= H8). assert (C:= H17). apply valid_begins_with_start in H8.
  apply valid_begins_with_start in H17. pose proof (multi_from_start _ _ _ H8 H17). destruct H19.
  unfold gray in *. simplify. assert (M.find p (get_f_times x1) = None). pose proof (v_finished_iff_not_remain
  _ _ _ _ B H10). destruct H22. apply contrapositive in H23. destruct (M.find p (get_f_times x1) ) eqn : ?.
  exfalso. apply H23. exists n. reflexivity. reflexivity. rewrite H21. intro. inversion H24.
  eapply finish_time_constant in H18. rewrite H18 in H22. inversion H22. apply C. apply H19. apply H19. }
  assert (B:= H19). apply time_incr_multi in H19. destruct H19. subst.
  exfalso. eapply all_times_unique. apply H. apply H4. apply H12. 
  assert (p <> u). intro. subst. eapply neq_parent. apply H1. apply H2. reflexivity.
  subst. pose proof (times_ordering _ _ _ _ _ _ _ _ _ H H20 H11 H4 H12 H5). 
  assert (get_time x1 < x /\ x < get_time x3). apply H16. omega.
  eapply time_interval_implies_descendant. apply H. apply H20. apply H11. apply H12. apply H4. apply H5.
  omega. apply H8. apply H10.
Qed.

(*Part 4: If (p, u) is in the graph and u is white at time dp, then u is a descendant of p in the forest*)

(*If u is white and (v, u) is in the graph, then (u, Some v) is added to the stack*)
Lemma white_neighbors_added: forall v g r u,
  G.contains_edge g v u = true ->
  u <> v ->
  S.mem u r = true ->
  In (u, Some v) (add_to_stack v g r).
Proof.
  intros. unfold add_to_stack. destruct (G.neighbors_set g v) eqn : ?.
  remember ((fold_right
     (fun (v0 : S.elt) (t0 : list (S.elt * option O.t)) =>
      if S.mem v0 (S.remove v r) then (v0, Some v) :: t0 else t0) nil)) as f.
  assert (forall l x, In x l -> x <> v  -> S.mem x r = true -> In (x, Some v) (f l)). { intros. induction l.
  - inversion H2.
  - subst. simpl in *. destruct (S.mem a (S.remove v r)) eqn : ?.
    + destruct H2. subst. left. reflexivity. right. apply IHl. apply H2.
    + destruct H2. subst. rewrite P2.FM.remove_neq_b in Heqb. rewrite Heqb in H4. inversion H4.
      auto. apply IHl. apply H2. }
  subst. apply H2. rewrite In_InA_equiv. rewrite <- P2.Dec.F.elements_iff. rewrite <- G.neighbors_set_2.
    apply H. apply Heqo. apply H0. apply H1.
    rewrite G.neighbors_set_1 in Heqo. rewrite <- G.neighbors_list_1 in Heqo.
    apply G.contains_edge_1 in H. rewrite Heqo in H. inversion H.
Qed.

(*If u is white at time dp and if (p, u) is in the graph, then u is a descendant of p in the DFS forest*)
Lemma white_neighbor_is_desc: forall s g o u p x,
  valid_dfs_state x g o ->
  valid_dfs_state s g o ->
  done s = true ->
  M.find p (get_d_times x) = Some (get_time x) ->
  G.contains_edge g p u = true ->
  white x u = true ->
  F.desc (get_forest s) p u.
Proof.
  intros. unfold white in *. induction H; subst; simpl in *.
  - rewrite P.F.empty_o in H2. inversion H2.
  - inversion H5; assert (g = g0) by ((assert (A: get_graph s1 = g0) by (subst; reflexivity)); rewrite <- A;
    symmetry; apply (graph_constant _ _ _ H)); subst; simpl in *.
    + destruct (O.eq_dec p x).
      * unfold O.eq in e. subst. assert (u <> x). intro. subst. simplify. rewrite remove_eq_false in H8.
        inversion H8. eapply on_stack_descendant. apply H0. apply H1. eapply step. apply H.
        apply H5. simpl. apply in_or_app. left. eapply white_neighbors_added. apply H3. apply H8.
        simplify. rewrite P2.FM.remove_neq_b in H9. apply H9. auto.
      * rewrite F.add_neq_o in H2. remember (g0, f, f_times, d_times, time, remain_d, remain_f, st) as s'.
        replace (d_times) with (get_d_times s') in H2 by (subst; reflexivity) . eapply d_times_leq_current_time in H2.
        subst; simpl in *. omega. apply H. auto.
    + destruct (O.eq_dec p x).
      * unfold O.eq in e. subst. assert (u <> x). intro. subst. simplify. rewrite remove_eq_false in H8.
        inversion H8. eapply on_stack_descendant. apply H0. apply H1. eapply step. apply H.
        apply H5. simpl. apply in_or_app. left. eapply white_neighbors_added. apply H3. apply H8.
        simplify. rewrite P2.FM.remove_neq_b in H9. apply H9. auto.
      * rewrite F.add_neq_o in H2. remember (g0, f, f_times, d_times, time, remain_d, remain_f, st) as s'.
        replace (d_times) with (get_d_times s') in H2 by (subst; reflexivity) . eapply d_times_leq_current_time in H2.
        subst; simpl in *. omega. apply H. auto.
    + remember (g0, f, f_times, d_times, time, remain_d, remain_f, st) as s'.
      replace (d_times) with (get_d_times s') in H2 by (subst; reflexivity) . 
      eapply d_times_leq_current_time in H2. subst; simpl in *. omega. apply H.
Qed. 

(*sketch of proof - we know that w is desc of u. If v already discovered at time dw, then v is desc of u
      because u has not finished yet and it was white at time du. If not already discovered, follows by induction*)

(*The other side of the white path theorem: If there is a white path from u to v at time du, then v is a 
  descendant of u in the DFS forest
Proof sketch: If the path is empty, then it follows immediately from the previous lemma. If not, then
  we have that w is a descendant of u and (w, v) exists in g. Then, at time dw, if v is white, then
  the claim again follows from the previous lemma (since v is a desc of w and w is a desc of u. Otherwise
  if v is not white at time dw, then since v is white at time du, du < dv. Since w is a descendant, by
  Corollary 22.8, we have that du < dw < fw < fu. So since v is not white at time du, we know that
  du < dw < dv < fu. By the parenthesees theoren, du < dv < fv < fu, and by Corollary 22.8, v is
  a descendant of u*)
Lemma white_path_implies_desc: forall s g o u v x l,
  valid_dfs_state s g o ->
  valid_dfs_state x g o ->
  done s = true ->
  M.find u (get_d_times x) = Some (get_time x) ->
  Pa.path_list_ind g u v (fun a => white x a) l ->
  F.desc (get_forest s) u v.
Proof.
  intros. remember (fun a : G.vertex => white x a) as f. induction H3; subst.
  - eapply white_neighbor_is_desc. apply H0. apply H. apply H1. apply H2. apply H3. apply H4.
  - assert (G.contains_vertex g w = true). eapply G.contains_edge_1. apply H5.
    pose proof (all_times_when_done _ _ _ _ H H1 H6). destruct_all;simplify.
    pose proof (discovery_time_means_discovered _ _ _ _ _ H H7). destruct_all; subst.
    destruct (white x2 v) eqn : ?.
    + eapply F.is_descendant_trans. apply H10. eapply white_neighbor_is_desc. apply H12.
      apply H. apply H1. apply H13. apply H5. apply Heqb.
    + assert (G.contains_vertex g u = true). eapply discovered_vertices_in_graph. apply H0.
      apply H2. pose proof (all_times_when_done _ _ _ _ H H1 H11). destruct_all.
      assert (dfs_multi x s). { assert (A:= H). assert (B:= H0). apply valid_begins_with_start in H0.
      apply valid_begins_with_start in H. pose proof (multi_from_start _ _ _ H H0). destruct H16. apply H16.
      inversion H16. subst. apply multi_refl. subst. pose proof (done_cannot_step _ _ _ A H1). 
      exfalso. apply H19. exists y. apply H17. } assert (B:= H2). eapply discovery_time_constant in H2. 
      rewrite H2 in H14. inversion H14; subst. 
      assert (G.contains_vertex g v = true). eapply G.contains_edge_2. apply H5.
      pose proof (all_times_when_done _ _ _ _ H H1 H17). destruct_all.
      assert (A:= H10). pose proof (desc_iff_time_interval _ _ _ _ _ _ _ _ _ H H1 H2 H15 H7 H8).
      rewrite H20 in A. clear H20. 
      pose proof (discovery_time_means_discovered _ _ _ _ _ H H18). destruct_all; subst.
      assert (dfs_multi x x5). { assert (A:= H0). assert (C:= H22). eapply valid_begins_with_start in H0.
      eapply valid_begins_with_start in H22. pose proof (multi_from_start _ _ _ H22 H0). destruct H21.
      apply H21. assert (M.find v (get_d_times x) = Some (get_time x5)). eapply discovery_time_constant.
      apply C. apply H23. apply H21. unfold white in *.
      assert (S.mem v (get_remain_d x) = true). simplify. pose proof (v_discovered_iff_not_remain
      _ _ _ _ A H17). destruct H29. apply contrapositive in H30. exfalso. apply H30.
      exists (get_time x5). apply H27. rewrite H28. intro. inversion H31. }
      apply time_incr_multi in H21. destruct H21. subst. 
      pose proof (d_times_unique _ _ _ _ _ _ _ H H18 H2). assert (u = v). apply H21. reflexivity.
      subst. assert (S.mem v (get_remain_d x5) = false). rewrite v_discovered_iff_not_remain.
      exists (get_time x5). assumption. apply H22. assumption. unfold white in *. rewrite H27 in H4.
      simpl in H4. inversion H4. 
      assert (dfs_multi x5 x2). { assert (E:= H20). assert (F:= H12). apply valid_begins_with_start in H22.
      apply valid_begins_with_start in H12. pose proof (multi_from_start _ _ _ H22 H12). destruct H27.
      unfold white in Heqb. assert (S.mem v (get_remain_d x2) = false). simplify. 
      epose proof (not_f_if_not_d _ _ _ _ F). apply contrapositive in H29. destruct (S.mem v (get_remain_d x2) ) eqn : ?.
      rewrite Heqb in H29. contradiction. reflexivity. rewrite H28. intro. inversion H30.
      rewrite v_discovered_iff_not_remain in H28. destruct_all. 
      assert (C:=H28). eapply discovery_time_constant in H28. rewrite H28 in H23. inversion H23; subst.
      eapply d_times_leq_current_time in C. apply time_incr_multi in H27. destruct H27. subst. apply multi_refl.
      omega. apply F. apply F. apply H27. apply F. assumption. apply H27. } apply time_incr_multi in H27.
      destruct H27. subst. pose proof (d_times_unique _ _ _ _ _ _ _ H H7 H18). assert (v = w).
      apply H27. reflexivity. subst. assumption. assert (u <> v). intro. subst.
      assert (exists n, M.find v (get_d_times x) = Some n). exists (get_time x). apply B.
      rewrite <- v_discovered_iff_not_remain in H28. unfold white in *. rewrite H28 in H4. inversion H4.
      apply H0. assumption. 
      pose proof (times_ordering _ _ _ _ _ _ _ _ _ H H28 H2 H18 H15 H19). 
      assert (get_time x < get_time x5 /\ get_time x5 < x1) by omega. apply H29 in H30; clear H29.
      pose proof (desc_iff_time_interval _ _ _ _ _ _ _ _ _ H H1 H2  H15 H18 H19). rewrite H29. omega. apply H0. apply H16.
Qed.

(** The White Path Theorem: for any two vertices u and v, u is a descendant of v in the DFS forest
    iff there exists a path of vertices from u to v such that at time du, all the vertices on the path except
    u are colored white. **)
Theorem white_path_theorem: forall s g o u v x,
  valid_dfs_state s g o ->
  valid_dfs_state x g o ->
  done s = true ->
  M.find u (get_d_times x) = Some (get_time x) ->
  (exists l, Pa.path_list_ind g u v (fun a => white x a) l) <->
  F.desc (get_forest s) u v.
Proof.
  intros. split; intros. destruct_all. eapply white_path_implies_desc; try(eassumption).
  setoid_rewrite Pa.path_list_ind_rev.  pose proof desc_implies_white_path.
  specialize (H4 _ _ _ _ _ _ H H1 H3 H0 H2). apply H4.
Qed. 

End DFS.