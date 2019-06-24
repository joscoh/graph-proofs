Require Import Graph.
Require Import Tree.
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
            (T: Tree O St S G).

Module P := FMapFacts.WProperties_fun O M.
Module F := P.F.
Module P2 := FSetProperties.WProperties_fun O S.
Module O2 := OrderedTypeFacts O.

(*First, we define the types we will need*)
Definition vertex := O.t.
Definition graph := G.graph.
Definition tree := T.tree.
Definition forest := list tree.
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
    (g, (T.singleton x) :: f, f_times, (M.add x (time + 1) d_times), (time + 1), (S.remove x remain_d), 
    remain_f, (add_to_stack x g remain_d) ++  ((x, None) :: tl))
    (*Discover a vertex: add all of its neighbors who have not been discovered to the stack,
      add it to the stack, add it to the discover times with the current time, and remove it from
      remain_d. We also add it to the forest as a new singleton tree*)
  | dfs_discover_child : forall g t f f_times d_times time remain_d remain_f st x y tl,
    S.mem x remain_d = true ->
    (x, Some y) :: tl = start_new (pop_stack st remain_f) remain_d ->
    dfs_step (g, t :: f, f_times, d_times, time, remain_d, remain_f, st)
    (g, (T.add_child t y x) :: f, f_times, (M.add x (time + 1) d_times), (time + 1), (S.remove x remain_d), 
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
    + rewrite <- H14 in H2. inversion H2; subst. reflexivity.
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
  (g, nil, M.empty nat, M.empty nat, 0, (G.set_of_graph g), (G.set_of_graph g), init_stack).

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

(*Set Inequality*)
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
    + remember (g0, t :: f, f_times, d_times, time, remain_d, remain_f, st) as s.
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

Lemma nempty_stack_forest: forall s g o x y,
  valid_dfs_state s g o ->
  In (x, Some y) (get_stack s) ->
  get_forest s <> nil.
Proof.
  intros. induction H; subst; simpl in *.
  - destruct o. destruct (G.contains_vertex g v). inversion H0. inversion H. inversion H. inversion H0.
    inversion H0.
  - inversion H1; subst; simpl in *; intro A; inversion A.
    destruct (pop_stack st remain_f) eqn : ?.
    simpl in H4. destruct (S.min_elt remain_d) eqn : ?.
    + inversion H4; subst. inversion H0.
    + inversion H4.
    + simpl in H4. inversion H4; subst. apply IHvalid_dfs_state.
      eapply in_pop_rev. rewrite Heqs. right. apply H0. reflexivity.
Qed.


Definition next_state (s: state) : state :=
  match s with
  | (g, f, f_times, d_times, time, remain_d, remain_f, st) =>
    match (start_new (pop_stack st remain_f) remain_d) with
    (*Impossibly*)
    | nil => s
    | (x,o) :: tl =>
      if S.mem x remain_d then match o with
      | None => (g, T.singleton x :: f, f_times, M.add x (time + 1) d_times, time + 1,
                 S.remove x remain_d, remain_f, (add_to_stack x g remain_d ++ (x,None) :: tl))
      | Some y => match f with
                   (*Impossible*)
                   | nil => s
                   | t :: fs => (g, T.add_child t y x :: fs, f_times, M.add x (time+1) d_times,
                                 time + 1, S.remove x remain_d, remain_f, (add_to_stack x g remain_d ++
                                  (x, Some y) :: tl))
                    end
      end
      else if S.mem x remain_f then (g, f, M.add x (time + 1) f_times, d_times, time+1, remain_d, 
                                    S.remove x remain_f, tl)
      (*Impossible*)
      else s
    end
  end.


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
    + destruct o0. epose proof (nempty_stack_forest _ _ _ t3 t4 H).
      assert (get_stack st = s) by (subst; reflexivity). rewrite H2 in H1.
      destruct (pop_stack s t) eqn : ?. simpl in Heqs0. destruct (S.min_elt t0); inversion Heqs0. 
      simpl in Heqs0. inversion Heqs0. rewrite H5 in Heqs1. rewrite H4 in Heqs1.
      assert (get_forest st <> nil). apply H1. eapply in_pop_rev. rewrite Heqs1. left. reflexivity.
      * destruct f. 
        -- subst; simpl in *; contradiction.
        -- apply dfs_discover_child. apply Heqb. subst. rewrite Heqs1. simpl. reflexivity.
      * apply dfs_discover_root. apply Heqb. symmetry; assumption.
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

(*Falls out as a simple corollary of the above*)
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

Inductive dfs_multi_alt : state -> state -> Prop :=
  | refl': forall s, dfs_multi_alt s s
  | step': forall s1 s2 s3, dfs_multi_alt s1 s2 -> dfs_step s2 s3 -> dfs_multi_alt s1 s3.

Lemma multi_alt_trans: forall s s' s'',
  dfs_multi_alt s s' ->
  dfs_multi_alt s' s'' ->
  dfs_multi_alt s s''.
Proof.
  intros. induction H0.
  - assumption.
  - eapply step'. apply IHdfs_multi_alt. apply H. apply H1.
Qed. 

Lemma multi_equiv: forall s s',
  dfs_multi s s' <-> dfs_multi_alt s s'.
Proof.
  intros. split; intros; induction H.
  - apply refl'.
  - eapply multi_alt_trans. eapply step'. apply refl'. apply H. apply IHmulti.
  - apply multi_refl.
  - eapply multi_trans. apply IHdfs_multi_alt. apply multi_R. apply H0.
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

Lemma list_cons_neq: forall (A: Type) (x: A) l,
  l <> x :: l.
Proof.
  intros. induction l. intro. inversion H.
  intro. inversion H. contradiction.
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

Lemma pop_no_app: forall l l1 r,
  l1 <> nil ->
  pop_stack l r <> l1 ++ l.
Proof.
  intros. generalize dependent l1. induction l; intros; simpl in *.
  + destruct l1. contradiction. intro. inversion H0.
  + destruct a. destruct (S.mem t r); simpl in *.
    - intro. destruct l1. contradiction.
      inversion H0; subst. eapply list_app_neq.
      assert (l1 ++ (t,o):: nil <> nil). intro. destruct l1; inversion H1.
      apply H1. rewrite <- app_assoc. apply H3.
    - intro. assert (l1 ++ (t,o) :: l = l1 ++ (t,o) :: nil ++ l). simpl. reflexivity.
      rewrite H1 in H0. eapply IHl. 
      assert (l1 ++ (t,o) :: nil <> nil). intro. destruct l1; inversion H2.
      apply H2. rewrite <- app_assoc. apply H0.
Qed.

Lemma pop_no_add: forall x l r,
  pop_stack l r <> x :: l.
Proof.
  intros. assert (x :: l = x :: nil ++ l). simpl. reflexivity. rewrite H.
  intro. eapply pop_no_app. assert (x :: nil <> nil). intro. inversion H1.
  apply H1. simpl. apply H0.
Qed.


Lemma pop_stack_app_distr: forall l1 l2 a b r,
   S.mem a r = true -> pop_stack (l1 ++ (a,b) :: l2) r = (pop_stack l1 r) ++ ((a,b) :: l2).
Proof.
  intros. generalize dependent l2. induction l1; subst; intros.
    + simpl. rewrite H. simpl. reflexivity.
    + simpl in *. destruct a0. destruct (S.mem e r) eqn : ?; simpl. reflexivity.
      apply IHl1.
Qed. 

(*The descedant of a vertex (in terms of the stack). We will prove that it is equivalent
  to being a descendent in the DFS forest*)
Inductive stack_desc: state -> vertex -> vertex -> Prop :=
  | parent: forall x y s, In (x, Some y) (get_stack s) -> stack_desc s x y
  | path: forall x y z s, stack_desc s x y -> In (y, Some z) (get_stack s) -> stack_desc s x z.

Lemma stack_desc_trans: forall x y z s,
  stack_desc s x y ->
  stack_desc s y z ->
  stack_desc s x z.
Proof.
  intros. induction H0.
  - eapply path. apply H. apply H0.
  - eapply path. apply IHstack_desc. apply H. apply H1.
Qed.

Lemma stack_desc_has_child: forall x y s,
  stack_desc s x y -> 
  In (x, Some y) (get_stack s) \/ exists z, stack_desc s x z /\ In (z, Some y) (get_stack s).
Proof.
  intros. induction H.
  - left. apply H.
  - destruct IHstack_desc. right. exists y. split. apply H. apply H0.
    destruct H1. destruct H1. right. exists y. split. apply H. apply H0.
Qed. 

Lemma stack_desc_has_child_rev: forall x y s,
  stack_desc s x y -> 
  In (x, Some y) (get_stack s) \/ exists z,  In (x, Some z) (get_stack s) /\ stack_desc s z y.
Proof.
  intros. induction H.
  - left. apply H.
  - destruct IHstack_desc. right. exists y. split. apply H1. eapply parent. apply H0. 
    destruct H1. destruct H1. right. exists x0. split. apply H1. eapply stack_desc_trans.
    apply H2. apply parent. apply H0.  
Qed. 




(*
Lemma right_left_stacks: forall s g o v,
  valid_dfs_state s g o ->
  exists tl o',
  gray s v = true ->
  (exists l1, get_stack s = l1 ++ (v,o') :: tl /\ (forall o'', ~In (v, o'') l1) /\
  (forall y, ~In (y, Some v) tl) /\ (forall x, stack_desc s x v <-> exists p, In (x,p) l1)).
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
        split. intros. intro. inversion H5. intros; split; intros. apply stack_desc_has_child in H5; simpl in *.
        destruct H5. exists (Some v). apply in_app_or in H5. destruct H5. apply H5. simpl in H5.
        destruct H5; inversion H5. destruct H5. destruct H5. apply stack_desc_has_child in H5; simpl in *.
        destruct H5. apply in_app_or in H5. destruct H5. apply add_to_stack_adds_parent in H5.
        inversion H5; subst. exfalso. eapply neq_parent. eapply step. apply H. apply H0. simpl.
        apply H6. reflexivity. simpl in H5. destruct H5; inversion H5. destruct H5. destruct H5.
        apply in_app_or in H7. destruct H7. apply add_to_stack_adds_parent in H7. inversion H7; subst.
        exfalso. eapply neq_parent. eapply step. apply H. apply H0. simpl. apply H6. reflexivity.
        destruct H7; inversion H7. destruct H5. eapply parent. simpl. 
        assert (x2 = Some v). eapply add_to_stack_adds_parent. apply H5. subst. apply in_or_app.
        left. apply H5. 
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
        rewrite e. reflexivity. assert (forall o'' : option O.t, ~ In (v, o'') (add_to_stack x g0 remain_d)).
        intros. intro. apply add_to_stack_neq in H5. rewrite e in H5.
        contradiction. split. apply H5. assert (forall y0, ~In (y0, Some v) tl). intros.
        intro. rewrite e in H1. 
        remember (g0, t :: f, f_times, d_times, time, remain_d, remain_f, st) as s.
        assert (white s v = true). unfold white; subst; simpl; simplify.
        pose proof parents_not_white. specialize (H8 s g o y0 v). apply H8 in H. rewrite H in H7. inversion H7.
         subst; simpl. destruct (pop_stack st remain_f) eqn : ?.
        -- simpl in H2. destruct (S.min_elt remain_d). inversion H2; subst. inversion H2.
        -- simpl in H2. rewrite <- H2 in Heqs. eapply in_pop_rev. rewrite Heqs. right. apply H6.
        -- split. apply H6. intros; split; intros.
          ++ apply stack_desc_has_child in H7; simpl in H7. destruct H7.
             apply in_app_or in H7. destruct H7. exists (Some v). apply H7.
             simpl in H7. destruct H7. inversion H7; subst. rewrite e in H2.
             exfalso. eapply neq_parent. eapply step. apply H. apply H0. simpl. apply in_or_app.
             right. left. reflexivity. apply e. specialize (H6 x2). contradiction.
             destruct H7. destruct H7. apply stack_desc_has_child in H7; simpl in H7. destruct H7.
             apply in_app_or in H8. destruct H8. assert (B:=H8). apply add_to_stack_adds_parent in H8. inversion H8; subst.
             apply in_app_or in H7. destruct H7. assert (A:=H7). apply add_to_stack_adds_parent in H7. inversion H7; subst.
             exists (Some x). apply A. assert (C:= H7). simpl in H7. destruct H7. inversion H7; subst.
             Search add_to_stack.
             
             
             
             


 destruct H6. apply add_to_stack_adds_parent in H6.  inversion H6; subst.
             exfalso. eapply neq_parent. eapply step. apply H. apply H0. simpl. apply H7. apply e.
             apply in_app_or in H7. destruct H7. exfalso. eapply neq_parent. eapply step. apply H. apply H0.
              simpl. apply in_or_app. left. apply H7. apply add_to_stack_adds_parent in H7. inversion H7.

             apply in_app_or in H7. destruct H7. apply add_to_stack_adds_parent in H7. inversion H7; subst.
             
             
      * exists x0. exists x1. intros. destruct H3.
        rewrite P2.FM.remove_neq_b in H4. apply H4. apply n.
        destruct (pop_stack st) eqn : ?.
        -- simpl in H2. destruct (S.min_elt remain_d); inversion H2.
        -- simpl in H2. exists (add_to_stack x g0 remain_d ++ (pop_stack (x2) remain_f)).
        split. destruct H3. rewrite H2. rewrite <- Heqs. rewrite H3. rewrite pop_stack_app_distr.
        rewrite app_assoc. reflexivity. simplify. split. intros. intro. apply in_app_or in H5.
        destruct H5. apply only_add_yet_to_be_discovered in H5. simplify.
        rewrite P2.FM.remove_neq_b in H6. rewrite H6 in H5. inversion H5. intuition. 
        destruct H3. destruct H6. apply (H6 o''). eapply in_pop_rev. apply H5.
        intros. intro. destruct H3. destruct H6. apply (H7 y0). apply H5.
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
               apply (H5 o''). eapply in_pop_rev. rewrite Heqs0. right. apply H4.
                destruct H5. apply H5.
            ++ apply H7.
       -- intuition.
Qed. 
*)

(*An important lemma: The stack to the left of a gray vertex does not change. Moreover,
  the rest of the stack does not contain v, and the previous does not have v as a parent.
  This is key to proving that the search proceeds in a depth first manner*)
(*TODO: may want to add that o' is parent in forest (or if none then it is root)*)
Lemma right_left_stacks: forall s g o v,
  valid_dfs_state s g o ->
  exists tl o',
  gray s v = true ->
  (exists l1, get_stack s = l1 ++ (v,o') :: tl /\ (forall o'', ~In (v, o'') l1) /\
  (forall y, ~In (y, Some v) tl)).
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
        intros. intro. inversion H5.
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
        contradiction. intros. intro. rewrite e in H1. 
        remember (g0, t :: f, f_times, d_times, time, remain_d, remain_f, st) as s.
        assert (white s v = true). unfold white; subst; simpl; simplify.
        pose proof parents_not_white. specialize (H7 s g o y0 v). apply H7 in H. rewrite H in H6. inversion H6.
         subst; simpl. destruct (pop_stack st remain_f) eqn : ?.
        -- simpl in H2. destruct (S.min_elt remain_d). inversion H2; subst. inversion H2.
        -- simpl in H2. rewrite <- H2 in Heqs. eapply in_pop_rev. rewrite Heqs. right. apply H5.
      * exists x0. exists x1. intros. destruct H3.
        rewrite P2.FM.remove_neq_b in H4. apply H4. apply n.
        destruct (pop_stack st) eqn : ?.
        -- simpl in H2. destruct (S.min_elt remain_d); inversion H2.
        -- simpl in H2. exists (add_to_stack x g0 remain_d ++ (pop_stack (x2) remain_f)).
        split. destruct H3. rewrite H2. rewrite <- Heqs. rewrite H3. rewrite pop_stack_app_distr.
        rewrite app_assoc. reflexivity. simplify. split. intros. intro. apply in_app_or in H5.
        destruct H5. apply only_add_yet_to_be_discovered in H5. simplify.
        rewrite P2.FM.remove_neq_b in H6. rewrite H6 in H5. inversion H5. intuition. 
        destruct H3. destruct H6. apply (H6 o''). eapply in_pop_rev. apply H5.
        intros. intro. destruct H3. destruct H6. apply (H7 y0). apply H5.
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
               apply (H5 o''). eapply in_pop_rev. rewrite Heqs0. right. apply H4.
                destruct H5. apply H5.
            ++ apply H7.
       -- intuition.
Qed. 




(*
Lemma proper_stack: forall s g o v o' tl,
  valid_dfs_state s g o ->
  get_stack s = (v, o') :: tl ->
  white s v = true ->
  (forall s', dfs_multi s s' ->
    gray s' v = true ->
    exists l1, get_stack s' = l1 ++ (v, o') :: tl /\ (forall o'', ~In (v, o'') l1)).
Proof.
  intros. assert (valid_dfs_state s' g o). eapply multistep_preserves_valid. apply H. apply H2.
   eapply right_left_stacks in H4. destruct H4. destruct H4. apply H4 in H3. destruct H3.
    unfold gray in *; unfold white in *. induction H2.
  - simplify. rewrite H2 in H1. inversion H1.
  - inversion H2; subst; simpl in *.
    + 


   unfold whit 
*)

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

Lemma parent_gray: forall s g o y,
  valid_dfs_state s g o ->
  (exists x, In (x, Some y) (get_stack s)) ->
  gray s y = true.
Proof.
  intros. unfold gray. induction H; subst; simpl in *.
  - destruct o. destruct (G.contains_vertex g v). all: repeat(try(inversion H); try(inversion H0); try(inversion H1)).
  - inversion H1; subst; simpl in *.
    + assert (tl = nil). remember (g0, T.singleton x :: f, f_times, M.add x (time + 1) d_times, time + 1, S.remove x remain_d, remain_f,
       add_to_stack x g0 remain_d ++ (x, None) :: tl) as s.
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
      remember (g0, t :: f, f_times, d_times, time, remain_d, remain_f, st) as s.
      assert (S.mem x (get_remain_d s) = true) by (subst; simpl; assumption). eapply not_f_if_not_d in H4.
      subst; simpl in *; assumption. apply H. destruct (pop_stack st remain_f) eqn : ?; simpl in H3.
      * destruct (S.min_elt remain_d); inversion H3; subst.
      * rewrite andb_true_iff. assert (exists x, In (x, Some y) st). exists x0. eapply in_pop_rev.
        rewrite Heqs. rewrite <- H3. apply H0. apply IHvalid_dfs_state in H4. split. simplify.
        rewrite P2.Dec.F.remove_b. simplify. simplify.
    + destruct H0. (*ugh, need to know that if we are remvoving this, then there are none in the end*)
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
              apply H10. } exfalso. apply (H7 x0). rewrite e. apply H9. apply H3.
      * destruct (pop_stack st remain_f) eqn : ?.
        ++ simpl in H4. destruct (S.min_elt remain_d); inversion H4; subst. destruct H0.
        ++ simpl in H4. rewrite <- H4 in Heqs. assert (exists x, In (x, Some y) st). exists x0. eapply in_pop_rev.
           rewrite Heqs. right. apply H0. apply IHvalid_dfs_state in H5. simplify.
Qed.

Lemma parent_gray_when_child_active: forall s g o x y,
  valid_dfs_state s g o ->
  In (x, Some y) (get_stack s) ->
  gray s x = true ->
  gray s y = true.
Proof.
  intros. eapply parent_gray. apply H. exists x. apply H0.
Qed.

Lemma stack_desc_child: forall x y s,
  stack_desc s x y -> (exists z, In (z, Some y) (get_stack s)).
Proof.
  intros. induction H.
  - exists x. apply H.
  - exists y. apply H0.
Qed.

Lemma stack_desc_child_first: forall x y s,
  stack_desc s x y -> (exists z, In (x, Some z) (get_stack s)).
Proof.
  intros. induction H.
  - exists y. apply H.
  - destruct IHstack_desc. exists x0. apply H1.
Qed.

Lemma descendant_gray: forall s g o x y,
  valid_dfs_state s g o ->
  stack_desc s x y ->
  gray s y = true.
Proof.
  intros. induction H0.
  - eapply parent_gray. apply H. exists x. apply H0.
  - eapply parent_gray. apply H. exists y. apply H1.
Qed.

Lemma descendant_implies_gray_at_start: forall s g o x y,
  valid_dfs_state s g o ->
  stack_desc s x y ->
  Some (get_time s) = M.find x (get_d_times s) ->
  gray s y = true.
Proof.
  intros. eapply descendant_gray. apply H. apply H0.
Qed.

Lemma parent_in: forall s g o x y,
  valid_dfs_state s g o ->
  In (x, Some y) (get_stack s) ->
  exists z, In (y, z) (get_stack s).
Proof.
  intros. assert (gray s y = true). eapply parent_gray. apply H. exists x. apply H0.
  eapply gray_on_stack. apply H. apply H1.
Qed.

Lemma in_split: forall (A: Type) (x: A) l,
  In x l <->
  exists l1 l2, l = l1 ++ x :: l2.
Proof.
  intros. induction l; split; intros; simpl in *.
  - destruct H.
  - destruct H. destruct H. destruct x0; inversion H.
  - destruct H. subst. exists nil. exists l. reflexivity.
    apply IHl in H. destruct H. destruct H. rewrite H. exists (a :: x0). exists x1. reflexivity.
  - destruct H. destruct H. destruct x0. simpl in H. inversion H; subst. left. reflexivity.
    inversion H. assert (exists l1 l2, l = l1 ++ x :: l2). exists x0. exists x1. assumption.
    apply IHl in H0. right. rewrite <- H2. apply H0.
Qed. 

(*A vertex always comes after its parent on the stack*)
Lemma parent_ordered: forall s g o x y,
  valid_dfs_state s g o ->
  In (x, Some y) (get_stack s) ->
  exists l1 l2 l3 z, get_stack s = l1 ++ (x, Some y) :: l2 ++ (y, z) :: l3 /\ 
  (forall o'', ~In (y,o'') (l1 ++ (x, Some y) :: l2)) /\ (forall a, ~In(a, Some y) l3).
Proof.
  intros. assert (gray s y = true). eapply parent_gray. apply H. exists x. apply H0.
  assert (A:=H). eapply right_left_stacks in A. destruct A. destruct H2. apply H2 in H1.
  clear H2. destruct H1. destruct H1. destruct H2. 
  rewrite H1 in H0. apply in_app_or in H0. destruct H0.
  + assert (B:=H0). apply in_split in H0. destruct H0. destruct H0. exists x3. exists x4.
    exists x0. exists x1. split. rewrite H1. rewrite H0. rewrite <- app_assoc. reflexivity.
    split.
    setoid_rewrite <- H0. apply H2. apply H3.  
  + simpl in H0. destruct H0.
    * inversion H0; subst. exfalso. eapply neq_parent. apply H. rewrite H1. apply in_or_app.
      right. left. reflexivity. reflexivity.
    * exfalso. apply (H3 x). apply H0.
Qed.

Ltac destruct_all :=
repeat(match goal with
            |[H: (exists _, _) |- _] => destruct H
            |[H: _ /\ _ |- _] => destruct H 
            end; try(rewrite andb_true_iff in *)).

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

Lemma app_inv_rev_l: forall (A: Type) (l1 l2 l3: list A),
  l1 = l2 -> l3 ++ l1 = l3 ++ l2.
Proof.
  intros. subst. reflexivity.
Qed.

Lemma app_inv_rev_r : forall (A: Type) (l1 l2 l3: list A),
  l1 = l2 ->l1 ++ l3 = l2 ++ l3.
Proof.
  intros. subst. reflexivity.
Qed.

Lemma descendants_ordered: forall s g o x y,
  valid_dfs_state s g o ->
  stack_desc s x y ->
  exists l1 l2 l3 z o', get_stack s = l1 ++ (x, Some z) :: l2 ++ (y, o') :: l3 /\ 
  (forall o'', ~ In(y, o'') (l1 ++ (x, Some z) :: l2) ) /\ (forall a, ~In(a, Some y) l3).
Proof.
  intros. induction H0.
  - eapply parent_ordered in H. destruct_all.  exists x0. exists x1. exists x2. exists y.
    exists x3. split. apply H. split. apply H1. apply H2.  apply H0.
  - specialize (IHstack_desc H). eapply parent_ordered in H1. destruct_all.
    exists x0. assert (exists l1, x5 = x0 ++ l1).  rewrite H2 in H1.  assert (H7:=H1). apply app_match in H1.
    destruct H1. destruct H1; subst. rewrite <- app_assoc in H7. apply app_inv_head in H7. 
    destruct x9. inversion H7; subst. exfalso. eapply H3. simpl. apply in_or_app.
    right. left. reflexivity. inversion H7; subst. exfalso. apply (H3 (Some z)). apply in_or_app.
    left. apply in_or_app. right. left. reflexivity. apply H1.
    destruct H7. subst. rewrite H2 in H1. rewrite <- app_assoc in H1. apply app_inv_head in H1.
    destruct x9. inversion H1; subst. exfalso. apply (H3 (Some z)). apply in_or_app. right. left.
    reflexivity. inversion H1; subst. assert (exists l1, x9 = x1 ++ l1). assert (A:=H9). apply app_match in H9.
    destruct H9; destruct_all; subst. rewrite <- app_assoc in A. apply app_inv_head in A.
    destruct x5. exists nil. repeat(rewrite app_nil_r). reflexivity. inversion A; subst.
    exfalso. apply (H3 (Some z)). apply in_or_app. right. simpl. right. apply in_or_app.
    right. left. reflexivity. exists x5. reflexivity. destruct_all. subst.
    rewrite <- app_assoc in H9. apply app_inv_head in H9. destruct x5. inversion H9; subst.
    exists (x1 ++ (y, Some z) :: x6). exists x7. exists x3. exists x8.
    split. rewrite H2. rewrite <- app_assoc. reflexivity. rewrite app_nil_r in H5.
    rewrite <- app_assoc in H5. split. apply H5. apply H6.
    inversion H9; subst. exists (x1 ++ (y, x4) :: x5 ++ (y, Some z) :: x6). exists x7.
    exists x3. exists x8. split. rewrite H2. repeat(rewrite <- app_assoc).
    apply app_inv_rev_l.
    assert ((y, x4) :: x5 ++ (y, Some z) :: x6 ++ (z, x8) :: x7 =
   ((y, x4) :: x5 ++ (y, Some z) :: x6) ++ (z, x8) :: x7).
    simpl. rewrite <- app_assoc. reflexivity. 
    apply (app_inv_rev_l _ _ _ ((x, Some x3) :: x1)). simpl. rewrite <- app_assoc. reflexivity.
    assert (((x0 ++ (x, Some x3) :: x1 ++ (y, x4) :: x5) ++ (y, Some z) :: x6) =
    (x0 ++ (x, Some x3) :: x1 ++ (y, x4) :: x5 ++ (y, Some z) :: x6)). rewrite <- app_assoc.
    simpl. rewrite <- app_assoc. simpl. reflexivity. setoid_rewrite <- H7. split. apply H5. apply H6. apply H.
Qed.

Lemma in_app_end: forall (A: Type) l1 (x y z : A) l2 l3,
  l1 ++ x :: nil = l2 ++ y :: z :: l3 ->
  In y l1.
Proof.
  intros. generalize dependent l1. induction l2; intros.
  - simpl in H. destruct l1. simpl in H. inversion H. simpl in *.
    inversion H. left. reflexivity.
  - simpl in H. destruct l1.
    + simpl in H. inversion H. destruct l2; inversion H2.
    + simpl in H. inversion H; subst. simpl. right. apply IHl2. apply H2.
Qed. 
(*
Lemma consecutive_stack_elts: forall s g o x y x' y' l1 l2,
  valid_dfs_state s g o ->
  get_stack s = l1 ++ (x, y) :: (x', y') :: l2 ->
  y = y' \/ y = Some x'.
Proof.
  intros. generalize dependent l1. revert x y x' y' l2. induction H; intros; subst; simpl in *.
  - destruct o. destruct (G.contains_vertex g v). destruct l1; inversion H0. destruct l1; inversion H2.
    destruct l1; inversion H0. destruct l1; inversion H0.
  - inversion H0; subst; simpl in *.
    + assert (tl = nil). eapply root_nil. eapply step. apply H. apply H0. simpl.
      reflexivity. subst. destruct l2. 
      pose proof (app_inversion _ (x0, None) (x', y') (add_to_stack x0 g0 remain_d) (l1 ++ (x,y) :: nil)).
      destruct H4. rewrite <- app_assoc. simpl. apply H1. inversion H5; subst.
      right. eapply add_to_stack_adds_parent. rewrite H4. apply in_or_app. right. left. reflexivity.
      assert (In (x,y) (add_to_stack x0 g0 remain_d)). eapply in_app_end in H1. apply H1.
      assert (In (x', y') (add_to_stack x0 
      apply add_to_stack_adds_parent in H4.  
 simpl. rewrite H1.
      apply app_inversion in H1. simpl in H1. assert (A:=H1). eapply app_match in H1.
      destruct H1. destruct H1. rewrite H1 in A. rewrite <- app_assoc in A.
      apply app_inv_head in A. destruct x1. inversion A; subst.
       subst. inversion H2.  generalize dependent l2.
*)


Lemma no_cycles: forall s g o x y,
  valid_dfs_state s g o ->
  stack_desc s x y ->
  ~stack_desc s y x.
Proof.
  intros.  intro. eapply descendants_ordered in H0.
  eapply descendants_ordered in H1. destruct_all.
  rewrite H1 in H0. assert (A:=H0).
  apply app_match in H0. destruct H0; destruct_all; subst.
  rewrite <- app_assoc in A. apply app_inv_head in A. destruct x10; inversion A; subst.
  apply (H2 (Some x8)). apply in_or_app. right. left. reflexivity.
  apply (H2 (Some x8)). apply in_or_app. left. apply in_or_app. right. left. reflexivity.
   simpl. rewrite <- app_assoc in A. apply app_inv_head in A. destruct x10; inversion A; subst.
    apply (H2 (Some x8)). apply in_or_app. right. left. reflexivity.
    apply (H4 (Some x3)). apply in_or_app. left. apply in_or_app. right. left. reflexivity.
    all: apply H.
Qed. 


Fixpoint sublist (A: Type) (l: list A) (n: nat) :=
  match l with
  | nil => nil
  | x :: t => if ge_dec n (length l) then l else sublist _ t (n)
  end.

Lemma sublist_length: forall (A: Type) (l: list A),
  sublist _ l (length l) = l.
Proof.
  intros. destruct l. simpl. reflexivity. simpl.  destruct (ge_dec (S (length l)) (S (length l))) eqn : ?.
  reflexivity. omega.
Qed.

Lemma sublist_nil: forall (A: Type)(l:list A),
  sublist _ l 0 = nil.
Proof.
  intros. induction l. simpl. reflexivity. simpl. apply IHl.
Qed. 
(*
Lemma sublist_cons: forall (A: Type) (l: list A) x n,
  sublist _ 

Check sublist_nil.

Fixpoint list_ind_alt (A: Type) (l: list A) (P: list A -> Prop) (base: P (sublist _ 1 0))
  (base': P nil) (ind: forall n,
  P (sublist _ l n) -> P(sublist _ l (n+1))) : P ( sublist _ l (length l)) :=
  match l as l0 return P l0 with
  | nil => base'
  | x :: t => 

fun (A : Type) (P : list A -> Prop) (f : P nil) (f0 : forall (a : A) (l : list A), P l -> P (a :: l)) =>
fix F (l : list A) : P l := match l as l0 return (P l0) with
                            | nil => f
                            | y :: l0 => f0 y l0 (F l0)
                            end
*)
Lemma list_ind_alt: forall (A: Type) (P: list A -> Prop),
  forall l,
  P nil ->
  (forall n, P (sublist _ l n) -> P(sublist _ l (n+1))) ->
  P l.
Proof.
  intros. erewrite <- sublist_nil in H.   rewrite <- sublist_length.  induction (length l).
  - apply H. 
  - apply H0 in IHn. assert (S n = n + 1) by  omega. rewrite H1. apply IHn.
Qed. 
   
   

Lemma sublist_cons: forall A (x: A) l n,
  n < length (x :: l) ->
  sublist _ (x::l) n = sublist _ l n.
Proof.
  intros. simpl in *. assert (~ n >= S (length l)) by omega.
  destruct (ge_dec n (S (length l)))  eqn : ?. omega. reflexivity.
Qed.

Lemma sublist_ge: forall A (l: list A) n,
  n >= length l ->
  sublist _ l n = l.
Proof.
  intros. destruct l. reflexivity. simpl in *.
  destruct (ge_dec n (S (length l))) eqn : ?. reflexivity. omega.
Qed.

Lemma sublist_app: forall (A: Type) (l1: list A) l2 n,
  l1 = sublist _ l2 n ->
  exists x, x ++ l1 = l2.
Proof.
  intros. generalize dependent l1. induction l2; intros; subst.
  - exists nil. reflexivity.
  - simpl. destruct (ge_dec n (S (length l2))).
    + exists nil. reflexivity.
    + specialize (IHl2 (sublist A l2 n)). destruct IHl2. reflexivity.
      exists (a :: x). simpl. rewrite H. reflexivity.
Qed.

Lemma sublist_plus_one: forall (A: Type) (l: list A) n x l1,
  sublist _ l (n+1) = x :: l1 ->
  (sublist _ l n = x :: l1 \/ sublist _ l n = l1).
Proof.
  intros. induction l.
  - simpl in H. inversion H.
  - simpl in *. destruct (ge_dec n (S (length l))).
    + destruct (ge_dec (n + 1) (S (length l))) eqn : ?.
      * inversion H; subst. left. reflexivity.
      * omega.
    + destruct (ge_dec (n + 1) (S (length l)) ).
      * assert (n = length l) by omega. rewrite H0. right. inversion H; subst.
        apply sublist_length.
      * apply IHl. apply H.
Qed.

 
Lemma left_of_stack_descendant: forall s g o x y l1 l3 o'',
  valid_dfs_state s g o ->
  get_stack s = l1 ++ (y, o'') :: l3 ->
  x <> y ->
  ((exists o, In (x, o) l1) ->
  stack_desc s x y).
Proof.
  intros. revert H2.  revert H1. revert x. apply (list_ind_alt _ (fun l => forall l1,
  l = l1 ++ (y, o'') :: l3 -> forall x : O.t,
x <> y ->
((exists o0 : option O.t, In (x, o0) l1) -> stack_desc s x y)) (get_stack s)).
  - intros. destruct l0; inversion H1.
  - intros. assert (A:=H2). symmetry in H2. apply sublist_app in H2. destruct H2. rewrite <- H2 in H0.
    destruct H4. destruct x1. (*none case will be false*)
    assert (gray s t = true). eapply parent_gray. apply H. exists x. rewrite <- H2.
    apply in_or_app. right. apply in_or_app. left. apply H4. 
    assert (B:=H). eapply right_left_stacks in H. destruct_all. apply H in H5. clear H. destruct_all.
    assert (C:=H2).
    rewrite H in H2. assert(D:=H2). apply app_match in H2. destruct H2; destruct_all; subst.
    + rewrite <- app_assoc in D. apply app_inv_head in D. assert (x4 = nil).
      destruct x4. reflexivity. inversion D; subst. exfalso. apply (H6 x). apply in_or_app.
      right. apply in_or_app. left. apply H4. subst. simpl in *.
      destruct l0. inversion H4. inversion D; subst. destruct H4. inversion H2; subst.
      exfalso. eapply neq_parent. apply B. rewrite <- C. apply in_or_app.  right. apply in_or_app.
      left. left. reflexivity. reflexivity.
      exfalso. apply (H6 x). apply in_or_app. left. apply H2.
    + rewrite <- app_assoc in D. apply app_inv_head in D. assert (E := D). apply app_match in D.
      destruct D; destruct_all; subst.
      * rewrite <- app_assoc in E. apply app_inv_head in E. destruct x3; inversion E; subst.
        apply parent. rewrite H. apply in_or_app. left. apply in_or_app. right. rewrite app_nil_r in H4. apply H4.
        apply in_app_or in H4. destruct H4. destruct x0; simpl in *.
        destruct x4; simpl in *. destruct H2. assert (F:=A). apply sublist_plus_one in A.
        destruct A. destruct (O.eq_dec t y). unfold O.eq in e. subst.
        apply parent. rewrite H. simpl. destruct H2. left. apply H2. right. apply in_or_app.
        left. apply H2. eapply stack_desc_trans. apply parent. rewrite H. simpl.
        destruct H2. left. apply e. right. apply in_or_app. left. apply i. apply 
        (H1 (p :: (x4 ++ (t, x2) :: x3))). simpl. apply H4. apply n0. exists x2.
        simpl. right. apply in_or_app. right. left. reflexivity.
        destruct (O.eq_dec y t). unfold O.eq in e. subst. apply parent.
        rewrite H. simpl. destruct H2. left. apply H2. right. apply in_or_app. left. assumption.
        eapply stack_desc_trans. apply parent. rewrite H. simpl. destruct H2. left. apply e.
        right. apply in_or_app. left. apply i. apply (H1 (x4 ++ (t, x2) :: x3)).
        apply H4. intuition. exists x2. apply in_or_app. right. left. reflexivity.
        destruct x4. inversion H2. simpl in A.
         apply sublist_plus_one in A. destruct A.
        apply (H1 (p0 :: (x4 ++ (t, x2) :: x3))). apply H4. apply H3. exists (Some t).
        simpl. destruct H2. left. assumption. right. apply in_or_app. left. apply H2.
        simpl in H2. destruct (O.eq_dec y t). unfold O.eq in e. subst.
        apply parent. rewrite H. destruct H2. simpl. right. apply in_or_app.
        left. apply in_or_app. right. left. apply H2. simpl. right. apply in_or_app.
         left. apply in_or_app. right. right. apply H2.
        eapply stack_desc_trans. apply parent. rewrite H. destruct H2. simpl. right. apply in_or_app.
        left. apply in_or_app. right. left. apply e. simpl. right. apply in_or_app. left. apply in_or_app.
        right. right. assumption. apply (H1 (x4 ++ (t, x2) :: x3)). apply H4. intuition.
        exists x2. apply in_or_app. right. left. reflexivity.
        simpl in H2. destruct H2. inversion H2; subst.
        exfalso. eapply neq_parent. apply B. rewrite H. apply in_or_app. right. left. reflexivity.
        reflexivity. exfalso. apply (H6 x). apply in_or_app. left. apply H2.
      * rewrite <- app_assoc in E. apply app_inv_head in E.
        destruct (O.eq_dec y t). unfold O.eq in e. subst.
        apply parent. rewrite H. apply in_or_app. left. apply in_or_app. right.
        apply in_or_app. left. apply H4. destruct l0. inversion H4. simpl in A.
        apply sublist_plus_one in A. destruct A.
        -- eapply stack_desc_trans. apply parent. rewrite H. destruct H4. apply in_or_app.
           left. apply in_or_app. right. simpl. left. apply e. apply in_or_app. left.
           apply in_or_app. right. simpl. right. apply in_or_app. left. apply i.
           destruct x3. inversion E; subst. exfalso. apply n0. reflexivity.
           inversion E; subst. (*pick up here tomorrow, maybe try stronger claim (I might need it)*)
            (*Also think through and make niver proof - try to automate finidhing item*)
           apply (H1  apply e.
            right. left. apply e.


 apply H2.
        apply (H1 ((x4 ++ (t, x2) :: x3))). apply H4. apply H3. exists (Some t).


 rewrite <- app_assoc. simpl.
        rewrite <- app_assoc. simpl. apply H4.
        inversion 
        
        simpl.
        contradiction.  rewrite  app_assoc.
        apply H4.
        simpl in E. 
        destruct x4; simpl in *. destruct H4. apply sublist_plus_one in A. destruct A.
        --  apply parent. rewrite <- C. apply in_or_app. right.
           simpl. destruct H4. left. apply e. right. apply in_or_app. left. apply i.
             
          
         rewrite H in A. destruct x0; simpl in *. destruct (ge_dec (n + 1) (S (length (x4 ++ (t, x2) :: x1)))).
         destruct H4. inversion H2; subst. 
         
      
 des



 rewrite H0 in H2. destruct l1; simpl in *.
    + destruct (lt_dec n (length (get_stack s))). rewrite H0 in l. simpl in l.
      destruct (ge_dec (n + 1) (S (length l3))). destruct l0; inversion H2; subst.
      destruct H4. inversion H4. assert (l3 = (l0 ++ (y,o'') :: nil) ++ l3).
      simpl. rewrite <- app_assoc. simpl. apply H7. apply list_app_neq in H5. destruct H5.
      intro. destruct l0; inversion H6. 

list_app_neq
      

destruct l0; inversion H2.
      
      
      destruct l0. destruct H4. inversion H4. simpl in *.
      inversion H2; subst. destruct H4. destruct H4. inversion H4; subst. contradiction.
      eapply H1.



 rewrite   

(*not true - things before you could be your siblings - can only prove that everything 
  before you is not a descendant, but it is not an ancestor*)
Lemma left_of_stack_descendant: forall s g o x y l1 l3 o'',
  valid_dfs_state s g o ->
  get_stack s = l1 ++ (y, o'') :: l3 ->
  x <> y ->
  ((exists o, In (x, o) l1) ->
  stack_desc s x y) /\ ((exists o, In (x, o) l3) -> ~stack_desc s x y).
Proof.
  intros. revert H1. revert x. apply (list_ind_alt _ (fun l => forall l1 l3,
  l = l1 ++ (y, o'') :: l3 -> forall x : O.t,
x <> y ->
((exists o0 : option O.t, In (x, o0) l1) -> stack_desc s x y) /\
((exists o0 : option O.t, In (x, o0) l3) -> ~ stack_desc s x y)) (get_stack s)).
  - intros. destruct l0; inversion H1.
  - intros. rewrite H0 in H2. destruct l1; simpl in *.
    + destruct (n+1 =? 0). destruct l0; inversion H2.
      destruct l0; simpl in *; inversion H2; subst.
      * split. intros. destruct H4. destruct H4.
        
      *  
   


 induction l1; intros; subst; simpl in *.
  - split; intros. destruct H2. destruct H2. intro. eapply descendants_ordered in H3.
    destruct_all. rewrite H3 in H0. destruct x0; inversion H0; subst.
    apply (H4 (Some x3)). simpl. left. reflexivity.
    apply (H4 o''). apply in_or_app. left. left. reflexivity. apply H.
  - split; intros.
    + destruct H2. destruct H2.
      * inversion H2; subst. 

(*idea: modified induction principle: if I have a claim true for 1 element in the stack and 
if it is true for an element, it is true for the next element, then it is true for all elements in the stack*)


 revert H2. revert H1.
    remember ((y, o'') :: l3) as l. induction l. inversion Heql. inversion Heql; subst. generalize dependent y. revert o''. induction l3; intros; subst.
    + destruct H2. inversion H2.
    + destruct H2. simpl in H2. destruct H2. inversion H2; subst. intro.
      eapply descendants_ordered in H2. destruct_all. rewrite H2 in H0.
      destruct x1. inversion H0; subst. contradiction. inversion H0; subst.
      apply (H4 o''). apply in_or_app. left. left. reflexivity. apply H.
      



 destruct H1. destruct H1.
  - destruct H2. destruct H2. inversion H2; subst.
    assert (gray s y = true). Search gray. eapply gray_on_stack.

 revert H0. revert x y. revert l2 l3 o' o''. revert x y. remember  induction l1; intros; subst; simpl in *.
  - 
  induction H; intros; subst; simpl in *.
  - destruct o. destruct (G.contains_vertex g v). destruct l1. inversion H0. destruct l2; inversion H3.
    inversion H0. destruct l1; inversion H2. destruct l1; inversion H0. destruct l1; inversion H0.
  - inversion H0; subst; simpl in *.
    + destruct (O.eq_dec x0 x).
      * unfold O.eq in e. subst.  


Lemma gray_at_start_implies_desc: forall s g o x y,
  valid_dfs_state s g o ->
  Some (get_time s ) = M.find x (get_d_times s) ->
  gray s y = true ->
  stack_desc s x y.

Lemma right_left_stacks': forall s g o v,
  valid_dfs_state s g o ->
  exists tl o',
  gray s v = true ->
  (exists l1, get_stack s = l1 ++ (v,o') :: tl /\ (forall o'', ~In (v, o'') l1) /\
  (forall y, ~In (y, Some v) tl) /\ (forall x, (exists p, In (x,p) l1) -> stack_desc s x v)).
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
        split. intros. intro. inversion H5. intros. eapply parent. destruct H5. assert (A:=H5).
        apply add_to_stack_adds_parent in H5. subst. simpl. apply in_or_app. left. apply A.
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
        rewrite e. reflexivity. assert (forall o'' : option O.t, ~ In (v, o'') (add_to_stack x g0 remain_d)).
        intros. intro. apply add_to_stack_neq in H5. rewrite e in H5.
        contradiction. split. apply H5. assert (forall y0, ~In (y0, Some v) tl). intros.
        intro. rewrite e in H1. 
        remember (g0, t :: f, f_times, d_times, time, remain_d, remain_f, st) as s.
        assert (white s v = true). unfold white; subst; simpl; simplify.
        pose proof parents_not_white. specialize (H8 s g o y0 v). apply H8 in H. rewrite H in H7. inversion H7.
         subst; simpl. destruct (pop_stack st remain_f) eqn : ?.
        -- simpl in H2. destruct (S.min_elt remain_d). inversion H2; subst. inversion H2.
        -- simpl in H2. rewrite <- H2 in Heqs. eapply in_pop_rev. rewrite Heqs. right. apply H6.
        -- split. apply H6. intros. eapply parent. simpl. destruct H7. apply in_or_app. left.
               assert (A:=H7). apply add_to_stack_adds_parent in H7. subst. rewrite <- e. apply A.  
      * exists x0. exists x1. intros. destruct H3.
        rewrite P2.FM.remove_neq_b in H4. apply H4. apply n.
        destruct (pop_stack st) eqn : ?.
        -- simpl in H2. destruct (S.min_elt remain_d); inversion H2.
        -- simpl in H2. exists (add_to_stack x g0 remain_d ++ (pop_stack (x2) remain_f)).
        split. destruct H3. rewrite H2. rewrite <- Heqs. rewrite H3. rewrite pop_stack_app_distr.
        rewrite app_assoc. reflexivity. simplify.
        assert (forall o'' : option O.t, ~ In (v, o'') (add_to_stack x g0 remain_d ++ pop_stack x2 remain_f)).
         intros. intro. apply in_app_or in H5.
        destruct H5. apply only_add_yet_to_be_discovered in H5. simplify.
        rewrite P2.FM.remove_neq_b in H6. rewrite H6 in H5. inversion H5. intuition. 
        destruct H3. destruct H6. apply (H6 o''). eapply in_pop_rev. apply H5.
        split. apply H5. assert (forall y0 : S.elt, ~ In (y0, Some v) x0) .
        intros. intro. destruct H3. destruct H7. destruct H8. apply (H8 y0). apply H6. split. apply H6.
        intros. destruct H7. apply in_app_or in H7. destruct H7.
        ++ destruct H3. destruct H8. destruct H9. eapply stack_desc_trans. eapply parent.
          simpl. apply in_or_app. left. assert (A:=H7). apply add_to_stack_adds_parent in H7. subst.
          apply A. apply H10. apply H7.

 split; intros.
        ++ apply stack_desc_has_child_rev in H7; simpl in H7; destruct H7.
          ** destruct H3. destruct H8. destruct H9. apply in_app_or in H7. destruct H7.
             apply add_to_stack_adds_parent in H7. inversion H7; subst. exfalso. apply n. reflexivity.
              simpl in H7. destruct H7. inversion H7; subst.
            rewrite pop_stack_app_distr in Heqs. rewrite <- H2 in Heqs.
            destruct (pop_stack x2 remain_f) eqn : ?; simpl in Heqs.
            inversion Heqs; subst. exfalso. apply n. reflexivity. inversion Heqs; subst.
            exists (Some v). apply in_or_app. right. left. reflexivity. simplify.
            subst. rewrite <- H2 in Heqs. rewrite pop_stack_app_distr in Heqs.
             destruct (pop_stack (x2) remain_f) eqn : ?; simpl in Heqs. inversion Heqs; subst.
            exfalso. apply n. reflexivity. inversion Heqs; subst. inversion H2; subst.
            apply in_app_or in H7. destruct H7. exists (Some v). apply in_or_app. right. right.
            apply H3. simpl in H3. destruct H3. inversion H3; subst.
            exfalso. eapply neq_parent. eapply step. apply H. apply H0. simpl.
            apply in_or_app. right. simpl. right. apply in_or_app. right. left. reflexivity. reflexivity.
            specialize (H9 x3). contradiction. simplify.
          ** (*pick up here tomorrow almost donw tih this*)

 destruct H7. destruct H7. apply stack_desc_child_first in H7. destruct H7; simpl in H7.
             


destruct H3. destruct H8. destruct H9. destruct H7. destruct H7. apply in_app_or in H11. destruct H11.
             apply add_to_stack_adds_parent in H11. inversion H11; subst. exfalso. apply n. reflexivity.
              simpl in H11. destruct H11. inversion H11; subst.
            rewrite pop_stack_app_distr in Heqs. rewrite <- H2 in Heqs.
            destruct (pop_stack x2 remain_f) eqn : ?; simpl in Heqs.
            inversion Heqs; subst. exfalso. apply n. reflexivity. inversion Heqs; subst.
            
            exists (Some v). apply in_or_app. right. left. reflexivity. simplify.
            subst. rewrite <- H2 in Heqs. rewrite pop_stack_app_distr in Heqs.
             destruct (pop_stack (x2) remain_f) eqn : ?; simpl in Heqs. inversion Heqs; subst.
            exfalso. apply n. reflexivity. inversion Heqs; subst. inversion H2; subst.
            apply in_app_or in H7. destruct H7. exists (Some v). apply in_or_app. right. right.
            apply H3. simpl in H3. destruct H3. inversion H3; subst.
            exfalso. eapply neq_parent. eapply step. apply H. apply H0. simpl.
            apply in_or_app. right. simpl. right. apply in_or_app. right. left. reflexivity. reflexivity.
            specialize (H9 x3). contradiction. simplify.
            remember (g0, T.add_child t y x :: f, f_times, M.add x (time + 1) d_times, time + 1, S.remove x remain_d, remain_f,
       add_to_stack x g0 remain_d ++ (x, Some y) :: s0 ++ (x3, Some x3) :: x0) as s.
            assert (gray s x3 = true). left.
            refl 
            inversion Heqs. inversion Heqs; subst.  right Search x2.
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
               apply (H5 o''). eapply in_pop_rev. rewrite Heqs0. right. apply H4.
                destruct H5. apply H5.
            ++ apply H7.
       -- intuition.
Qed. 

(*maybe come back but its a ton of repetition*)

Lemma right_left_stack': forall s g o v,
  valid_dfs_state s g o ->
  exists tl o',
  gray s v = true ->
  (exists l1, get_stack s = l1 ++ (v,o') :: tl /\ (forall o'', ~In (v, o'') l1) /\
  (forall y, ~In (y, Some v) tl) /\ (forall x, stack_desc s x v <-> exists p, In (x,p) l1)).
Proof.
  intros. pose proof right_left_stacks. assert (A:=H). eapply H0 in H. destruct H. destruct H. exists x. exists x0.
  intros. assert (B:= H1). apply H in H1. destruct H1. exists x1. repeat(split; try (apply H1)).
  clear H0. clear H. unfold gray in *. generalize dependent x1. induction A; intros; subst; simpl in *.
  - simplify. rewrite H0 in H2. inversion H2.
  - inversion H; subst; simpl in *.
    + destruct H1. destruct H4. assert (tl = nil). eapply root_nil. eapply step. 
      apply A. apply H. simpl. reflexivity. subst.
      destruct (O.eq_dec x3 v).
      * unfold O.eq in e. subst. destruct x. simpl in H1. eapply (app_inversion) in H1.
        destruct H1. inversion H6; subst. 
      apply stack_desc_has_child in H0; simpl in H0. destruct H0.
       exists (Some v). apply in_app_or in H0. destruct H0. apply H0.
      simpl in H0. destruct H0; inversion H0. destruct H0. destruct H0.
      apply stack_desc_has_child in H0; simpl in H0; destruct H0.
      apply in_app_or in H0. apply in_app_or in H1. destruct H0. 
      apply add_to_stack_adds_parent in H0.  inversion H0; subst. exfalso.
      eapply neq_parent. eapply step. apply A. apply H. simpl. apply in_or_app. apply H1. reflexivity.
      destruct H0; inversion H0. destruct H0. destruct H0. 
      apply in_app_or in H7. destruct H7.
      apply add_to_stack_adds_parent in H7. inversion H7; subst. exfalso. eapply neq_parent.
      eapply step. apply A. apply H. simpl. apply H1. reflexivity. destruct H7; inversion H7.
      pose proof (app_inversion_2). specialize (H6 _ (v, None) (add_to_stack v g0 remain_d)
      (x1 ++ (v, x0) :: nil) (p :: x)). destruct H6. intro. inversion H6.
      rewrite <- app_assoc. symmetry. apply H1. rewrite H6 in H1.
      pose proof app_inversion. specialize (H7 _ (v, None) (v, None) (add_to_stack v g0 remain_d)
      (x1 ++ (v, x0) :: x3)). destruct H7. rewrite <- app_assoc. apply H1. 
      exfalso. eapply neq_parent. eapply step. apply A. apply H. simpl. rewrite H7. apply in_or_app.
      left. apply in_or_app. right. left. assert (In (v, x0) (add_to_stack v g0 remain_d)).
      rewrite H7. apply in_or_app. right. left. reflexivity. apply add_to_stack_adds_parent in H9.
      rewrite H9. reflexivity.  reflexivity.
      * destruct x. apply app_inversion in H1. destruct H1. inversion H6; subst. exfalso.
        apply n. reflexivity. pose proof (app_inversion_2 _ (x3, None) (add_to_stack x3 g0 remain_d)
        (x1 ++ (v, x0) :: nil) (p :: x)). destruct H6. intro. inversion H6.
        rewrite <- app_assoc. symmetry. apply H1. rewrite H6 in H1.
        pose proof (app_inversion _ (x3, None) (x3, None) (add_to_stack x3 g0 remain_d) (x1 ++ (v, x0) :: x4)).
        destruct H7. rewrite <- app_assoc. apply H1. assert (In (v, x0) (add_to_stack x3 g0 remain_d)).
        rewrite H7. apply in_or_app. right. left. reflexivity. assert (A1:=H9). apply add_to_stack_adds_parent
        in H9. subst. apply stack_desc_has_child in H0; simpl in H0. destruct H0.
        apply in_app_or in H0. destruct H0. apply add_to_stack_adds_parent in H0. inversion H0. subst.
        exfalso. apply n. reflexivity. destruct H0; inversion H0.
        destruct H0. destruct H0. apply in_app_or in H9. destruct H9. apply add_to_stack_adds_parent in H9.
        inversion H9; subst. exfalso. apply n. reflexivity. destruct H9; inversion H9.
    + destruct H1. destruct H4. destruct (O.eq_dec v x3).
      * unfold O.eq in e. subst.
 apply app_inversion in H1.
        intuition.
      right.  apply app_inversion in H1.
      ex
       
      destruct (O.eq_dec x3 v).


 destruct o. destruct (G.contains_vertex g v0). destruct H1. destruct x1; inversion H; subst.
 inversion H.
  
  



  valid_dfs_state s g o ->
  In (x, Some y) ->
  
  


(*Let's prove a stronger version of this
If (x, Some y) is on the stack and x is gray, then y is gray - did even better - if (x,y) is on the stack,
  then y is gray  q*)
(*Then prove: If x -> y is in the tree, then (x, Some y) is on the stack*)

(*
Lemma tree_not_white: forall s g o v,
  valid_dfs_state s g o ->
  G.contains_vertex g v = true ->
  (exists t f, get_forest s = t :: f /\ T.contains_vertex t v = true) <-> white s v = false.
Proof.
  intros. unfold white. induction H; subst; simpl in *; split; intros.
  - destruct H. destruct H. destruct H. inversion H.
  - simplify. apply G.set_of_graph_1 in H0. apply S.mem_1 in H0. rewrite H in H0. inversion H0.
  - inversion H1; subst; simpl in *.
    + destruct H2. destruct H2. destruct H2. inversion H2; subst. rewrite T.singleton_2 in H5. subst.
      simplify. left. destruct (S.mem x(S.remove x remain_d)) eqn : ?. exfalso. eapply remove_eq. apply Heqb.
      reflexivity.
    + destruct H2. destruct H2. destruct H2. inversion H2; subst. apply T.add_child_6 in H5. destruct H5.
      * destruct IHvalid_dfs_state. apply H0. simplify. destruct H6.
        exists t. exists x1. split. reflexivity. apply H5. left. rewrite P2.FM.remove_b. simplify.
        right. apply H6.
      *  subst. simplify. left. destruct (S.mem x (S.remove x remain_d)) eqn : ?. exfalso.
        eapply remove_eq. apply Heqb. reflexivity.
    + simplify. right. rewrite P2.FM.remove_b. simplify.
  - inversion H1; subst; simpl in *.
    + destruct (O.eq_dec x v).
      * unfold O.eq in e. subst. exists (T.singleton v). exists f. split. reflexivity.
        apply T.singleton_2. reflexivity.
      * destruct IHvalid_dfs_state. apply H0.
        rewrite P2.FM.remove_b in H2. simplify.
        -- simplify. destruct H7. destruct H2.
        
      assert (T.contains_vertex_1: forall 

*)

(**)
Lemma stack_contains_parents: forall s g o x y,
  valid_dfs_state s g o ->
  white s x = false ->
  In (x, Some y) (get_stack s) ->
  (exists t f, get_forest s = t :: f /\ T.is_child t y x = true).
Proof.
  intros. unfold white in H0. induction H; subst; simpl in *.
  - destruct o. destruct (G.contains_vertex g v). inversion H1. inversion H.
    inversion H. inversion H1. inversion H1.
  - inversion H2; subst; simpl in *.
    assert (tl = nil). { remember (g0, T.singleton x0 :: f, f_times, M.add x0 (time + 1) d_times, time + 1, S.remove x0 remain_d, remain_f,
       add_to_stack x0 g0 remain_d ++ (x0, None) :: tl) as s'.
      pose proof (only_1_root s' g o x0). destruct H5. eapply step. apply H.
      apply H2. subst; simpl. apply in_or_app. right. left. reflexivity. destruct H5; subst; simpl in *.
      destruct tl. reflexivity. pose proof (app_inversion_2 _ (x0, None) x1 
      (add_to_stack x0 g0 remain_d ++ (x0, None) :: nil) (p :: tl)). destruct H7. intro. inversion H7.
      rewrite <- app_assoc. apply H5. rewrite H7 in H5. pose proof (app_inversion _ (x0, None) (x0, None)
      (add_to_stack x0 g0 remain_d ++ (x0, None) :: x2) x1). destruct H8. rewrite <- app_assoc. apply H5.
      rewrite <- H8 in H6. exfalso. apply (H6 x0). apply in_or_app. right. left. reflexivity. } subst.
    + destruct (O.eq_dec x x0).
      * unfold O.eq in e. subst. apply in_app_or in H1. destruct H1.
        -- apply add_to_stack_neq in H1. contradiction.
        -- simpl in H1. destruct H1. inversion H1. destruct H1.
      * simplify. rewrite P2.FM.remove_neq_b in H5. apply in_app_or in H1.
        destruct H1. apply only_add_yet_to_be_discovered in H1. 
        remember (g0, f, f_times, d_times, time, remain_d, remain_f, st) as s'. rewrite H1 in H5. inversion H5.
        simpl in H1. destruct H1; inversion H1. intro; subst. apply n. reflexivity.
        apply in_app_or in H1. destruct H1. apply only_add_yet_to_be_discovered in H1.
        remember(g0, f, f_times, d_times, time, remain_d, remain_f, st) as s'.
        assert (S.mem x (get_remain_d s') = true) by (subst; simpl; assumption).
        eapply not_f_if_not_d in H6. subst; simpl in *. rewrite H6 in H5. inversion H5. apply H.
        destruct H1; inversion H1.
    + destruct (pop_stack st remain_f) eqn : ?.
      * simpl in H4. destruct (S.min_elt remain_d); inversion H4.
      * simpl in *. rewrite <- H4 in Heqs. pose proof (pop_stack_app st remain_f).
        destruct H5. destruct H5. destruct H5. subst. apply in_app_or in H1.
        destruct H1. assert (A:=H1). apply add_to_stack_neq in H1.
        apply only_add_yet_to_be_discovered in A. simplify. rewrite P2.FM.remove_neq_b in H5.
        rewrite A in H5. inversion H5. intro. subst. apply H1. reflexivity.
        remember (g0, t :: f, f_times, d_times, time, remain_d, remain_f, x1 ++ x2) as s'.
        assert (S.mem x (get_remain_d s') = true) by (subst; simpl; assumption).
        eapply not_f_if_not_d in H7. subst; simpl in *. rewrite H7 in H5. inversion H5. subst. apply H.
        simplify.
        -- destruct (O.eq_dec x x0). unfold O.eq in e. subst. simpl in H1. destruct H1. inversion H1; subst.
            exists (T.add_child t y x0). exists f. split. reflexivity. apply T.add_child_1.
            
        destruct (O.eq_dec x x0).
        -- unfold O.eq in e. subst. simpl in H1.
      * 


 rewrite 

 apply H0. apply in_app_or in H0. destruct H0. apply add_to_stack_adds_parent in H0. inversion H0; subst.
        

Lemma after_stack_gray: forall s g o v x y l1 l2 p,
  valid_dfs_state s g o ->
  gray s v = true ->
  (l1 ++ (v,p) :: l2 = get_stack s /\ forall p', ~In(v, p') l1) ->
  v <> x ->
  In (x,y) l1 ->
  (exists t f, get_forest s = t :: f /\ T.is_descendent t v x = true).
Proof.
  intros. unfold gray in H0. simplify. induction H; subst; simpl in *.
  - rewrite H4 in H5. inversion H5.
  - inversion H1; subst; simpl in *.
    + remember (g0, T.singleton x0 :: f, f_times, M.add x0 (time + 1) d_times, time + 1, S.remove x0 remain_d, remain_f,
       add_to_stack x0 g0 remain_d ++ (x0, None) :: tl) as s'.
      assert ( tl = nil). { pose proof (only_1_root s' g o x0). destruct H9. eapply step. apply H.
      apply H1. subst; simpl. apply in_or_app. right. left. reflexivity. destruct H9; subst; simpl in *.
      destruct tl. reflexivity. pose proof (app_inversion_2 _ (x0, None) x1 
      (add_to_stack x0 g0 remain_d ++ (x0, None) :: nil) (p0 :: tl)). destruct H11. intro. inversion H11.
      rewrite <- app_assoc. apply H9. rewrite H11 in H9. pose proof (app_inversion _ (x0, None) (x0, None)
      (add_to_stack x0 g0 remain_d ++ (x0, None) :: x2) x1). destruct H12. rewrite <- app_assoc. apply H9.
      rewrite <- H12 in H10. exfalso. apply (H10 x0). apply in_or_app. right. left. reflexivity. }
      subst. destruct (O.eq_dec v x0).
      * unfold O.eq in e. subst. destruct l2. apply app_inversion in H0. destruct H0. inversion H9; subst.
         simpl in H0. unfold e.
    
only_1_root

 destruct (O.eq_dec x x0).
      * unfold O.eq in e. subst. 


 destruct tl; simpl in *.
      * assert (In (v, p) (add_to_stack x0 g0 remain_d ++ (x0, None) :: nil)).
        rewrite <- H0. apply in_or_app. right. left. reflexivity. apply in_app_or in H8.
        destruct H8. apply only_add_yet_to_be_discovered in H8. 



 assert exists p', In (v p) ( 


 destruct o. destruct (G.contains_ve

Lemma top_of_stack_gray: forall s g o v x y tl,
  valid_dfs_state s g o ->
  gray s v = true ->
  black s x = false ->
  get_stack s = (x, y) :: tl ->
  exists t f, get_forest s = t :: f /\ T.is_descendent t v x = true.
Proof.
  intros. unfold gray in H0. unfold black in H1. induction H.
  - simpl in *. simplify. rewrite H3 in H. inversion H.
  - inversion H3; subst; simpl in *.
    + simplify.

only_1_root


 destruct o. destruc simpl in H1.
  

(*TODO: Parentheses Theorem - next big goal *)

(*Discovered at definition*)
(*
Definition discovered_at (v: vertex)(s: state) g o :=
  exists x, valid_dfs_state x g o /\
  dfs_step x s /\ white x v = true /\ gray s v = true.
Definition discovery_time (v: vertex)  s g o :=
  valid_dfs_state s g o /\
  M.find v (get_d_times s) = Some (get_time s).
Lemma discovered_at_time: forall v s g o,
  discovered_at v s g o <-> discovery_time v s g o.
Proof.
  intros. unfold discovered_at; unfold discovery_time; split; intros.
  - destruct H. destruct H. split. eapply step. apply H. apply H0. generalize dependent s.
    induction H; intros.
    + unfold white in *; unfold gray in *; simpl in *. destruct H0. inversion H; subst; simpl in *.
      * destruct (O.eq_dec v x).
        -- rewrite e. apply P.F.add_eq_o. reflexivity.
        -- destruct H0. rewrite andb_true_iff in H1. destruct H1.
           rewrite P2.Dec.F.remove_neq_b in H1. rewrite H2 in H1. inversion H1. intuition.
      * rewrite H11 in H10. inversion H10.
   + destruct H1. unfold white in *; unfold gray in *; inversion H1; subst; simpl in *.
    *  inversion H1; 
      
Definition discovery_time (v: vertex) n  
(*Prove it is equivalent to time definition*)
  
(*Parentheses Theorem*)
Lemma 
*)
End DFS.