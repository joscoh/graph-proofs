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

(** ** The inductive definition **)

(*The inductive definition of DFS. It is simply a relation between two states*)
Inductive dfs_step: state -> state -> Prop :=
  | dfs_discover_root : forall g f f_times d_times time remain_d remain_f x tl,
    S.mem x remain_d = true ->
    dfs_step (g, f, f_times, d_times, time, remain_d, remain_f, (x, None) :: tl)
    (g, (T.singleton x) :: f, f_times, (M.add x (time + 1) d_times), (time + 1), (S.remove x remain_d), 
    remain_f, (add_to_stack x g remain_d) ++  ((x, None) :: tl))
    (*Discover a vertex: add all of its neighbors who have not been discovered to the stack,
      add it to the stack, add it to the discover times with the current time, and remove it from
      remain_d. We also add it to the forest as a new singleton tree*)
  | dfs_discover_child : forall g t f f_times d_times time remain_d remain_f x y tl,
    S.mem x remain_d = true ->
    dfs_step (g, t :: f, f_times, d_times, time, remain_d, remain_f, (x, Some y) :: tl)
    (g, (T.add_child t y x) :: f, f_times, (M.add x (time + 1) d_times), (time + 1), (S.remove x remain_d), 
    remain_f, (add_to_stack x g remain_d) ++  ((x, Some y) :: tl))
    (*The same as the previous except we add the vertex as a child of its parent in the tree*)
  | dfs_finish: forall g f f_times d_times time remain_d remain_f x o tl,
    S.mem x remain_d = false ->
    S.mem x remain_f = true ->
    dfs_step (g, f, f_times, d_times, time, remain_d, remain_f, (x,o) :: tl)
    (g,  f, (M.add x (time + 1) f_times), d_times, (time + 1), remain_d, (S.remove x remain_f), tl)
    (*Finish a vertex by adding it to finish_times whileremoving it from remain_f and the stack*)
  | dfs_done_already: forall g f f_times d_times time remain_d remain_f x y tl s,
    S.mem x remain_d = false ->
    S.mem x remain_f = false ->
    (S.is_empty remain_d && S.is_empty remain_f) = false  ->
    dfs_step (g, f, f_times, d_times, time, remain_d, remain_f, tl) s ->
    dfs_step (g, f, f_times, d_times, time, remain_d, remain_f, (x,y) :: tl) s
    (*If we see a vertex that is already finished, keep stepping until we discover/finish a vertex*)
  | dfs_new_cc: forall g f f_times d_times time remain_d remain_f min s,
      S.min_elt remain_d = Some min ->
     dfs_step (g, f, f_times, d_times, time, remain_d, remain_f, (min, None) :: nil) s ->
     dfs_step (g, f, f_times, d_times, time, remain_d, remain_f, nil) s
    (*If the stack is empty but we still have more vertices to discover, get the minimum element
      of the remaining vertices and start again*).

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

(*Determinism*)
Lemma dfs_step_deterministic : forall s1 s2 s,
  dfs_step s s1 -> dfs_step s s2 -> s1 = s2.
Proof.
  intros. generalize dependent s2. induction H; intros; subst; simpl in *.
  - inversion H0; subst; simpl in *.
    + reflexivity.
    + rewrite H12 in H. inversion H.
    + rewrite H12 in H. inversion H.
  - inversion H0; subst; simpl in *.
    + reflexivity.
    + rewrite H12 in H. inversion H.
    + rewrite H12 in H. inversion H.
  - inversion H1; subst; simpl in *.
    + rewrite H13 in H. inversion H.
    + rewrite H13 in H. inversion H.
    + reflexivity.
    + rewrite H14 in H0. inversion H0.
  - inversion H3; subst; simpl in *.
    + rewrite H15 in H. inversion H.
    + rewrite H15 in H. inversion H.
    + rewrite H16 in H0. inversion H0.
    + eapply IHdfs_step. apply H18.
  - inversion H0; subst; simpl in *.
    + inversion H1; subst; simpl in *. eapply IHdfs_step. 
      rewrite H10 in H. inversion H; subst. apply H11.
    + apply S.min_elt_1 in H. apply S.mem_1 in H. rewrite H13 in H. inversion H.
    + apply S.min_elt_1 in H. apply S.mem_1 in H. rewrite H13 in H. inversion H.
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

(*Helper lemmas*)

(*Invariants*)

(*Due to the different definitions, it becomes much easier to prove that certain properties
  are preserved in each iteration than to prove everything directly*)

(*The following lemma justifies this approach: If we can prove that a property holds at the start
  state, and we can prove it is preserved in each step, then it holds for all valid states*)

Lemma invariant: forall (P: state -> Prop) g o,
  P (start_state g o) ->
  (forall s s', P s -> dfs_step s s' -> P s') ->
  forall s, valid_dfs_state s g o ->
  P s.
Proof.
  intros. induction H1.
  - apply H.
  - eapply H0. apply IHvalid_dfs_state. apply H. apply H2.
Qed.

Lemma v_discovered_step: forall s s' v,
  S.mem v (get_remain_d s) = false ->
  dfs_step s s' ->
  S.mem v (get_remain_d s') = false.
Proof.
  intros. induction H0; subst; simpl in *; try(apply IHdfs_step); try (assumption).
  - destruct (O.eq_dec v x); rewrite P2.Dec.F.remove_b; rewrite andb_false_iff.
    + rewrite e. right. rewrite negb_false_iff. unfold P2.Dec.F.eqb.
      destruct (O.eq_dec x x). reflexivity. exfalso. apply n. reflexivity.
    + left. apply H.
  - destruct (O.eq_dec v x); rewrite P2.Dec.F.remove_b; rewrite andb_false_iff.
    + rewrite e. right. rewrite negb_false_iff. unfold P2.Dec.F.eqb.
      destruct (O.eq_dec x x). reflexivity. exfalso. apply n. reflexivity.
    + left. apply H.
Qed.

Lemma v_finished_step: forall s s' v,
  S.mem v (get_remain_f s) = false ->
  dfs_step s s' ->
  S.mem v (get_remain_f s') = false.
Proof.
  intros. induction H0; subst; simpl in *; try(apply IHdfs_step); try (assumption).
  destruct (O.eq_dec v x); rewrite P2.Dec.F.remove_b; rewrite andb_false_iff.
    + rewrite e. right. rewrite negb_false_iff. unfold P2.Dec.F.eqb.
      destruct (O.eq_dec x x). reflexivity. exfalso. apply n. reflexivity.
    + left. apply H.
Qed.

Lemma v_discovered_iff_not_remain_step: forall s s' v,
  S.mem v (get_remain_d s) = false <-> (exists n, M.find v (get_d_times s) = Some n) ->
  dfs_step s s' ->
  S.mem v (get_remain_d s') = false <-> (exists n, M.find v (get_d_times s') = Some n).
Proof.
  intros. induction H0; subst; simpl in *; try(apply IHdfs_step); try(assumption); split; intros.
  - destruct (O.eq_dec x v).
    + exists (time + 1). rewrite e. apply P.F.add_eq_o. reflexivity.
    + rewrite P2.FM.remove_neq_b in H1. apply H in H1. destruct H1. exists x0.
      rewrite P.F.add_neq_o. apply H1. apply n. apply n.
  - rewrite P2.FM.remove_b. rewrite andb_false_iff. destruct (O.eq_dec x v).
    + right. rewrite negb_false_iff. unfold P2.FM.eqb. rewrite e.
      destruct (O.eq_dec v v). reflexivity. intuition.
    + rewrite P.F.add_neq_o in H1. apply H in H1. left. apply H1. apply n.
  - destruct (O.eq_dec x v).
    + exists (time + 1). rewrite e. apply P.F.add_eq_o. reflexivity.
    + rewrite P2.FM.remove_neq_b in H1. apply H in H1. destruct H1. exists x0.
      rewrite P.F.add_neq_o. apply H1. apply n. apply n.
  - rewrite P2.FM.remove_b. rewrite andb_false_iff. destruct (O.eq_dec x v).
    + right. rewrite negb_false_iff. unfold P2.FM.eqb. rewrite e.
      destruct (O.eq_dec v v). reflexivity. intuition.
    + rewrite P.F.add_neq_o in H1. apply H in H1. left. apply H1. apply n.
Qed.

Lemma v_discovered_iff_not_remain_start: forall g o v,
  G.contains_vertex g v = true ->
  S.mem v (get_remain_d (start_state g o)) = false <-> 
  (exists n, M.find v (get_d_times (start_state g o)) = Some n).
Proof.
  intros. split; intros.
  - unfold start_state; simpl in *. apply (G.set_of_graph_1) in H. apply S.mem_1 in H.
    rewrite H in H0. inversion H0.
  - unfold start_state; simpl in *. destruct H0. rewrite P.F.empty_o in H0. inversion H0.
Qed.

Lemma v_discovered_iff_not_remain: forall s g o v,
  valid_dfs_state s g o ->
  G.contains_vertex g v = true ->
  S.mem v (get_remain_d s) = false <-> (exists n, M.find v (get_d_times s) = Some n).
Proof.
  intros. eapply (invariant 
  (fun s => S.mem v (get_remain_d s) = false <-> (exists n : nat, M.find v (get_d_times s) = Some n))).
  - apply v_discovered_iff_not_remain_start. apply H0.
  - intros. eapply v_discovered_iff_not_remain_step. apply H1. apply H2.
  - apply H.
Qed.

(*A gray vertex is on the stack*)

Lemma gray_on_stack_step: forall s v s',
  (gray s v = true -> (exists y, In (v,y) (get_stack s))) ->
  dfs_step s s' ->
  (gray s' v = true -> (exists y, In (v,y) (get_stack s'))).
Proof.
  intros. unfold gray in *. rewrite andb_true_iff in *. destruct H1. assert (A:=H0). induction H0;
  subst; simpl in *; try (apply IHdfs_step); try(assumption).
  - destruct (O.eq_dec x v).
    + exists None. apply in_or_app. right. rewrite e. left. reflexivity.
    + rewrite P2.Dec.F.remove_neq_b in H1. destruct H. split; assumption. 
      exists x0. apply in_or_app. right. simpl. apply H. apply n.
  - destruct (O.eq_dec x v).
    + exists (Some y). apply in_or_app. right. rewrite e. left. reflexivity.
    + rewrite P2.Dec.F.remove_neq_b in H1. destruct H. split; assumption. 
      exists x0. apply in_or_app. right. simpl. apply H. apply n.
  - destruct (O.eq_dec v x).
    + rewrite e in H2. rewrite P2.Dec.F.remove_b in H2.
      rewrite andb_true_iff in H2. destruct H2. rewrite negb_true_iff in H4.
      unfold P2.Dec.F.eqb in H4. destruct (O.eq_dec x x). inversion H4. exfalso.
      apply n. reflexivity.
    + destruct H. split. apply H1. rewrite P2.Dec.F.remove_neq_b in H2.
      apply H2. intro; subst; intuition. destruct H. inversion H; subst; intuition.
      exfalso. apply n. reflexivity. exists x0. apply H.
  - intros. assert (A':=H6). apply H in H6. destruct H6. destruct H6. inversion H6; subst.
    destruct A'. rewrite H8 in H3. inversion H3. exists x0. apply H6.
  - intros. apply H in H4. destruct H4. destruct H4.
Qed. 

Lemma gray_on_stack_start: forall g o v,
  gray (start_state g o) v = true -> (exists y, In (v,y) (get_stack (start_state g o))).
Proof.
  intros. unfold start_state in *; unfold gray in *; subst; simpl in *.
  rewrite andb_true_iff in H; destruct H; rewrite H0 in H; inversion H.
Qed.

Lemma gray_on_stack: forall s g o v,
  valid_dfs_state s g o ->
  gray s v = true ->
  (exists y, In (v, y) (get_stack s)).
Proof.
  intros. eapply (invariant (fun s =>gray s v = true ->
  (exists y, In (v, y) (get_stack s)))). 
  - apply gray_on_stack_start.
  - intros. eapply gray_on_stack_step. apply H1. apply H2. apply H3.
  - apply H.
  - apply H0.
Qed.

(*Information about times*)
Lemma time_plus_1: forall s s',
  dfs_step s s' ->
  get_time s +1 = get_time s'.
Proof.
  intros. induction H; subst; simpl in *; try(reflexivity); try(apply IHdfs_step; reflexivity).
Qed.

Lemma time_incr_step: forall s s',
  dfs_step s s' ->
  get_time s < get_time s'.
Proof.
  intros. erewrite <- (time_plus_1 _ _ H). omega.
Qed.

Lemma time_incr_multi: forall s s',
  dfs_multi s s' ->
  s = s' \/ get_time s < get_time s'.
Proof.
  intros. induction H.
  - left. reflexivity.
  - destruct IHmulti. subst. right. apply time_incr_step. apply H. right. 
    apply time_incr_step in H. omega.
Qed.

(* remain_d and remain_f contain vertices in the graph *)
Lemma remaining_in_graph_step: forall s s' g,
  (forall v, S.In v (get_remain_d s) \/ S.In v (get_remain_f s) -> G.contains_vertex g v = true) ->
  dfs_step s s' ->
  (forall v, S.In v (get_remain_d s') \/ S.In v (get_remain_f s') -> G.contains_vertex g v = true).
Proof.
  intros. assert (A:=H0). induction H0; subst; simpl in *.
  - destruct H1.
    + destruct (O.eq_dec v x).
      * rewrite e in H1. rewrite P2.FM.remove_iff in H1. destruct H1. contradiction.
      * rewrite P2.Dec.F.remove_neq_iff in H1. apply H. left. apply H1. intro. subst. intuition.
    + apply H. right. apply H1.
  - destruct H1.
    + destruct (O.eq_dec v x).
      * rewrite e in H1. rewrite P2.FM.remove_iff in H1. destruct H1. contradiction.
      * rewrite P2.Dec.F.remove_neq_iff in H1. apply H. left. apply H1. intro. subst. intuition.
    + apply H. right. apply H1.
  - destruct H1.
    + apply H. left. apply H1.
    + destruct (O.eq_dec v x).
      * rewrite e in H1. rewrite P2.FM.remove_iff in H1. destruct H1. contradiction.
      * rewrite P2.Dec.F.remove_neq_iff in H1. apply H. right. apply H1. intro. subst. intuition.
  - apply IHdfs_step. apply H. apply H1. apply H4.
  - apply IHdfs_step. apply H. apply H1. apply H2.
Qed.

Lemma remaining_in_graph_start: forall g o,
  (forall v, S.In v (get_remain_d (start_state g o)) \/ S.In v (get_remain_f (start_state g o)) ->
   G.contains_vertex g v = true).
Proof.
  intros. simpl in *. destruct H; apply G.set_of_graph_1 in H; assumption.
Qed.

Lemma remaining_in_graph: forall s g o v,
  valid_dfs_state s g o ->
  S.In v (get_remain_d s) \/ S.In v (get_remain_f s) ->
  G.contains_vertex g v = true.
Proof.
  intros. eapply (invariant (fun s => 
  (forall v, S.In v (get_remain_d s) \/ S.In v (get_remain_f s) -> G.contains_vertex g v = true))); intros;
  try(assumption).
  - eapply remaining_in_graph_start. apply H1.
  - eapply remaining_in_graph_step. apply H1. apply H2. apply H3.
  - apply H.
  - apply H0.
Qed.

(*map has only valid vertices*)
Lemma times_valid_vertices_step: forall s s' g,
  (forall v, S.In v (get_remain_d s) \/ S.In v (get_remain_f s) ->
  G.contains_vertex g v = true) ->
  (forall v, (exists n, M.find v (get_d_times s) = Some n) \/ (exists n, M.find v (get_f_times s) = Some n) ->
     G.contains_vertex g v = true) ->
  dfs_step s s' ->
  (forall v, (exists n, M.find v (get_d_times s') = Some n) \/ (exists n, M.find v (get_f_times s') = Some n) ->
     G.contains_vertex g v = true).
Proof.
  intros. assert (A:=H1). induction H1; subst; simpl in *.
  - destruct (O.eq_dec x v).
    + rewrite e in H1. apply H. left. apply S.mem_2 in H1. apply H1.
    + specialize (H0 v). rewrite F.add_neq_o in H2. apply H0. apply H2. apply n.
  - destruct (O.eq_dec x v).
    + rewrite e in H1. apply H. left. apply S.mem_2 in H1. apply H1.
    + specialize (H0 v). rewrite F.add_neq_o in H2. apply H0. apply H2. apply n.
  - destruct (O.eq_dec x v).
    + rewrite e in H3. apply H. right. apply S.mem_2 in H3. apply H3.
    + specialize (H0 v). rewrite F.add_neq_o in H2. apply H0. apply H2. apply n.
  - apply IHdfs_step; assumption.
  - apply IHdfs_step; assumption.
Qed.

Lemma times_valid_vertices_start: forall g o,
   (forall v, (exists n, M.find v (get_d_times (start_state g o)) = Some n) \/ 
    (exists n, M.find v (get_f_times (start_state g o)) = Some n) ->
     G.contains_vertex g v = true).
Proof.
  intros. simpl in *. destruct H; destruct H; rewrite P.F.empty_o in H; inversion H.
Qed.

Lemma times_valid_vertices: forall s g o v,
  valid_dfs_state s g o ->
  (exists n, M.find v (get_d_times s) = Some n) \/ (exists n, M.find v (get_f_times s) = Some n) ->
     G.contains_vertex g v = true.
Proof.
  intros. generalize dependent v. induction H; intros.
  - eapply times_valid_vertices_start. apply H0.
  - eapply times_valid_vertices_step. intros. eapply remaining_in_graph. apply H.
    apply H2. intros. apply IHvalid_dfs_state. apply H2. apply H0. apply H1.
Qed.

(*Preservation of times*)
Lemma preserve_dtime_step: forall s s' v n g o,
  valid_dfs_state s g o ->
  M.find v (get_d_times s) = Some n ->
  dfs_step s s' ->
  M.find v (get_d_times s') = Some n.
Proof.
  intros. assert (A:=H1). induction H1; subst; simpl in *.
  - destruct (O.eq_dec v x).
    + rewrite e in H0. assert (exists n, M.find x d_times = Some n) by (exists n; apply H0).
      remember (g0, f, f_times, d_times, time, remain_d, remain_f, (x, None) :: tl) as s.
      assert (d_times = get_d_times s) by (subst; reflexivity). rewrite H3 in H2.
      rewrite <- v_discovered_iff_not_remain in H2. subst; simpl in *.
      rewrite H2 in H1. inversion H1. apply H. eapply remaining_in_graph.
      apply H. subst; simpl in *. left. apply S.mem_2. apply H1.
    + rewrite P.F.add_neq_o. apply H0. intuition.
  - destruct (O.eq_dec v x).
    + rewrite e in H0. assert (exists n, M.find x d_times = Some n) by (exists n; apply H0).
      remember (g0, t :: f, f_times, d_times, time, remain_d, remain_f, (x, Some y) :: tl) as s.
      assert (d_times = get_d_times s) by (subst; reflexivity). rewrite H3 in H2.
      rewrite <- v_discovered_iff_not_remain in H2. subst; simpl in *.
      rewrite H2 in H1. inversion H1. apply H. eapply remaining_in_graph.
      apply H. subst; simpl in *. left. apply S.mem_2. apply H1.
    + rewrite P.F.add_neq_o. apply H0. intuition.
  - apply H0.
  - apply IHdfs_step; try(assumption). 

(*tommorrow*) 

Lemma discover_before_finish: forall s s' v n m,
  (M.find v (get_d_times s)

(*Next, we want to prove that if a vertex is on the stack, there is a point where
  everything to the right of it is unequal. Then, we want to show that all vertices in this
  portion of the stack are descendants of x*)

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

Lemma In_split: forall (x: O.t * option O.t) l,
  In x l ->
  exists l1 l2, l = l1 ++ (x :: l2) /\ (forall y, In y l1 -> y <> x).
Proof.
  intros. induction l.
  - inversion H.
  - simpl in H. destruct H.
    + subst. exists nil. exists l. split. reflexivity. intros. inversion H.
    + destruct (stack_elt_dec a x).
      * subst. exists nil. exists l. split. reflexivity. intros. inversion H0.
      * apply IHl in H. destruct H. destruct H. destruct H. exists (a :: x0). exists x1.
      split. rewrite H. simpl. reflexivity. intros. simpl in H1. destruct H1.
      subst. apply n. apply H0. apply H1.
Qed.


Definition desc_list l v s g o,
  exists l1 o, get_stack s = 1 ++ (v,0) :: l1 /\ (forall u o', In (u, o') l -> u 

Definition vertex_discovered_at_before s s' v :=
  dfs_step s s' /\ white s v = true /\ gray s' v = true.

Definition vertex_discovered_at (s: state) (v: vertex) g o : Prop :=
  exists s', valid_dfs_state s' g o /\
  dfs_step s' s /\
  white s' v = true /\
  gray s v = true.

(*The goal*)
Lemma discover_while_gray: forall s g o v v',
  valid_dfs_state s g o ->
  gray s v = true ->
  vertex_discovered_at s v' g o ->
  v = v' \/ exists t f, get_forest s = t :: f /\ T.is_descendent t v v' = true.
Proof.
  intros. unfold vertex_discovered_at in H1. unfold gray in *.
  unfold white in *. destruct H1. destruct H1. destruct H2. destruct H3.
  rewrite andb_true_iff in *. destruct H0. destruct H3. destruct H4.
  rewrite negb_true_iff in *. induction H2; subst; simpl in *.
  - destruct (O.eq_dec v v').
    + unfold O.eq in e. subst. left. reflexivity.
    + 
    

