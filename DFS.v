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

(*In order to perform DFS, we need a lawful Graph (the input), Tree (the output), Set (for keeping
  track of the vertices not yet seen), Map (for storing discover/finish times), and UsualOrderedType
  (for the vertices). Also, we could use different sets for the Graph and Tree instances.*)
Module DFS (O: UsualOrderedType)(M: FMapInterface.Sfun O) (S St: FSetInterface.Sfun O) (G: Graph O S)
            (T: Tree O St S G).

Module P := FMapFacts.WProperties_fun O M.
Module F := P.F.
Module P2 := FSetProperties.WProperties_fun O S.

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
    |Some s => fold_right (fun v t => if S.mem v remaining then (v, Some vertex) :: t else t) nil (S.elements s)
  end.

(** ** The inductive definition **)

(*The inductive definition of DFS. It is simply a relation between two states*)
Inductive dfs_step: state -> state -> Prop :=
  | dfs_discover_root : forall g f f_times d_times time remain_d remain_f x tl,
    S.mem x remain_d = true ->
    dfs_step (g, f, f_times, d_times, time, remain_d, remain_f, (x, None) :: tl)
    (g, (T.singleton x) :: f, f_times, (M.add x time d_times), (time + 1), (S.remove x remain_d), 
    remain_f, (add_to_stack x g remain_d) ++  ((x, None) :: tl))
    (*Discover a vertex: add all of its neighbors who have not been discovered to the stack,
      add it to the stack, add it to the discover times with the current time, and remove it from
      remain_d. We also add it to the forest as a new singleton tree*)
  | dfs_discover_child : forall g t f f_times d_times time remain_d remain_f x y tl,
    S.mem x remain_d = true ->
    dfs_step (g, t :: f, f_times, d_times, time, remain_d, remain_f, (x, Some y) :: tl)
    (g, (T.add_child t y x) :: f, f_times, (M.add x time d_times), (time + 1), (S.remove x remain_d), 
    remain_f, (add_to_stack x g remain_d) ++  ((x, Some y) :: tl))
    (*The same as the previous except we add the vertex as a child of its parent in the tree*)
  | dfs_finish: forall g f f_times d_times time remain_d remain_f x o tl,
    S.mem x remain_d = false ->
    S.mem x remain_f = true ->
    dfs_step (g, f, f_times, d_times, time, remain_d, remain_f, (x,o) :: tl)
    (g,  f, (M.add x time f_times), d_times, (time + 1), remain_d, (S.remove x remain_f), tl)
    (*Finish a vertex by adding it to finish_times whileremoving it from remain_f and the stack*)
  | dfs_done_already: forall g f f_times d_times time remain_d remain_f x y tl,
    S.mem x remain_d = false ->
    S.mem x remain_f = false ->
    (S.is_empty remain_d && S.is_empty remain_f) = false  ->
    dfs_step (g, f, f_times, d_times, time, remain_d, remain_f, (x,y) :: tl)
    (g, f, f_times, d_times, time, remain_d, remain_f, tl)
    (*If we have already finished the current vertex (but are not yet done), then just remove this vertex
      from the stack and continue*)
  | dfs_new_cc: forall g f f_times d_times time remain_d remain_f min,
      S.min_elt remain_d = Some min ->
     dfs_step (g, f, f_times, d_times, time, remain_d, remain_f, nil)
     (g, f, f_times, d_times, time, remain_d, remain_f, (min, None) :: nil)
    (*If the stack is empty but we still have more vertices to discover, get the minimum element
      of the remaining vertices and start again*).

(*A few state-related definitions to make the proofs simpler*)
(*Is the DFS done? We will show that this condition holds iff there are no more steps*)
Definition done' (s: state) : bool :=
  match s with
  | (_, _, _, _, _, start, finish, _) => S.is_empty start && S.is_empty finish
  end.

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
  intros.
  generalize dependent s2. induction H; intros.
  - inversion H0; subst.
    + reflexivity.
    + rewrite H12 in H. inversion H.
    + rewrite H12 in H. inversion H.
  - inversion H0; subst.
    + reflexivity.
    + rewrite H12 in H. inversion H.
    + rewrite H12 in H. inversion H.
  - inversion H1; subst.
    + rewrite H13 in H. inversion H.
    + rewrite H13 in H. inversion H.
    + reflexivity.
    + rewrite H14 in H0. inversion H0.
  - inversion H2; subst.
    + rewrite H14 in H. inversion H.
    + rewrite H14 in H. inversion H.
    + rewrite H15 in H0. inversion H0.
    + reflexivity.
  - inversion H0; subst. rewrite H9 in H. inversion H; subst; reflexivity.
Qed.

(*A few lemmas about time TODO: Use these lemmas later in more proofs about time*)
Lemma dfs_time_geq: forall s1 s2,
  dfs_step s1 s2 -> get_time s1 <= get_time s2.
Proof.
  intros.
  inversion H; simpl; omega.
Qed.

Lemma dfs_time_incr_when_vertex_info_changes : forall s1 s2,
  dfs_step s1 s2 ->
  get_remain_d s1 <> get_remain_d s2 \/
  get_remain_f s1 <> get_remain_f s2 \/
  get_d_times s1 <> get_d_times s2 \/
  get_f_times s1 <> get_f_times s2 ->
  get_time s1 + 1 = get_time s2.
Proof.
  intros. inversion H; simpl; try (reflexivity); subst; simpl in *;repeat(destruct H0; try(contradiction)).
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

(*If a vertex is discovered, it is not in remain_d*)
Lemma discovered_vertex_not_remaining: forall s g o v,
  valid_dfs_state s g o ->
  G.contains_vertex g v = true ->
  (exists n, (M.find v (get_d_times s) = Some n)) <-> S.mem v (get_remain_d s) = false.
Proof.
  intros. generalize dependent v. induction H; subst; simpl; intros; split; intros.
  - rewrite P.F.empty_o in H. inversion H. inversion H1.
  - rewrite G.set_of_graph_1 in H0. apply S.mem_1 in H0. rewrite H in H0. inversion H0.
  - inversion H0; subst; simpl in *; try (apply IHvalid_dfs_state; assumption; assumption).
    + destruct (O.eq_dec x v).
      * setoid_rewrite e. setoid_rewrite e in H2. rewrite P2.Dec.F.remove_b.
        rewrite andb_false_iff. right. unfold P2.Dec.F.eqb. 
        destruct (O.eq_dec v v). reflexivity. exfalso. apply n. apply eq_refl.
      * rewrite P2.FM.remove_neq_b. rewrite <- IHvalid_dfs_state. 
        rewrite P.F.add_neq_o in H2. apply H2. intro. subst. apply n.
        apply eq_refl. apply H1. intro. subst. apply n. apply eq_refl.
    + destruct (O.eq_dec x v).
      * setoid_rewrite e. setoid_rewrite e in H2. rewrite P2.Dec.F.remove_b.
        rewrite andb_false_iff. right. unfold P2.Dec.F.eqb. 
        destruct (O.eq_dec v v). reflexivity. exfalso. apply n. apply eq_refl.
      * rewrite P2.FM.remove_neq_b. rewrite <- IHvalid_dfs_state. 
        rewrite P.F.add_neq_o in H2. apply H2. intro. subst. apply n.
        apply eq_refl. apply H1. intro. subst. apply n. apply eq_refl.
  - inversion H0; subst; simpl in *; try (apply IHvalid_dfs_state; assumption; assumption).
    + destruct (O.eq_dec x v).
      * setoid_rewrite e. exists time. apply P.F.add_eq_o. reflexivity.
      * rewrite P2.Dec.F.remove_neq_b in H2. rewrite <- IHvalid_dfs_state in H2.
        rewrite P.F.add_neq_o. apply H2. auto.
        apply H1. auto.
    + destruct (O.eq_dec x v).
      * setoid_rewrite e. exists time. apply P.F.add_eq_o. reflexivity.
      * rewrite P2.Dec.F.remove_neq_b in H2. rewrite <- IHvalid_dfs_state in H2.
        rewrite P.F.add_neq_o. apply H2. auto.
        apply H1. auto.
Qed.

Lemma add_to_stack_adds_valid_vertices: forall v g r v' y,
  In (v', y) (add_to_stack v g r) ->
  G.contains_vertex g v' = true.
Proof.
  intros. unfold add_to_stack in H. destruct (G.neighbors_set g v) eqn : ?.
  - assert (forall a b l, In (a,b) ((fold_right (fun (v0 : S.elt) (t : list (S.elt * option O.t)) => if S.mem v0 r then (v0, Some v) :: t else t)
         nil l)) -> In a l). {
    intros. induction l. simpl in H0. destruct H0. simpl.
    simpl in H0. destruct (S.mem a0 r). simpl in H0. destruct H0. inversion H0; subst. left. reflexivity.
    right. apply IHl. apply H0. right. apply IHl. apply H0. }
    apply H0 in H. rewrite In_InA_equiv in H. apply S.elements_2 in H.
     Search G.neighbors_set. rewrite <- G.neighbors_set_2 in H.
    eapply G.contains_edge_2. apply H. apply Heqo.
  - simpl in H. destruct H.
Qed. 

Definition get_graph (s: state) :=
  match s with
  | (g, _, _, _, _, _, _, _) => g
  end.

Lemma graph_is_constant: forall s g o,
  valid_dfs_state s g o ->
  get_graph s = g.
Proof.
  intros. induction H.
  - simpl. reflexivity.
  - inversion H0; subst; simpl in *; reflexivity.
Qed.

Lemma remain_d_contains_valid_vertices: forall s g o v,
  valid_dfs_state s g o ->
  S.mem v (get_remain_d s) = true ->
  G.contains_vertex g v = true.
Proof.
  intros. generalize dependent v. induction H; intros.
  - simpl in H0. rewrite G.set_of_graph_1. apply S.mem_2. apply H0.
  - inversion H0; subst; simpl in *; try (apply IHvalid_dfs_state; assumption).
    + rewrite P2.Dec.F.remove_b in H1. rewrite andb_true_iff in H1. destruct H1.
      unfold P2.Dec.F.eqb in H3. destruct (O.eq_dec x v). inversion H3.
      apply IHvalid_dfs_state. apply H1.
    + rewrite P2.Dec.F.remove_b in H1. rewrite andb_true_iff in H1. destruct H1.
      unfold P2.Dec.F.eqb in H3. destruct (O.eq_dec x v). inversion H3.
      apply IHvalid_dfs_state. apply H1.
Qed.

Lemma stack_contains_valid_vertices: forall s g o v st (y: option vertex),
  valid_dfs_state s g o ->
  get_stack s = st ->
  In (v, y) st ->
  G.contains_vertex g v = true.
Proof.
  intros. generalize dependent st. induction H; simpl in *; intros.
  - destruct o. destruct (G.contains_vertex g v0) eqn : ?.
    + rewrite <- H0 in H1. simpl in H1. destruct H1. inversion H; subst. apply Heqb. destruct H.
    + rewrite <- H0 in H1. simpl in H1. destruct H1.
    + rewrite <- H0 in H1. simpl in H1. destruct H1.
  - inversion H0; simpl in *; subst.
    + assert (g0 = g).
        remember (g0, f, f_times, d_times, time, remain_d, remain_f, (x, None) :: tl) as s.
        assert (get_graph s = g0). rewrite Heqs. simpl. reflexivity. 
        apply graph_is_constant in H. rewrite H1 in H. apply H. subst.
      simpl in H2. apply in_app_or in H2. destruct H2.
      * eapply add_to_stack_adds_valid_vertices. apply H1.
      * simpl in IHvalid_dfs_state. eapply IHvalid_dfs_state.
        reflexivity. apply H1.
    + simpl in *. assert (g0 = g).
        remember (g0, f, f_times, d_times, time, remain_d, remain_f, (x, None) :: tl) as s.
        assert (get_graph s = g0). rewrite Heqs. simpl. reflexivity. 
        apply graph_is_constant in H. simpl in H. apply H. subst. 
       apply in_app_or in H2. destruct H2.
      * eapply add_to_stack_adds_valid_vertices. apply H1.
      * simpl in IHvalid_dfs_state. eapply IHvalid_dfs_state.
        reflexivity. apply H1.
    + simpl in *. eapply IHvalid_dfs_state. reflexivity. simpl. right. apply H2.
    + simpl in *. eapply IHvalid_dfs_state. reflexivity. simpl. right. apply H2.
    + simpl in *. destruct H2. 
      * inversion H1; subst. apply S.min_elt_1 in H3. apply S.mem_1 in H3.
        eapply remain_d_contains_valid_vertices. apply H. simpl. apply H3.
      * destruct H1.
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
      * setoid_rewrite <- e. eapply stack_contains_valid_vertices.
        apply H. simpl. reflexivity. simpl. left. reflexivity.
      * rewrite P.F.add_neq_o in H1. eapply IHvalid_dfs_state. apply H1.
        auto.
    + destruct (O.eq_dec x v).
      * setoid_rewrite <- e. eapply stack_contains_valid_vertices.
        apply H. simpl. reflexivity. simpl. left. reflexivity.
      * rewrite P.F.add_neq_o in H1. eapply IHvalid_dfs_state. apply H1.
        auto.
    + eapply IHvalid_dfs_state. apply H1.
    + eapply IHvalid_dfs_state. apply H1.
    + eapply IHvalid_dfs_state. apply H1.
Qed. 

(*Once a vertex's discovery time has been set, it is never changed*)
Lemma discovery_time_constant_step: forall s s' g o v n,
  valid_dfs_state s g o ->
  M.find v (get_d_times s) = Some n ->
  dfs_step s s' ->
  M.find v (get_d_times s') = Some n.
Proof.
  intros. inversion H; subst.
  - simpl in H0. rewrite P.F.empty_o in H0. inversion H0.
  - inversion H1; subst; simpl in *; try (assumption).
    + remember (g0, f, f_times, d_times, time, remain_d, remain_f, (x, None) :: tl) as s.
      assert (exists n, M.find v (get_d_times s)  = Some n). rewrite Heqs. simpl. exists n. apply H0.
      rewrite discovered_vertex_not_remaining in H5. subst. simpl in H5.
      destruct (O.eq_dec x v).
      * setoid_rewrite e in H4. rewrite H5 in H4. inversion H4.
      * rewrite P.F.add_neq_o. apply H0. auto.
      * apply H.
      * eapply discovered_vertices_in_graph. apply H. rewrite Heqs; simpl. apply H0.
    + destruct (O.eq_dec x v).
      * setoid_rewrite e in H4. 
        remember (g0, t :: f, f_times, d_times, time, remain_d, remain_f, (x, Some y) :: tl) as s.
        assert (exists n, M.find v (get_d_times s) = Some n). exists n. subst; simpl.  apply H0. 
        rewrite discovered_vertex_not_remaining in H5. subst; simpl in *. rewrite H5 in H4. inversion H4.
        apply H. eapply remain_d_contains_valid_vertices. apply H. subst; simpl. apply H4.
      * rewrite F.add_neq_o. apply H0. auto.
Qed.

Lemma discovery_time_constant: forall s s' g o v n,
  valid_dfs_state s g o ->
  M.find v (get_d_times s) = Some n ->
  dfs_multi s s' ->
  M.find v (get_d_times s') = Some n.
Proof.
  intros. induction H1.
  - apply H0.
  - apply IHmulti. eapply step. apply H. apply H1. eapply discovery_time_constant_step.
    apply H. apply H0. apply H1.
Qed. 

