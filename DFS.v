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

(** ** Results about discovery times **)
(*In this section we prove several important results: namely that each vertex in the graph
  is assigned a discovery time that is fixed, and that a vertex has a discovery time
  iff it is no longer in remain_d*)

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

(*The add_to_stack function adds only vertices in the graph*)
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
    rewrite <- G.neighbors_set_2 in H.
    eapply G.contains_edge_2. apply H. apply Heqo.
  - simpl in H. destruct H.
Qed. 

Definition get_graph (s: state) :=
  match s with
  | (g, _, _, _, _, _, _, _) => g
  end.

(*The graph does not change between states*)
Lemma graph_is_constant: forall s g o,
  valid_dfs_state s g o ->
  get_graph s = g.
Proof.
  intros. induction H.
  - simpl. reflexivity.
  - inversion H0; subst; simpl in *; reflexivity.
Qed.

(*remain_d always contains only vertices in the graph g*)
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

(*Every vertex on the stack is in graph g*)
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

(*If a vertex has a discovery time, it is in the graph*)
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

(** ** Results about finish times **)

(*The analogues of the results for discovery times TODO: finish*)
Lemma finished_vertex_not_remaining: forall s g o v,
  valid_dfs_state s g o ->
  G.contains_vertex g v = true ->
  (exists n, (M.find v (get_f_times s) = Some n)) <-> S.mem v (get_remain_f s) = false.
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
  - inversion H0; subst; simpl in *; try (apply IHvalid_dfs_state; assumption; assumption).
    + destruct (O.eq_dec x v).
      * setoid_rewrite e. exists time. apply P.F.add_eq_o. reflexivity.
      * rewrite P2.Dec.F.remove_neq_b in H2. rewrite <- IHvalid_dfs_state in H2.
        rewrite P.F.add_neq_o. apply H2. auto.
        apply H1. auto.
Qed.

(*remain_d always contains only vertices in the graph g*)
Lemma remain_f_contains_valid_vertices: forall s g o v,
  valid_dfs_state s g o ->
  S.mem v (get_remain_f s) = true ->
  G.contains_vertex g v = true.
Proof.
  intros. generalize dependent v. induction H; intros.
  - simpl in H0. rewrite G.set_of_graph_1. apply S.mem_2. apply H0.
  - inversion H0; subst; simpl in *; try (apply IHvalid_dfs_state; assumption).
    + rewrite P2.Dec.F.remove_b in H1. rewrite andb_true_iff in H1. destruct H1.
      unfold P2.Dec.F.eqb in H4. destruct (O.eq_dec x v). inversion H4.
      apply IHvalid_dfs_state. apply H1.
Qed.

Lemma finished_vertices_in_graph: forall s g o v n,
  valid_dfs_state s g o ->
  M.find v (get_f_times s) = Some n ->
  G.contains_vertex g v = true.
Proof.
  intros. generalize dependent n. induction H; intros.
  - simpl in H0. rewrite F.empty_o in H0. inversion H0.
  - inversion H0; subst; simpl in *; try (eapply IHvalid_dfs_state; apply H1).
    destruct (O.eq_dec x v).
      * eapply remain_f_contains_valid_vertices. apply H.
      simpl. setoid_rewrite <- e. apply H3.
      * rewrite F.add_neq_o in H1. eapply IHvalid_dfs_state. apply H1.
        auto.
Qed.
(** ** The done condition **)

(*We are done if there are no more vertices to discover or finish*)
Definition done (s: state) : bool :=
  S.is_empty (get_remain_f s) && S.is_empty (get_remain_d s).

(*Alternately, we are done if there are no more vertices to finish*)
Definition done' (s: state) : bool :=
  S.is_empty (get_remain_f s).

(*If a vertex still has to be discovered, then it still has to be finished*)
Lemma vertex_in_finish_if_not_discovered: forall s g o,
  valid_dfs_state s g o ->
  (forall x, 
  S.mem x (get_remain_d s) = true ->
  S.mem x (get_remain_f s) = true).
Proof.
  intros. induction H.
  - unfold start_state in *; simpl in *. assumption.
  - inversion H1; subst; simpl in *.
    + apply IHvalid_dfs_state. apply S.mem_1. eapply S.remove_3.
      apply S.mem_2. apply H0.
    + assert (x <> x0). intro. subst. rewrite P2.FM.remove_b in H0. rewrite andb_true_iff in H0.
      destruct H0. unfold P2.FM.eqb in H3. destruct (O.eq_dec x0 x0). inversion H3. apply n.
      apply eq_refl. rewrite P2.Dec.F.remove_neq_b in H0. apply IHvalid_dfs_state.
      apply H0. auto.
    + assert (x <> x0). intro. subst. rewrite H2 in H0. inversion H0. rewrite P2.Dec.F.remove_neq_b.
      apply IHvalid_dfs_state. apply H0. auto.
    + apply IHvalid_dfs_state. apply H0.
    + apply IHvalid_dfs_state. apply H0.
Qed. 

(*A non empty set has at least one element*)
Lemma non_empty_set_has_elements: forall (s: S.t),
  (S.is_empty s) = false <-> exists x, S.In x s.
Proof.
  intros. split; intros.
  - assert (~S.Empty s). intro. apply S.is_empty_1 in H0. rewrite H0 in H. inversion H.
    assert (S.cardinal s <> 0). intro. apply P2.cardinal_inv_1 in H1. contradiction.
    apply P2.cardinal_inv_2b in H1. destruct H1. exists x. apply i.
  - destruct H. destruct (S.is_empty s) eqn : ?.
    + apply S.is_empty_2 in Heqb. apply P2.empty_is_empty_1 in Heqb.
      setoid_rewrite Heqb in H. apply P2.Dec.F.empty_iff in H. destruct H.
    + reflexivity.
Qed.

(*When all vertices are finished, all vertices have been discovered*)
Lemma finish_discover_before_finishing : forall (s: state) g o,
  valid_dfs_state s g o ->
  S.is_empty (get_remain_f s) = true ->
  S.is_empty (get_remain_d s) = true.
Proof.
  intros. destruct (S.is_empty (get_remain_d s)) eqn : ?.
  + reflexivity.
  + rewrite non_empty_set_has_elements in Heqb. destruct Heqb.
    apply S.mem_1 in H1. eapply vertex_in_finish_if_not_discovered in H1.
    apply S.mem_2 in H1. apply S.is_empty_2 in H0. apply P2.empty_is_empty_1 in H0.
    setoid_rewrite H0 in H1. apply P2.Dec.F.empty_iff in H1. destruct H1. apply H.
Qed.

Lemma done_done': forall s g o,
  valid_dfs_state s g o ->
  done s = done' s.
Proof.
  intros. unfold done. unfold done'. remember s as s'. destruct s. repeat(destruct p).
  simpl. assert (t = get_remain_f s'). subst; simpl; reflexivity. rewrite Heqs'.
  simpl. assert (t0 = get_remain_d s'). subst; simpl; reflexivity.
  destruct (S.is_empty t) eqn : ?.
  - apply finish_discover_before_finishing in H. rewrite <- H1 in H. rewrite H. reflexivity.
    rewrite <- H0. apply Heqb.
  - destruct (S.is_empty t0); reflexivity.
Qed. 

(*Some tactics for proving that sets with elements are nonempty*)

Lemma empty_set_no_elts: forall s x,
  S.is_empty s = true /\ S.mem x s = true -> False.
Proof.
  intros. destruct H. apply S.is_empty_2 in H. apply P2.empty_is_empty_1 in H.
      setoid_rewrite H in H0. rewrite P2.Dec.F.empty_b in H0. inversion H0.
Qed.

Ltac empty_set_mem :=
  match goal with
  | [H : S.is_empty ?s = true |- _] => 
    match goal with
    | [H1 : S.mem _ s = true |- _ ] =>
      exfalso; eapply empty_set_no_elts; split;
      try(apply H); try(apply H1)
    end
  end.

Ltac prove_set_empty :=
  match goal with
  | [H: S.mem _ ?s = true |- S.is_empty ?s = false] => destruct (S.is_empty s) eqn : A; try (empty_set_mem);
    try (reflexivity)
  end.

Ltac solve_set_empty :=
  try (empty_set_mem); try (prove_set_empty).

(** ** Properties of [add_to_stack] **)

(*Each tuple added to the stack contains the input vertex as its second element*)
Lemma add_to_stack_adds_parent: forall v g r x y,
  In (x,y) (add_to_stack v g r) ->
  y = Some v.
Proof.
  intros. unfold add_to_stack in H. destruct (G.neighbors_set g v).
  assert (forall x y l, In (x,y)(fold_right (fun (v0 : S.elt) (t : list (S.elt * option O.t)) => if S.mem v0 r then (v0, Some v) :: t else t)
         nil l) -> y = Some v). { intros. induction l; simpl in H0. destruct H0.
        destruct (S.mem a r). simpl in H0. destruct H0. inversion H0. reflexivity. apply IHl.
        apply H0. apply IHl. apply H0. }
  eapply H0. apply H. inversion H.
Qed.

(*If a vertex is added, it has not been discovered*)
Lemma only_add_yet_to_be_discovered: forall v g r x y,
  In (x,y) (add_to_stack v g r) ->
  S.mem x r = true.
Proof.
  intros. unfold add_to_stack in H. destruct (G.neighbors_set g v).
  assert (forall x y l, In (x, y)
      (fold_right (fun (v0 : S.elt) (t : list (S.elt * option O.t)) => if S.mem v0 r then (v0, Some v) :: t else t)
         nil l) -> S.mem x r = true). { intros. induction l; simpl in H0. destruct H0. destruct (S.mem a r) eqn : ?.
        simpl in H0. destruct H0. inversion H0; subst. apply Heqb. all: apply IHl; apply H0. }
  eapply H0. apply H. inversion H.
Qed.

(*Every vertex we add is a neighbor of the input vertex*)
Lemma only_add_neighbors: forall v g r x y,
  In (x,y) (add_to_stack v g r) ->
  G.contains_edge g v x = true.
Proof.
  intros. unfold add_to_stack in H. destruct (G.neighbors_set g v) eqn : ?.
  - assert (forall x y l, In (x, y)
      (fold_right (fun (v0 : S.elt) (t : list (S.elt * option O.t)) => if S.mem v0 r then (v0, Some v) :: t else t)
         nil (l)) -> In x l). { intros. induction l; simpl in H0. destruct H0. destruct (S.mem a r). simpl in H0.
      destruct H0. inversion H0; subst. simpl. left. reflexivity. simpl. right. apply IHl. apply H0.
      simpl. right. apply IHl. apply H0. }
    assert (In x (S.elements t)). eapply H0. apply H. clear H0. rewrite In_InA_equiv in H1.
    apply S.elements_2 in H1. rewrite <- G.neighbors_set_2 in H1. apply H1. apply Heqo.
    - inversion H.
Qed.

(*If a vertex is discovered but not yet finished, it is on the stack*)
Lemma vertices_not_finished_on_stack: forall s g o v,
  valid_dfs_state s g o ->
  S.mem v (get_remain_d s) = false ->
  S.mem v (get_remain_f s) = true ->
  (exists y, In (v, y) (get_stack s)).
Proof.
  intros. generalize dependent v. induction H; intros; subst; simpl in *.
  - rewrite H1 in H0. inversion H0.
  - inversion H0; subst; simpl in *.
    + destruct (O.eq_dec v x).
      * setoid_rewrite e. exists None. apply in_or_app. right. simpl. left. reflexivity.
      * rewrite P2.Dec.F.remove_neq_b in H1. apply IHvalid_dfs_state in H1. destruct H1.
        exists x0. apply in_or_app. right. simpl. apply H1. apply H2. auto.
    + destruct (O.eq_dec v x).
      * setoid_rewrite e. exists (Some y). apply in_or_app. right. simpl. left. reflexivity.
      * rewrite P2.Dec.F.remove_neq_b in H1. apply IHvalid_dfs_state in H1. destruct H1.
        exists x0. apply in_or_app. right. simpl. apply H1. apply H2. auto.
    + destruct (O.eq_dec v x).
      * setoid_rewrite <- e in H2. rewrite P2.FM.remove_b in H2. rewrite andb_true_iff in H2.
        destruct H2. unfold P2.FM.eqb in H5. destruct (O.eq_dec v v). inversion H5.
        exfalso. apply n. apply eq_refl.
      * rewrite P2.Dec.F.remove_neq_b in H2. apply IHvalid_dfs_state in H1. destruct H1.
        destruct H1. inversion H1; subst. exfalso. apply n. apply eq_refl. exists x0. apply H1.
        apply H2. auto.
    + destruct (O.eq_dec x v).
      * setoid_rewrite e in H4. rewrite H4 in H2. inversion H2.
      * apply IHvalid_dfs_state in H1. destruct H1. destruct H1. inversion H1; subst.
        exfalso. apply n. apply eq_refl. exists x0. apply H1. apply H2.
    + apply IHvalid_dfs_state in H1. destruct H1. destruct H1. apply H2.
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

(*Why we needed this set stuff: when stack is empty, same vertices left to be discovered and finished*)
Lemma empty_stack_no_gray: forall s g o,
  valid_dfs_state s g o ->
  get_stack s = nil ->
  S.Equal (get_remain_d s) (get_remain_f s).
Proof.
(*Idea: either the two sets are equal or not. If not, then there is one element in 1 that is not in another*)
(*This element cannot be in remain_f, since then it would have to be in remain_d. So there is an
  element in remain_d not in remain_f, by previous result, stack is nonempty, a contradiction*)
intros. apply S.equal_2. destruct (S.equal (get_remain_d s) (get_remain_f s)) eqn : ?.
 - reflexivity.
 - apply unequal_sets in Heqb. destruct Heqb.
  + destruct H1. destruct H1. apply P2.FM.mem_iff in H1. 
    destruct (S.mem x (get_remain_f s)) eqn : ?. apply P2.FM.mem_iff in Heqb.
    contradiction. eapply vertex_in_finish_if_not_discovered in H1. rewrite Heqb in H1.
    inversion H1. apply H.
  + destruct H1. destruct H1.  apply P2.FM.mem_iff in H2. destruct (S.mem x (get_remain_d s)) eqn : ?.
    apply P2.FM.mem_iff in Heqb. contradiction. eapply vertices_not_finished_on_stack in Heqb.
    rewrite H0 in Heqb. destruct Heqb. simpl in H3. destruct H3. apply H. apply H2.
Qed.

(*I'm sure this is in the standard library somewhere, but I didn't want to find it*)
Lemma contrapositive: forall (P Q: Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros. intro. apply H in H1. contradiction.
Qed.

(** ** Proving progress **)

(*We want to prove progress (a state can step iff it is not done). For various reasons, we need 
  the following seemingly unrelated lemmas*)

(*A really specific lemma: if the stack is nonempty, the forest is also nonempty (obviously we will
  have stronger results about the forest later *)
Lemma nempty_stack_forest: forall s g o x y,
  valid_dfs_state s g o ->
  In (x, Some y) (get_stack s) ->
  get_forest s <> nil.
Proof.
  intros. induction H; subst; simpl in *.
  - destruct o. destruct (G.contains_vertex g v). inversion H0. inversion H. inversion H.
    inversion H0. inversion H0.
  - inversion H1; subst; simpl in *.
    + intro. inversion H3.
    + intro. inversion H3.
    + apply IHvalid_dfs_state. right. apply H0.
    + apply IHvalid_dfs_state. right. apply H0.
    + destruct H0; inversion H0.
Qed.

(*We need one more result: That if we have a stack (x,o) :: (y, o') :: t, then x <> y (In other words,
  we never add the same vertex twice in a row to the stack). This turns out to be highly nontrivial to prove,
  and I need several stronger results.*)

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
  Forall (pair_lt (a,y))  (fold_right (fun (v0 : S.elt) (t : list (S.elt * option O.t)) => if S.mem v0 r then (v0, Some v) :: t else t) nil l)).
  { intros. induction l.
    - simpl. constructor.
    - simpl. inversion H; subst. destruct (S.mem a0 r). constructor. unfold pair_lt. apply H2.
      apply IHl. apply H3. apply IHl. apply H3. }
 assert (forall l, StronglySorted O.lt l ->
  StronglySorted pair_lt (fold_right (fun (v0 : S.elt) (t : list (S.elt * option O.t)) => if S.mem v0 r then (v0, Some v) :: t else t) nil l)).
  { intros. induction l.
    - simpl. constructor.
    - simpl. inversion H0; subst. destruct (S.mem a r). constructor.
      + apply IHl. apply H3.
      + apply H. apply H4.
      + apply IHl. apply H3. }
 destruct (G.neighbors_set) eqn : ?.
  - apply H0. apply Sorted_StronglySorted.  unfold Relations_1.Transitive. apply O.lt_trans.
    apply S.elements_3.
  - constructor.
Qed. 

(*A way to destruct equal appended lists. Basically, it outlines the possible
  ways two lists with the below structure could interact*)
Lemma split_app: forall A l1 l2 l3 l4 (x y z : A),
  l1++ x :: l2 = l3 ++ y :: z :: l4 ->
  (exists l, l1 = l3 ++ y :: z :: l) \/  (l1 = l3 ++ y :: nil /\ x = z) \/
  (l1 = l3 /\ x = y /\ l2 = z :: l4) \/ (exists  l,
    l2 = l ++ y :: z :: l4).
Proof.
  intros A l1. induction l1; intros.
  - simpl in *. destruct l3; simpl in *.
    + right. right. left. inversion H; subst. split; try (split); reflexivity.
    + right. right. right. inversion H; subst. exists l3. reflexivity.
  - destruct l3; simpl in *.
    + inversion H; subst. destruct l1; simpl in *.
      * inversion H2; subst. right. left. split; reflexivity.
      * inversion H2; subst. left. exists l1. reflexivity.
    + inversion H; subst. apply IHl1 in H2.
      destruct H2.
      * left. destruct H0. exists x0. rewrite H0. reflexivity.
      * destruct H0.
        -- right. left. destruct H0. split. rewrite H0. reflexivity. apply H1.
        -- destruct H0.
           ++ right. right. left. destruct H0. destruct H1. subst. split; try (split); reflexivity.
           ++ right. right. right. destruct H0. exists x0. apply H0.
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

(*The stronger claim: If two vertices appear consecutively anywhere in the stack,
  then they are not equal*)
Lemma no_vertex_twice_in_stack: forall s g o x y o' o'' t l1,
  valid_dfs_state s g o ->
  get_stack s = l1 ++ (x, o') :: (y, o'') :: nil ++ t ->
  x <> y.
Proof.
  intros. generalize dependent l1. revert x y o' o'' t. induction H; intros; subst; simpl in *.
  - destruct o. destruct (G.contains_vertex g v). destruct l1. inversion H0. inversion H0.
    symmetry in H2. apply app_eq_nil in H2. destruct H2. inversion H2. symmetry in H0.
    apply app_eq_nil in H0. destruct H0. inversion H0. symmetry in H0.
    apply app_eq_nil in H0. destruct H0. inversion H0.
  - inversion H0; subst; simpl in *.
    + apply split_app in H1. destruct H1.
      * destruct H1. assert (StronglySorted pair_lt (l1 ++ (x, o') :: (y, o'') :: x1)).
        rewrite <- H1. apply add_to_stack_sorted. apply sort_app in H3.
        destruct H3. inversion H4; subst. rewrite Forall_forall in H8.
        specialize (H8 (y, o'')). unfold pair_lt in H8.
        apply O.lt_not_eq. apply H8. simpl. left. reflexivity.
      * destruct H1.
        -- destruct H1. inversion H3; subst.
           assert (y <> x). eapply G.contains_edge_3. eapply only_add_neighbors. 
           rewrite H1. apply in_or_app. right. simpl. left. reflexivity. auto.
        -- destruct H1.
           ++ destruct H1. destruct H3. subst. eapply (IHvalid_dfs_state _ _ _ _ _ nil). simpl.
              rewrite H3.  reflexivity.
           ++ destruct H1. eapply (IHvalid_dfs_state _ _ o' o'' t ((x0, None) :: x1)).
              rewrite H1. simpl. reflexivity.
   + (*shouldnt copy and paste so much*)
      apply split_app in H1. destruct H1.
      * destruct H1. assert (StronglySorted pair_lt (l1 ++ (x, o') :: (y, o'') :: x1)).
        rewrite <- H1. apply add_to_stack_sorted. apply sort_app in H3.
        destruct H3. inversion H4; subst. rewrite Forall_forall in H8.
        specialize (H8 (y, o'')). unfold pair_lt in H8.
        apply O.lt_not_eq. apply H8. simpl. left. reflexivity.
      * destruct H1.
        -- destruct H1. inversion H3; subst.
           assert (y <> x). eapply G.contains_edge_3. eapply only_add_neighbors. 
           rewrite H1. apply in_or_app. right. simpl. left. reflexivity. auto.
        -- destruct H1.
           ++ destruct H1. destruct H3. subst. eapply (IHvalid_dfs_state _ _ _ _ _ nil). simpl.
              rewrite H3.  reflexivity.
           ++ destruct H1. eapply (IHvalid_dfs_state _ _ o' o'' t ((x0, Some y0) :: x1)).
              rewrite H1. simpl. reflexivity.
    + apply (IHvalid_dfs_state _ _ o' o'' t ((x0, o0) :: l1)). rewrite H1. simpl.
      reflexivity.
    + apply (IHvalid_dfs_state _ _ o' o'' t ((x0, y0) :: l1)). rewrite H1. simpl.
      reflexivity.
    + destruct l1. simpl in H1. inversion H1. inversion H1.
      pose proof (app_cons_not_nil l1 ((y, o'') :: t) (x, o') ).  rewrite <- H5 in H3. contradiction.
Qed.

(*In particular, this is true for vertices in the front of the stack*)
Corollary stack_beginning_different: forall s g o x y o' o'' t,
  valid_dfs_state s g o ->
  get_stack s = (x, o') :: (y, o'') :: t ->
  x <> y.
Proof.
  intros. eapply (no_vertex_twice_in_stack _ _ _ _ _ _ _ _ nil). apply H. simpl.
  apply H0.
Qed.

(*An important theorem: any valid state can step iff it is not done. This not only shows that our
  choice of the done property was a good one, but it ensures that the DFS relation will never get stuck. 
  The next goal is to prove that this sequence of states terminates in a done state*)
Lemma dfs_progress: forall s g o,
  valid_dfs_state s g o ->
  (exists s', dfs_step s s') <-> done' s = false.
Proof.
  intros. unfold done'. split; intros.
  - induction H.
    + unfold start_state in *; simpl. destruct o.
      * destruct (G.contains_vertex g v).
        -- destruct H0. inversion H; subst; try(solve_set_empty). rewrite andb_false_iff in H13. 
           destruct H13; assumption.
        -- destruct H0. inversion H; subst. apply S.min_elt_1 in H8. apply S.mem_1 in H8.
          solve_set_empty. 
      * destruct H0. inversion H; subst.  apply S.min_elt_1 in H8. apply S.mem_1 in H8.
        solve_set_empty. 
    + inversion H1; subst; simpl in *.
      * destruct H0. remember ((g0, f, f_times, d_times, time, remain_d, remain_f, (x, None) :: tl)) as s.
        assert (S.mem x (get_remain_d s) = true) by (subst; simpl; assumption).
        eapply vertex_in_finish_if_not_discovered in H3. subst; simpl in *. solve_set_empty. apply H.
      * destruct H0. remember ((g0, t :: f, f_times, d_times, time, remain_d, remain_f, (x, Some y) :: tl)) as s.
        assert (S.mem x (get_remain_d s) = true) by (subst; simpl; assumption).
        eapply vertex_in_finish_if_not_discovered in H3. subst; simpl in *. solve_set_empty. apply H.
      * destruct H0. destruct (S.is_empty (S.remove x remain_f)) eqn : A.
        -- inversion H0; subst; simpl in *. 
           ++ assert (x <> x1). intro. subst. rewrite H13 in H2. inversion H2.
           remember ((g0, f, f_times, d_times, time, remain_d, remain_f, (x, o0) :: (x1, None) :: tl0)) as s'.
           assert (S.mem x1 (get_remain_d s') = true) by (subst; simpl; assumption).
           eapply vertex_in_finish_if_not_discovered in H5. subst; simpl in *.
           pose proof (@P2.Dec.F.remove_neq_b remain_f x x1). apply H6 in H4. rewrite H5 in H4.
            solve_set_empty. apply H.
           ++ assert (x <> x1). intro. subst. rewrite H13 in H2. inversion H2.
           remember (g0, t :: f0, f_times, d_times, time, remain_d, remain_f, (x, o0) :: (x1, Some y) :: tl0) as s'.
           assert (S.mem x1 (get_remain_d s') = true) by (subst; simpl; assumption).
           eapply vertex_in_finish_if_not_discovered in H5. subst; simpl in *.
           pose proof (@P2.Dec.F.remove_neq_b remain_f x x1). apply H6 in H4. rewrite H5 in H4.
            solve_set_empty. rewrite Heqs'. apply H.
          ++ solve_set_empty.
          ++ rewrite andb_false_iff in H15. destruct H15. rewrite non_empty_set_has_elements in H4.
            destruct H4. apply S.mem_1 in H4.
            remember ((g0, f, f_times, d_times, time, remain_d, remain_f, (x, o0) :: (x1, y) :: tl0)) as s'.
            assert (S.mem x0 (get_remain_d s') = true) by (subst; simpl; assumption).
            eapply vertex_in_finish_if_not_discovered in H5. subst; simpl in *.
            destruct (O.eq_dec x x0).
            ** setoid_rewrite <- e in H4. rewrite H4 in H2. inversion H2.
            ** rewrite <- (@P2.FM.remove_neq_b _ x x0) in H5. solve_set_empty. auto.
            ** apply H.
            ** rewrite H4 in A. inversion A.
        ++ apply S.min_elt_1 in H13. apply S.mem_1 in H13. assert (min <> x).
          intro. subst. rewrite H13 in H2. inversion H2.
          remember ((g0, f, f_times, d_times, time, remain_d, remain_f, (x, o0) :: nil)) as s'.
          assert (S.mem min (get_remain_d s') = true) by (subst; simpl; assumption).
          eapply vertex_in_finish_if_not_discovered in H5. subst; simpl in *.
          rewrite <- (@P2.FM.remove_neq_b _ x min) in H5. solve_set_empty. auto. rewrite Heqs'.
          apply H.
      -- reflexivity.
      * rewrite andb_false_iff in H4. destruct H4.
        remember (g0, f, f_times, d_times, time, remain_d, remain_f, (x, y) :: tl) as s'.
        assert (S.is_empty (get_remain_d s') = false) by (subst; simpl; assumption).
        pose proof (finish_discover_before_finishing _ _ _ H).
        apply contrapositive in H6. subst; simpl in *. destruct (S.is_empty remain_f).
        contradiction. reflexivity. rewrite H5. auto. apply H4.
      * apply S.min_elt_1 in H2. apply S.mem_1 in H2. 
        remember (g0, f, f_times, d_times, time, remain_d, remain_f, nil) as s'.
        assert (S.mem min (get_remain_d s') = true) by (subst; simpl; assumption).
        eapply vertex_in_finish_if_not_discovered in H3. subst; simpl in *. solve_set_empty.
        apply H.
  - inversion H; subst; simpl in *.
    + unfold start_state in *. destruct o.
      * destruct (G.contains_vertex g v) eqn : ?.
        -- exists (g, (T.singleton v) :: nil, M.empty nat, (M.add v 0 (M.empty nat)), 1, (S.remove v (G.set_of_graph g)),
           (G.set_of_graph g), (add_to_stack v g (G.set_of_graph g)) ++ (v, None) :: nil).
            apply dfs_discover_root. apply S.mem_1. apply G.set_of_graph_1 in Heqb. apply Heqb.
        -- destruct (S.min_elt (G.set_of_graph g)) eqn : ?. 
          ++ exists (g, @nil tree, M.empty nat, M.empty nat, 0, G.set_of_graph g, G.set_of_graph g, 
           (e, None)::nil). apply dfs_new_cc. apply Heqo.
          ++ apply S.min_elt_3 in Heqo. apply S.is_empty_1 in Heqo. rewrite Heqo in H0. inversion H0.
      * destruct (S.min_elt (G.set_of_graph g)) eqn : ?. 
          ++ exists (g, @nil tree, M.empty nat, M.empty nat, 0, G.set_of_graph g, G.set_of_graph g, 
           (e, None)::nil). apply dfs_new_cc. apply Heqo.
          ++ apply S.min_elt_3 in Heqo. apply S.is_empty_1 in Heqo. rewrite Heqo in H0. inversion H0.
    + inversion H2; subst; simpl in *.
      * destruct (add_to_stack x g0 remain_d) eqn : ?.
        -- simpl. econstructor. apply dfs_finish. rewrite P2.Dec.F.remove_b. rewrite H3.
            simpl. unfold P2.Dec.F.eqb. destruct (O.eq_dec x x). reflexivity. exfalso.
            apply n. apply eq_refl.
            remember (g0, f, f_times, d_times, time, remain_d, remain_f, (x, None) :: tl) as s'.
            assert (S.mem x (get_remain_d s') = true) by (subst; simpl; assumption).
            eapply vertex_in_finish_if_not_discovered in H4. subst; simpl in *. apply H4. apply H1.
        -- simpl. destruct p. assert (o0 = Some x). eapply add_to_stack_adds_parent. 
            rewrite Heqs. simpl. left. reflexivity. rewrite H4.
            econstructor. apply dfs_discover_child. assert (x <> t). { eapply G.contains_edge_3.
            eapply only_add_neighbors. rewrite Heqs. simpl. left. reflexivity. }
            rewrite P2.Dec.F.remove_neq_b. eapply only_add_yet_to_be_discovered.
            rewrite Heqs. simpl. left. reflexivity. apply H5. 
      * destruct (add_to_stack x g0 remain_d) eqn : ?.
        -- simpl. econstructor. apply dfs_finish. rewrite P2.Dec.F.remove_b. rewrite H3.
            simpl. unfold P2.Dec.F.eqb. destruct (O.eq_dec x x). reflexivity. exfalso.
            apply n. apply eq_refl.
            remember (g0, t :: f, f_times, d_times, time, remain_d, remain_f, (x, Some y) :: tl) as s'.
            assert (S.mem x (get_remain_d s') = true) by (subst; simpl; assumption).
            eapply vertex_in_finish_if_not_discovered in H4. subst; simpl in *. apply H4. apply H1.
        -- simpl. destruct p. assert (o0 = Some x). eapply add_to_stack_adds_parent. 
            rewrite Heqs. simpl. left. reflexivity. rewrite H4.
            econstructor. apply dfs_discover_child. assert (x <> t0). { eapply G.contains_edge_3.
            eapply only_add_neighbors. rewrite Heqs. simpl. left. reflexivity. }
            rewrite P2.Dec.F.remove_neq_b. eapply only_add_yet_to_be_discovered.
            rewrite Heqs. simpl. left. reflexivity. apply H5.
      * destruct tl.
        -- remember (g0, f, M.add x time f_times, d_times, time + 1, remain_d, S.remove x remain_f, nil) as s'.
            assert (S.Equal (get_remain_d s') (get_remain_f s')). { eapply empty_stack_no_gray.
            apply H. subst. simpl. reflexivity. } subst; simpl in *. setoid_rewrite <- H5 in H0.
            destruct (S.min_elt remain_d) eqn : ?. econstructor. apply dfs_new_cc. apply Heqo1.
            apply S.min_elt_3 in Heqo1. apply S.is_empty_1 in Heqo1. rewrite Heqo1 in H0. inversion H0.
        -- destruct p. destruct (S.mem e remain_d) eqn : ?.
          ++ destruct o1.
            ** assert (f <> nil). 
              remember (g0, f, f_times, d_times, time, remain_d, remain_f, (x, o0) :: (e, Some t) :: tl) as s'.
              assert (f = get_forest s') by (subst; simpl; reflexivity). rewrite H5.
              eapply nempty_stack_forest. apply H1.
               subst; simpl. right. left. reflexivity.
              destruct f. contradiction. econstructor. apply dfs_discover_child. apply Heqb.
            ** econstructor. apply dfs_discover_root. apply Heqb.
          ++ destruct (S.mem e remain_f) eqn : ?.
            ** econstructor. apply dfs_finish. apply Heqb. rewrite P2.Dec.F.remove_neq_b. apply Heqb0.
               eapply stack_beginning_different. apply H1. simpl.
                reflexivity.
            ** econstructor. apply dfs_done_already. apply Heqb. rewrite P2.Dec.F.remove_neq_b.
               apply Heqb0. eapply stack_beginning_different. apply H1. simpl. reflexivity.
               rewrite andb_false_iff. right. apply H0.
      * destruct tl.
        -- pose proof empty_stack_no_gray. specialize (H6 _ _ _ H). simpl in H6.
           assert (S.Equal remain_d remain_f) by (apply H6; reflexivity). clear H6.
           setoid_rewrite <- H7 in H0. destruct (S.min_elt remain_d) eqn : ?.
           econstructor. apply dfs_new_cc. apply Heqo0. apply S.min_elt_3 in Heqo0. 
            apply S.is_empty_1 in Heqo0. rewrite Heqo0 in H0. inversion H0.
        -- destruct p. destruct (S.mem e remain_d) eqn : ?.
           ++ destruct o0.
              ** assert (f <> nil). 
                 remember (g0, f, f_times, d_times, time, remain_d, remain_f, (e, Some t) :: tl) as s'.
                  assert (f = get_forest s') by (subst; simpl; reflexivity). rewrite H6.
                  eapply nempty_stack_forest. apply H. rewrite Heqs'. simpl. left. reflexivity.
                  destruct f. contradiction. econstructor. apply dfs_discover_child. apply Heqb.
              ** econstructor. apply dfs_discover_root. apply Heqb.
            ++ destruct (S.mem e remain_f) eqn : ?.
                ** econstructor. apply dfs_finish. apply Heqb. apply Heqb0.
                ** econstructor. apply dfs_done_already. apply Heqb. apply Heqb0. apply H5.
        * econstructor. apply dfs_discover_root. apply S.min_elt_1 in H3. apply S.mem_1. apply H3.
Qed.

(*The termination argument*)

(*We define the following measure_dfs (the total number of vertices we have to discover plus
  the total number of vertices we have to finish) and then prove that every valid state multisteps
  to a state with strictly smaller measure. We need this somewhat convoluted way of proving this
  because some states, such as dfs_already_finished, do not actually change the measure, so we
  must show that eventually they will step to a state with a smaller measure. With this (large)
  lemma, the actual termination argument is simple. We prove that every valid dfs state
  multisteps to a state that is done, proving that this procedure terminates*)

Definition measure_dfs (s: state) :=
  S.cardinal (get_remain_d s) + S.cardinal (get_remain_f s).

Lemma done_size_zero:
  forall s g o,
  valid_dfs_state s g o ->
  done' s = true <-> measure_dfs s = 0.
Proof.
  intros. split; intros; unfold measure_dfs in *.
  - erewrite <- done_done' in H0. unfold done in H0.
    rewrite andb_true_iff in H0. destruct H0. apply S.is_empty_2 in H0. apply S.is_empty_2 in H1.
    apply P2.cardinal_1 in H0. apply P2.cardinal_1 in H1. rewrite H0. rewrite H1. omega.
    apply H.
  - apply plus_is_O in H0. destruct H0. apply P2.cardinal_inv_1 in H0. apply P2.cardinal_inv_1 in H1.
    erewrite <- done_done'. unfold done. rewrite andb_true_iff. split; apply S.is_empty_1; assumption.
    apply H.
Qed.

(*Tactics for proving that a set that we remove something from is smaller than the original set*)
Ltac prove_in_set x s :=
  match goal with
  | [H : S.min_elt s = Some x |- _] => apply S.min_elt_1; apply H
  | [H: S.mem x s = true |- _ ] => apply S.mem_2; apply H
  | [H: S.In x s |- _] => apply H
  | [H: _ |- _] => auto
  end. 

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

(*The main lemma: any state that is not finished multisteps to some state with strictly smaller
  measure. Large parts of this proof are similar to progress TODO: maybe fix that or improve the proof*)
Lemma not_done_multisteps_to_smaller: 
  forall s g o,
  valid_dfs_state s g o ->
  done' s = false ->
  exists s', dfs_multi s s' /\ measure_dfs s' < measure_dfs s.
Proof.
  intros. unfold done' in H0. unfold measure_dfs. remember (get_stack s) as l. generalize dependent s. induction l; intros; subst; simpl in *.
  - inversion H; subst; simpl in *.
    + unfold start_state in *; simpl in *. destruct o. destruct (G.contains_vertex g v). inversion Heql.
      * destruct (S.min_elt (G.set_of_graph g)) eqn : ?.
        -- econstructor. split. eapply multi_trans. apply multi_R. apply dfs_new_cc. apply Heqo.
           apply multi_R. apply dfs_discover_root. apply S.mem_1. apply S.min_elt_1. apply Heqo. simpl.
           size_of_remove.
        -- apply S.min_elt_3 in Heqo. apply S.is_empty_1 in Heqo. rewrite Heqo in H0. inversion H0.
      * destruct (S.min_elt (G.set_of_graph g)) eqn : ?.
        -- econstructor. split. eapply multi_trans. apply multi_R. apply dfs_new_cc. apply Heqo.
           apply multi_R. apply dfs_discover_root. apply S.mem_1. apply S.min_elt_1. apply Heqo. simpl.
           size_of_remove.
        -- apply S.min_elt_3 in Heqo. apply S.is_empty_1 in Heqo. rewrite Heqo in H0. inversion H0.
    + inversion H2; subst; simpl in *; subst.
      * pose proof (app_cons_not_nil (add_to_stack x g0 remain_d) tl (x, None)). contradiction.
      * pose proof (app_cons_not_nil (add_to_stack x g0 remain_d) tl (x, Some y)). contradiction.
      * remember (g0, f, M.add x time f_times, d_times, time + 1, remain_d, S.remove x remain_f, nil) as s'.
        assert (S.Equal (get_remain_d s') (get_remain_f s')). { eapply empty_stack_no_gray. eapply step.
        apply H1. apply H2. subst; reflexivity. }
        subst; simpl in *. setoid_rewrite <- H5 in H0.
        destruct (S.min_elt remain_d) eqn : ?.
        -- econstructor. split. eapply multi_trans. apply multi_R. apply dfs_new_cc. apply Heqo1.
           apply multi_R. apply dfs_discover_root. apply S.min_elt_1 in Heqo1. apply S.mem_1. apply Heqo1.
           simpl. size_of_remove. 
        -- apply S.min_elt_3 in Heqo1. apply S.is_empty_1 in Heqo1. rewrite Heqo1 in H0. inversion H0.
      * remember (g0, f, f_times, d_times, time, remain_d, remain_f, nil) as s'.
        assert (S.Equal (get_remain_d s') (get_remain_f s')). { eapply empty_stack_no_gray. eapply step.
        apply H1. apply H2. subst; reflexivity. }
        subst; simpl in *. setoid_rewrite <- H6 in H0.
        destruct (S.min_elt remain_d) eqn : ?.
        -- econstructor. split. eapply multi_trans. apply multi_R. apply dfs_new_cc. apply Heqo0.
           apply multi_R. apply dfs_discover_root. apply S.min_elt_1 in Heqo0. apply S.mem_1. apply Heqo0.
           simpl. size_of_remove. 
        -- apply S.min_elt_3 in Heqo0. apply S.is_empty_1 in Heqo0. rewrite Heqo0 in H0. inversion H0.
      * econstructor. split. apply multi_R. apply dfs_discover_root. apply S.min_elt_1 in H3. apply S.mem_1. apply H3.
        simpl. size_of_remove.
  - inversion H; subst; simpl in *.
    + unfold start_state in *; simpl in *. destruct o. destruct (G.contains_vertex g v) eqn : ?.
      * inversion Heql; subst. econstructor. split. apply multi_R. apply dfs_discover_root.
        apply S.mem_1. apply G.set_of_graph_1. apply Heqb. simpl. apply G.set_of_graph_1 in Heqb. size_of_remove.
      * inversion Heql.
      * inversion Heql.
    + inversion H2; subst; simpl in *; subst.
      * assert (S.mem x remain_f = true). {
        remember ((g0, f, f_times, d_times, time, remain_d, remain_f, (x, None) :: tl)) as s'.
        assert (S.mem x (get_remain_d s') = true) by (subst; simpl; assumption). 
        eapply vertex_in_finish_if_not_discovered in H4. subst; simpl; apply H4. apply H1. }
        destruct (add_to_stack x g0 remain_d) eqn : ?.
        -- simpl. econstructor. split. apply multi_R. apply dfs_finish. rewrite P2.Dec.F.remove_b.
          rewrite andb_false_iff. right. unfold P2.Dec.F.eqb. destruct (O.eq_dec x x). reflexivity.
          exfalso. apply n. apply eq_refl. apply H4. 
          simpl. size_of_remove. 
        -- simpl. destruct p. assert (In (t, o0) (add_to_stack x g0 remain_d )). rewrite Heqs.
          simpl. left. reflexivity. assert (o0 = Some x). eapply add_to_stack_adds_parent. apply H5.
          subst. assert (x <> t). eapply G.contains_edge_3. eapply only_add_neighbors. apply H5.
          econstructor. split. apply multi_R. apply dfs_discover_child. rewrite P2.Dec.F.remove_neq_b.
          eapply only_add_yet_to_be_discovered. apply H5. apply H6. simpl.
          assert (S.mem t (S.remove x remain_d) = true). rewrite P2.Dec.F.remove_neq_b. eapply only_add_yet_to_be_discovered. apply H5.
          apply H6. size_of_remove.
       * assert (S.mem x remain_f = true). {
        remember (g0, t :: f, f_times, d_times, time, remain_d, remain_f, (x, Some y) :: tl) as s'.
        assert (S.mem x (get_remain_d s') = true) by (subst; simpl; assumption). 
        eapply vertex_in_finish_if_not_discovered in H4. subst; simpl; apply H4. apply H1. }
        destruct (add_to_stack x g0 remain_d) eqn : ?.
        -- simpl. econstructor. split. apply multi_R. apply dfs_finish. rewrite P2.Dec.F.remove_b.
          rewrite andb_false_iff. right. unfold P2.Dec.F.eqb. destruct (O.eq_dec x x). reflexivity.
          exfalso. apply n. apply eq_refl. apply H4. 
          simpl. size_of_remove. 
        -- simpl. destruct p. assert (In (t0, o0) (add_to_stack x g0 remain_d )). rewrite Heqs.
          simpl. left. reflexivity. assert (o0 = Some x). eapply add_to_stack_adds_parent. apply H5.
          subst. assert (x <> t0). eapply G.contains_edge_3. eapply only_add_neighbors. apply H5.
          econstructor. split. apply multi_R. apply dfs_discover_child. rewrite P2.Dec.F.remove_neq_b.
          eapply only_add_yet_to_be_discovered. apply H5. apply H6. simpl.
          assert (S.mem t0 (S.remove x remain_d) = true). rewrite P2.Dec.F.remove_neq_b. eapply only_add_yet_to_be_discovered. apply H5.
          apply H6. size_of_remove.
     * destruct a. destruct (S.mem t remain_d) eqn : ?.
        -- destruct o1.
          ** assert (f <> nil). 
              remember (g0, f, f_times, d_times, time, remain_d, remain_f, (x, o0) :: (t, Some t0) :: l) as s'.
              assert (f = get_forest s') by (subst; simpl; reflexivity). rewrite H5.
              eapply nempty_stack_forest. apply H1.
               subst; simpl. right. left. reflexivity.
              destruct f. contradiction. econstructor. split. apply multi_R. apply dfs_discover_child. apply Heqb.
              simpl. size_of_remove. 
          ** econstructor. split. apply multi_R. apply dfs_discover_root. apply Heqb. simpl. size_of_remove.
         -- destruct (S.mem t remain_f) eqn : ?.
            ** assert (x <> t). eapply stack_beginning_different. apply H1. simpl. reflexivity. econstructor.
                split. apply multi_R. apply dfs_finish. apply Heqb. rewrite P2.Dec.F.remove_neq_b. apply Heqb0.
                apply H5. simpl.  assert (S.mem t (S.remove x remain_f) = true). rewrite P2.Dec.F.remove_neq_b.
               apply Heqb0. apply H5. size_of_remove.
            ** remember (g0, f, M.add x time f_times, d_times, time + 1, remain_d, S.remove x remain_f, (t, o1) :: l) as s'.
               assert (dfs_step s' (g0, f, M.add x time f_times, d_times, time + 1, remain_d, S.remove x remain_f, l)).
               subst. apply dfs_done_already. apply Heqb. rewrite P2.Dec.F.remove_neq_b. apply Heqb0.
               eapply stack_beginning_different. apply H1. simpl. reflexivity. rewrite andb_false_iff.
               right. apply H0. 
               remember (g0, f, M.add x time f_times, d_times, time + 1, remain_d, S.remove x remain_f, l) as s''.
               specialize (IHl s''). assert (valid_dfs_state s'' g o). eapply step. apply H. subst. apply H5.
                specialize (IHl H6). rewrite Heqs'' in IHl; simpl in IHl. specialize (IHl H0).
                destruct IHl. reflexivity. destruct H7. econstructor. split. eapply multi_trans. apply multi_R.
               apply dfs_done_already. apply Heqb. rewrite P2.Dec.F.remove_neq_b. apply Heqb0.
               eapply stack_beginning_different. apply H1. simpl. reflexivity. rewrite andb_false_iff.
               right. apply H0.  apply H7. apply H8.
      * destruct a. assert (x <> t). eapply stack_beginning_different. apply H1. simpl. reflexivity.
        destruct (S.mem t remain_d) eqn : ?.
        --  destruct o0.
          ** assert (f <> nil). 
              remember (g0, f, f_times, d_times, time, remain_d, remain_f, (x, y) :: (t, Some t0) :: l) as s'.
              assert (f = get_forest s') by (subst; simpl; reflexivity). rewrite H7.
              eapply nempty_stack_forest. apply H1.
               subst; simpl. right. left. reflexivity.
              destruct f. contradiction. econstructor. split. apply multi_R. apply dfs_discover_child. apply Heqb.
              simpl. size_of_remove. 
          ** econstructor. split. apply multi_R. apply dfs_discover_root. apply Heqb. simpl. size_of_remove.
         -- destruct (S.mem t remain_f) eqn : ?.
            ** econstructor. split. apply multi_R. apply dfs_finish. apply Heqb. apply Heqb0. 
               simpl. size_of_remove.  
            ** remember (g0, f, f_times, d_times, time, remain_d, remain_f, (t, o0) :: l) as s'.
               remember (g0, f, f_times, d_times, time, remain_d, remain_f, l) as s''.
               assert (dfs_step s' s'').
               subst. apply dfs_done_already. apply Heqb. apply Heqb0. apply H5.
               specialize (IHl s''). assert (valid_dfs_state s'' g o). eapply step. apply H. subst. apply H7.
                specialize (IHl H8). rewrite Heqs'' in IHl; simpl in IHl. specialize (IHl H0).
                destruct IHl. reflexivity. destruct H9. econstructor. split. eapply multi_trans. apply multi_R.
               apply dfs_done_already. apply Heqb. apply Heqb0. apply H5. apply H9. apply H10.
      * econstructor. split. apply multi_R. apply dfs_discover_root. apply S.min_elt_1 in H3. apply S.mem_1. apply H3.
        simpl. size_of_remove.
Qed.

(*Now we can prove what we want: every state multisteps to a state with measure 0*)

(*We need strong induction*)
Lemma all_step_to_measure_zero: forall s g o,
  valid_dfs_state s g o ->
  exists s', dfs_multi s s' /\ measure_dfs s' = 0.
Proof.
  intros. remember (measure_dfs s) as n. generalize dependent s.
  induction n as [ n IHn ] using (well_founded_induction lt_wf).
  intros. destruct (done' s) eqn : ?.
  - exists s. split. apply multi_refl. rewrite <- done_size_zero. apply Heqb.
    apply H.
  - assert (A:=H). apply not_done_multisteps_to_smaller in H. destruct H.
    destruct H. specialize (IHn (measure_dfs x)). subst. specialize (IHn H0).
    specialize (IHn x). assert (valid_dfs_state x g o). eapply multistep_preserves_valid.
    apply A. apply H. specialize (IHn H1). destruct IHn. reflexivity.
    exists x0. split. eapply multi_trans. apply H. apply H2. apply H2. apply Heqb.
Qed.

(*Finally, what we want to show is a simple corollary: any valid DFS state multisteps to a finished state*)
Lemma all_states_terminate: forall s g o,
  valid_dfs_state s g o ->
  exists s', dfs_multi s s' /\ done' s' = true.
Proof.
  intros. pose proof (all_step_to_measure_zero s g o H). destruct H0. exists x.
  split. apply H0. rewrite done_size_zero. apply H0. eapply multistep_preserves_valid. apply H. apply H0.
Qed.

(*In particular, for any graph and any start vertex, DFS terminates*)
Lemma all_start_states_terminate: forall g o,
  exists s', dfs_multi (start_state g o) s' /\ done' s' = true.
Proof.
  intros. eapply all_states_terminate. constructor.
Qed.

Print state.
Print exist.
Locate "{ _ : _ | _ }".
Print sig.
Print exist.
Lemma zgtz : 0 > 0 -> False.
omega. Qed.
(*
Program Fixpoint pred_strong2 g o (H : {n : state | valid_dfs_state n g o})  : nat :=
  match H with
    | exist _ (s) _ => get_time s
  end.*)
Require Import Coq.Program.Wf.

Fixpoint pop_off_stack (s: stack) (remaining: S.t) : stack :=
  match s with
  | nil => nil
  | (v,p) :: t => if (negb (S.mem v remaining)) then pop_off_stack t remaining
                  else s
  end.
Print forallb.
Lemma pop_off_stack_off: forall s r,
  exists l1, s = l1 ++ pop_off_stack s r  /\ forallb (fun (x: O.t * option O.t) => 
  let (a,b) := x in negb (S.mem a r)) l1 = true.
Proof.
  intros. induction s.
  - simpl. exists nil. split. reflexivity. simpl. reflexivity.
  - simpl. destruct a. destruct (negb (S.mem t r)) eqn : ?.
    + destruct IHs. exists ((t,o) :: x). split. destruct H. rewrite H at 1. reflexivity.
      simpl. rewrite Heqb. destruct H. rewrite H0. reflexivity.
    + exists nil. split; reflexivity.
Qed. 

Lemma pop_off_stack_on: forall s r x y t,
  pop_off_stack s r = (x,y) :: t ->
  S.mem x r = true.
Proof.
 intro. induction s; intros.
  - simpl in H. inversion H.
  - simpl in H. destruct a. destruct (S.mem t0 r) eqn : ?.
    + simpl in H. inversion H; subst. apply Heqb.
    + simpl in H. eapply IHs. apply H.
Qed.

Lemma pop_multi: forall g d_times f_times n remain_d remain_f f st g' o,
  valid_dfs_state (g, f, f_times, d_times, n, remain_d, remain_f, st) g' o ->
  done (g, f, f_times, d_times, n, remain_d, remain_f, st) = false ->
  dfs_multi (g, f, f_times, d_times, n, remain_d, remain_f, st)
   (g, f, f_times, d_times, n, remain_d, remain_f, pop_off_stack st remain_f).
Proof.
  intros. induction st.
  - simpl in *. apply multi_refl.
  - simpl. destruct a. destruct (S.mem t remain_f) eqn : ?.
    + simpl. apply multi_refl.
    + remember (g, f, f_times, d_times, n, remain_d, remain_f, (t, o0) :: st) as s.
      remember (g, f, f_times, d_times, n, remain_d, remain_f, st) as s'.
      assert (dfs_step s s'). rewrite Heqs. rewrite Heqs'. apply dfs_done_already. 
      assert (S.mem t (get_remain_f s) = false) by (subst; simpl; assumption).
      pose proof vertex_in_finish_if_not_discovered. specialize (H2 s g o).
      rewrite Heqs in H2; simpl in H2.
      assert (g = g'). assert (g = get_graph s) by (subst; reflexivity). 
      rewrite H3. rewrite Heqs. eapply graph_is_constant. apply H. subst.
      specialize (H2 H t).
      apply contrapositive in H2. destruct (S.mem t remain_d) eqn : ?. contradiction. reflexivity.
      intro. rewrite H3 in Heqb. inversion Heqb. apply Heqb. unfold done in H0. simpl in H0.
      rewrite andb_comm. apply H0.
      simpl. eapply multi_trans. apply multi_R. subst. apply H1.
      subst. apply IHst. eapply step. apply H. apply H1. unfold done in *; simpl in *. apply H0.
Qed. 


Lemma pop_pres_valid: forall g d_times f_times n remain_d remain_f f st g' o,
  done (g, f, f_times, d_times, n, remain_d, remain_f, st) = false ->
  valid_dfs_state (g, f, f_times, d_times, n, remain_d, remain_f, st) g' o ->
  valid_dfs_state (g, f, f_times, d_times, n, remain_d, remain_f, pop_off_stack st remain_f) g' o.
Proof.
  intros. eapply multistep_preserves_valid. apply H0. eapply pop_multi. apply H0. apply H.
Qed.


Lemma invalid_state: forall (s: state) g o,
  valid_dfs_state s g o ->
  ~ valid_dfs_state s g o ->
  False.
Proof.
  intros. contradiction.
Qed.

Definition dfs_helper (s : state) : state  :=
  match s with
  | (g, f, f_times, d_times, n, remain_d, remain_f, nil) =>
    match S.min_elt remain_d with
    | None => s
    | Some min => (g, (T.singleton min :: f), f_times, M.add min n d_times, n+1, 
          S.remove min remain_d, remain_f, (add_to_stack min g remain_d) ++ (min, None) :: nil)
    end
  | (g, f, f_times, d_times, n, remain_d, remain_f, (x, None) :: tl) =>
    if bool_dec (S.mem x remain_d) true then
        (g, (T.singleton x :: f), f_times, M.add x n d_times, n+1, S.remove x remain_d,
        remain_f, (add_to_stack x g remain_d) ++ (x, None) :: tl)
    (*The condition is not strictly needed but it makes the proof simpler for now and doesn't make
      a difference*)
    else if bool_dec (S.mem x remain_f) true then
      (g, f, M.add x n f_times, d_times, n+1, remain_d, S.remove x remain_f, tl)
    else if  negb (done s) then
      (g, f, f_times, d_times, n, remain_d, remain_f, (pop_off_stack ((x, None) :: tl) remain_f))
    else s
  |(g, t :: f, f_times, d_times, n, remain_d, remain_f, (x, Some y) :: tl) =>
    if bool_dec (S.mem x remain_d) true then
        (g, (T.add_child t y x) :: f, f_times, M.add x n d_times, n+1,  
        S.remove x remain_d, remain_f, (add_to_stack x g remain_d) ++ (x,Some y) :: tl)
    else if bool_dec (S.mem x remain_f) true then
        (g, t :: f, M.add x n f_times, d_times, n+1, remain_d, S.remove x remain_f, tl)
    else if  negb (done s) then
      (g, t :: f, f_times, d_times, n, remain_d, remain_f, (pop_off_stack ((x, Some y) :: tl) remain_f))
    else s
  (*Impossible*)
  | _ => s
  end.

Lemma dfs_helper_multisteps: forall s g o,
  valid_dfs_state s g o ->
  dfs_multi s (dfs_helper s).
Proof.
  intros. unfold dfs_helper. destruct s. repeat( destruct p). destruct f.
  - destruct s.
    + destruct (S.min_elt t0) eqn : ?.
      * eapply multi_trans; apply multi_R. apply dfs_new_cc. apply Heqo0.
        apply dfs_discover_root. apply S.mem_1. apply S.min_elt_1. assumption.
      * apply multi_refl.
    + destruct p. destruct o0.
      * apply multi_refl.
      * destruct (S.mem t3 t0) eqn : ?; simpl.
        -- apply multi_R. apply dfs_discover_root. apply Heqb.
        -- destruct (bool_dec (S.mem t3 t)).
           ++ apply multi_R.  apply dfs_finish; assumption.
           ++ remember (g0, @nil tree, t2, t1, n, t0, t, (t3, None) :: s) as s'.
              setoid_rewrite <- Heqs'. destruct (done s') eqn : ?; simpl.
              ** subst. apply multi_refl. 
              ** destruct (S.mem t3 t) eqn : ?; simpl.
                --- subst; apply multi_refl.
                --- remember  (g0, @nil tree, t2, t1, n, t0, t,  s) as s''.
                    assert (dfs_step s' s''). subst. unfold done in *; simpl in *.
                    apply dfs_done_already; try(assumption). rewrite andb_comm. assumption.
                    eapply multi_trans.
                    apply multi_R. subst. apply H0. subst. eapply pop_multi.
                    eapply step. apply H. apply H0. unfold done in *; simpl in *; assumption.
  - destruct s.
    + destruct (S.min_elt t0) eqn : ?.
      * eapply multi_trans; apply multi_R. apply dfs_new_cc. apply Heqo0.
        apply dfs_discover_root. apply S.mem_1. apply S.min_elt_1. assumption.
      * apply multi_refl.
    + destruct p. destruct o0.
      * destruct (S.mem t4 t0) eqn : ?; simpl.
        -- apply multi_R. apply dfs_discover_child. apply Heqb.
        -- destruct (bool_dec (S.mem t4 t)).
           ++ apply multi_R. apply dfs_finish; assumption.
           ++ remember (g0, t3 :: f, t2, t1, n, t0, t, (t4, Some t5) :: s) as s'.
              setoid_rewrite <- Heqs'. destruct (done s') eqn : ?; simpl.
              ** subst. apply multi_refl. 
              ** destruct (S.mem t4 t) eqn : ?; simpl.
                --- subst. apply multi_refl. 
                --- remember  (g0, t3 :: f, t2, t1, n, t0, t, s) as s''.
                    assert (dfs_step s' s''). subst. unfold done in *; simpl in *.
                    apply dfs_done_already; try(assumption). rewrite andb_comm. assumption.
                    eapply multi_trans.
                    apply multi_R. subst. apply H0. subst. eapply pop_multi.
                    eapply step. apply H. apply H0. unfold done in *; simpl in *; assumption.
      * destruct (S.mem t4 t0) eqn : ?; simpl.
        -- apply multi_R. apply dfs_discover_root. apply Heqb.
        -- destruct (bool_dec (S.mem t4 t)).
           ++ apply multi_R. apply dfs_finish; assumption.
           ++ remember (g0, t3 :: f, t2, t1, n, t0, t, (t4, None) :: s) as s'.
              setoid_rewrite <- Heqs'. destruct (done s') eqn : ?; simpl.
              ** subst. apply multi_refl.
              ** destruct (S.mem t4 t) eqn : ?; simpl.
                --- subst. apply multi_refl. 
                --- remember  (g0, t3 :: f, t2, t1, n, t0, t, s) as s''.
                    assert (dfs_step s' s''). subst. unfold done in *; simpl in *.
                    apply dfs_done_already; try(assumption). rewrite andb_comm. assumption.
                     eapply multi_trans.
                    apply multi_R. subst. apply H0. subst. eapply pop_multi.
                    eapply step. apply H. apply H0. unfold done in *; simpl in *; assumption.
Qed. 
  

Lemma dfs_helper_preserves_valid: forall s g o,
  valid_dfs_state s g o ->
  valid_dfs_state (dfs_helper s) g o.
Proof.
  intros. eapply multistep_preserves_valid. apply H. eapply dfs_helper_multisteps.
  apply H.
Qed.

Program Fixpoint dfs_exec (g: graph) (o: option vertex) (s: state) (H: valid_dfs_state s g o) 
   {measure (measure_dfs s)} : 
  {s' : state | dfs_multi s s' /\ done' s' = true} :=
  match s  with
  (*If the stack is empty*)
  | (g, f, f_times, d_times, n, remain_d, remain_f, nil) => 
      match S.min_elt remain_d with
        (*If there are no more elements to be discovered, we are done*)
        | None => exist _ s _
        (*Otherwise, we discover the minimum element in the graph and add it and its neighbors to the stack*)
        | Some min => 
          exist _ (proj1_sig (dfs_exec g o (dfs_helper s) _)) _
       end
  (*If the vertex on top of the stack has no parent (is a root in the dfs forest)*)
  | (g, f, f_times, d_times, n, remain_d, remain_f, (x, None) :: tl) =>
     exist _ (proj1_sig (dfs_exec g o (dfs_helper s) _)) _
  (*If the vertex on top of the stack has a parent (is an internal node/leaf in the dfs forest*)
  | (g, t :: f, f_times, d_times, n, remain_d, remain_f, (x, Some y) :: tl) =>
    if bool_dec (S.mem x remain_f) true then
      exist _ (proj1_sig (dfs_exec g o (dfs_helper s) _)) _
    else 
      exist _ (proj1_sig (dfs_exec g o (dfs_helper (dfs_helper s)) _)) _
  | (_, _, _, _, _, _, _, _) => match invalid_state s g o H _ with end
    end.
Next Obligation.
split. apply multi_refl. unfold done'; simpl. symmetry in Heq_anonymous. apply S.min_elt_3 in Heq_anonymous.
apply S.is_empty_1. assert (A:= H).  apply empty_stack_no_gray in H.
 simpl in H. setoid_rewrite <- H. assumption. reflexivity.
Defined.
Next Obligation.
eapply dfs_helper_preserves_valid. assert (g = g0). 
assert (g = get_graph (g, f, f_times, d_times, n, remain_d, remain_f, nil)) by (reflexivity).
rewrite H0. eapply graph_is_constant. apply H. subst. apply H.
Defined.
Next Obligation. 
unfold measure_dfs in *; simpl in *. 
simpl. destruct f. destruct (S.min_elt remain_d) eqn : ?; simpl.
- size_of_remove.
- inversion Heq_anonymous.
- destruct (S.min_elt remain_d) eqn : ?; simpl.
  + size_of_remove.
  + inversion Heq_anonymous.
Defined.
Next Obligation.
remember (dfs_exec g o (dfs_helper (g, f, f_times, d_times, n, remain_d, remain_f, nil))
        (dfs_exec_func_obligation_2 g0 o (g, f, f_times, d_times, n, remain_d, remain_f, nil) H dfs_exec g f
           f_times d_times n remain_d remain_f eq_refl)
        (dfs_exec_func_obligation_3 g0 o (g, f, f_times, d_times, n, remain_d, remain_f, nil) H dfs_exec g f
           f_times d_times n remain_d remain_f eq_refl min Heq_anonymous)) as s'.
setoid_rewrite <- Heqs'. destruct Heqs'. destruct s'. simpl. destruct a. split.
eapply multi_trans. eapply dfs_helper_multisteps. apply H. apply H0. apply H1.
Defined.
Next Obligation.
eapply dfs_helper_preserves_valid. assert (g = g0). 
assert (g = get_graph (g, f, f_times, d_times, n, remain_d, remain_f, (x, None) :: tl) ) by (reflexivity).
rewrite H0. eapply graph_is_constant. apply H. subst. apply H.
Defined.
Next Obligation.
unfold measure_dfs in *. simpl in *. destruct f.
destruct (S.mem x remain_d) eqn : ?; simpl. size_of_remove.
destruct (S.mem x remain_f) eqn : ?; simpl. size_of_remove.
Admitted.
Next Obligation.
remember (dfs_exec g o (dfs_helper (g, f, f_times, d_times, n, remain_d, remain_f, (x, None) :: tl))
        (dfs_exec_func_obligation_5 g0 o (g, f, f_times, d_times, n, remain_d, remain_f, (x, None) :: tl) H
           dfs_exec g f f_times d_times n remain_d remain_f x tl eq_refl)
        (dfs_exec_func_obligation_6 g0 o (g, f, f_times, d_times, n, remain_d, remain_f, (x, None) :: tl) H
           dfs_exec g f f_times d_times n remain_d remain_f x tl eq_refl)) as s'.
setoid_rewrite <- Heqs'. destruct Heqs'. destruct s'. simpl. destruct a. split.
eapply multi_trans. eapply dfs_helper_multisteps. apply H. apply H0. apply H1.
Defined.
Next Obligation.
eapply dfs_helper_preserves_valid. assert (g = g0). 
assert (g = get_graph (g, t :: f, f_times, d_times, n, remain_d, remain_f, (x, Some y) :: tl)) by (reflexivity).
rewrite H1. eapply graph_is_constant. apply H. subst. apply H.
Defined.
Next Obligation.
unfold measure_dfs in *. simpl in *.
destruct (S.mem x remain_d) eqn : ?; simpl. size_of_remove.
destruct (S.mem x remain_f) eqn : ?. simpl. size_of_remove.
simpl. 
destruct (done (g, t :: f, f_times, d_times, n, remain_d, remain_f, (x, Some y) :: tl)) eqn : ?; simpl;
setoid_rewrite Heqb1; simpl. inversion H0. inversion H0.
Defined.
Next Obligation.
remember (dfs_exec g o (dfs_helper (g, t :: f, f_times, d_times, n, remain_d, remain_f, (x, Some y) :: tl))
        (dfs_exec_func_obligation_8 g0 o (g, t :: f, f_times, d_times, n, remain_d, remain_f, (x, Some y) :: tl)
           H dfs_exec g t f f_times d_times n remain_d remain_f x y tl eq_refl)
        (dfs_exec_func_obligation_9 g0 o (g, t :: f, f_times, d_times, n, remain_d, remain_f, (x, Some y) :: tl)
           H dfs_exec g t f f_times d_times n remain_d remain_f x y tl eq_refl H0)) as s'.
setoid_rewrite <- Heqs'. destruct Heqs'. destruct s'. simpl. destruct a. split.
eapply multi_trans. eapply dfs_helper_multisteps. apply H. apply H1. apply H2.
Defined.
Next Obligation.
 assert (g = g0). 
assert (g = get_graph (g, t :: f, f_times, d_times, n, remain_d, remain_f, (x, Some y) :: tl)) by (reflexivity).
rewrite H1. eapply graph_is_constant. apply H. subst.
eapply dfs_helper_preserves_valid. eapply dfs_helper_preserves_valid.  apply H.
Defined.
Next Obligation.
unfold measure_dfs in *; simpl in *.
destruct (S.mem x remain_d) eqn : ?; simpl.
destruct (add_to_stack x g remain_d ++ (x, Some y) :: tl) eqn : ?; simpl.
destruct (S.min_elt (S.remove x remain_d)) eqn : ?; simpl. size_of_remove. size_of_remove.
destruct p. destruct o0.
destruct (S.mem t0 (S.remove x remain_d)) eqn : ?; simpl.
size_of_remove. destruct (S.mem t0 remain_f) eqn : ?; simpl.
assert (S.cardinal (S.remove x remain_d) + 0 < S.cardinal remain_d + 0) by size_of_remove.
assert (S.cardinal (S.remove t0 remain_f) + 0 < S.cardinal remain_f + 0) by (size_of_remove).
omega.
simpl.
destruct (done
            (g, T.add_child t y x :: f, f_times, M.add x n d_times, n + 1, S.remove x remain_d, remain_f,
            (t0, Some t1) :: l)) eqn : ? ; simpl. size_of_remove. size_of_remove.
destruct (S.mem t0 (S.remove x remain_d)) eqn : ?; simpl. size_of_remove. 
destruct (S.mem t0 remain_f) eqn : ?; simpl. size_of_remove.
 destruct ((done
            (g, T.add_child t y x :: f, f_times, M.add x n d_times, n + 1, S.remove x remain_d, remain_f,
            (t0, None) :: l))) eqn : ?; simpl. size_of_remove. size_of_remove.
destruct (S.mem x remain_f) eqn : ?;simpl. contradiction.
destruct (done (g, t :: f, f_times, d_times, n, remain_d, remain_f, (x, Some y) :: tl)) eqn : ?; setoid_rewrite Heqb1; simpl.
rewrite Heqb; simpl. rewrite Heqb0; simpl. setoid_rewrite Heqb1; simpl.
(*Need to fix - make sure we do not accidentally step with done in the program*)
simpl.

 destruct tl; simpl.
destruct (S.min_elt remain_d) eqn : ?; simpl. size_of_remove. size_of_remove. 
 destruct p. destruct o0.
destruct (S.mem t0 remain_d) eqn : ?; simpl. size_of_remove.  
 destruct (S.mem t0 (S.remove x remain_f)) eqn : ?; simpl. size_of_remove.
destruct (done (g, t :: f, M.add x n f_times, d_times, n + 1, remain_d, S.remove x remain_f, (t0, Some t1) :: tl)) eqn : ?; simpl.
size_of_remove. size_of_remove. contradiction.


 size_of_remove.
assert (S(S.cardinal (S.remove x remain_d)) = S.cardinal remain_d) by 
assert (S(S(S.cardinal (S.remove e (S.remove x remain_d)))) = S.cardinal remain_d). 
    rewrite P2.remove_cardinal_1;

 [apply P2.remove_cardinal_1| prove_in_set e (S.remove x remain_d) ]; prove_in_set x remain_d. omega. remain_d. omega.


 size_of_remove. 
assert (S(S(S.cardinal (S.remove e (S.remove x remain_d)) )) = S.cardinal remain_d).
rewrite P2.remove_cardinal_1. apply P2.remove_cardinal_1. apply S.mem_2. apply Heqb.
prove_in_set e (S.remove x remain_d). omega. size_of_remove.
destruct p. destruct o0.
destruct ((S.mem t0 (S.remove x remain_d))) eqn : ?; simpl. 





    (*If we are discovering this vertex for the first time, then do the discovery process*)
    if bool_dec (S.mem x remain_d) true then
        exist _ (dfs_exec g o (g, (T.add_child t y x) :: f, f_times, M.add x n d_times, n+1,  
        S.remove x remain_d, remain_f, (add_to_stack x g remain_d) ++ (x,Some y) :: tl)_) _
    (*Otherwise, if it is not yet finished, then finish it*)
    else if bool_dec (S.mem x remain_f) true then
        exist _ (dfs_exec g o((g, t :: f, M.add x n f_times, d_times, n+1, remain_d, S.remove x remain_f, tl))_) _
    else
    (*Otherwise, it is done. Due to the decreasing measure condition in Program Fixpoint, we need to
      continue this iteration until we start/finish another vertex. First, we pop off all finished vertices
      from the stack*)
      match (pop_off_stack ((x,Some y) :: tl) remain_f) with
        (*If the resulting stack is empty, then we are either done (if remain_d is empty), or we 
          discover the minimum element*)
        | nil => match S.min_elt remain_d  with
                 | None => exist _  (g, t::f, f_times, d_times, n, remain_d, remain_f, nil) _
                 | Some min =>
                    exist _ (dfs_exec g o (g, (T.singleton min :: f), f_times, M.add min n d_times, n+1, 
                    S.remove min remain_d, remain_f, (min, None) :: nil)_) _
              end
        (*Otherwise, if the top element is *)
        | (a,Some b) :: tl => if bool_dec (S.mem a remain_d) true then
          exist _ (dfs_exec g o(g, (T.add_child t b a) :: f, f_times, M.add a n d_times, n+1, S.remove a remain_d, remain_f,
          (add_to_stack a g remain_d) ++ (a,Some b) :: tl)_) _
          else exist _ (dfs_exec g o (g, t::f, M.add a n f_times, d_times, n+1, remain_d, S.remove a remain_f, tl)_) _
        | (a, None) :: tl => exist _ (dfs_exec g o (g, f, M.add a n f_times, d_times, n+1, remain_d, 
          S.remove a remain_f, tl)_) _
    end
    | (_, _, _, _, _, _, _, _) => match invalid_state s g o H _ with end
    end.


    (*Otherwise, it is done. Due to the decreasing measure condition in Program Fixpoint, we need to
      continue this iteration until we start/finish another vertex. First, we pop off all finished vertices
      from the stack*)
      match (pop_off_stack ((x,Some y) :: tl) remain_f) with

Program Fixpoint dfs_exec (g: graph) (o: option vertex) (s: state) (H: valid_dfs_state s g o) 
   {measure (measure_dfs s)} : 
  {s' : state | dfs_multi s s' /\ done' s' = true} :=
  match s  with
  (*If the stack is empty*)
  | (g, f, f_times, d_times, n, remain_d, remain_f, nil) => 
      match S.min_elt remain_d with
        (*If there are no more elements to be discovered, we are done*)
        | None => exist _ s _
        (*Otherwise, we discover the minimum element in the graph and add it and its neighbors to the stack*)
        | Some min => 
          exist _ (proj1_sig (dfs_exec g o (g, (T.singleton min :: f), f_times, M.add min n d_times, n+1, 
          S.remove min remain_d, remain_f, (add_to_stack min g remain_d) ++ (min, None) :: nil) _)) _
       end
  (*If the vertex on top of the stack has no parent (is a root in the dfs forest)*)
  | (g, f, f_times, d_times, n, remain_d, remain_f, (x, None) :: tl) =>
    (*If it has not been discovered yet*)
    if bool_dec (S.mem x remain_d) true) then
        exist _ (dfs_exec g o (g, (T.singleton x :: f), f_times, M.add x n d_times, n+1, S.remove x remain_d,
        remain_f, (add_to_stack x g remain_d) ++ (x, None) :: tl) _ ) _
    (*Otherwise, it is finished, so we finish it by removing it from the stack and remain_f and adding a finish time*)
    else exist _ (dfs_exec g o (g, f, M.add x n f_times, d_times, n+1, remain_d, S.remove x remain_f, tl) _) _
  (*If the vertex on top of the stack has a parent (is an internal node/leaf in the dfs forest*)
  | (g, t :: f, f_times, d_times, n, remain_d, remain_f, (x, Some y) :: tl) =>
    (*If we are discovering this vertex for the first time, then do the discovery process*)
    if bool_dec (S.mem x remain_d) true then
        exist _ (dfs_exec g o (g, (T.add_child t y x) :: f, f_times, M.add x n d_times, n+1,  
        S.remove x remain_d, remain_f, (add_to_stack x g remain_d) ++ (x,Some y) :: tl)_) _
    (*Otherwise, if it is not yet finished, then finish it*)
    else if bool_dec (S.mem x remain_f) true then
        exist _ (dfs_exec g o((g, t :: f, M.add x n f_times, d_times, n+1, remain_d, S.remove x remain_f, tl))_) _
    else
    (*Otherwise, it is done. Due to the decreasing measure condition in Program Fixpoint, we need to
      continue this iteration until we start/finish another vertex. First, we pop off all finished vertices
      from the stack*)
      match (pop_off_stack ((x,Some y) :: tl) remain_f) with
        (*If the resulting stack is empty, then we are either done (if remain_d is empty), or we 
          discover the minimum element*)
        | nil => match S.min_elt remain_d  with
                 | None => exist _  (g, t::f, f_times, d_times, n, remain_d, remain_f, nil) _
                 | Some min =>
                    exist _ (dfs_exec g o (g, (T.singleton min :: f), f_times, M.add min n d_times, n+1, 
                    S.remove min remain_d, remain_f, (min, None) :: nil)_) _
              end
        (*Otherwise, if the top element is *)
        | (a,Some b) :: tl => if bool_dec (S.mem a remain_d) true then
          exist _ (dfs_exec g o(g, (T.add_child t b a) :: f, f_times, M.add a n d_times, n+1, S.remove a remain_d, remain_f,
          (add_to_stack a g remain_d) ++ (a,Some b) :: tl)_) _
          else exist _ (dfs_exec g o (g, t::f, M.add a n f_times, d_times, n+1, remain_d, S.remove a remain_f, tl)_) _
        | (a, None) :: tl => exist _ (dfs_exec g o (g, f, M.add a n f_times, d_times, n+1, remain_d, 
          S.remove a remain_f, tl)_) _
    end
    | (_, _, _, _, _, _, _, _) => match invalid_state s g o H _ with end
    end.
Next Obligation.
split. apply multi_refl. unfold done'; simpl. symmetry in Heq_anonymous. apply S.min_elt_3 in Heq_anonymous.
apply S.is_empty_1. assert (A:= H).  apply empty_stack_no_gray in H.
 simpl in H. setoid_rewrite <- H. assumption. reflexivity.
Defined.
Next Obligation.
remember(g, f, f_times, d_times, n, remain_d, remain_f, @nil (O.t * option O.t)) as s.
assert (g0 = g). assert (g = get_graph s) by (subst; reflexivity). rewrite H0. symmetry. 
eapply graph_is_constant. subst; apply H. subst.
eapply multistep_preserves_valid. apply H. eapply multi_trans.
apply multi_R. apply dfs_new_cc. symmetry. apply Heq_anonymous. 
apply multi_R. apply dfs_discover_root. apply S.mem_1. apply S.min_elt_1. symmetry. assumption.
Defined.
Next Obligation.
unfold measure_dfs; simpl. symmetry in Heq_anonymous. size_of_remove.
Defined.
Next Obligation. 
remember (g, T.singleton min :: f, f_times, M.add min n d_times, n + 1, S.remove min remain_d, remain_f,
        add_to_stack min g remain_d ++ (min, None) :: nil) as s.
split. eapply multi_trans. eapply multi_trans. apply multi_R. apply dfs_new_cc.
symmetry. apply Heq_anonymous. apply multi_R. apply dfs_discover_root.
apply S.mem_1. apply S.min_elt_1. symmetry. assumption. 
remember 
     (dfs_exec g o
        (g, T.singleton min :: f, f_times, M.add min n d_times, n + 1, S.remove min remain_d, remain_f,
        add_to_stack min g remain_d ++ (min, None) :: nil)
        (dfs_exec_func_obligation_2 g0 o (g, f, f_times, d_times, n, remain_d, remain_f, nil) H dfs_exec g f
           f_times d_times n remain_d remain_f eq_refl min Heq_anonymous)
        (dfs_exec_func_obligation_3 g0 o (g, f, f_times, d_times, n, remain_d, remain_f, nil) H dfs_exec g f
           f_times d_times n remain_d remain_f eq_refl min Heq_anonymous)) as s'. setoid_rewrite <- Heqs'.
destruct Heqs'. destruct s'. simpl. destruct a. apply H0.
remember 
(dfs_exec g o
        (g, T.singleton min :: f, f_times, M.add min n d_times, n + 1, S.remove min remain_d, remain_f,
        add_to_stack min g remain_d ++ (min, None) :: nil)
        (dfs_exec_func_obligation_2 g0 o (g, f, f_times, d_times, n, remain_d, remain_f, nil) H dfs_exec g f
           f_times d_times n remain_d remain_f eq_refl min Heq_anonymous)
        (dfs_exec_func_obligation_3 g0 o (g, f, f_times, d_times, n, remain_d, remain_f, nil) H dfs_exec g f
           f_times d_times n remain_d remain_f eq_refl min Heq_anonymous)) as s'.
setoid_rewrite <- Heqs'. destruct s'. simpl. destruct Heqs'. destruct a. apply H1.
Defined.
Next Obligation.
assert (g = g0). remember (g, f, f_times, d_times, n, remain_d, remain_f, (x, None) :: tl) as s.
assert (g = get_graph s) by (subst; reflexivity). rewrite H0. eapply graph_is_constant. subst. apply H.
subst. eapply step. apply H. apply dfs_finish. 
eapply step. apply H.

 destruct Heqs'.
  destruct s'.  
assert (dfs_multi s s' /\ done s' = true). subst. Check dfs_exe eapply proj2_sig.
 eapply proj2_sig.
assert (A:=dfs_exec). specialize (A g o s). destruct A.
subst. eapply dfs_exec_func_obligation_2. apply H. intros. eapply dfs_exec. apply H0.
apply recproof. reflexivity. assumption. subst; unfold measure_dfs; simpl; symmetry in Heq_anonymous; size_of_remove.
destruct a. rewrite Heqs in H0. 



  Check dfs_exec_func_obligation_1.
assert (A:=dfs_exec).
specialize (A g o s).


 specialize (dfs_exec g o  rewrite dfs_exec. simpl.
simpl.
  graph_is_constantapply H0.

      
    
(H : {s : state | valid_dfs_state s g o})

  | (g, f, f_times, d_times, n, remain_d, remain_f, st)=>
    match st with
    | nil => match S.min_elt remain_d with
             | None => exist _ (proj1_sig H) _
             | Some min => let new_st := pop_off_stack st remain_f in
                           match new_st with
                           | nil => 



    match S.min_elt remain_d with
    | None => 
  end.



Program Fixpoint dfs_exec (g: graph) (o: option vertex) (H : {s : state | valid_dfs_state s g o})
   {measure (measure_dfs (proj1_sig H))} : 
  {s' : state | dfs_multi (proj1_sig H) s' /\ done' s' = true} :=
  match H  with
  | (g, f, f_times, d_times, n, remain_d, remain_f, st)   => exist _ (proj1_sig H) _ 
  end.
  
(g, f, f_times, d_times, n, remain_d, remain_f, st)



destruct H. destruct x. simpl. inversion v.
Proof.
  destruct H. simpl. apply (all_states_terminate) in v. apply v. destruct v. econstructor.


 pose proof (all_states_terminate _ _ _ v). simpl.  econstructor. destruct H. split. destruct a. apply d. apply a.
  simpl.
  apply H. unfold sig.
  

(*Next steps: executable program, parentheses them, white path thm, reachability*)

(*TODO*)
(*
Lemma all_vertices_discovered_at_end: forall s g o v,
  valid_dfs_state s g o ->
  done s ->
  (exists n, M.find v (get_d_times s) = Some n).
*)
End DFS.
