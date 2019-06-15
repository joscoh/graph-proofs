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

Fixpoint list_neq (l1 l2: list O.t) :=
  match l1, l2 with
  | x1 :: t1, x2 :: t2 => if O.eq_dec x1 x2 then list_neq t1 t2 else true
  | nil, nil => false
  | _, _ => true
  end.

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

(*When stack is empty, same vertices left to be discovered and finished*)
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

Lemma contrapositive: forall (P Q: Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros. intro. apply H in H1. contradiction.
Qed.

Lemma contra_bool: forall b,
  ~(b = true) <-> b = false.
Proof.
  intros; split; intros; destruct b; try (reflexivity); try (contradiction); try (inversion H).
  intro. inversion H0.
Qed. 

Definition in_forest (f: forest) (v: vertex) :=
  fold_right (fun t tl => T.contains_vertex t v || tl) false f.
(*
Lemma parent_in_same_tree: forall s g o x y t f,
  valid_dfs_state s g o ->
  (get_forest s) = t :: f ->
  In (x, Some y) (get_stack s) ->
  T.contains_vertex t y = true.
Proof.
  intros. generalize dependent f. generalize dependent x. revert y. revert t. induction H; simpl in *; intros.
  - inversion H0.
  - inversion H2; subst; simpl in *.
    + inversion H0; subst; simpl in *.
      apply in_app_or in H1. destruct H1.
      * eapply add_to_stack_adds_parent in H1. inversion H1. inversion H2; subst.
        apply T.singleton_2. reflexivity.
      * destruct f. inversion H2; subst. 


 simpl in H2. simpl in H1. destruct H1. inversion H1. eapply IHvalid_dfs_state. right. apply H1.
         apply  simpl in H0. destruct o. inversion H0.
Admitted.

Lemma discovered_in_forest: forall s g o v n,
  valid_dfs_state s g o ->
  M.find v (get_d_times s) = Some n ->
  in_forest (get_forest s) v = true.
Proof.
  intros. induction H; subst; simpl in *.
  - rewrite P.F.empty_o in H0. inversion H0.
  - inversion H1; subst; simpl in *.
    + destruct (O.eq_dec v x); rewrite orb_true_iff.
      *  left. setoid_rewrite e. rewrite T.singleton_2. reflexivity.
      * right. apply IHvalid_dfs_state. rewrite F.add_neq_o in H0. apply H0. auto.
    + destruct (O.eq_dec v x); rewrite orb_true_iff.
      * left. setoid_rewrite e. apply T.add_child_5. 


 rewrite T.add_child. reflexivity.
      * right. apply IHvalid_dfs_state. rewrite F.add_neq_o in H0. apply H0. auto.

Lemma finished_in_forest: forall s g o v n,
  valid_dfs_state s g o ->
  M.find v (get_f_times s) = Some n ->
  in_forest (get_forest s) v = true.
Proof.
  intros. induction H; subst; simpl in *.
  - rewrite P.F.empty_o in H0. inversion H0.
  - inversion H1; subst; simpl in *.
    + rewrite IHvalid_dfs_state. apply orb_true_r. apply H0.
    + apply IHvalid_dfs_state in H0. rewrite orb_true_iff in H0.
      destruct H0. rewrite T.add_child_3. reflexivity. apply H0.
      rewrite H0. apply orb_true_r.
    +  simpl. remember (g0, f, M.add x time f_times, d_times, time + 1, remain_d, S.remove x remain_f, tl) as s'.
      assert (valid_dfs_state s' g o). econstructor. apply H. apply H1.
      destruct (O.eq_dec x v).
      * assert (G.contains_vertex g v = true). eapply remain_f_contains_valid_vertices. apply H.
      subst; simpl. setoid_rewrite <- e. apply H3. 
      pose proof finished_vertex_not_remaining. apply (H6 _ _ _ _ H) in H5. subst; simpl in *.
      destruct H5. clear H6. setoid_rewrite e in H3. apply contrapositive in H5.  


 in H4.
       


 Search T.contains_vertex.


 rewrite IHvalid_dfs_state. apply orb_true_r. apply H0.

Lemma forest_empty_only_at_start: forall s g o,
  valid_dfs_state s g o ->
  get_forest s = nil <-> get_time s = 0.
Proof.
  intros. induction H; subst; simpl in *.
  - split; reflexivity.
  - inversion H0; subst; simpl in *; split; intros.
    + inversion H2.
    + omega.
    + inversion H2.
    + omega.
    + assert (A:= H3). rewrite IHvalid_dfs_state in H3. subst.
      


 subst. assert (time = 0). apply IHva destruct time. inversion H2.

Lemma dfs_never_returns_to_start: forall s s' g o,
  valid_dfs_state s g o ->
  dfs_step s s' ->
  s' <> start_state g o.
Proof.
  intros. inversion H0; unfold start_state.
  - destruct o. destruct (G.contains_vertex g v); intro;
    inversion H4. intro. inversion H4.
  - destruct o. destruct (G.contains_vertex g v); intro;
    inversion H4. intro. inversion H4.
  - destruct o. intro. inversion H5; subst. assert (M.mem x (M.empty nat) = true).
    rewrite <- H9. rewrite F.add_b. rewrite orb_true_iff. left. unfold F.eqb.
    intuition. rewrite P.F.empty_a in H3. inversion H3. 
    intro. inversion H5; subst. assert (M.mem x (M.empty nat) = true).
    rewrite <- H9. rewrite F.add_b. rewrite orb_true_iff. left. unfold F.eqb.
    intuition. rewrite P.F.empty_a in H3. inversion H3.
  - destruct o; intro A; inversion A; subst.
    + assert (G.contains_vertex g x = true). {
      eapply stack_contains_valid_vertices. apply H. simpl. reflexivity.
      simpl. left. reflexivity. } 
      rewrite G.set_of_graph_1 in H4. apply S.mem_1 in H4. rewrite H4 in H1. inversion H1.
    + assert (G.contains_vertex g x = true). {
      eapply stack_contains_valid_vertices. apply H. simpl. reflexivity.
      simpl. left. reflexivity. } 
      rewrite G.set_of_graph_1 in H4. apply S.mem_1 in H4. rewrite H4 in H1. inversion H1.
  - (*ugh this one is annoying, need to prove that either the start option was none (or different),
      or that it cannot be the same because that is already done*)
    destruct o eqn : ?. 
    + destruct (G.contains_vertex g v) eqn : ?.
      * intro. inversion H4; subst.



       destruct (G.contains_vertex g v) eqn : ?.
      * 
    auto. apply eq_refl.


 destruct o; intro A; inversion A.
    intro. inversion H4; subst. intro. inversion H4. intro.

Lemma forest_empty_only_at_start: forall s g o,
  valid_dfs_state s g o ->
  get_forest s = nil ->
  s = start_state g o.
Proof.
  intros. induction H; subst; simpl in *.
  - reflexivity.
  - inversion H1; subst; simpl in *; unfold start_state.
    + 
*)
(*really specific, maybe generalize it later or make it follow from other things*)
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

Definition pair_lt (x y : vertex * option vertex) : Prop :=
  match x,y with
  | (a,b), (c,d) => O.lt a c
  end.

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

Lemma no_vertex_twice: forall s g o x y o' o'' t l1,
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
    + destruct (add_to_stack x0 g0 remain_d) eqn : ?.
      * simpl in H1. eapply IHvalid_dfs_state. apply H1.
      * simpl in H1. (*do later lots of list manipulation and stuff*)
    syme

Lemma no_vertex_twice: forall s g o x y o' o'' t,
  valid_dfs_state s g o ->
  get_stack s = (x, o') :: (y, o'') :: t ->
  x <> y.
Proof.
  intros. generalize dependent x. revert o' o'' y. induction H; intros; subst; simpl in *.
  - destruct o. destruct (G.contains_vertex g v). inversion H0. inversion H0. inversion H0.
  - inversion H0; subst; simpl in *.
    + destruct (add_to_stack x0 g0 remain_d) eqn : ?.
      * simpl in H1. eapply IHvalid_dfs_state. apply H1.
      * simpl in H1. inversion H1; subst. destruct s eqn : ?.
        -- simpl in H5. inversion H5; subst. 
           assert (g = g0). 
           remember ((g0, f, f_times, d_times, time, remain_d, remain_f, (y, None) :: t)) as s'.
           assert (g0 = get_graph s') by (subst; reflexivity). rewrite H3. symmetry. eapply graph_is_constant.
           subst. apply H. subst. assert (G.contains_edge g0 y x = true). eapply only_add_neighbors.
           rewrite Heqs. simpl. left. reflexivity. assert (y <> x).
           eapply G.contains_edge_3. apply H3. auto.
         -- inversion H5; subst. assert (pair_lt (x, o') (y, o'')). 
            assert (StronglySorted pair_lt ((x, o') :: (y, o'') :: l)). rewrite <- Heqs.
            apply add_to_stack_sorted. inversion H3; subst. inversion H8; subst. apply H9.
            unfold pair_lt in H3. apply O.lt_not_eq. apply H3.
      + destruct (add_to_stack x0 g0 remain_d) eqn : ?.
      * simpl in H1. eapply IHvalid_dfs_state. apply H1.
      * simpl in H1. inversion H1; subst. destruct s eqn : ?.
        -- simpl in H1. inversion H1; subst. 
           assert (g = g0). 
           remember (g0, t0 :: f, f_times, d_times, time, remain_d, remain_f, (y, Some y0) :: t) as s'.
           assert (g0 = get_graph s') by (subst; reflexivity). rewrite H3. symmetry. eapply graph_is_constant.
           subst. apply H. subst. assert (G.contains_edge g0 y x = true). eapply only_add_neighbors.
           rewrite Heqs. simpl. left. reflexivity. assert (y <> x).
           eapply G.contains_edge_3. apply H3. auto.
         -- inversion H1; subst. assert (pair_lt (x, o') (y, o'')). 
            assert (StronglySorted pair_lt ((x, o') :: (y, o'') :: l)). rewrite <- Heqs.
            apply add_to_stack_sorted. inversion H3; subst. inversion H8; subst. apply H9.
            unfold pair_lt in H3. apply O.lt_not_eq. apply H3.
      + 


 destruct tl. inversion H1. inversion H1; subst. eapply IHvalid_dfs_state. apply H1. 
      *

(*An important theorem: any valid state can step iff it is not done*)
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
            ** econstructor. apply dfs_finish. apply Heqb. rewrite P2.Dec.F.remove_neq_b.
               apply Heqb0.  



  auto.

 exists (g0, T.singleton x :: f, (M.add x (time + 1) f_times), (M.add x d_times),
            time + 2, S.remove x remain_d, S.remove x remain_f, tl).


dfs_step (g, f, f_times, d_times, time, remain_d, remain_f, (x,o) :: tl)
    (g,  f, (M.add x time f_times), d_times, (time + 1), remain_d, (S.remove x remain_f), tl)


(g, (T.singleton x) :: f, f_times, (M.add x time d_times), (time + 1), (S.remove x remain_d), 
    remain_f, (add_to_stack x g remain_d) ++  ((x, None) :: tl))


 dfs_discover_root.
  


  apply H6 in H. subst; simpl in *.
        rewrite H4 in H. inversion H.  subst; simpl in *. 
        
        
        ++


 intro.
               subst. apply n. apply eq_refl. 
           ** setoid_rewrite x in H4.


 rewrite H4 in  apply H. 
           rewrite -> (P2.Dec.F.remove_neq_b _ x) in H5. solve_set_empty.
        destruct (S.is_empty remain_f) eqn : ?.



 inversion H0; subst; simpl in *.
        -- 
            ++
        --

(*This gives us an idea that our choice of the [done] property was a good one: a state is done
  if it cannot step, actually might be better to do existence way first but well see*)
Lemma done_cannot_step: forall s g o,
  valid_dfs_state s g o ->
  (done' s = true <-> (forall s', ~dfs_step s s')).
Proof.
  intros. split; intros.
  - intro contra. inversion contra; unfold done' in *; subst; simpl in *.
    + remember (g0, f, f_times, d_times, time, remain_d, remain_f, (x, None) :: tl) as s.
      assert (S.is_empty (get_remain_f s) = true) by (subst; simpl; assumption).
      eapply finish_discover_before_finishing in H2. subst; simpl in *.
      empty_set_mem. apply H.
    + remember (g0, t :: f, f_times, d_times, time, remain_d, remain_f, (x, Some y) :: tl) as s.
      assert (S.is_empty (get_remain_f s) = true) by (subst; simpl; assumption).
      eapply finish_discover_before_finishing in H2. subst; simpl in *.
      empty_set_mem. apply H.
    + empty_set_mem.
    + rewrite andb_false_iff in H3. destruct H3. 
      * remember (g0, f, f_times, d_times, time, remain_d, remain_f, (x, y) :: tl) as s.
        assert (S.is_empty (get_remain_f s) = true) by (subst; simpl; assumption).
        eapply finish_discover_before_finishing in H4. subst; simpl in *.
        rewrite H4 in H3. inversion H3. apply H.
      * rewrite H3 in H0. inversion H0.
    + remember (g0, f, f_times, d_times, time, remain_d, remain_f, nil) as s.
      assert (S.is_empty (get_remain_f s) = true) by (subst; simpl in *; assumption).
      eapply finish_discover_before_finishing in H2. subst; simpl in *.
      apply S.min_elt_1 in H1. apply S.mem_1 in H1. empty_set_mem. apply H.
  - induction H; subst; unfold done'; simpl in *.
    + destruct (S.is_empty (G.set_of_graph g)) eqn : ?.
      * reflexivity.
      * unfold start_state in H0. destruct o.
        -- destruct (G.contains_vertex g v) eqn : ?.
          ++ exfalso. eapply H0. apply dfs_discover_root. apply S.mem_1.
             rewrite <- G.set_of_graph_1. apply Heqb0.
          ++ destruct (S.min_elt (G.set_of_graph g)) eqn : ?.
              ** exfalso. eapply H0. apply dfs_new_cc. apply Heqo.
              ** apply S.min_elt_3 in Heqo. apply S.is_empty_1 in Heqo.
                 rewrite Heqo in Heqb. inversion Heqb.
       -- destruct (S.min_elt (G.set_of_graph g)) eqn : ?.
          ++ exfalso. eapply H0. apply dfs_new_cc. apply Heqo.
          ++ apply S.min_elt_3 in Heqo. apply S.is_empty_1 in Heqo.
             rewrite Heqo in Heqb. inversion Heqb.
    + inversion H1; subst; simpl in *.
      * destruct ( add_to_stack x g0 remain_d) eqn : ?.
        -- exfalso. eapply H0. simpl. apply dfs_finish. rewrite P2.FM.remove_b. rewrite andb_false_iff.
           right. unfold P2.FM.eqb. destruct (O.eq_dec x x). reflexivity. exfalso.
            apply n. apply eq_refl. 
           remember (g0, f, f_times, d_times, time, remain_d, remain_f, (x, None) :: tl)  as s.
           assert (S.mem x (get_remain_d s) = true) by (subst; simpl; assumption).
           eapply vertex_in_finish_if_not_discovered in H3. subst; simpl in *. apply H3.
           apply H.
        -- exfalso. destruct p. assert (o0 = Some x). { eapply add_to_stack_adds_parent. 
            rewrite Heqs. simpl. left. reflexivity. } eapply H0. rewrite H3. apply dfs_discover_child.
            assert (G.contains_edge g x t = true). eapply only_add_neighbors.
            assert (g = g0). remember (g0, f, f_times, d_times, time, remain_d, remain_f, (x, None) :: tl) as s'. 
            assert (g0 = get_graph s') by (subst; simpl; reflexivity). rewrite H4. symmetry. eapply graph_is_constant.
            apply H. rewrite H4. simpl. rewrite Heqs. simpl. left. reflexivity. 
            apply G.contains_edge_3 in H4. rewrite P2.FM.remove_neq_b. eapply only_add_yet_to_be_discovered.
            rewrite Heqs. simpl. left. reflexivity. apply H4.
      * destruct ( add_to_stack x g0 remain_d) eqn : ?.
        -- exfalso. eapply H0. simpl. apply dfs_finish. rewrite P2.FM.remove_b. rewrite andb_false_iff.
           right. unfold P2.FM.eqb. destruct (O.eq_dec x x). reflexivity. exfalso.
            apply n. apply eq_refl. 
           remember (g0, t :: f, f_times, d_times, time, remain_d, remain_f, (x, Some y) :: tl)  as s.
           assert (S.mem x (get_remain_d s) = true) by (subst; simpl; assumption).
           eapply vertex_in_finish_if_not_discovered in H3. subst; simpl in *. apply H3.
           apply H.
        -- exfalso. destruct p. assert (o0 = Some x). { eapply add_to_stack_adds_parent. 
            rewrite Heqs. simpl. left. reflexivity. } eapply H0. rewrite H3. apply dfs_discover_child.
            assert (G.contains_edge g x t0 = true). eapply only_add_neighbors.
            assert (g = g0). remember (g0, t :: f, f_times, d_times, time, remain_d, remain_f, (x, Some y) :: tl) as s'. 
            assert (g0 = get_graph s') by (subst; simpl; reflexivity). rewrite H4. symmetry. eapply graph_is_constant.
            apply H. rewrite H4. simpl. rewrite Heqs. simpl. left. reflexivity. 
            apply G.contains_edge_3 in H4. rewrite P2.FM.remove_neq_b. eapply only_add_yet_to_be_discovered.
            rewrite Heqs. simpl. left. reflexivity. apply H4.
       * destruct (S.is_empty (S.remove x remain_f)) eqn : ?. 
         -- reflexivity.
         -- destruct tl. destruct (S.min_elt (S.remove x remain_f)) eqn : ?.
            ++ assert (A:=Heqo1). apply S.min_elt_1 in Heqo1. apply S.mem_1 in Heqo1.
               destruct (S.mem e remain_d) eqn : ?.
               ** exfalso. 
                   remember ((g0, f, M.add x time f_times, d_times, time + 1, remain_d, S.remove x remain_f, nil)) as s'.
 assert (S.Equal (get_remain_d s') (get_remain_f s')). { eapply empty_stack_no_gray.
      eapply step. apply H. apply H1. subst. reflexivity. } subst; simpl in H4. 
    (*Figure this out tomorrow*)
      setoid_rewrite <- H4 in A.
               ** (S.remove x remain_f)). {
                  
                  eapply empty_stack_no_gray.


 Search S.min_elt. rewrite non_empty_set_has_elements in Heqb. destruct Heqb.
            apply S.mem_1 in H4. destruct (S.mem x0 (remain_d)) eqn : ?.
            ++ 
        +



(*finish case, we could be done, or if there is still someone in remain_f, we have to prove that
           they are still on the stack - for tomorrow*)
           
            
            

 
        -- unfold start_state in H0.
           dest rewrite non_empty_set_has_elements in Heqb. Search S.min_elt.
        d

 auto.  empty_set_mem.
      apply S.is_empty_2 in H2. apply P2.empty_is_empty_1 in H2.
      setoid_rewrite H2 in H1. rewrite P2.Dec.F.empty_b in H1. inversion H1. apply H.
    + 
  



  induction H; unfold done' in *; subst; simpl in *.
  - intro contra. unfold start_state in contra. destruct o.
    destruct (G.contains_vertex g v) eqn : ?.
    + rewrite G.set_of_graph_1 in Heqb. apply S.is_empty_2 in H0.
        apply P2.empty_is_empty_1 in H0. setoid_rewrite H0 in Heqb.
        rewrite P2.FM.empty_iff in Heqb. destruct Heqb.
    + inversion contra; subst; simpl in *.
      * apply S.min_elt_1 in H8.  apply S.is_empty_2 in H0.
        apply P2.empty_is_empty_1 in H0. setoid_rewrite H0 in H8.
        rewrite P2.FM.empty_iff in H8. apply H8.
    + inversion contra; subst; simpl in *. apply S.min_elt_1 in H8.  apply S.is_empty_2 in H0.
        apply P2.empty_is_empty_1 in H0. setoid_rewrite H0 in H8.
        rewrite P2.FM.empty_iff in H8. apply H8.
  - intro contra. inversion H1; subst; simpl in *.
    + remember ((g0, f, f_times, d_times, time, remain_d, remain_f, (x, None) :: tl)) as s.
      assert (S.is_empty (get_remain_f s) = true). subst; simpl; assumption.
      eapply finish_discover_before_finishing in H3. subst; simpl in *.
      apply S.is_empty_2 in H3. apply P2.empty_is_empty_1 in H3.
      setoid_rewrite H3 in H2. rewrite P2.FM.empty_b in H2. inversion H2. apply H.
    + remember ((g0, t ::f, f_times, d_times, time, remain_d, remain_f, (x, Some y) :: tl)) as s.
      assert (S.is_empty (get_remain_f s) = true). subst; simpl; assumption.
      eapply finish_discover_before_finishing in H3. subst; simpl in *.
      apply S.is_empty_2 in H3. apply P2.empty_is_empty_1 in H3.
      setoid_rewrite H3 in H2. rewrite P2.FM.empty_b in H2. inversion H2.  apply H.
    +  


 rewri simpl. simpl in *. inversion contra; subst; simpl in *.
    + destruct o. destruct (G.contains_vertex g v) eqn : ?.
      * rewrite G.set_of_graph_1 in Heqb. apply S.is_empty_2 in H0.
        apply P2.empty_is_empty_1 in H0. setoid_rewrite H0 in Heqb.
        rewrite P2.FM.empty_iff in Heqb. destruct Heqb.
      * inversion H8.
      * inversion H8.
    + 
    +


Lemma done_cannot_step: forall s g,
  valid_dfs_state s g ->
  done' s = true ->
  (forall s', ~dfs_step s s').
Proof.
  intros. intro. unfold done' in H0. inversion H1; subst; simpl in *.
  - remember ((g0, t, f_times, d_times, time, remain_d, remain_f, (x, y) :: tl)) as s.
    assert (remain_f_of_state s = remain_f). subst; simpl; reflexivity.
    rewrite <- H3 in H0. apply (finish_discover_before_finishing s g H) in H0.
    apply S.is_empty_2 in H0. apply P2.empty_is_empty_1 in H0.
    assert (remain_d_of_state s = remain_d). subst; simpl; reflexivity. 
    rewrite H4 in H0. setoid_rewrite H0 in H2. apply S.mem_2 in H2. apply P2.FM.empty_iff in H2.
    apply H2.
  - apply S.mem_2 in H3. apply S.is_empty_2 in H0. apply P2.empty_is_empty_1 in H0.
    setoid_rewrite H0 in H3. apply P2.FM.empty_iff in H3. apply H3.
  - apply S.mem_2 in H3. apply S.is_empty_2 in H0. apply P2.empty_is_empty_1 in H0.
    setoid_rewrite H0 in H3. apply P2.FM.empty_iff in H3. apply H3.
  - assert (S.is_empty remain_d = false). destruct (S.is_empty remain_d) eqn : ?.
    apply S.is_empty_2 in Heqb. apply S.min_elt_1 in H2. apply P2.empty_is_empty_1 in Heqb.
    setoid_rewrite Heqb in H2. apply P2.FM.empty_iff in H2. destruct H2. reflexivity.
    remember (g0, t, f_times, d_times, time, remain_d, remain_f, []) as s.
    assert (remain_f_of_state  s = remain_f). subst; simpl; reflexivity.
    assert (remain_d_of_state s = remain_d). subst; reflexivity.
    rewrite <- H4 in H0. eapply finish_discover_before_finishing in H0.
    rewrite H5 in H0. rewrite H3 in H0. inversion H0. apply H.
Qed. 



Lemma all_vertices_discovered_at_end: forall s g o v,
  valid_dfs_state s g o ->
  done s ->
  (exists n, M.find v (get_d_times s) = Some n).

