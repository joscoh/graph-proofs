Require Import DFSSpec.
Require Import Coq.FSets.FSetInterface.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Graph.
Require Import Forest.
Require Import Path.
Require Import Coq.Init.Nat.
Require Import Helper.
Require Import Coq.Arith.PeanoNat.
Require Import Omega.
Require Import Coq.Lists.ListDec.
Require Import SCCDef.

(* This module consists of proofs of both properties and applications of DFS that use only the specification
    defined in DFSBase and thus are independent of any actual DFS algorithm. The significant results include
    - A necessary and sufficient condition for graph reachability - u is reachable from v iff when we start
        DFS from v, u is a descendant
    - The existence of a path between two vertices is decidable
    - A necessary and sufficient condition for (nontrivial) cycle existence - there is a nontrivial cycle
      (ie, a cycle that contains more than 1 vertex) iff there is a back edge (an edge (u,v) in g such that
      u is a descendant of v in the DFS forest). This does not yet give a cycle detection algorithm
    - A proof of the CLRS topological sorting algorithm: A list of vertices sorted in reverse order of their
      finish times is topologically sorted*)
Module DerivedProofs(O: UsualOrderedType)(S: FSetInterface.Sfun O)(G: Graph O S)(F: Forest O S)(D: DFSBase O S G F).

Module P:= D.P. 
Module P2 := FSetProperties.WProperties_fun O S.
Module O2 := OrderedTypeFacts O.
Module M := (Helper.MinMax O).
Module SD := (SCCDef.SCCDef O S G).
Module Pa := (Helper.Partition O S).

Lemma desc_implies_path: forall g o u v l,
  F.desc_list (D.dfs_forest o g) u v l = true ->
  P.path_list_rev g u v l = true.
Proof.
  intros. generalize dependent v. induction l; intros.
  - simpl in *. eapply D.same_edges. apply H. 
  - simpl in *. simplify. eapply D.same_edges. apply H0. 
Qed. 

(*Technically I could add this to the DFS spec so that it is true even if there is only 1 vertex in the graph,
  but I will see if I need it*)
Lemma discover_before_finish: forall g o u v,
  G.contains_vertex g u = true ->
  G.contains_vertex g v = true ->
  u <> v ->
  D.d_time o g u < D.f_time o g u.
Proof.
  intros. pose proof (D.parentheses_theorem o g u v H H0 H1). omega.
Qed.

(** ** Application 1 of DFS: Reachability **)
Theorem reachability: forall g u v,
  u <> v ->
  (exists l, P.path_list_rev g u v l = true) <-> F.desc (D.dfs_forest (Some u) g) u v.
Proof.
  intros. split; intros.
  - destruct_all. apply P.path_start_unique in H0. destruct_all. assert (G.contains_vertex g u = true).
    eapply P.path_implies_in_graph in H0. simplify. 
    pose proof (D.discovery_exists (Some u) _ _ H2). destruct_all.
    assert (forall a, In a x0 -> D.white (Some u) g x1 a = true). { intros.
    assert (G.contains_vertex g a = true). { eapply P.path_implies_in_graph in H0. destruct_all.
    apply H6. apply H4. } pose proof (D.start_vertex _ _ _ H2 H5).
    assert (u <> a). intro. subst. contradiction. apply H6 in H7; clear H6.
    rewrite D.white_def. rewrite H3. rewrite Nat.ltb_lt. apply H7. }
    eapply D.white_path_theorem. apply H2. intros.
    assert (s = x1). eapply D.state_time_unique. rewrite H3. rewrite H5. reflexivity. subst.
    exists x0. rewrite D.P.path_list_ind_rev. split. apply H0. split. apply H4. rewrite D.white_def. 
    assert (G.contains_vertex g v = true). eapply P.path_implies_in_graph in H0. simplify.
    pose proof (D.start_vertex _ _ _ H2 H6 H). rewrite H5. apply Nat.ltb_lt. apply H7.
  - rewrite <- F.desc_list_iff_desc in H0. destruct H0. exists x.
    eapply desc_implies_path. apply H0.
Qed.

Theorem unique_paths: forall g u v,
  u <> v ->
  (exists l, P.path_list_rev g u v l = true) ->
  exists l, P.path_list_rev g u v l = true /\ NoDup l /\ ~In u l /\ ~In v l.
Proof.
  intros. eapply reachability in H0. rewrite <- F.desc_list_iff_desc in H0. destruct H0. exists x.
  split. eapply desc_implies_path. apply H0. split. destruct (NoDup_dec O.eq_dec x). apply n.
  rewrite no_no_dup in n. destruct_all. subst. apply F.desc_app in H0. destruct H0.
  apply F.desc_app in H1. destruct H1. assert (exists l, F.desc_list (D.dfs_forest (Some u) g) x0 x0 l = true).
  exists x2. assumption. rewrite F.desc_list_iff_desc in H3. apply F.desc_neq in H3. contradiction. apply O.eq_dec.
  split. intro. apply in_split_app_fst in H1. destruct_all. subst. apply F.desc_app in H0.
  destruct H0. assert (exists l, F.desc_list (D.dfs_forest (Some u) g) u u l = true). exists x1. assumption.
  rewrite F.desc_list_iff_desc in H3. apply F.desc_neq in H3. contradiction. apply O.eq_dec.
  intro.   apply in_split_app_fst in H1. destruct_all. subst. apply F.desc_app in H0.
  destruct H0. assert (exists l, F.desc_list (D.dfs_forest (Some u) g) v v l = true). exists x0. assumption.
  rewrite F.desc_list_iff_desc in H3. apply F.desc_neq in H3. contradiction. apply O.eq_dec. apply H.
Qed.

(*Prove cycle later*)
Lemma desc_decidable: forall g u v,
  (F.desc (D.dfs_forest (Some u) g) u v) \/ ~(F.desc (D.dfs_forest (Some u) g) u v).
Proof.
  intros. destruct (G.contains_vertex g u) eqn : ?. destruct (G.contains_vertex g v) eqn : ?.
  pose proof (D.descendant_iff_interval (Some u) _ _ _ Heqb Heqb0).
   assert ((D.d_time (Some u) g u < D.d_time (Some u) g v /\
    D.d_time (Some u) g v < D.f_time (Some u) g v < D.f_time (Some u) g u) \/ 
    (~(D.d_time (Some u) g u < D.d_time (Some u) g v /\
    D.d_time (Some u) g v < D.f_time (Some u) g v < D.f_time (Some u) g u))) by omega.
  destruct H0. left. rewrite H. apply H0. right. intro. rewrite H in H1. omega.
  right. intro. apply F.desc_in_forest in H. destruct H. apply D.same_vertices in H0.
  rewrite H0 in Heqb0. inversion Heqb0. right. intro.
  apply F.desc_in_forest in H. destruct H. apply D.same_vertices in H. rewrite H in Heqb. inversion Heqb.
Qed.

(* As a Corollary of reachability, we can prove that the existence of a path between two vertices is decidable. *)
Corollary path_decidable: forall g u v,
  u <> v ->
  (exists l, P.path_list_rev g u v l = true) \/ ~(exists l, P.path_list_rev g u v l = true).
Proof.
  intros. destruct (desc_decidable g u v). left. eapply reachability. apply H. apply H0.
  right. intro. apply reachability in H1. contradiction. apply H.
Qed.

(** ** Application 2: Cycle Detection **)




(*We want to be able to reason about the vertex in the cycle that is discovered first. So we need a few
  helper definitions and lemmas*)

(*A function to compute the vertex with the smallest discovery time*)
Fixpoint first_vertex o g (l: list G.vertex) (d: G.vertex) : G.vertex :=
  match l  with
  | nil => d
  | x :: t => match t with
              | nil => x
              | _ =>  if D.d_time o g x <? D.d_time o g (first_vertex o g t d) then x else first_vertex o g t d
              end
  end.

(*The result of [first_vertex] is in the original list*)
Lemma first_vertex_in_list: forall o g l d,
  l <> nil ->
  In (first_vertex o g l d) l.
Proof.
  intros. induction l.
  - contradiction.
  - simpl. destruct l.
    + left. reflexivity.
    + destruct (D.d_time o g a <? D.d_time o g (first_vertex o g (v :: l) d)) eqn : ?.
      left. reflexivity. right. apply IHl. intro. inversion H0.
Qed.

(*[first_vertex] actually finds the vertex with the (strictly) smallest discovery time as long as
  everything in the list is in the graph*)
Lemma first_vertex_finds_smallest: forall g o l d u,
  l <> nil ->
  G.contains_vertex g u = true ->
  (forall x, In x l -> G.contains_vertex g x = true) ->
  u = (first_vertex o g l d) ->
  forall x, In x l -> x <> u -> D.d_time o g u < D.d_time o g x.
Proof.
  intros. subst. induction l.
  - contradiction.
  - simpl in *. destruct l.
    + simpl in *. destruct H3. subst. contradiction. destruct H2.
    + destruct (D.d_time o g a <? D.d_time o g (first_vertex o g (v :: l) d)) eqn : ?.
      * destruct H3. subst. contradiction. destruct (O.eq_dec x (first_vertex o g (v :: l) d)).
        -- unfold O.eq in e. subst. rewrite Nat.ltb_lt in Heqb. apply Heqb.
        -- assert (D.d_time o g (first_vertex o g (v :: l) d) < D.d_time o g x). apply IHl.
           intro. inversion H3. apply H1. right. apply first_vertex_in_list. intro.
           inversion H3. intros. apply H1. right. apply H3. apply H2. apply n. rewrite  Nat.ltb_lt in Heqb. omega.
      * rewrite Nat.ltb_antisym in Heqb. rewrite negb_false_iff in Heqb.
        rewrite Nat.leb_le in Heqb. assert ((D.d_time o g (first_vertex o g (v :: l) d) = D.d_time o g a)
        \/ (D.d_time o g (first_vertex o g (v :: l) d) < D.d_time o g a)) by omega.
        destruct H2. eapply D.d_times_unique in H2.
        subst. destruct H3. subst. contradiction. apply IHl. intro. inversion H3. apply H1. left.
        reflexivity. intros. apply H1. right. apply H3. apply H2. apply H4.
        apply H1. right. apply first_vertex_in_list. intro. inversion H6. apply H1. left.
        reflexivity. destruct H3. subst. apply H2. apply IHl. intro. inversion H5.
        apply H1. right. apply first_vertex_in_list. intro. inversion H5. intros. apply H1.
        right. apply H5. apply H3. apply H4.
Qed. 

(*A path has a vertex that finishes first*)
Lemma path_has_smallest_vertex: forall o g l (v: G.vertex),
  l <> nil ->
  (forall x, In x l -> G.contains_vertex g x = true) ->
  exists u, In u l /\ (forall x, In x l -> x <> u -> D.d_time o g u < D.d_time o g x).
Proof.
  intros. exists (first_vertex o g l v). split. apply first_vertex_in_list. apply H.
   eapply first_vertex_finds_smallest. apply H. apply H0. apply first_vertex_in_list. apply H.
  apply H0. reflexivity.
Qed.

(*A more specific and helper lemma for cycles: If we have a cycle from v to v, then there is a cycle
  from u to u such that every vertex in the original cycle is also in the new cycle and
   u has a smaller finish time than every vertex in the cycle. This allows us to directly work with
  the first vertex discovered in a cycle without having to destruct into cases*)
Lemma cycle_smallest: forall o g l v,
  l <> nil ->
  P.path_list_rev g v v l = true ->
  exists l1 u, P.path_list_rev g u u l1 = true /\ (u <> v -> In u l) /\ (u <> v -> In v l1)
   /\ l1 <> nil /\ (forall x, In x l1 -> x <> u -> D.d_time o g u < D.d_time o g x) /\
  (forall x, x <> u -> x <> v -> (In x l <-> In x l1)).
Proof.
  intros. assert (A:=H0). assert (forall x, In x l -> G.contains_vertex g x = true). intros.
  eapply D.P.path_implies_in_graph in H0. destruct_all. apply H3. apply H1. assert (B:= H).
  eapply (path_has_smallest_vertex o g) in H. destruct_all.
  assert (D.d_time o g x < D.d_time o g v \/ D.d_time o g v < D.d_time o g x \/ D.d_time o g x = D.d_time o g v)
  by omega. destruct H3. eapply (P.any_cycle _ _ x) in H0. destruct_all. exists x0.
  exists x. split. apply H0. split. intros. apply H. split. intros. apply H4. split. intro. subst. inversion H4.
  split.
  intros. destruct (O.eq_dec x1 v). unfold O.eq in e. subst. apply H3. apply H2.
  rewrite H5. apply H6. apply n. apply H7. apply H7. intros. apply H5; auto. apply H.
  destruct H3. exists l. exists v. split. apply H0. split. intros. contradiction. split. intros.
  contradiction. split. apply B. split. intros.  destruct (O.eq_dec x x0). unfold O.eq in e. subst.
  apply H3. apply H2 in H4. omega. auto. intros. reflexivity. assert (x = v). eapply D.d_times_unique.
  apply H1. apply H. eapply D.P.path_implies_in_graph in H0. simplify. apply H3. subst.
   exists l. exists v. split. apply H0. split. intros. contradiction. split. intros. contradiction.
  split. apply B. split. apply H2. intros. reflexivity. apply v. apply H1.
Qed.

Lemma desc_iff_gray_when_discovered: forall (g : G.graph) o u v,
  G.contains_vertex g v = true ->
  G.contains_vertex g u = true ->
  u <> v ->
  F.desc (D.dfs_forest o g) u v <-> (forall s, D.time_of_state o g s = D.d_time o g v -> D.gray o g s u = true).
Proof.
  intros. split; intros.
  - apply D.descendant_iff_interval in H2. destruct_all. rewrite D.gray_def.
    simplify. rewrite H3. apply Nat.ltb_lt. omega. rewrite H3. apply Nat.leb_le. omega.
    apply F.desc_in_forest in H2. destruct_all. eapply D.same_vertices. apply H2.
    apply F.desc_in_forest in H2. destruct_all. eapply D.same_vertices. apply H5.
  - pose proof (D.discovery_exists o g v H). destruct_all. specialize (H2 x H3). rewrite D.gray_def in H2.
    simplify. rewrite Nat.ltb_lt in H4. rewrite Nat.leb_le in H5.
    rewrite H3 in H4. rewrite H3 in H5. assert (D.d_time o g u < D.d_time o g v).
    assert ((D.d_time o g u < D.d_time o g v) \/ (D.d_time o g u = D.d_time o g v)) by omega.
    destruct H2. apply H2. apply D.d_times_unique in H2. subst. contradiction.
    all: try(assumption). clear H5. pose proof (D.parentheses_theorem
    o g u v H0 H H1). destruct H5. eapply D.descendant_iff_interval. apply H0. apply H. apply H5.
    repeat (destruct H5; omega).
Qed.

(*Alternative definition of back edge: an edge (u, v) in g such that v is gray when u is discovered*)
Definition back_edge' g u v o := exists s, u <> v /\ D.time_of_state o g s = D.d_time o g u /\ G.contains_edge g u v = true
   /\ D.gray o g s v = true.

(*The two definitions are equivalent*)
Lemma back_edge_equiv: forall o g u v,
  D.back_edge g u v o <->  back_edge' g u v o.
Proof.
  intros. split; intros.
  - rewrite D.back_edge_def in H. unfold back_edge'. destruct_all.
    assert (G.contains_vertex g u = true). eapply G.contains_edge_1. apply H.
    pose proof (D.discovery_exists o g u H1). destruct_all. assert (A:= H0). 
    eapply desc_iff_gray_when_discovered in H0. exists x. split. assert (v <> u). eapply F.desc_neq. apply A.
    auto. split. apply H2. split. apply H. apply H0. apply H1. eapply G.contains_edge_2. apply H.
    eapply F.desc_neq. apply H0. apply H2.
  - unfold back_edge' in H. rewrite D.back_edge_def.  destruct_all. split. apply H1.
    eapply desc_iff_gray_when_discovered. eapply G.contains_edge_1. apply H1.
    eapply G.contains_edge_2. apply H1. auto. intros.
    assert (s = x). eapply D.state_time_unique. omega. subst. apply H2.
Qed.



(** The big result (Lemma 22.11 in CLRS) **)
(*There is a nontrivial cycle (ie, a cycle that does not consist of a single vertex) iff there is a back
  edge.*)
Lemma cycle_iff_back_edge: forall g o,
  P.nontrivial_cyclic g <-> (exists u v, back_edge' g u v o).
Proof.
  intros. split; intros.
  - unfold P.nontrivial_cyclic in H. destruct_all.
    eapply (cycle_smallest o) in H0. destruct_all.
    eapply P.cycle_no_dups_strong in H0. destruct_all. 
    destruct x4. contradiction. simpl in *. unfold back_edge'. 
    simplify.
    assert (F.desc (D.dfs_forest o g) x3 v). { eapply D.white_path_theorem.
    eapply G.contains_edge_2. apply H11. intros.
    exists x4. rewrite D.P.path_list_ind_rev. split. apply H12. split. intros. rewrite D.white_def.
    rewrite H8. apply Nat.ltb_lt. apply H5. apply H10. right. apply H14.
    intro. subst. contradiction. rewrite D.white_def. apply Nat.ltb_lt. rewrite H8. apply H5.
    apply H10. left. reflexivity. apply H0. }
    pose proof (D.discovery_exists o g v). assert (G.contains_vertex g v = true). 
    eapply G.contains_edge_1. apply H11. apply H14 in H15; clear H14. destruct_all.
    eapply desc_iff_gray_when_discovered in H8. exists v. exists x3. exists x5.
    split. apply H0. split. apply H14. split. apply H11. apply H8. eapply G.contains_edge_1. apply H11.
    eapply G.contains_edge_2. apply H11. auto. apply H14. destruct (O.eq_dec x x3). unfold O.eq in e.
    subst. exists x1. split. rewrite <- H6. apply H1. auto. auto. auto. exists x. split. apply H3.
    auto. auto. intro. subst. inversion H1.
  - destruct_all. assert (A:=H). rewrite <- back_edge_equiv in H. rewrite D.back_edge_def in H. 
    unfold P.nontrivial_cyclic. destruct_all.
    unfold back_edge' in A. destruct_all. rewrite <- F.desc_list_iff_desc in H0.
    destruct_all. apply desc_implies_path in H0. exists x0. exists (x :: x2). split.
    exists x. split. auto. solve_in. simpl. simplify.
Qed.

(** ** Topological Sorting **)

(*CLRS defines a simple topological sorting algorithm: run DFS and return a list of the vertices reverse sorted
  by finish time. We will prove that this is a valid topological ordering*)

(*The resulting list is sorted in reverse order of finish time*)


(*Helpful to know that color is total*)
Lemma color_total: forall g o s u,
  D.white o g s u = true \/ D.gray o g s u = true \/ D.black o g s u = true.
Proof.
  intros. rewrite D.white_def. rewrite D.gray_def. rewrite D.black_def. simplify. repeat(rewrite Nat.ltb_lt).
  repeat(rewrite Nat.leb_le). omega.
Qed.

(*A key lemma for topological sorting: If the edge (u,v) exists, then u finishes after v*)
Lemma finish_time_edge: forall g o u v,
  P.acyclic g ->
  G.contains_edge g u v = true ->
  D.f_time o g v < D.f_time o g u.
Proof.
  intros. assert (G.contains_vertex g u = true) by (eapply G.contains_edge_1; apply H0).
  pose proof (D.discovery_exists o g u H1). destruct_all.
  pose proof (color_total g o x v). destruct H3.
  - assert (F.desc (D.dfs_forest o g) u v). eapply D.white_path_theorem.
    apply H1. intros. exists nil. rewrite P.path_list_ind_rev. split.
    simpl. apply H0. split. intros. inversion H5.
    assert (s = x). eapply D.state_time_unique. omega. subst. apply H3.
    eapply D.descendant_iff_interval in H4. omega. apply H1. eapply G.contains_edge_2. apply H0.
  - destruct H3. assert (H4:= H). apply P.acylic_no_nontrivial in H. exfalso. apply H.
    rewrite (cycle_iff_back_edge _ o). unfold back_edge'. exists u. exists v. exists x. split.
    intro. subst. unfold P.acyclic in H4. apply H4. exists v. 
    constructor. apply H0. split. apply H2. split. apply H0. apply H3. rewrite D.black_def in H3.
    rewrite Nat.leb_le in H3. 
    assert ((D.f_time o g v = D.time_of_state o g x) \/ (D.f_time o g v < D.time_of_state o g x)) by omega.
    assert (G.contains_vertex g v = true). eapply G.contains_edge_2. apply H0.
    destruct H4. pose proof (D.all_times_unique o g v u H5 H1). omega. assert (u <> v).
    intro. subst. unfold P.acyclic in H. apply H. exists v. constructor. apply H0.
    pose proof (D.parentheses_theorem o g u v H1 H5 H6). omega.
Qed.

(** Topological Sort Correctness **)
(*Given a list of vertices sorted by reverse order of finish time, if g is a DAG and every vertex in g is in
  the list, then the list is a topological sorting of g*)
Lemma topological_sort_correct: forall l g o,
  P.acyclic g ->
  (forall v, G.contains_vertex g v = true <-> In v l) ->
  StronglySorted (D.rev_f_time o g) l ->
  G.topological_sort l g.
Proof.
  intros. rewrite G.topological_sort_def. split. apply H0. split. apply (StronglySorted_NoDup _ (D.rev_f_time o g)).
  intros. intro. rewrite D.rev_f_time_def in H2.  omega. apply H1.
  intros. subst. apply sort_app in H1. destruct H1. inversion H2; subst.
  rewrite Forall_forall in H6. destruct (G.contains_edge g v u) eqn : ?.
  specialize (H6 v). assert (D.rev_f_time o g u v). apply H6. solve_in.
  rewrite D.rev_f_time_def in H3. apply (finish_time_edge g o v u) in Heqb.
  omega. apply H. reflexivity.
Qed. 

(** General Results about DFS Trees and their times **)

(*TODO: This is more or less copy and pasted from SCCAlg. Try to see if I can reduce the copy and pasting*)
Lemma get_tree_in_graph: forall g o v t,
  InA S.Equal t (F.get_trees (D.dfs_forest o g)) ->
  S.In v t ->
  G.contains_vertex g v = true.
Proof.
  intros. eapply F.get_trees_root in H. destruct H. destruct_all. destruct (O.eq_dec v x).
  unfold O.eq in e. subst. eapply D.same_vertices. apply F.is_root_5. apply H.
  rewrite H2 in H0. apply F.desc_in_forest in H0. eapply D.same_vertices. apply H0. auto.
Qed.

Lemma get_trees_partition_graph : forall o g,
  Pa.partition G.contains_vertex g (F.get_trees (D.dfs_forest o g)). 
Proof.
  intros. unfold Pa.partition. pose proof (F.get_trees_partition (D.dfs_forest o g)).
  unfold F.P.partition in H. destruct_all. split. intros. apply H.
  apply D.same_vertices. apply H1. apply H0.
Qed.

(*Given two DFS trees t1 and t2 with roots r1 and r2, r1 is discovered before r2 iff it
  finishes before r2*)
Lemma root_times: forall g o t1 t2 r1 r2,
  InA S.Equal t1 (F.get_trees (D.dfs_forest o g)) ->
  InA S.Equal t2 (F.get_trees (D.dfs_forest o g)) ->
  S.In r1 t1 ->
  S.In r2 t2 ->
  F.is_root (D.dfs_forest o g) r1 = true ->
  F.is_root (D.dfs_forest o g) r2 = true ->
  D.f_time o g r1 < D.f_time o g r2 <-> D.d_time o g r1 < D.d_time o g r2.
Proof.
  intros. assert (G.contains_vertex g r1 = true). eapply get_tree_in_graph. apply H. assumption.
  assert (G.contains_vertex g r2 = true). eapply get_tree_in_graph. apply H0. assumption.
  destruct (O.eq_dec r1 r2). unfold O.eq in e. subst. omega.
  assert (r1 <> r2) by auto. clear n. pose proof (D.parentheses_theorem o g r1 r2 H5 H6 H7).
  destruct H8.
  - assert (F.desc (D.dfs_forest o g) r1 r2). eapply D.descendant_iff_interval; try(assumption); try(omega).
    eapply F.root_no_desc in H4. exfalso. apply H4. apply H9. eapply D.same_vertices. assumption.
  - destruct H8.
    + assert (F.desc (D.dfs_forest o g) r2 r1). eapply D.descendant_iff_interval; try(assumption); try(omega).
      eapply F.root_no_desc in H3. exfalso. apply H3. apply H9. eapply D.same_vertices. assumption.
    + omega.
Qed.

(*Given 2 DFS trees t1 and t2 and roots r1 and r2, if r1 finishes before r2, then r1 finishes before r2 starts*)
Lemma root_start_end: forall g o t1 t2 r1 r2,
  InA S.Equal t1 (F.get_trees (D.dfs_forest o g)) ->
  InA S.Equal t2 (F.get_trees (D.dfs_forest o g)) ->
  S.In r1 t1 ->
  S.In r2 t2 ->
  F.is_root (D.dfs_forest o g) r1 = true ->
  F.is_root (D.dfs_forest o g) r2 = true ->
  D.f_time o g r1 < D.f_time o g r2 ->
  D.f_time o g r1 < D.d_time o g r2.
Proof.
  intros. assert (G.contains_vertex g r1 = true). eapply get_tree_in_graph. apply H. assumption.
  assert (G.contains_vertex g r2 = true). eapply get_tree_in_graph. apply H0. assumption.
  destruct (O.eq_dec r1 r2). unfold O.eq in e. subst. omega.
  assert (r1 <> r2) by auto. clear n. pose proof (D.parentheses_theorem o g r1 r2 H6 H7 H8).
  destruct H9.
  - assert (F.desc (D.dfs_forest o g) r1 r2). eapply D.descendant_iff_interval; try(assumption); try(omega).
    eapply F.root_no_desc in H4. exfalso. apply H4. apply H10. eapply D.same_vertices. assumption.
  - destruct H9.
    + assert (F.desc (D.dfs_forest o g) r2 r1). eapply D.descendant_iff_interval; try(assumption); try(omega).
      eapply F.root_no_desc in H3. exfalso. apply H3. apply H10. eapply D.same_vertices. assumption.
    + omega.
Qed.
    
(*Let t1 and t2 be 2 DFS trees with roots r1 and r2. Let u be in t1 and v be in t2. Then u finishes
  before v is discovered*)
Lemma tree_times: forall g o t1 t2 u v r1 r2,
  InA S.Equal t1 (F.get_trees (D.dfs_forest o g)) ->
  InA S.Equal t2 (F.get_trees (D.dfs_forest o g)) ->
  S.In r1 t1 ->
  S.In r2 t2 ->
  F.is_root (D.dfs_forest o g) r1 = true ->
  F.is_root (D.dfs_forest o g) r2 = true ->
  D.f_time o g r1 < D.f_time o g r2 ->
  S.In u t1 ->
  S.In v t2 ->
  D.f_time o g u < D.d_time o g v.
Proof.
  intros. assert (G.contains_vertex g u = true).
  eapply get_tree_in_graph. apply H. apply H6.
  assert (G.contains_vertex g v = true). eapply get_tree_in_graph. apply H0. apply H7.
  assert (A :~S.In v t1 /\ ~S.In u t2). { split; intro;
  pose proof (get_trees_partition_graph o g); unfold Pa.partition in H11;
  destruct_all; specialize (H12 t1 t2); destruct (S.equal t1 t2) eqn : ?.
  - apply S.equal_2 in Heqb; rewrite <- Heqb in H2.  assert (r1 = r2). { eapply F.tree_root_unique.
    apply H. apply H3. apply H4. apply H1. apply H2. } subst. omega.
  - assert (Pa.disjoint t1 t2). apply H12. reflexivity. assumption. assumption. unfold Pa.disjoint in H13.
    apply (H13 v). split; assumption.
  - apply S.equal_2 in Heqb; rewrite <- Heqb in H2.  assert (r1 = r2). { eapply F.tree_root_unique.
    apply H. apply H3. apply H4. apply H1. apply H2. } subst. omega.
  - assert (Pa.disjoint t1 t2). apply H12. reflexivity. assumption. assumption. unfold Pa.disjoint in H13.
    apply (H13 u). split; assumption. }
  assert (u <> v). { intro. subst. destruct_all. contradiction. }
  pose proof (D.parentheses_theorem o g u v H8 H9 H10). destruct H11.
  - assert (F.desc (D.dfs_forest o g) u v). eapply D.descendant_iff_interval. apply H8.
    apply H9. omega. assert (F.desc (D.dfs_forest o g) r1 v). { assert (R:=H).
    apply F.get_trees_root in H. destruct_all. assert (x = r1). eapply F.tree_root_unique.
    apply R. all: try(assumption). subst. destruct (O.eq_dec u r1). unfold O.eq in e. subst. assumption.
    eapply F.is_descendant_trans. apply (H18 u). auto. assumption. assumption. }
    assert (S.In v t1). { assert (R:=H).
    apply F.get_trees_root in H. destruct_all. assert (x = r1). eapply F.tree_root_unique.
    apply R. assumption. assumption. assumption. assumption. subst. destruct (O.eq_dec v r1). unfold O.eq in e.
    subst. assumption. apply H19. auto. assumption. } destruct_all; contradiction.
  - destruct H11.
    +  assert (F.desc (D.dfs_forest o g) v u). eapply D.descendant_iff_interval. apply H9.
    apply H8. omega. assert (F.desc (D.dfs_forest o g) r2 u). { assert (R:=H0).
    apply F.get_trees_root in H0. destruct_all. assert (x = r2). eapply F.tree_root_unique.
    apply R. all: try(assumption). subst. destruct (O.eq_dec v r2). unfold O.eq in e. subst. assumption.
    eapply F.is_descendant_trans. apply (H18 v). auto. assumption. assumption. }
    assert (S.In u t2). { assert (R:=H0).
    apply F.get_trees_root in H0. destruct_all. assert (x = r2). eapply F.tree_root_unique.
    apply R. assumption. assumption. assumption. assumption. subst. destruct (O.eq_dec u r2). unfold O.eq in e.
    subst. assumption. apply H19. auto. assumption. } destruct_all; contradiction.
    + destruct H11.
      * omega.
      * assert (R1 := H). assert (R2 := H0). eapply F.get_trees_root in H. eapply F.get_trees_root in H0.
        destruct_all. assert (x0 = r1). eapply F.tree_root_unique. apply R1. all: try(assumption). subst.
        assert (x = r2). eapply F.tree_root_unique. apply R2. all: try(assumption). subst.
        destruct (O.eq_dec u r1). unfold O.eq in e. subst. destruct (O.eq_dec v r2). unfold O.eq in e. subst.
        omega. assert (F.desc (D.dfs_forest o g) r2 v). eapply H17. auto. assumption.
        eapply D.descendant_iff_interval in H20. assert (D.d_time o g r1 < D.d_time o g r2).
        eapply root_times. apply R1. apply R2. all: try(assumption). omega. eapply get_tree_in_graph.
        apply R2. assumption. 
        assert (F.desc (D.dfs_forest o g) r1 u). eapply H19. auto. assumption.
        eapply D.descendant_iff_interval in H20. assert (D.d_time o g r1 < D.d_time o g r2).
        eapply root_times. apply R1. apply R2. all: try(assumption). destruct (O.eq_dec v r2). unfold O.eq in e.
        subst. omega.  assert (F.desc (D.dfs_forest o g) r2 v). eapply H17. auto. assumption.
        eapply D.descendant_iff_interval in H22. eapply root_start_end in H5. omega. apply R1. apply R2.
        all: try(assumption). eapply get_tree_in_graph. apply R2. assumption. 
        eapply get_tree_in_graph. apply R1. assumption.
Qed. 

(*Every path has a vertex along it that was discovered first*)
Lemma path_has_first_discovered: forall o g u v l,
  P.path_list_rev g u v l = true ->
  NoDup l -> ~In u l -> ~In v l ->
   u <> v ->
  exists x, (x = u \/ x = v \/ In x l) /\ (forall y,  (y = u \/ y = v \/ In y l) ->y <> x ->
  D.d_time o g x < D.d_time o g y).
Proof.
  intros. 
  remember (M.min_elt_path u v (D.d_time o g) l) as y.
  exists y. split. symmetry in Heqy. eapply M.min_elt_path_in in Heqy. simplify. 
  eapply M.min_elt_path_finds_min. intros.
  pose proof (P.path_implies_in_graph g u v l H).
  apply (D.d_times_unique o g x0 y0). destruct H4. subst. simplify. destruct H4; subst; simplify.
  destruct H5. subst. simplify. destruct H5; subst; simplify. apply H6. 
  all: symmetry in Heqy; assumption.
Qed.

(*Important lemma characterizing DFS trees. TODO: try to see about not having to repeat it all for SCC*)
(*The proof turns out to be quite complicated.
  Essentially, assume there is a path and let x be the element in the path that is first discovered.
  If x is in t2 (the later tree), this contradicts the fact that u, the starting vertex, was in an
  earlier tree. If x is in an earlier tree, then v (the end vertex) becomes a descendant of x by
  the white path theorem, so v is in an earlier tree, which contradicts the fact that any two
  DFS trees are djsoint.*)
Lemma no_path_to_later_tree: forall o g t1 t2 r1 r2 u v,
  InA S.Equal t1 (F.get_trees (D.dfs_forest o g)) ->
  InA S.Equal t2 (F.get_trees (D.dfs_forest o g)) ->
  S.In r1 t1 ->
  S.In r2 t2 ->
  F.is_root (D.dfs_forest o g) r1 = true ->
  F.is_root (D.dfs_forest o g) r2 = true ->
  D.f_time o g r1 < D.f_time o g r2 ->
  S.In u t1 ->
  S.In v t2 ->
  ~P.path g u v.
Proof.
  intros. intro. assert (D.f_time o g u < D.d_time o g v). eapply tree_times.
  apply H. apply H0. apply H1. apply H2. all: try assumption.
  assert (G.contains_vertex g v = true). eapply get_tree_in_graph. apply H0. assumption.
  assert (G.contains_vertex g u = true). eapply get_tree_in_graph. apply H. assumption.
  assert (A :~S.In v t1 /\ ~S.In u t2). { split; intro;
  pose proof (get_trees_partition_graph o g); unfold Pa.partition in H13;
  destruct_all; specialize (H14 t1 t2); destruct (S.equal t1 t2) eqn : ?.
  - apply S.equal_2 in Heqb; rewrite <- Heqb in H2.  assert (r1 = r2). { eapply F.tree_root_unique.
    apply H. all: try assumption. }  subst. omega.
  - assert (Pa.disjoint t1 t2). apply H14. reflexivity. assumption. assumption. unfold Pa.disjoint in H15.
    apply (H15 v). split; assumption.
  - apply S.equal_2 in Heqb; rewrite <- Heqb in H2.  assert (r1 = r2). { eapply F.tree_root_unique.
    apply H. all: try assumption. }  subst. omega.
  - assert (Pa.disjoint t1 t2). apply H14. reflexivity. assumption. assumption. unfold Pa.disjoint in H15.
    apply (H15 u). split; assumption. } destruct A as [N1 N2].
  assert (N: u <> v). intro. subst. contradiction.
  rewrite P.path_path_list_rev in H8. destruct H8 as [l]. eapply P.path_no_dups in H8.
  destruct H8 as [ld]. destruct_all. assert (A:= H8). apply (path_has_first_discovered o _ _ _ ) in A.
  destruct A as [fst]. destruct_all. assert (R1 := H). assert (R2 := H0). eapply F.get_trees_root in H.
  destruct H as [x]. destruct H as [HR1 HI1]. destruct HI1 as [HI1 HD1]. assert (x = r1). eapply F.tree_root_unique.
  apply R1. all: try assumption. subst. eapply F.get_trees_root in H0. destruct H0 as [x]. destruct H as [HR2 HI2].
  destruct HI2 as [HI2 HD2]. assert (x = r2). eapply F.tree_root_unique. apply R2. all: try assumption. subst. 
  clear HR1. clear HR2. clear HI1. clear HI2. 
  destruct H16. subst. 
  - assert (F.desc (D.dfs_forest o g) u v). { eapply D.white_path_theorem. apply H11. intros.
    exists ld. rewrite D.P.path_list_ind_rev. split. apply H8. split.
    + intros. rewrite D.white_def. rewrite H. rewrite Nat.ltb_lt. apply H17. simplify. intro. subst. contradiction.
    + rewrite D.white_def. rewrite H. rewrite Nat.ltb_lt. apply H17. simplify. intro. subst. contradiction. }
   assert (F.desc (D.dfs_forest o g) r1 v). destruct (O.eq_dec r1 u). unfold O.eq in e. subst.
   assumption. eapply F.is_descendant_trans. apply (HD1 u). auto. assumption. assumption.
   rewrite <- HD1 in H0. contradiction. intro. subst. contradiction.
  - destruct H. 
    + subst. specialize (H17 u). assert (D.d_time o g v < D.d_time o g u).
      apply H17. left. reflexivity. apply N.
      assert (D.d_time o g u < D.f_time o g u). 
      pose proof (D.parentheses_theorem o g u v H11 H10 N). omega. omega.
    + destruct (P2.In_dec fst t2).
      * specialize (H17 u). assert (D.d_time o g fst < D.d_time o g u).
        apply H17. left. reflexivity. intro. subst. contradiction.
        assert (D.f_time o g u < D.d_time o g fst). eapply tree_times.
        apply R1. apply R2. apply H1. apply H2. all: try assumption.
        assert (D.d_time o g u < D.f_time o g u). 
        pose proof (D.parentheses_theorem o g u v H11 H10 N). omega. omega.
      * assert (G.contains_vertex g fst = true). eapply P.path_implies_in_graph.
        apply H8. apply H. pose proof (get_trees_partition_graph o g).
        unfold Pa.partition in H16. destruct H16. specialize (H16 _ H0). destruct H16 as [t3].
        destruct H16 as [R3 H16]. assert (A:= R3). eapply F.get_trees_root in A. destruct A as [r3].
        destruct H19 as [HR3 HI3]. destruct HI3 as [HI3 HD3].
        assert (D.f_time o g r3 > D.f_time o g r2 \/ D.f_time o g r3 = D.f_time o g r2 \/
                D.f_time o g r3 < D.f_time o g r2) by omega.
        destruct H19.
        -- assert (D.f_time o g r2 < D.d_time o g r3). eapply root_start_end.
           apply R2. apply R3. all: try assumption. 
           destruct (O.eq_dec v r2). unfold O.eq in e. subst. destruct (O.eq_dec fst r3). unfold O.eq in e.
           subst. specialize (H17 r2). assert (D.d_time o g r3 < D.d_time o g r2).
           apply H17. simplify. intro. subst. contradiction. 
           assert (D.d_time o g r2 < D.f_time o g r2). assert (r2 <> u) by auto.
           pose proof (D.parentheses_theorem o g r2 u H10 H11 H22). omega. omega.
           assert (F.desc (D.dfs_forest o g ) r3 fst). apply HD3. auto. assumption.
           apply D.descendant_iff_interval in H21. specialize (H17 r2).
           assert (D.d_time o g fst < D.d_time o g r2). apply H17. simplify.
           intro. subst. contradiction. 
            assert (D.d_time o g r2 < D.f_time o g r2). assert (r2 <> u) by auto.
           pose proof (D.parentheses_theorem o g r2 u H10 H11 H23). omega. omega.
           eapply get_tree_in_graph. apply R3. assumption. assumption.
           assert (F.desc (D.dfs_forest o g) r2 v). apply HD2. auto. assumption.
           eapply D.descendant_iff_interval in H21. destruct (O.eq_dec fst r3). unfold O.eq in e. subst.
            specialize (H17 v). assert (D.d_time o g r3 < D.d_time o g v). apply H17.
            simplify. intro. subst. contradiction. omega.
            assert (F.desc (D.dfs_forest o g) r3 fst). apply HD3. auto. assumption.
            apply D.descendant_iff_interval in H22. specialize (H17 v).
            assert (D.d_time o g fst < D.d_time o g v). apply H17. simplify.
            intro. subst. contradiction.  omega. eapply get_tree_in_graph. apply R3. assumption.
            assumption. eapply get_tree_in_graph. apply R2. assumption. assumption.
        -- destruct H19.
           ++ assert (r3 = r2). eapply D.f_times_unique. eapply get_tree_in_graph. apply R3. assumption.
              eapply get_tree_in_graph. apply R2. assumption. apply H19. subst.
              destruct (S.equal t2 t3) eqn : ?. apply S.equal_2 in Heqb. rewrite Heqb in n. contradiction.
              apply H18 in Heqb. unfold Pa.disjoint in Heqb. apply (Heqb r2). split; assumption.
              assumption. assumption.
           ++ assert (A:= H). eapply in_split_app_fst in A. destruct A as [l1]. destruct H20 as  [l2].
              destruct H20; subst. apply P.path_app in H8. destruct H8 as [HP1 HP2].
              assert (F.desc (D.dfs_forest o g) fst v). eapply D.white_path_theorem.
              assumption. intros. exists l1. rewrite D.P.path_list_ind_rev. split.
              assumption. split. intros. rewrite D.white_def. rewrite H8. rewrite Nat.ltb_lt.
              apply H17. simplify. intro. subst. apply (H21 fst). apply H20. reflexivity.
              rewrite D.white_def. rewrite H8. rewrite Nat.ltb_lt. apply H17. simplify.
              intro. subst. contradiction. destruct (O.eq_dec fst r3). unfold O.eq in e. subst.
              rewrite <- HD3 in H8. destruct (S.equal t2 t3) eqn : ?. apply S.equal_2 in Heqb.
              rewrite Heqb in n. contradiction. apply H18 in Heqb. unfold Pa.disjoint in Heqb.
              apply (Heqb v). split; assumption. assumption. assumption. intro. subst. contradiction.
              assert (F.desc (D.dfs_forest o g) r3 v). eapply F.is_descendant_trans. apply (HD3 fst).
              auto. assumption. assumption. rewrite <- HD3 in H20. destruct (S.equal t2 t3) eqn : ?.
              apply S.equal_2 in Heqb. rewrite Heqb in n. contradiction. apply H18 in Heqb.
              unfold Pa.disjoint in Heqb. apply (Heqb v). split; assumption. assumption. assumption.
              intro. subst. apply F.desc_neq in H20. contradiction. apply O.eq_dec.
Qed.
Import SD.
(** ** Finding Connected Components **)
Lemma desc_path: forall o g u v l,
  u <> v ->
  F.desc_list (D.dfs_forest o g) u v l = true ->
  Pa.path_list_rev g u v l = true.
Proof.
  intros. generalize dependent v. induction l; intros; simpl in *.
  - eapply D.same_edges. apply H0.
  - simplify. eapply D.same_edges. apply H1. apply IHl. intros. eapply F.desc_neq.
    rewrite <- F.desc_list_iff_desc. exists l. apply H2. auto. apply H2.
Qed. 

Lemma path_equiv: forall g u v,
  Pa.path g u v <-> P.path g u v.
Proof.
  intros. split; intros; induction H; try(constructor; assumption).
  - eapply P.p_continue. apply IHpath. apply H0.
  - eapply Pa.p_continue. apply IHpath. apply H0.
Qed.

Lemma undirected_path_iff: forall g u v,
  G.undirected g ->
  Pa.path g u v <-> Pa.path g v u.
Proof.
  intros. split; intros.
  - induction H0.
    + constructor. apply H. apply H0.
    + eapply Pa.path_trans. apply Pa.p_start. apply H. apply H1. apply IHpath. apply H.
  - induction H0.
    + constructor. apply H. apply H0.
    + eapply Pa.path_trans. apply Pa.p_start. apply H. apply H1. apply IHpath. apply H.
Qed.

(*For an undirected graph, SCCs and connected components are identical. We prove that every tree in the DFS
  forest of an undirected graph is an SCC*)
Lemma undirected_tree_connected: forall g o t,
  G.undirected g ->
  InA S.Equal t (F.get_trees (D.dfs_forest o g)) ->
  strongly_connected t g.
Proof.
  intros.  assert (A:= H0). apply F.get_trees_root in H0. destruct_all.
  unfold strongly_connected. split. destruct (S.is_empty t) eqn : ?.
  apply S.is_empty_2 in Heqb. apply P2.empty_is_empty_1 in Heqb. rewrite Heqb in H1.
  rewrite P2.Dec.F.empty_iff in H1. destruct H1. reflexivity. split.
  intros. eapply get_tree_in_graph. apply A. apply H3. intros.
  destruct (O.eq_dec x x0). unfold O.eq in e. subst.
  rewrite H2 in H4. rewrite <- F.desc_list_iff_desc in H4. destruct H4 as [l].
  rewrite Pa.path_path_list_rev. exists l. eapply desc_path. auto. apply H4. auto.
  destruct (O.eq_dec x y). unfold O.eq in e. subst. rewrite (undirected_path_iff g x0 y).
  apply H2 in H3. rewrite <- F.desc_list_iff_desc in H3. destruct H3 as [l].
  rewrite Pa.path_path_list_rev. exists l. eapply desc_path. auto. apply H3. auto.
  assumption. assert (Pa.path g x0 x). rewrite undirected_path_iff. apply H2 in H3.
  rewrite <- F.desc_list_iff_desc in H3. destruct H3 as [l]. rewrite Pa.path_path_list_rev.
  exists l. eapply desc_path. auto. apply H3. auto. assumption. 
  eapply Pa.path_trans. apply H6. apply H2 in H4. rewrite <- F.desc_list_iff_desc in H4.
  destruct H4 as [l]. rewrite Pa.path_path_list_rev. exists l. eapply desc_path. auto. apply H4.
  auto.
Qed.

(*For undirected graphs, each DFS tree found is a separate connected component*)
Theorem undirected_dfs_finds_ccs: forall g o t,
  G.undirected g ->
  InA S.Equal t (F.get_trees (D.dfs_forest o g)) ->
  scc t g.
Proof.
  intros. pose proof (undirected_tree_connected g o t H H0).
  destruct (scc_dec t g). apply s. pose proof (non_scc_has_another t g H1 n).
  destruct H2 as [v]. destruct H2. assert (R:= H0). apply F.get_trees_root in H0. destruct H0 as [r1].
  destruct_all. pose proof (get_trees_partition_graph o g). unfold P.partition in H6.
  destruct H6. assert (G.contains_vertex g v = true). { unfold strongly_connected in H3. apply H3.
  apply S.add_1. reflexivity. } specialize (H6 _ H8). destruct H6 as [t2]. destruct H6.
  assert (R2 := H6). apply F.get_trees_root in H6. destruct H6 as [r2]. destruct_all.
  unfold strongly_connected in H3. destruct_all.
  assert (r1 <> v). intro. subst. pose proof (get_trees_partition_graph o g).
  unfold P.partition in H14. destruct H14. destruct (S.equal t t2) eqn : ?. apply S.equal_2 in Heqb.
  rewrite Heqb in H2. contradiction. apply H15 in Heqb. unfold P.disjoint in Heqb.
  apply (Heqb v). split; assumption. assumption. assumption.
  assert (Pa.path g r1 v). apply H13. apply S.add_2. assumption. apply S.add_1. reflexivity. apply H14.
  assert (Pa.path g v r1). apply H13. apply S.add_1. reflexivity. apply S.add_2. assumption. auto.  
  assert (D.f_time o g r1 < D.f_time o g r2 \/
          D.f_time o g r1 = D.f_time o g r2 \/
          D.f_time o g r1 > D.f_time o g r2) by omega.
  destruct H17.
  - exfalso. eapply no_path_to_later_tree. apply R. apply R2. apply H4. apply H10. assumption.
    assumption. assumption. apply H4. apply H9. apply path_equiv. apply H15.
  - destruct H17.
    + assert (r1 = r2). eapply D.f_times_unique. eapply get_tree_in_graph. apply R.
      assumption. eapply get_tree_in_graph. apply R2. assumption. apply H17. subst.
      pose proof (get_trees_partition_graph o g).
      unfold Pa.partition in H18. destruct H18. destruct (S.equal t t2) eqn : ?. apply S.equal_2 in Heqb.
      rewrite Heqb in H2. contradiction. apply H19 in Heqb. unfold P.disjoint in Heqb.
      exfalso. apply (Heqb r2). split; assumption. all: try assumption.
    + exfalso. eapply no_path_to_later_tree. apply R2. apply R. apply H10. apply H4. assumption.
      assumption. assumption. apply H9. apply H4. apply path_equiv. apply H16.
Qed.

End DerivedProofs.

(*In particular, any implementation of [DFSWithCycleDetect] is correct*)

Module CycleCorrect(O: UsualOrderedType)(S: FSetInterface.Sfun O)(G: Graph O S)(F: Forest O S)
  (D: DFSWithCycleDetect O S G F).

  Module A := (DerivedProofs O S G F D).

  Lemma cycle_detection_correct: forall g o,
    D.cycle_detect o g = true <-> A.P.nontrivial_cyclic g.
  Proof.
    intros.
    rewrite A.cycle_iff_back_edge. rewrite D.cycle_detect_back_edge. setoid_rewrite <- A.back_edge_equiv.
    reflexivity.
  Qed.

  Lemma cycle_decidable: forall g,
    A.P.nontrivial_cyclic g \/ ~ A.P.nontrivial_cyclic g.
  Proof.
    intros. destruct (D.cycle_detect None g) eqn : ?.
    rewrite cycle_detection_correct in Heqb. left. apply Heqb.
    right. intro. rewrite <- cycle_detection_correct in H. rewrite H in Heqb. inversion Heqb.
  Qed.

End CycleCorrect.

(* The same for [DFSWithTopologicalSort] *)
Module TopoSortCorrect(O: UsualOrderedType)(S: FSetInterface.Sfun O)(G: Graph O S)(F: Forest O S)
  (D: DFSWithTopologicalSort O S G F).

  Module A := (DerivedProofs O S G F D).

  Lemma topological_sort_alg_correct: forall g o,
    A.P.acyclic g ->
    G.topological_sort (D.rev_f_time_list g o) g.
  Proof.
    intros. eapply A.topological_sort_correct. apply H. apply D.topological_sort_condition.
    apply D.topological_sort_condition.
  Qed. 

End TopoSortCorrect.
   
  
