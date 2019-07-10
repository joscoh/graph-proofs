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
Module DerivedProofs(O: UsualOrderedType)(S: FSetInterface.Sfun O)(G: Graph O S)(F: Forest O S G)(D: DFSBase O S G F).

Module P:= D.P. 

Lemma desc_implies_path: forall g o u v l,
  F.desc_list (D.dfs_forest o g) u v l = true ->
  P.path_list_rev g u v l = true.
Proof.
  intros. generalize dependent v. induction l; intros.
  - simpl in *. eapply D.same_edges. apply H. 
  - simpl in *. simplify. eapply D.same_edges. apply H0. 
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

End DerivedProofs.

  
