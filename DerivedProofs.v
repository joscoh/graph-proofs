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
    unfold D.white. rewrite H3. rewrite Nat.ltb_lt. apply H7. }
    eapply D.white_path_theorem. apply H2. intros.
    assert (s = x1). eapply D.state_time_unique. rewrite H3. rewrite H5. reflexivity. subst.
    exists x0. rewrite D.P.path_list_ind_rev. split. apply H0. split. apply H4. unfold D.white.
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

(*A back edge is an edge (u, v) in g such that v is gray when u is discovered*)
Definition back_edge g s u v o := D.time_of_state g s = D.d_time o g u /\ G.contains_edge g u v = true
   /\ D.gray o g s v = true.

Fixpoint first_vertex o g (l: list G.vertex) (d: G.vertex) : G.vertex :=
  match l  with
  | nil => d
  | x :: t => match t with
              | nil => x
              | _ =>  if D.d_time o g x <? D.d_time o g (first_vertex o g t d) then x else first_vertex o g t d
              end
  end.

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

Lemma path_has_smallest_vertex: forall o g l (v: G.vertex),
  l <> nil ->
  (forall x, In x l -> G.contains_vertex g x = true) ->
  exists u, In u l /\ (forall x, In x l -> x <> u -> D.d_time o g u < D.d_time o g x).
Proof.
  intros. exists (first_vertex o g l v). split. apply first_vertex_in_list. apply H.
   eapply first_vertex_finds_smallest. apply H. apply H0. apply first_vertex_in_list. apply H.
  apply H0. reflexivity.
Qed.

Lemma cycle_smallest: forall o g l v,
  l <> nil ->
  P.path_list_rev g v v l = true ->
  exists l1 u, P.path_list_rev g u u l1 = true /\ (u <> v -> In u l) /\ (u <> v -> In v l1) /\ l1 <> nil /\ (forall x, In x l1 -> x <> u ->
  D.d_time o g u < D.d_time o g x).
Proof.
  intros. assert (A:=H0). assert (forall x, In x l -> G.contains_vertex g x = true). intros.
  eapply D.P.path_implies_in_graph in H0. destruct_all. apply H3. apply H1. assert (B:= H).
  eapply (path_has_smallest_vertex o g) in H. destruct_all.
  assert (D.d_time o g x < D.d_time o g v \/ D.d_time o g v < D.d_time o g x \/ D.d_time o g x = D.d_time o g v)
  by omega. destruct H3. eapply (P.any_cycle _ _ x) in H0. destruct_all. exists x0.
  exists x. split. apply H0. split. intros. apply H. split. intros. apply H4. split. intro. subst. inversion H4.
  intros. destruct (O.eq_dec x1 v). unfold O.eq in e. subst. apply H3. apply H2.
  rewrite H5. apply H6. apply n. apply H7. apply H7. apply H.
  destruct H3. exists l. exists v. split. apply H0. split. intros. contradiction. split. intros.
  contradiction. split. apply B. intros. destruct (O.eq_dec x x0). unfold O.eq in e. subst.
  apply H3. apply H2 in H4. omega. auto. assert (x = v). eapply D.d_times_unique.
  apply H1. apply H. eapply D.P.path_implies_in_graph in H0. simplify. apply H3. subst.
   exists l. exists v. split. apply H0. split. intros. contradiction. split. intros. contradiction.
  split. apply B. apply H2. apply v. apply H1.
Qed.


(** The big result (Lemma 22.11 in CLRS) **)
(*Note that this doesn't work for self loops - although the CLRS proof fails for this case as well. However,
  this is a trivial case, since cycle detection is easy and efficient - 
  iterate over all the vertices and check for self loops*)

(*Need to know that there is another vertex in the cycle - cycle with no dups*)
(*So I don't have to repeat the same proof 3 times*)
(*Lemma smallest_at_cycle_back_edge: forall g o u l,
  P.path_list_rev g u u l = true ->
  (forall x, In x l -> D.d_time o g u < D.d_time o g x) ->
  (exists s u v, back_edge g s u v o).
Proof.
Admitted.*)

Lemma cycle_iff_back_edge: forall g o,
  P.cyclic_no_self_loop g <-> (exists s u v, back_edge g s u v o).
Proof.
  intros. split; intros.
  - unfold P.cyclic_no_self_loop in H. destruct_all.
    eapply (cycle_smallest o) in H0. destruct_all.
    eapply P.cycle_no_dups_strong in H0. destruct_all. 
    destruct x4. contradiction. simpl in *. unfold back_edge. 
    simplify.  
    (*The plan from here: (I have all the pieces)
      - At tmie d(x3), there is a white path to v
      - Therefore v is a descendant of x3
      - Therefore, x3 finishes after v
      - Therefore, at time d(v), x3 is gray
      - Then use that time for a back edge *)
 
