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
Require Import Coq.FSets.FSetProperties.
Require Import DerivedProofs.
Require Import SCCDef.
Require Import Coq.Classes.RelationClasses.

Module SCCAlg(O: UsualOrderedType)(S: FSetInterface.Sfun O)(G: Graph O S)(F: Forest O S G)(D: DFSBase)
  (D' : DFSCustomOrder).

  
  Module P2 := FSetProperties.WProperties_fun O S.
  Module O2 := OrderedTypeFacts O.
  Module SN := Helper.SetNeq O S.
  Module SC := SCCDef.SCCDef O S G.
  Module Pa := SC.Pa.
  Import SC.
  
(** Correctness of SCC algorithm **)

(*Lemma 22.13 in CLRS*)
Lemma scc_path_one_dir: forall g C C' u v u' v',
  scc C g ->
  scc C' g ->
  S.equal C C' = false ->
  S.In u C ->
  S.In v C ->
  S.In u' C' ->
  S.In v' C' ->
  Pa.path g u u' ->
  ~Pa.path g v' v.
Proof.
  intros. intro. rewrite Pa.path_path_list_rev in H6.
  rewrite Pa.path_path_list_rev in H7. destruct_all.
  assert (A:= H0).
  unfold scc in H0. destruct H0. unfold strongly_connected in H0. destruct_all.
  destruct (O.eq_dec u' v'). unfold O.eq in e. subst.
  assert (Pa.path_list_rev g u v (x ++ v' :: x0) = true). apply Pa.path_app. split; assumption.
  assert (S.In v' C). eapply scc_path_within. apply H. apply H2. apply H3. apply H11. solve_in.
  eapply neq_scc_disjoint in H1. apply H1. split. apply H12. apply H4. apply H. apply A.
  assert (Pa.path g u' v'). apply H10; try(assumption). rewrite Pa.path_path_list_rev in H11. destruct H11.
  assert (Pa.path_list_rev g u v (x ++ v' :: x1 ++ u' :: x0) = true). apply Pa.path_app. split. apply H7.
  apply Pa.path_app. split. apply H11. apply H6. assert (S.In v' C). eapply scc_path_within. apply H.
  apply H2. apply H3. apply H12. solve_in. eapply neq_scc_disjoint in H1. apply H1. split. 
  apply H13. apply H5. apply H. apply A.
Qed.

(** Results about times of 1st DFS Pass **)
Module D1 := (D O S G F).
Module Der1 := (DerivedProofs.DerivedProofs O S G F D1).

(*Finding the minimum element in a list based on a given function (needed to find vertex with smallest
  discovery time in SCC*)
Definition min_elt_list (l: list O.t) (f: O.t -> nat) : option O.t :=
  fold_right (fun x s => match s with
                     | None => Some x
                     | Some y =>  if (f x <? f y) then Some x else s
                     end) None l.

Definition min_elt_set (c: S.t) (f: O.t -> nat) : option O.t:=
  min_elt_list (S.elements c) f.

Lemma min_elt_list_none_iff_empty: forall l f,
  min_elt_list l f = None <-> l = nil.
Proof.
  intros. induction l; simpl in *; split; intros; try(reflexivity).
  - destruct (min_elt_list l f) eqn : ?.
    + destruct (f a <? f t); inversion H.
    + inversion H.
  - inversion H.
Qed.

Lemma min_elt_list_in_list: forall f x l,
  min_elt_list l f = Some x ->
  In x l.
Proof.
  intros. generalize dependent x. induction l; intros.
  - simpl in H. inversion H.
  - simpl in *. destruct (min_elt_list l f) eqn : ?.
    + destruct (f a <? f t) eqn : ?; inversion H; subst. left. reflexivity. right. apply IHl.
      reflexivity.
    + inversion H; subst. left. reflexivity.
Qed.

Lemma min_elt_list_finds_min: forall f x l,
  (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
  min_elt_list l f = Some x ->
  forall y, In y l -> y <> x -> f x < f y.
Proof.
  intros. generalize dependent x. induction l; intros.
  - destruct H1.
  - simpl in H1. simpl in H0. destruct H1.
    + subst. destruct (min_elt_list l f ) eqn : ?.
      * destruct (f y <? f t ) eqn : ?.
        -- inversion H0; subst. contradiction.
        -- inversion H0; subst.  rewrite Nat.ltb_antisym in Heqb. simplify.
        rewrite Nat.leb_le in Heqb. assert (f x < f y \/ f x = f y) by omega.
        destruct H1. apply H1. apply H in H1. subst. contradiction. simpl. right.
        eapply  min_elt_list_in_list. apply Heqo. left. reflexivity.
      * inversion H0; subst. contradiction.
    + destruct (min_elt_list l f) eqn : ?. destruct (f a <? f t ) eqn : ?.
      * rewrite Nat.ltb_lt in Heqb. inversion H0; subst. destruct (O.eq_dec t y). unfold O.eq in e.
        subst. apply Heqb. assert (f t < f y). apply IHl. intros. apply H; try(solve_in).
        apply H1. reflexivity. auto. omega.
      * inversion H0; subst.  rewrite Nat.ltb_antisym in Heqb. simplify.
      * inversion H0; subst. rewrite min_elt_list_none_iff_empty in Heqo. subst. inversion H1.
Qed.

Lemma min_elt_set_none_iff_empty: forall s f,
  min_elt_set s f = None <-> S.is_empty s = true.
Proof.
  intros. unfold min_elt_set. rewrite min_elt_list_none_iff_empty. rewrite <- P2.elements_Empty.
  apply P2.FM.is_empty_iff.
Qed.

Lemma min_elt_set_finds_min: forall f x s,
  (forall x y, S.In x s -> S.In y s -> f x = f y -> x = y) ->
  min_elt_set s f = Some x ->
  forall y, S.In y s -> y <> x -> f x < f y.
Proof.
  intros. unfold min_elt_set in H0. eapply min_elt_list_finds_min in H0. apply H0. intros.
  apply H. apply S.elements_2. rewrite <- In_InA_equiv. apply H3.
  apply S.elements_2. rewrite <- In_InA_equiv. apply H4. apply H5.
  apply S.elements_1 in H1. rewrite <- In_InA_equiv in H1. apply H1. apply H2.
Qed.

Lemma min_elt_set_in_set: forall f x s,
  min_elt_set s f = Some x ->
  S.In x s.
Proof.
  intros. unfold min_elt_set in H. apply min_elt_list_in_list in H.
  rewrite In_InA_equiv in H.
  apply S.elements_2 in H. apply H.
Qed.

Lemma find_min_scc_exists: forall f g c,
  scc c g ->
  exists x, min_elt_set c f = Some x.
Proof.
  intros. destruct (min_elt_set c f) eqn : ?. exists t. reflexivity.
  rewrite min_elt_set_none_iff_empty in Heqo. unfold scc in H. destruct H.
  unfold strongly_connected in H. destruct_all. rewrite H in Heqo. inversion Heqo.
Qed.

(*Definition of discovery time of SCC - I define it as the vertex that is discovered first (rather than the
  time*)
Definition d_time_scc g c (H: scc c g) :=
  min_elt_set c (D1.d_time None g).

(*The same but for max/finish time*)

Definition max_elt_list (l: list O.t) (f: O.t -> nat) : option O.t :=
  fold_right (fun x s => match s with
                     | None => Some x
                     | Some y =>  if (f y <? f x) then Some x else s
                     end) None l.

Definition max_elt_set (c: S.t) (f: O.t -> nat) : option O.t:=
  max_elt_list (S.elements c) f.

Lemma max_elt_list_none_iff_empty: forall l f,
  max_elt_list l f = None <-> l = nil.
Proof.
  intros. induction l; simpl in *; split; intros; try(reflexivity).
  - destruct (max_elt_list l f) eqn : ?.
    + destruct (f t <? f a); inversion H.
    + inversion H.
  - inversion H.
Qed.

Lemma max_elt_list_in_list: forall f x l,
  max_elt_list l f = Some x ->
  In x l.
Proof.
  intros. generalize dependent x. induction l; intros.
  - simpl in H. inversion H.
  - simpl in *. destruct (max_elt_list l f) eqn : ?.
    + destruct (f t <? f a) eqn : ?; inversion H; subst. left. reflexivity. right. apply IHl.
      reflexivity.
    + inversion H; subst. left. reflexivity.
Qed.

Lemma max_elt_list_finds_max: forall f x l,
  (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
  max_elt_list l f = Some x ->
  forall y, In y l -> y <> x -> f y < f x.
Proof.
  intros. generalize dependent x. induction l; intros.
  - destruct H1.
  - simpl in H1. simpl in H0. destruct H1.
    + subst. destruct (max_elt_list l f ) eqn : ?.
      * destruct (f t <? f y ) eqn : ?.
        -- inversion H0; subst. contradiction.
        -- inversion H0; subst.  rewrite Nat.ltb_antisym in Heqb. simplify.
        rewrite Nat.leb_le in Heqb. assert (f y < f x \/ f y = f x) by omega.
        destruct H1. apply H1. apply H in H1. subst. contradiction. left. reflexivity.
        right. eapply max_elt_list_in_list. apply Heqo.
      * inversion H0; subst. contradiction.
    + destruct (max_elt_list l f) eqn : ?. destruct (f t <? f a ) eqn : ?.
      * rewrite Nat.ltb_lt in Heqb. inversion H0; subst. destruct (O.eq_dec t y). unfold O.eq in e.
        subst. apply Heqb. assert (f y < f t). apply IHl. intros. apply H; try(solve_in). apply H1.
        reflexivity. auto. omega.
      * inversion H0; subst.  rewrite Nat.ltb_antisym in Heqb. simplify.
      * inversion H0; subst. rewrite max_elt_list_none_iff_empty in Heqo. subst. inversion H1.
Qed.

Lemma max_elt_set_none_iff_empty: forall s f,
  max_elt_set s f = None <-> S.is_empty s = true.
Proof.
  intros. unfold max_elt_set. rewrite max_elt_list_none_iff_empty. rewrite <- P2.elements_Empty.
  apply P2.FM.is_empty_iff.
Qed.

Lemma max_elt_set_finds_max: forall f x s,
  (forall x y, S.In x s -> S.In y s -> f x = f y -> x = y) ->
  max_elt_set s f = Some x ->
  forall y, S.In y s -> y <> x -> f y < f x.
Proof.
  intros. unfold max_elt_set in H0. eapply max_elt_list_finds_max in H0. apply H0. intros.
  apply H. apply S.elements_2. rewrite <- In_InA_equiv. apply H3.
  apply S.elements_2. rewrite <- In_InA_equiv. apply H4. apply H5.
  apply S.elements_1 in H1. rewrite <- In_InA_equiv in H1. apply H1. apply H2.
Qed.

Lemma max_elt_set_in_set: forall f x s,
  max_elt_set s f = Some x ->
  S.In x s.
Proof.
  intros. unfold max_elt_set in H. apply max_elt_list_in_list in H.
  rewrite In_InA_equiv in H.
  apply S.elements_2 in H. apply H.
Qed.

Lemma find_max_scc_exists: forall f g c,
  scc c g ->
  exists x, max_elt_set c f = Some x.
Proof.
  intros. destruct (max_elt_set c f) eqn : ?. exists t. reflexivity.
  rewrite max_elt_set_none_iff_empty in Heqo. unfold scc in H. destruct H.
  unfold strongly_connected in H. destruct_all. rewrite H in Heqo. inversion Heqo.
Qed.

(*Definition of finish time of SCC*)
Definition f_time_scc g c (H: scc c g) :=
  max_elt_set c (D1.f_time None g).

(*This is a consequence of either my poor planning or a less than optimal use of modules*)
Lemma path_module_equiv: forall g x y,
  Pa.path g x y <-> D1.P.path g x y.
Proof.
  intros. split; intros; induction H.
  - constructor. apply H.
  - eapply D1.P.p_continue. apply IHpath. apply H0.
  - constructor. apply H.
  - eapply Pa.p_continue. apply IHpath. apply H0.
Qed. 

(*A major lemma in establishing the correctness of the SCC algorithm: If we have two distinct SCCs C and C' and
  there is an edge from C to C', then f(C) > f(C') (implies that the SCC with largest finish times is a source
  node in G^SCC*)
(*Lemma 22.14 in CLRS*)
Lemma scc_finish_time: forall g c c' u v (Hc: scc c g) (Hc': scc c' g) x y,
  S.equal c c' = false ->
  G.contains_edge g u v = true ->
  S.In u c ->
  S.In v c' ->
  f_time_scc g c Hc = Some x ->
  f_time_scc g c' Hc' = Some y ->
  D1.f_time None g x > D1.f_time None g y.
Proof.
  intros. assert (exists x, d_time_scc g c Hc = Some x). unfold d_time_scc. eapply find_min_scc_exists.
  apply Hc. assert (exists x, d_time_scc g c' Hc' = Some x). unfold d_time_scc. eapply find_min_scc_exists.
  apply Hc'. destruct_all. assert (((D1.d_time None g x1) > (D1.d_time None g x0)) \/
  ((D1.d_time None g x1) < (D1.d_time None g x0)) \/ ((D1.d_time None g x1) = (D1.d_time None g x0))) by omega.
  destruct H7. (*D(c) > D(c')*)
  (*Proof- at time d[x0] all vertices in c' are white, so all descendants of x0, so x0 finishes after all of them,
    so x0 = y*)
  assert (S.In x0 c'). { unfold d_time_scc in H6. apply min_elt_set_in_set in H6. apply H6. }
  assert (A:= Hc). assert (B:= Hc').
  unfold scc in Hc. unfold scc in Hc'. destruct Hc. destruct_all.
  unfold strongly_connected in s0. unfold strongly_connected in s. destruct_all.
  assert (G.contains_vertex g x0 = true). apply e0. apply H8. 
  pose proof (D1.discovery_exists None g x0 H9). destruct H10 as [s].
  assert (forall v, S.In v c' -> v <> x0 -> D1.white None g s v = true). { intros.
  rewrite D1.white_def. rewrite Nat.ltb_lt. unfold d_time_scc in H6.
   eapply min_elt_set_finds_min in H6. rewrite <- H10 in H6. apply H6. intros.
  eapply D1.d_times_unique. apply e0. apply H13. apply e0. apply H14. apply H15.
  apply H11. apply H12. }
  assert (forall v, S.In v c' -> v <> x0 -> exists l, D1.P.path_list_ind g x0 v (fun x => D1.white None g s x) l). {
  intros. assert (C:=H12). apply (p x0) in H12. rewrite path_module_equiv in H12. 
  rewrite D1.P.path_path_list_rev in H12.
  destruct H12 as [l]. assert (exists l, D1.P.path_list_rev g x0 v0 l = true). exists l. apply H12.
  apply Der1.unique_paths in H14. destruct_all. exists x2. rewrite D1.P.path_list_ind_rev. split.
  apply H14. split. intros. eapply scc_path_within in H14. apply H11. apply H14. auto. intro. subst. contradiction.
  assumption. assumption. assumption. assumption. apply H11. assumption. assumption. auto. assumption. auto. }
  assert (forall v, S.In v c' -> v <> x0 -> F.desc (D1.dfs_forest None g) x0 v). intros. apply D1.white_path_theorem.
  apply e0. apply H8. intros. 
  assert (s = s0). eapply D1.state_time_unique. omega. subst. apply H12; try(assumption).
  assert (x0 = y). { destruct (O.eq_dec x0 y). apply e3. assert (D1.f_time None g x0 < D1.f_time None g y).
  unfold f_time_scc in H4. eapply max_elt_set_finds_max in H4. apply H4. intros.
  eapply D1.f_times_unique. apply e0. apply H14. apply e0. apply H15. rewrite H16. reflexivity. apply H8.
   auto. assert (F.desc (D1.dfs_forest None g) x0 y). apply H13. eapply max_elt_set_in_set. unfold f_time_scc in H4.
   apply H4. auto. rewrite D1.descendant_iff_interval in H15. omega. apply e0. apply H8. apply e0.
  eapply max_elt_set_in_set. unfold f_time_scc in H4. apply H4. }
  subst. (*Now we know that start and finish vertex are the same, need to show that all vertices in c are white
  when y finishes*)
  pose proof (D1.finish_exists None g y H9). destruct H14 as [s']. 
  assert (forall x, S.In x c -> D1.white None g s' x = true). { intros.
  assert (D1.white None g s x0 = true). rewrite D1.white_def. rewrite H10. destruct (O.eq_dec x0 x1).
  unfold O.eq in e3. subst. rewrite Nat.ltb_lt. omega. unfold d_time_scc in H5.
  eapply min_elt_set_finds_min in H5. assert ( D1.d_time None g x1 < D1.d_time None g x0). apply H5.
  rewrite Nat.ltb_lt. omega. intros. eapply D1.d_times_unique. apply e2. assumption. apply e2. assumption.
  rewrite H18. reflexivity. assumption. apply n1. 
  pose proof (Der1.color_total g None s' x0). destruct H17. apply H17. destruct H17.
  - rewrite D1.gray_def in H17. simplify. rewrite H14 in H18. rewrite H14 in H19.
    rewrite D1.white_def in H16. rewrite H10 in H16. 
    assert (G.contains_vertex g x0 = true). apply e2. apply H15.
    assert (y <> x0). intro. subst. eapply neq_scc_disjoint in H. apply H. split. apply H15. assumption.
    apply A. assumption.
    pose proof (D1.parentheses_theorem None g y x0 H9 H17 H20). rewrite Nat.ltb_lt in H16.
    rewrite Nat.ltb_lt in H18. rewrite Nat.leb_le in H19. omega.
  - rewrite D1.white_def in H16. rewrite D1.black_def in H17. rewrite H10 in H16. rewrite H14 in H17.
    rewrite Nat.ltb_lt in H16. rewrite Nat.leb_le in H17. assert (y <> x0). intro. subst.
    eapply neq_scc_disjoint in H. apply H. split. apply H15. assumption. apply A. assumption.
    assert ((D1.f_time None g x0 = D1.f_time None g y) \/ (D1.f_time None g x0 < D1.f_time None g y)) by omega.
    destruct H19. assert (y = x0). eapply D1.f_times_unique. apply H9. apply e2. apply H15.
    rewrite <- H19. reflexivity. subst. contradiction. clear H17.
    assert (F.desc (D1.dfs_forest None g) y x0). eapply D1.descendant_iff_interval. apply H9.
    apply e2. apply H15.   pose proof (Der1.discover_before_finish g None y x0). 
    assert (  D1.d_time None g y < D1.f_time None g y). apply H17; try(assumption); try(auto). 
    pose proof (Der1.discover_before_finish g None x0 y). 
    assert (D1.d_time None g x0 < D1.f_time None g x0). apply H21; try(assumption); try(auto). omega.
    eapply D1.white_path_theorem in H17. destruct H17 as [l]. rewrite D1.P.path_list_ind_rev in H17. destruct_all.
    destruct (O.eq_dec x0 u). unfold O.eq in e3. subst.
    destruct (O.eq_dec v y). unfold O.eq in e3. subst.
    assert (D1.P.path_list_rev g y y (u :: l) = true). simpl. simplify.
    assert (S.In u c'). eapply scc_path_within. apply B. apply H2. apply H2. apply H22. solve_in.
    exfalso. eapply neq_scc_disjoint in H. apply H. split. apply H15. apply H23. apply A. apply B.
    assert (Pa.path g v y). apply p. assumption. assumption. auto. rewrite path_module_equiv in H22.
    rewrite D1.P.path_path_list_rev in H22. destruct H22 as [l'].
    assert (D1.P.path_list_rev g y y (l' ++ v :: u :: l) = true). apply D1.P.path_app. split. apply H22.
    simpl. simplify. assert (S.In u c').  eapply scc_path_within. apply B. apply H8. apply H8. apply H23.
    apply in_or_app. right. simpl. right. left. reflexivity. exfalso. 
    eapply neq_scc_disjoint in H. apply H. split. apply H15. apply H24. apply A. apply B.
    assert (Pa.path g x0 u). apply p0; try(assumption); try(auto). rewrite path_module_equiv in H22.
    rewrite D1.P.path_path_list_rev in H22. destruct H22 as [l''].
    assert (D1.P.path_list_rev g y v (u :: l'' ++ x0 :: l) = true). simpl. simplify. apply D1.P.path_app.
    simplify. assert (S.In u c'). eapply scc_path_within. apply B. apply H8. apply H2. apply H23. solve_in.
    exfalso. eapply neq_scc_disjoint in H. apply H. split. apply H1. apply H24. apply A. apply B.
    apply H9. apply H10. } assert (D1.white None g s' x = true). apply H15.
    unfold f_time_scc in H3. eapply max_elt_set_in_set in H3. apply H3. rewrite D1.white_def in H16.
    rewrite H14 in H16. rewrite Nat.ltb_lt in H16. 
    pose proof (Der1.discover_before_finish g None x y).
    assert (D1.d_time None g x < D1.f_time None g x). apply H17. apply e2. unfold f_time_scc in H3.
    eapply max_elt_set_in_set in H3. apply H3. apply H9. intro. subst.
    eapply neq_scc_disjoint in H. apply H. split. unfold f_time_scc in H3.
    eapply max_elt_set_in_set in H3. apply H3. apply H8. apply A. apply B. omega.
    destruct H7. assert (A:= Hc). assert (B:= Hc'). unfold scc in Hc. unfold scc in Hc'.
    destruct_all. unfold strongly_connected in s0. unfold strongly_connected in s. destruct_all.
    unfold f_time_scc in *. unfold d_time_scc in *.
    (*Proof: there is a white path to every vertex in c', so all must finish before*)
    pose proof (D1.discovery_exists None g x1). destruct H8 as [s]. apply e2. 
    eapply  min_elt_set_in_set. apply H5.
    assert (forall x, S.In x c -> x1 <> x -> D1.white None g s x = true). {
    intros. rewrite D1.white_def. rewrite H8. rewrite Nat.ltb_lt. eapply min_elt_set_finds_min. intros.
    eapply D1.d_times_unique. apply e2. apply H11. apply e2. apply H12. rewrite H13. reflexivity. apply H5.
    apply H9. auto. }
    assert (forall x, S.In x c' -> D1.white None g s x = true). { intros. rewrite D1.white_def. rewrite H8.
    destruct (O.eq_dec x2 x0). unfold O.eq in e3. subst. rewrite Nat.ltb_lt. apply H7. rewrite Nat.ltb_lt.
    assert (D1.d_time None g x0 < D1.d_time None g x2). eapply min_elt_set_finds_min. intros.
    eapply D1.d_times_unique. apply e0. apply H11. apply e0. apply H12. rewrite H13. reflexivity.
    apply H6. apply H10. auto. omega. }
    assert (forall x, S.In x c' -> exists l, D1.P.path_list_ind g x1 x (fun y => D1.white None g s y) l). {
    intros. destruct (O.eq_dec x1 u). unfold O.eq in e3. subst. destruct (O.eq_dec x2 v). unfold O.eq in e3.
    subst. exists nil. constructor. apply H0. apply H10. apply H2. 
    assert (Pa.path g v x2). apply p. apply H2. apply H11. auto. rewrite path_module_equiv in H12.
    rewrite D1.P.path_path_list_rev in H12. destruct H12 as [l]. exists (l ++ v :: nil).
    rewrite D1.P.path_list_ind_rev. split. apply D1.P.path_app. simplify. split. intros.
    apply in_app_or in H13. destruct H13. apply H10. eapply scc_path_within in H12. apply H12.
    apply B. apply H2. apply H11. apply H13. simpl in H13. destruct H13. subst. apply H10. apply H2.
    destruct H13. apply H10. apply H11. assert (I: S.In x1 c). eapply min_elt_set_in_set. apply H5. 
    assert (Pa.path g x1 u). apply p0. apply I. apply H1. auto. rewrite path_module_equiv in H12.
    rewrite D1.P.path_path_list_rev in H12. eapply Der1.unique_paths in H12. destruct H12 as [l].
    destruct_all. destruct (O.eq_dec v x2). unfold O.eq in e3. subst. exists (u :: l). 
    rewrite D1.P.path_list_ind_rev. split. simpl. simplify. split. intros.
    simpl in H16. destruct H16. subst. apply H9. assumption. auto. 
    apply H9. eapply scc_path_within. apply A. apply I. apply H1. apply H12. apply H16. intro. subst.
    contradiction. apply H10. apply H11. 
    assert (Pa.path g v x2). apply p; try(assumption); try(auto). rewrite path_module_equiv in H16.
    rewrite D1.P.path_path_list_rev in H16. destruct H16 as [l'].
    exists (l' ++ v :: u :: l). rewrite D1.P.path_list_ind_rev. split. 
    apply D1.P.path_app. split. apply H16. simpl. simplify. split. intros.
    apply in_app_or in H17. destruct H17. apply H10. eapply scc_path_within. apply B.
    apply H2. apply H11. apply H16. apply H17. simpl in H17. destruct H17. subst.
    apply H10. apply H2. destruct H17. subst. apply H9. apply H1. auto.
    apply H9. eapply scc_path_within. apply A. apply I. apply H1. apply H12. apply H17.
    intro. subst. contradiction. apply H10. apply H11. auto. }
    assert (forall x, S.In x c' ->  F.desc (D1.dfs_forest None g) x1 x). intros.
    eapply D1.white_path_theorem. apply e2. eapply min_elt_set_in_set. apply H5.
    intros. assert (s0 = s). eapply D1.state_time_unique. omega. subst.
    apply H11. apply H12. assert (F.desc (D1.dfs_forest None g) x1 y). apply H12.
    eapply max_elt_set_in_set. apply H4. rewrite D1.descendant_iff_interval in H13.
    destruct (O.eq_dec x x1). unfold O.eq in e3. subst. omega.
    assert (D1.f_time None g x1 < D1.f_time None g x). eapply max_elt_set_finds_max in H3.
    apply H3. intros. eapply D1.f_times_unique. apply e2. apply H14. apply e2. apply H15.
    rewrite H16. reflexivity. eapply min_elt_set_in_set. apply H5. auto. omega.
    apply e2. eapply min_elt_set_in_set. apply H5. eapply e0. 
    eapply max_elt_set_in_set. apply H4. assert (A:= Hc). assert (B:= Hc').
    unfold scc in Hc. unfold scc in Hc'. destruct_all. unfold strongly_connected in s0.
    unfold strongly_connected in s. unfold f_time_scc in *. unfold d_time_scc in *.
    destruct_all. assert (x1 = x0). eapply D1.d_times_unique. apply H12.
    eapply min_elt_set_in_set. apply H5. apply H9. eapply min_elt_set_in_set. apply H6.
    rewrite H7. reflexivity. subst. eapply neq_scc_disjoint in H. exfalso. apply H.
    split. eapply min_elt_set_in_set. apply H5. eapply min_elt_set_in_set. apply H6.
    apply A. apply B.
Qed.

(*Corollary 22.15 in CLRS*)
Lemma scc_finish_time_transpose: forall g c c' u v (Hc: scc c g) (Hc': scc c' g) x y,
  S.equal c c' = false ->
  G.contains_edge (G.get_transpose g) u v = true ->
  S.In u c ->
  S.In v c' ->
  f_time_scc g c Hc = Some x ->
  f_time_scc g c' Hc' = Some y ->
  D1.f_time None g x < D1.f_time None g y.
Proof.
  intros. assert (D1.f_time None g x < D1.f_time None g y <-> D1.f_time None g y > D1.f_time None g x) by omega.
  rewrite H5. clear H5. eapply scc_finish_time. assert (S.equal c' c = false). destruct (S.equal c' c) eqn : ?.
  apply S.equal_2 in Heqb. rewrite Heqb in H. assert (~S.Equal c c). intro. 
  apply SCCAlg.P2.FM.equal_iff in H5. rewrite H5 in H. inversion H.
  pose proof (P2.equal_refl c). contradiction. reflexivity. apply H5.
  rewrite G.transpose_edges. apply H0. apply H2. apply H1. apply H4. apply H3.
Qed.

(** Defining the second DFS pass **)
Module D2 := (D' O S G F).

(*The second pass uses DFSCustomOrder, not DFSBase (since the order depends on the graph, and Coq's modules
  do not allow this. The vertices are ordered in reverse order of their finish times from the first pass. We
  prove that this is a valid Graphordering*)
Program Instance reverseF (g: G.graph) : D2.G'.GraphOrdering (G.get_transpose g) 
  (fun v1 v2 => (D1.f_time None g v2) <? (D1.f_time None g v1)) := {
  }.
Next Obligation.
rewrite Nat.ltb_lt in *. omega.
Defined.
Next Obligation.
intro. subst. rewrite Nat.ltb_lt in *. omega.
Defined.
Next Obligation.
repeat(rewrite Nat.ltb_lt). assert ((D1.f_time None g y < D1.f_time None g x) \/ (D1.f_time None g y > D1.f_time None g x)
\/ (D1.f_time None g y = D1.f_time None g x)) by omega. destruct H1; try(simplify). right. right.
eapply D1.f_times_unique. apply G.transpose_vertices. apply H.
apply G.transpose_vertices. apply H0. symmetry.  apply H2.
Defined. 


Section SecondPass.
  Variable g' : G.graph.
  Definition gt := G.get_transpose g'.
  Definition lt := (fun v1 v2 => D1.f_time None g' v2 <? D1.f_time None g' v1).

(*When the root of a tree in the forest is discovered, it has the largest finish time of all remaining vertices*)
Lemma root_largest_finish_time: forall v (s: D2.state gt lt (reverseF g') None),
  D2.time_of_state gt lt (reverseF g') None s = D2.d_time gt lt (reverseF g') None v ->
  F.is_root (D2.dfs_forest gt lt (reverseF g') None) v = true ->
  (forall (u : G.vertex), G.contains_vertex g' u = true -> D2.white gt lt (reverseF g') None s u = true -> 
  D1.f_time None g' v > D1.f_time None g' u).
Proof.
  intros. apply G.transpose_vertices in H1. replace (G.get_transpose g') with gt in H1. 
     pose proof  (D2.root_smallest gt ((fun v1 v2 : O.t =>
       D1.f_time None g' v2 <? D1.f_time None g' v1)) (reverseF g') v s H H0 u H1 H2). simpl in H3.
  rewrite Nat.ltb_lt in H3. apply H3. reflexivity. 
Qed. 

(*A few helper lemmas*)

Lemma get_tree_in_graph: forall g lt H o v t,
  InA S.Equal t (F.get_trees (D2.dfs_forest g lt H o)) ->
  S.In v t ->
  G.contains_vertex g v = true.
Proof.
  intros. eapply F.get_trees_root in H0. destruct H0. destruct_all. destruct (O.eq_dec v x).
  unfold O.eq in e. subst. eapply D2.same_vertices. apply F.is_root_5. apply H0.
  rewrite H3 in H1. apply F.desc_in_forest in H1. eapply D2.same_vertices. apply H1. auto.
Qed.

Lemma get_trees_partition_graph : forall g lt H o,
  Pa.partition G.contains_vertex g (F.get_trees (D2.dfs_forest g lt H o)). 
Proof.
  intros. unfold Pa.partition. pose proof (F.get_trees_partition (D2.dfs_forest g lt0 H o)).
  unfold F.P.partition in H0. destruct_all. split. intros. apply H0.
  apply D2.same_vertices. apply H2. apply H1.
Qed.

(** Further results about discovery and finish times as they relate to trees **)
(*TODO: see about extending this/proving for the more general case *)

(*Given two DFS trees t1 and t2 with roots r1 and r2, r1 is discovered before r2 iff it
  finishes before r2*)
Lemma root_times: forall g lt H o t1 t2 r1 r2,
  InA S.Equal t1 (F.get_trees (D2.dfs_forest g lt H o)) ->
  InA S.Equal t2 (F.get_trees (D2.dfs_forest g lt H o)) ->
  S.In r1 t1 ->
  S.In r2 t2 ->
  F.is_root (D2.dfs_forest g lt H o) r1 = true ->
  F.is_root (D2.dfs_forest g lt H o) r2 = true ->
  D2.f_time g lt H o r1 < D2.f_time g lt H o r2 <-> D2.d_time g lt H o r1 < D2.d_time g lt H o r2.
Proof.
  intros. assert (G.contains_vertex g r1 = true). eapply get_tree_in_graph. apply H0. assumption.
  assert (G.contains_vertex g r2 = true). eapply get_tree_in_graph. apply H1. assumption.
  destruct (O.eq_dec r1 r2). unfold O.eq in e. subst. omega.
  assert (r1 <> r2) by auto. clear n. pose proof (D2.parentheses_theorem g lt0 H o r1 r2 H6 H7 H8).
  destruct H9.
  - assert (F.desc (D2.dfs_forest g lt0 H o) r1 r2). eapply D2.descendant_iff_interval; try(assumption); try(omega).
    eapply F.root_no_desc in H5. exfalso. apply H5. apply H10. eapply D2.same_vertices. assumption.
  - destruct H9.
    + assert (F.desc (D2.dfs_forest g lt0 H o) r2 r1). eapply D2.descendant_iff_interval; try(assumption); try(omega).
      eapply F.root_no_desc in H4. exfalso. apply H4. apply H10. eapply D2.same_vertices. assumption.
    + omega.
Qed.

(*Given 2 DFS trees t1 and t2 and roots r1 and r2, if r1 finishes before r2, then r1 finishes before r2 starts*)
Lemma root_start_end: forall g lt H o t1 t2 r1 r2,
  InA S.Equal t1 (F.get_trees (D2.dfs_forest g lt H o)) ->
  InA S.Equal t2 (F.get_trees (D2.dfs_forest g lt H o)) ->
  S.In r1 t1 ->
  S.In r2 t2 ->
  F.is_root (D2.dfs_forest g lt H o) r1 = true ->
  F.is_root (D2.dfs_forest g lt H o) r2 = true ->
  D2.f_time g lt H o r1 < D2.f_time g lt H o r2 ->
  D2.f_time g lt H o r1 < D2.d_time g lt H o r2.
Proof.
  intros. assert (G.contains_vertex g r1 = true). eapply get_tree_in_graph. apply H0. assumption.
  assert (G.contains_vertex g r2 = true). eapply get_tree_in_graph. apply H1. assumption.
  destruct (O.eq_dec r1 r2). unfold O.eq in e. subst. omega.
  assert (r1 <> r2) by auto. clear n. pose proof (D2.parentheses_theorem g lt0 H o r1 r2 H7 H8 H9).
  destruct H10.
  - assert (F.desc (D2.dfs_forest g lt0 H o) r1 r2). eapply D2.descendant_iff_interval; try(assumption); try(omega).
    eapply F.root_no_desc in H5. exfalso. apply H5. apply H11. eapply D2.same_vertices. assumption.
  - destruct H10.
    + assert (F.desc (D2.dfs_forest g lt0 H o) r2 r1). eapply D2.descendant_iff_interval; try(assumption); try(omega).
      eapply F.root_no_desc in H4. exfalso. apply H4. apply H11. eapply D2.same_vertices. assumption.
    + omega.
Qed.
    
(*Let t1 and t2 be 2 DFS trees with roots r1 and r2. Let u be in t1 and v be in t2. Then u finishes
  before v is discovered*)
Lemma tree_times: forall g lt H o t1 t2 u v r1 r2,
  InA S.Equal t1 (F.get_trees (D2.dfs_forest g lt H o)) ->
  InA S.Equal t2 (F.get_trees (D2.dfs_forest g lt H o)) ->
  S.In r1 t1 ->
  S.In r2 t2 ->
  F.is_root (D2.dfs_forest g lt H o) r1 = true ->
  F.is_root (D2.dfs_forest g lt H o) r2 = true ->
  D2.f_time g lt H o r1 < D2.f_time g lt H o r2 ->
  S.In u t1 ->
  S.In v t2 ->
  D2.f_time g lt H o u < D2.d_time g lt H o v.
Proof.
  intros. assert (G.contains_vertex g u = true).
  eapply get_tree_in_graph. apply H0. apply H7.
  assert (G.contains_vertex g v = true). eapply get_tree_in_graph. apply H1. apply H8.
  assert (A :~S.In v t1 /\ ~S.In u t2). { split; intro;
  pose proof (get_trees_partition_graph g lt0 H o); unfold Pa.partition in H12;
  destruct_all; specialize (H13 t1 t2); destruct (S.equal t1 t2) eqn : ?.
  - apply S.equal_2 in Heqb; rewrite <- Heqb in H3.  assert (r1 = r2). { eapply F.tree_root_unique.
    apply H0. apply H4. apply H5. apply H2. apply H3. } subst. omega.
  - assert (Pa.disjoint t1 t2). apply H13. reflexivity. assumption. assumption. unfold Pa.disjoint in H14.
    apply (H14 v). split; assumption.
  - apply S.equal_2 in Heqb; rewrite <- Heqb in H3.  assert (r1 = r2). { eapply F.tree_root_unique.
    apply H0. apply H4. apply H5. apply H2. apply H3. } subst. omega.
  - assert (Pa.disjoint t1 t2). apply H13. reflexivity. assumption. assumption. unfold Pa.disjoint in H14.
    apply (H14 u). split; assumption. }
  assert (u <> v). { intro. subst. destruct_all. contradiction. }
  pose proof (D2.parentheses_theorem g lt0 H o u v H9 H10 H11). destruct H12.
  - assert (F.desc (D2.dfs_forest g lt0 H o) u v). eapply D2.descendant_iff_interval. apply H9.
    apply H10. omega. assert (F.desc (D2.dfs_forest g lt0 H o) r1 v). { assert (R:=H0).
    apply F.get_trees_root in H0. destruct_all. assert (x = r1). eapply F.tree_root_unique.
    apply R. all: try(assumption). subst. destruct (O.eq_dec u r1). unfold O.eq in e. subst. assumption.
    eapply F.is_descendant_trans. apply (H19 u). auto. assumption. assumption. }
    assert (S.In v t1). { assert (R:=H0).
    apply F.get_trees_root in H0. destruct_all. assert (x = r1). eapply F.tree_root_unique.
    apply R. assumption. assumption. assumption. assumption. subst. destruct (O.eq_dec v r1). unfold O.eq in e.
    subst. assumption. apply H20. auto. assumption. } destruct_all; contradiction.
  - destruct H12.
    +  assert (F.desc (D2.dfs_forest g lt0 H o) v u). eapply D2.descendant_iff_interval. apply H10.
    apply H9. omega. assert (F.desc (D2.dfs_forest g lt0 H o) r2 u). { assert (R:=H1).
    apply F.get_trees_root in H1. destruct_all. assert (x = r2). eapply F.tree_root_unique.
    apply R. all: try(assumption). subst. destruct (O.eq_dec v r2). unfold O.eq in e. subst. assumption.
    eapply F.is_descendant_trans. apply (H19 v). auto. assumption. assumption. }
    assert (S.In u t2). { assert (R:=H1).
    apply F.get_trees_root in H1. destruct_all. assert (x = r2). eapply F.tree_root_unique.
    apply R. assumption. assumption. assumption. assumption. subst. destruct (O.eq_dec u r2). unfold O.eq in e.
    subst. assumption. apply H20. auto. assumption. } destruct_all; contradiction.
    + destruct H12.
      * omega.
      * assert (R1 := H0). assert (R2 := H1). eapply F.get_trees_root in H0. eapply F.get_trees_root in H1.
        destruct_all. assert (x0 = r1). eapply F.tree_root_unique. apply R1. all: try(assumption). subst.
        assert (x = r2). eapply F.tree_root_unique. apply R2. all: try(assumption). subst.
        destruct (O.eq_dec u r1). unfold O.eq in e. subst. destruct (O.eq_dec v r2). unfold O.eq in e. subst.
        omega. assert (F.desc (D2.dfs_forest g lt0 H o) r2 v). eapply H18. auto. assumption.
        eapply D2.descendant_iff_interval in H21. assert (D2.d_time g lt0 H o r1 < D2.d_time g lt0 H o r2).
        eapply root_times. apply R1. apply R2. all: try(assumption). omega. eapply get_tree_in_graph.
        apply R2. assumption. 
        assert (F.desc (D2.dfs_forest g lt0 H o) r1 u). eapply H20. auto. assumption.
        eapply D2.descendant_iff_interval in H21. assert (D2.d_time g lt0 H o r1 < D2.d_time g lt0 H o r2).
        eapply root_times. apply R1. apply R2. all: try(assumption). destruct (O.eq_dec v r2). unfold O.eq in e.
        subst. omega.  assert (F.desc (D2.dfs_forest g lt0 H o) r2 v). eapply H18. auto. assumption.
        eapply D2.descendant_iff_interval in H23. eapply root_start_end in H6. omega. apply R1. apply R2.
        all: try(assumption). eapply get_tree_in_graph. apply R2. assumption. 
        eapply get_tree_in_graph. apply R1. assumption.
Qed. 

(** Finding the minimum element of a path **)
(*Because a path has the start, end, and intermediate list, this basically boils down to a ton of cases*)

Definition min_elt_path (u v : O.t) (f: O.t -> nat) l :=
  match (min_elt_list l f) with
  | Some x => if f u <? f x then 
                if f u <? f v then u 
                else v
             else if f v <? f x then v else x
  | None => if f u <? f v then u else v
  end.

Ltac destruct_if := 
  match goal with
  | [H : (if ?a <? ?b then _ else _) = _ |- _ ] => (destruct (a <? b) eqn : ?)
  end.

Lemma min_elt_path_in: forall u v l f x,
  min_elt_path u v f l = x ->
  x = u \/ x = v \/ In x l.
Proof.
  intros. unfold min_elt_path in H. destruct (min_elt_list l f) eqn : ?.
  repeat(destruct_if; try(simplify)). subst.
  right. right. apply min_elt_list_in_list in Heqo. assumption.
  destruct_if; inversion H; simplify.
Qed.

Lemma min_elt_path_finds_min: forall u v l f x,
  (forall x0 y0 : O.t, (u = x0 \/ v = x0 \/ In x0 l) -> (u = y0 \/ v = y0 \/ In y0 l) -> f x0 = f y0 -> x0 = y0) ->
  ~In u l -> ~In v l -> u <> v ->
  min_elt_path u v f l = x ->
  (forall y, y = u \/ y = v \/ In y l -> y <> x -> f x < f y).
Proof.
  intros. unfold min_elt_path in H3. destruct (min_elt_list l f) eqn : ?.
  repeat((destruct_if); repeat(rewrite Nat.ltb_lt in *)); subst.
  simplify; subst; try(assumption); try(omega). destruct (O.eq_dec y t). unfold O.eq in e. subst.
  assumption. eapply min_elt_list_finds_min in Heqo. assert (f t < f y) by apply Heqo. omega.
  intros; apply H; try(right; right; assumption); assumption. apply H4. auto.
  assert (f x < f u). { rewrite Nat.ltb_antisym in Heqb0. rewrite negb_false_iff in Heqb0.
  apply Nat.leb_le in Heqb0. assert ( f x < f u \/ f x = f u) by omega. destruct H3. apply H3.
  apply H in H3. subst. contradiction. right. left. reflexivity. left. reflexivity. }
  clear Heqb0. simplify; subst; try(assumption); try(omega).
  destruct (O.eq_dec t y). unfold O.eq in e. subst. omega. eapply min_elt_list_finds_min in Heqo.
  assert (f t < f y) by apply Heqo. omega. intros; apply H; try(right; right; assumption); assumption. 
  apply H4. auto. assert (f t < f u). { rewrite Nat.ltb_antisym in Heqb. rewrite negb_false_iff in Heqb.
  apply Nat.leb_le in Heqb. assert (f t < f u \/ f t = f u) by omega. destruct H3.
  apply H3. subst. eapply H in H3. subst. apply min_elt_list_in_list in Heqo. contradiction.
  right. right. apply min_elt_list_in_list in Heqo; assumption. left. reflexivity. }
  clear Heqb.  simplify; subst; try(assumption); try(omega). destruct (O.eq_dec y t). unfold O.eq in e.
  subst. omega. eapply min_elt_list_finds_min in Heqo. assert (f t < f y) by apply Heqo. omega.
  intros; apply H; try(right; right; assumption); assumption.  apply H4. auto.
  assert ( f x < f v). { rewrite Nat.ltb_antisym in Heqb0. rewrite negb_false_iff in Heqb0.
  apply Nat.leb_le in Heqb0. assert ( f x < f v \/ f x = f v) by omega. destruct H3. apply H3.
  apply H in H3. subst. apply min_elt_list_in_list in Heqo. contradiction. right. right.
  eapply min_elt_list_in_list. apply Heqo. right. left. reflexivity. } clear Heqb0.
  assert ( f x < f u). { rewrite Nat.ltb_antisym in Heqb. rewrite negb_false_iff in Heqb.
  apply Nat.leb_le in Heqb. assert (f x < f u \/ f x = f u) by omega. destruct H6.
  apply H6. subst. eapply H in H6. subst. apply min_elt_list_in_list in Heqo. contradiction.
  right. right. apply min_elt_list_in_list in Heqo; assumption. left. reflexivity. }
  clear Heqb. simplify; subst; try(assumption); try(omega).
  eapply min_elt_list_finds_min in Heqo. apply Heqo.  intros; apply H; try(right; right; assumption).
  assumption. assumption. auto. destruct_if; repeat( rewrite Nat.ltb_lt in *); subst.
  simplify; subst; try(assumption); try(omega). apply min_elt_list_none_iff_empty in Heqo. subst.
  inversion H4. assert (f x < f u). { rewrite Nat.ltb_antisym in Heqb. rewrite negb_false_iff in Heqb.
  apply Nat.leb_le in Heqb. assert ( f x < f u \/ f x = f u) by omega. destruct H3. apply H3.
  apply H in H3. subst. contradiction. right. left. reflexivity. left. reflexivity. }
  clear Heqb. simplify; subst; try(assumption); try(omega).  
  apply min_elt_list_none_iff_empty in Heqo. subst. inversion H4.
Qed.

(*Why we cared about this: every path has a vertex along it that was discovered first*)
Lemma path_has_first_discovered: forall g u v l lt H,
  Pa.path_list_rev g u v l = true ->
  NoDup l -> ~In u l -> ~In v l ->
   u <> v ->
  exists x, (x = u \/ x = v \/ In x l) /\ (forall y,  (y = u \/ y = v \/ In y l) ->y <> x ->
  D2.d_time g lt H None x < D2.d_time g lt H None y).
Proof.
  intros.
  remember (min_elt_path u v (D2.d_time g lt0 H None) l) as y.
  exists y. split. symmetry in Heqy. eapply min_elt_path_in in Heqy. simplify. 
  eapply min_elt_path_finds_min. intros.
  pose proof (Pa.path_implies_in_graph g u v l H0).
  eapply D2.d_times_unique. destruct H5. subst. simplify. destruct H5; subst; simplify.
  destruct H6. subst. simplify. destruct H6; subst; simplify. apply H7. 
  all: symmetry in Heqy; assumption.
Qed.

(*This is a key result towards proving the correctness of Kosaraju's Algorithm: There are no paths
  from an earlier DFS tree to a later tree*)
(*The proof turns out to be quite complicated.
  Essentially, assume there is a path and let x be the element in the path that is first discovered.
  If x is in t2 (the later tree), this contradicts the fact that u, the starting vertex, was in an
  earlier tree. If x is in an earlier tree, then v (the end vertex) becomes a descendant of x by
  the white path theorem, so v is in an earlier tree, which contradicts the fact that any two
  DFS trees are djsoint.*)
Lemma no_path_to_later_tree: forall g lt H t1 t2 r1 r2 u v,
  InA S.Equal t1 (F.get_trees (D2.dfs_forest g lt H None)) ->
  InA S.Equal t2 (F.get_trees (D2.dfs_forest g lt H None)) ->
  S.In r1 t1 ->
  S.In r2 t2 ->
  F.is_root (D2.dfs_forest g lt H None) r1 = true ->
  F.is_root (D2.dfs_forest g lt H None) r2 = true ->
  D2.f_time g lt H None r1 < D2.f_time g lt H None r2 ->
  S.In u t1 ->
  S.In v t2 ->
  ~Pa.path g u v.
Proof.
  intros. intro. assert (D2.f_time g lt0 H None u < D2.d_time g lt0 H None v). eapply tree_times.
  apply H0. apply H1. apply H2. apply H3. all: try assumption.
  assert (G.contains_vertex g v = true). eapply get_tree_in_graph. apply H1. assumption.
  assert (G.contains_vertex g u = true). eapply get_tree_in_graph. apply H0. assumption.
  assert (A :~S.In v t1 /\ ~S.In u t2). { split; intro;
  pose proof (get_trees_partition_graph g lt0 H None); unfold Pa.partition in H14;
  destruct_all; specialize (H15 t1 t2); destruct (S.equal t1 t2) eqn : ?.
  - apply S.equal_2 in Heqb; rewrite <- Heqb in H3.  assert (r1 = r2). { eapply F.tree_root_unique.
    apply H0. all: try assumption. }  subst. omega.
  - assert (Pa.disjoint t1 t2). apply H15. reflexivity. assumption. assumption. unfold Pa.disjoint in H16.
    apply (H16 v). split; assumption.
  - apply S.equal_2 in Heqb; rewrite <- Heqb in H3.  assert (r1 = r2). { eapply F.tree_root_unique.
    apply H0. all: try assumption. }  subst. omega.
  - assert (Pa.disjoint t1 t2). apply H15. reflexivity. assumption. assumption. unfold Pa.disjoint in H16.
    apply (H16 u). split; assumption. } destruct A as [N1 N2].
  assert (N: u <> v). intro. subst. contradiction.
  rewrite Pa.path_path_list_rev in H9. destruct H9 as [l]. eapply Pa.path_no_dups in H9.
  destruct H9 as [ld]. destruct_all. assert (A:= H9). apply (path_has_first_discovered _ _ _ _ _ H) in A.
  destruct A as [fst]. destruct_all. assert (R1 := H0). assert (R2 := H1). eapply F.get_trees_root in H0.
  destruct H0 as [x]. destruct H0 as [HR1 HI1]. destruct HI1 as [HI1 HD1]. assert (x = r1). eapply F.tree_root_unique.
  apply R1. all: try assumption. subst. eapply F.get_trees_root in H1. destruct H1 as [x]. destruct H0 as [HR2 HI2].
  destruct HI2 as [HI2 HD2]. assert (x = r2). eapply F.tree_root_unique. apply R2. all: try assumption. subst. 
  clear HR1. clear HR2. clear HI1. clear HI2. 
  destruct H17. subst. 
  - assert (F.desc (D2.dfs_forest g lt0 H None) u v). { eapply D2.white_path_theorem. apply H12. intros.
    exists ld. rewrite D2.P.path_list_ind_rev. split. apply H9. split.
    + intros. rewrite D2.white_def. rewrite H0. rewrite Nat.ltb_lt. apply H18. simplify. intro. subst. contradiction.
    + rewrite D2.white_def. rewrite H0. rewrite Nat.ltb_lt. apply H18. simplify. intro. subst. contradiction. }
   assert (F.desc (D2.dfs_forest g lt0 H None) r1 v). destruct (O.eq_dec r1 u). unfold O.eq in e. subst.
   assumption. eapply F.is_descendant_trans. apply (HD1 u). auto. assumption. assumption.
   rewrite <- HD1 in H1. contradiction. intro. subst. contradiction.
  - destruct H0. 
    + subst. specialize (H18 u). assert (D2.d_time g lt0 H None v < D2.d_time g lt0 H None u).
      apply H18. left. reflexivity. apply N.
      assert (D2.d_time g lt0 H None u < D2.f_time g lt0 H None u). 
      pose proof (D2.parentheses_theorem g lt0 H None u v H12 H11 N). omega. omega.
    + destruct (P2.In_dec fst t2).
      * specialize (H18 u). assert (D2.d_time g lt0 H None fst < D2.d_time g lt0 H None u).
        apply H18. left. reflexivity. intro. subst. contradiction.
        assert (D2.f_time g lt0 H None u < D2.d_time g lt0 H None fst). eapply tree_times.
        apply R1. apply R2. apply H2. apply H3. all: try assumption.
        assert (D2.d_time g lt0 H None u < D2.f_time g lt0 H None u). 
        pose proof (D2.parentheses_theorem g lt0 H None u v H12 H11 N). omega. omega.
      * assert (G.contains_vertex g fst = true). eapply Pa.path_implies_in_graph.
        apply H9. apply H0. pose proof (get_trees_partition_graph g lt0 H None).
        unfold Pa.partition in H17. destruct H17. specialize (H17 _ H1). destruct H17 as [t3].
        destruct H17 as [R3 H17]. assert (A:= R3). eapply F.get_trees_root in A. destruct A as [r3].
        destruct H20 as [HR3 HI3]. destruct HI3 as [HI3 HD3].
        assert (D2.f_time g lt0 H None r3 > D2.f_time g lt0 H None r2 \/ 
                D2.f_time g lt0 H None r3 = D2.f_time g lt0 H None r2 \/
                D2.f_time g lt0 H None r3 < D2.f_time g lt0 H None r2) by omega.
        destruct H20.
        -- assert (D2.f_time g lt0 H None r2 < D2.d_time g lt0 H None r3). eapply root_start_end.
           apply R2. apply R3. all: try assumption. 
           destruct (O.eq_dec v r2). unfold O.eq in e. subst. destruct (O.eq_dec fst r3). unfold O.eq in e.
           subst. specialize (H18 r2). assert (D2.d_time g lt0 H None r3 < D2.d_time g lt0 H None r2).
           apply H18. simplify. intro. subst. contradiction. 
           assert (D2.d_time g lt0 H None r2 < D2.f_time g lt0 H None r2). assert (r2 <> u) by auto.
           pose proof (D2.parentheses_theorem g lt0 H None r2 u H11 H12 H23). omega. omega.
           assert (F.desc (D2.dfs_forest g lt0 H None) r3 fst). apply HD3. auto. assumption.
           apply D2.descendant_iff_interval in H22. specialize (H18 r2).
           assert (D2.d_time g lt0 H None fst < D2.d_time g lt0 H None r2). apply H18. simplify.
           intro. subst. contradiction. 
            assert (D2.d_time g lt0 H None r2 < D2.f_time g lt0 H None r2). assert (r2 <> u) by auto.
           pose proof (D2.parentheses_theorem g lt0 H None r2 u H11 H12 H24). omega. omega.
           eapply get_tree_in_graph. apply R3. assumption. assumption.
           assert (F.desc (D2.dfs_forest g lt0 H None) r2 v). apply HD2. auto. assumption.
           eapply D2.descendant_iff_interval in H22. destruct (O.eq_dec fst r3). unfold O.eq in e. subst.
            specialize (H18 v). assert (D2.d_time g lt0 H None r3 < D2.d_time g lt0 H None v). apply H18.
            simplify. intro. subst. contradiction. omega.
            assert (F.desc (D2.dfs_forest g lt0 H None) r3 fst). apply HD3. auto. assumption.
            apply D2.descendant_iff_interval in H23. specialize (H18 v).
            assert (D2.d_time g lt0 H None fst < D2.d_time g lt0 H None v). apply H18. simplify.
            intro. subst. contradiction.  omega. eapply get_tree_in_graph. apply R3. assumption.
            assumption. eapply get_tree_in_graph. apply R2. assumption. assumption.
        -- destruct H20.
           ++ assert (r3 = r2). eapply D2.f_times_unique. eapply get_tree_in_graph. apply R3. assumption.
              eapply get_tree_in_graph. apply R2. assumption. apply H20. subst.
              destruct (S.equal t2 t3) eqn : ?. apply S.equal_2 in Heqb. rewrite Heqb in n. contradiction.
              apply H19 in Heqb. unfold Pa.disjoint in Heqb. apply (Heqb r2). split; assumption.
              assumption. assumption.
           ++ assert (A:= H0). eapply in_split_app_fst in A. destruct A as [l1]. destruct H21 as  [l2].
              destruct H21; subst. apply Pa.path_app in H9. destruct H9 as [HP1 HP2].
              assert (F.desc (D2.dfs_forest g lt0 H None) fst v). eapply D2.white_path_theorem.
              assumption. intros. exists l1. rewrite D2.P.path_list_ind_rev. split.
              assumption. split. intros. rewrite D2.white_def. rewrite H9. rewrite Nat.ltb_lt.
              apply H18. simplify. intro. subst. apply (H22 fst). apply H21. reflexivity.
              rewrite D2.white_def. rewrite H9. rewrite Nat.ltb_lt. apply H18. simplify.
              intro. subst. contradiction. destruct (O.eq_dec fst r3). unfold O.eq in e. subst.
              rewrite <- HD3 in H9. destruct (S.equal t2 t3) eqn : ?. apply S.equal_2 in Heqb.
              rewrite Heqb in n. contradiction. apply H19 in Heqb. unfold Pa.disjoint in Heqb.
              apply (Heqb v). split; assumption. assumption. assumption. intro. subst. contradiction.
              assert (F.desc (D2.dfs_forest g lt0 H None) r3 v). eapply F.is_descendant_trans. apply (HD3 fst).
              auto. assumption. assumption. rewrite <- HD3 in H21. destruct (S.equal t2 t3) eqn : ?.
              apply S.equal_2 in Heqb. rewrite Heqb in n. contradiction. apply H19 in Heqb.
              unfold Pa.disjoint in Heqb. apply (Heqb v). split; assumption. assumption. assumption.
              intro. subst. apply F.desc_neq in H21. contradiction. apply O.eq_dec.
Qed.

(*If vertex u is in DFS tree t and in scc C, then C is a subset of t*)
Lemma scc_subset: forall t u c g lt Ho,
  InA S.Equal t (F.get_trees (D2.dfs_forest g lt Ho None)) ->
  S.In u t ->
  S.In u c ->
  scc c g ->
  (forall y, S.In y c -> S.In y t).
Proof.
  intros. pose proof (get_trees_partition_graph g lt0 Ho None). pose proof (scc_partition_2 _ _ _ _ _ H2 H4 H H1 H0).
  destruct H5. apply H5. apply H3. destruct H5 as [a]. destruct H5 as [b]. destruct H5 as [t'].
  destruct_all. assert (P1 := H). assert (P2 := H6). apply F.get_trees_root in H. destruct H as [r1].
  apply F.get_trees_root in H6. destruct H6 as [r2]. destruct_all.
  assert (D2.f_time g lt0 Ho None r1 < D2.f_time g lt0 Ho None r2 \/
          D2.f_time g lt0 Ho None r1 = D2.f_time g lt0 Ho None r2 \/
          D2.f_time g lt0 Ho None r1 > D2.f_time g lt0 Ho None r2) by omega.
  assert (S := H2). unfold scc in H2. destruct H2. unfold strongly_connected in H2. destruct_all.
  assert (a <> b). { intro. subst. unfold Pa.partition in H4. destruct_all. apply H20 in H5.
  unfold Pa.disjoint in H5. apply (H5 b). split; assumption. all: try assumption. }
  destruct H16.
  - assert (Pa.path g a b). apply H19. all: try assumption. exfalso. eapply no_path_to_later_tree.
    apply P1. apply P2. apply H14. apply H12. assumption. assumption. assumption. apply H9.
    apply H10. apply H21.
  - destruct H16.
    + assert (r1 = r2). eapply D2.f_times_unique. eapply get_tree_in_graph. apply P1. assumption.
      eapply get_tree_in_graph. apply P2. assumption. apply H16. subst.
      unfold Pa.partition in H4. destruct H4. apply H21 in H5. unfold Pa.disjoint in H5.
      specialize (H5 r2). exfalso. apply H5. split; assumption. all: try assumption.
    + exfalso. eapply no_path_to_later_tree. apply P2. apply P1. apply H12. apply H14.
      assumption. assumption. omega. apply H10. apply H9. constructor. apply H11.
Qed.

Lemma desc_path: forall u v l,
  u <> v ->
  F.desc_list (D2.dfs_forest gt lt (reverseF g') None) u v l = true ->
  Pa.path_list_rev gt u v l = true.
Proof.
  intros. generalize dependent v. induction l; intros; simpl in *.
  - eapply D2.same_edges. apply H0.
  - simplify. eapply D2.same_edges. apply H1. apply IHl. intros. eapply F.desc_neq.
    rewrite <- F.desc_list_iff_desc. exists l. apply H2. auto. apply H2.
Qed. 

(*Every tree in the resulting DFS forest is strongly connected*)
Lemma all_trees_strongly_connected: forall t,
  InA S.Equal t (F.get_trees (D2.dfs_forest gt lt (reverseF g') None)) ->
  strongly_connected t gt.
Proof.
  intros. destruct (strongly_connected_dec t gt). apply s.
  assert (A:= H). apply F.get_trees_root in H. destruct_all.
  pose proof (vertex_in_scc gt x). assert (G.contains_vertex gt x = true).
   unfold gt in A. unfold lt in A. eapply get_tree_in_graph in A. apply A.
  apply H0. specialize (H2 H3). destruct H2 as [C]. destruct_all.
  assert (forall x0 : S.elt,
      S.In x0 t ->
      x0 <> x ->
      exists l : list G.vertex, Pa.path_list_rev gt x x0 l = true /\ (forall y : G.vertex, In y l -> S.In y t)). {
  intros. apply H1 in H5. assert (x <> x0) by auto. rewrite <- F.desc_list_iff_desc in H5.
  destruct H5 as [l']. assert (B:= H5). eapply (desc_path _ _ _  H7) in H5. exists l'. simplify.
  destruct (O.eq_dec y x). unfold O.eq in e. subst. assumption. apply H1. auto.
  eapply F.desc_list_all_desc. apply B. apply H8. auto. }
  assert ((forall x : S.elt, S.In x t -> G.contains_vertex gt x = true)). { intros.
  eapply get_tree_in_graph. apply A. apply H6. } 
     pose proof (scc_vertex x t C gt H5 H6 n H2 H4 H0). clear H5.
  destruct H7 as [v]. destruct H5 as [C']. destruct_all. 
  pose proof (find_max_scc_exists (D1.f_time None g') gt C H2).
   pose proof (find_max_scc_exists (D1.f_time None g') gt C' H8).
   destruct H12 as [fC]. destruct H13 as [fC'].
   assert (forall y, S.In y C -> S.In y t). { eapply scc_subset. apply A. apply H0. apply H4.
   apply H2. }
   assert (fC = x). { destruct (O.eq_dec fC x). apply e. 
  assert (F.desc (D2.dfs_forest gt lt (reverseF g') None) x fC). apply H1. auto.
  apply H14. eapply max_elt_set_in_set. apply H12. 
  eapply D2.descendant_iff_interval in H15. assert (B:= H12). 
  eapply max_elt_set_finds_max  in H12. assert (D1.f_time None g' x < D1.f_time None g' fC) by apply H12.
  clear H16. pose proof (D2.discovery_exists gt lt (reverseF g') None x H3).
  destruct H16 as [sx]. pose proof (root_largest_finish_time x sx H16 H fC).
  assert (D1.f_time None g' x > D1.f_time None g' fC). apply H17. rewrite G.transpose_vertices.
  apply H6. apply H14. eapply max_elt_set_in_set. apply B. rewrite D2.white_def. rewrite H16.
  rewrite Nat.ltb_lt. omega. omega. intros. eapply D1.f_times_unique. rewrite G.transpose_vertices.
  unfold scc in H2. destruct H2. unfold strongly_connected in s. apply s. apply H16.
  rewrite G.transpose_vertices.
  unfold scc in H2. destruct H2. unfold strongly_connected in H2. apply H2. apply H17. apply H18.
  assumption. auto. assumption. unfold scc in H2. destruct H2. unfold strongly_connected in H2. apply H2.
  eapply max_elt_set_in_set in H12. apply H12. } subst.
  assert (F.desc (D2.dfs_forest gt lt (reverseF g') None) x fC'). apply H1. intro. subst.
  eapply neq_scc_disjoint in H9. apply H9. split. apply max_elt_set_in_set in H12. apply H12.
  apply max_elt_set_in_set in H13. apply H13. apply H2. apply H8. eapply scc_subset.
  apply A. apply H5. apply H7. apply H8. eapply max_elt_set_in_set. apply H13. 
  eapply D2.descendant_iff_interval in H15. assert (scc C g'). rewrite scc_transpose.
  assumption. assert (scc C' g'). rewrite scc_transpose. assumption. pose proof (scc_finish_time_transpose
  g' C C' x0 v H16 H17 x fC' H9 H11 H10 H7). unfold f_time_scc in H18. specialize (H18 H12 H13).
  pose proof (D2.discovery_exists gt lt (reverseF g') None x H3). destruct H19 as [sx].
  assert (D1.f_time None g' x > D1.f_time None g' fC'). eapply root_largest_finish_time.
  apply H19. assumption. rewrite G.transpose_vertices. apply H6. eapply scc_subset.
  apply A. apply H5. apply H7. assumption. apply max_elt_set_in_set in H13. assumption.
  rewrite D2.white_def. rewrite H19. rewrite Nat.ltb_lt. omega. omega.
  assumption.  apply H6. eapply scc_subset.
  apply A. apply H5. apply H7. assumption. apply max_elt_set_in_set in H13. assumption.
Qed.

(*Finally, the proof that the algorithm is correct: Every tree in the DFS forest of the second pass
  of DFS is a SCC*)
Theorem scc_algorithm_correct: forall t,
  InA S.Equal t (F.get_trees (D2.dfs_forest gt lt (reverseF g') None)) ->
  scc t g'.
Proof.
  intros. rewrite scc_transpose. assert (A:= H). apply all_trees_strongly_connected in H.
  destruct (scc_dec t gt). apply s. pose proof (non_scc_has_another t gt H n).
  destruct H0 as [v]. destruct H0. assert (R:= A). apply F.get_trees_root in A. destruct A as [r1].
  destruct_all. pose proof (get_trees_partition_graph gt lt (reverseF g') None). unfold Pa.partition in H5.
  destruct H5. assert (G.contains_vertex gt v = true). { unfold strongly_connected in H1. apply H1.
  apply S.add_1. reflexivity. } specialize (H5 _ H7). destruct H5 as [t2]. destruct H5.
  assert (R2 := H5). apply F.get_trees_root in H5. destruct H5 as [r2]. destruct_all.
  unfold strongly_connected in H1. destruct_all.
  assert (r1 <> v). intro. subst. pose proof (get_trees_partition_graph gt lt (reverseF g') None).
  unfold Pa.partition in H13. destruct H13. destruct (S.equal t t2) eqn : ?. apply S.equal_2 in Heqb.
  rewrite Heqb in H0. contradiction. apply H14 in Heqb. unfold Pa.disjoint in Heqb.
  apply (Heqb v). split; assumption. assumption. assumption.
  assert (Pa.path gt r1 v). apply H12. apply S.add_2. assumption. apply S.add_1. reflexivity. apply H13.
  assert (Pa.path gt v r1). apply H12. apply S.add_1. reflexivity. apply S.add_2. assumption. auto.  
  assert (D2.f_time gt lt (reverseF g') None r1 < D2.f_time gt lt (reverseF g') None r2 \/
          D2.f_time gt lt (reverseF g') None r1 = D2.f_time gt lt (reverseF g') None r2 \/
          D2.f_time gt lt (reverseF g') None r1 > D2.f_time gt lt (reverseF g') None r2) by omega.
  destruct H16.
  - exfalso. eapply no_path_to_later_tree. apply R. apply R2. apply H3. apply H9. assumption.
    assumption. assumption. apply H3. apply H8. apply H14.
  - destruct H16.
    + assert (r1 = r2). eapply D2.f_times_unique. eapply get_tree_in_graph. apply R.
      assumption. eapply get_tree_in_graph. apply R2. assumption. apply H16. subst.
      pose proof (get_trees_partition_graph gt lt (reverseF g') None).
      unfold Pa.partition in H17. destruct H17. destruct (S.equal t t2) eqn : ?. apply S.equal_2 in Heqb.
      rewrite Heqb in H0. contradiction. apply H18 in Heqb. unfold Pa.disjoint in Heqb.
      exfalso. apply (Heqb r2). split; assumption. all: try assumption.
    + exfalso. eapply no_path_to_later_tree. apply R2. apply R. apply H9. apply H3. assumption.
      assumption. assumption. apply H8. apply H3. apply H15.
Qed.

End SecondPass.

End SCCAlg.

