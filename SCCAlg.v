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

(*We can create  UsualOrdered instance of the finish times. This is a really annoying function of the
  fact that Coq's modules do not support values as parameters, so we use a separate typeclass to define
  an ordering, along with a set. (We need the set fo efficiency reasons: if we just pass in an ordering
  function, it would take O(n) time to find the min each time we start a new tree. With a set, we can
  do this in O(log n). But it makes everything more complicated*)
(*
Module ReverseFTime (O: UsualOrderedType)(S: FSetInterface.Sfun O)(G: Graph O S)(F: Forest O S G)
  (D: DFSBase O S G F) .

  Module GO := (Graph.GraphOrder O S G).
  Import GO.


End ReverseFTime.*)
    
(*
(*In reality, our graoh is fixed, but Coq's modules do not seem to support a value parameter*)
Module ReverseFTime (O: UsualOrderedType)(S: FSetInterface.Sfun O)(G: Graph O S)(F: Forest O S G)
  (D: DFSBase O S G F) <: OrderedType.

  Definition t : Type := {x : G.graph * G.vertex | G.contains_vertex (fst x) (snd x) = true}.

  Definition eq (t1 t2 : t) := if G.Equal_dec (fst (proj1_sig t1)) (fst (proj1_sig t2)) then
    D.f_time None (fst (proj1_sig t1)) (snd (proj1_sig t1)) = 
         D.f_time None (fst (proj1_sig t2)) (snd (proj1_sig t2)) 
    else False.

  Definition lt (t1 t2 : t) :=
    if G.Equal_dec (fst (proj1_sig t1)) (fst (proj1_sig t2)) 
    then D.f_time None (fst (proj1_sig t1)) (snd (proj1_sig t1)) > 
         D.f_time None (fst (proj1_sig t2)) (snd (proj1_sig t2)) 
    else G.lt (fst (proj1_sig t1)) (fst (proj1_sig t2)).

  Lemma eq_refl : forall x : t, eq x x.
  Proof.
    intros. unfold eq. destruct x as [x H]. destruct x as [g v]. simpl in *.
    destruct (G.Equal_dec g g). omega. apply n. pose proof (G.Equal_equiv).
    destruct H0 as [refl]. apply refl.
  Qed.
  
  Lemma eq_sym : forall x y : t, eq x y -> eq y x.
  Proof.
    intros. unfold eq in *. destruct x as [x1 H1]. destruct y as [y1 H2]. destruct x1 as [g1 v1].
    destruct y1 as [g2 v2]. simpl in *. pose proof (G.Equal_equiv). destruct H0 as [refl sym trans].
    destruct (G.Equal_dec g2 g1). destruct (G.Equal_dec g1 g2). omega. 
    apply sym in e. contradiction. destruct (G.Equal_dec g1 g2). apply sym in e. contradiction. apply H.
  Qed.

  Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof.
    intros. unfold eq in *. destruct x as [x1 H1]. destruct y as [y1 H2]. destruct z as [z1 H3].
    destruct x1 as [g1 v1]. destruct y1 as [g2 v2]. destruct z1 as [g3 v3]. simpl in *.
    pose proof (G.Equal_equiv). destruct H4 as [refl sym trans].
    destruct (G.Equal_dec g1 g3). destruct (G.Equal_dec g1 g2). destruct (G.Equal_dec g2 g3). omega.
    assert (G.Equal g2 g3). eapply trans. apply sym. apply e0. apply e. contradiction.
    destruct H. destruct (G.Equal_dec g1 g2). destruct (G.Equal_dec g2 g3).
    assert (G.Equal g1 g3). eapply trans. apply e. apply e0. contradiction. destruct H0. destruct H.
  Qed. 

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    intros. destruct x. destruct y. destruct z. unfold lt in *. simpl in *.
    destruct x as [g1 v1]. destruct x0 as [g2 v2]. destruct x1 as [g3 v3]. simpl in *.
     pose proof G.Equal_equiv. destruct H1 as [refl sym trans].
    destruct (G.Equal_dec g1 g2). destruct (G.Equal_dec g2 g3). 
    destruct (G.Equal_dec g1 g3). omega.
    assert (G.Equal g1 g3). eapply trans. apply e2. apply e3. contradiction.
    destruct (G.Equal_dec g1 g3). assert (G.Equal g2 g3). eapply trans. eapply sym. apply e2.
    apply e3. contradiction. eapply G.Equal_lt_l. apply e2. apply H0.
    destruct (G.Equal_dec g1 g3). destruct (G.Equal_dec g2 g3). 
    assert (G.Equal g1 g2). eapply trans. apply e2. apply sym. apply e3. contradiction.
    assert (G.lt g2 g1). eapply G.Equal_lt_r. apply e2. apply H0.
    assert (G.lt g1 g1). eapply G.lt_trans. apply H. apply H1. eapply G.lt_not_eq in H2.
    exfalso. apply H2. apply refl. destruct (G.Equal_dec g2 g3). eapply G.Equal_lt_r. apply sym.
    apply e2. apply H. eapply G.lt_trans. apply H. apply H0.
  Qed.

 Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    intros. intro. unfold lt in *. unfold eq in *. destruct x as [x A]. simpl in *.
    destruct y as [y B]. destruct x as [g v]. destruct y as [g' v']. simpl in *.
    destruct (G.Equal_dec g g'). omega. apply H0.
  Qed.

 Definition compare : forall x y : t, Compare lt eq x y.
  Proof.
    intros. destruct x as [x1 H1]. destruct y as [y1 H2]. destruct x1 as [g1 v1]. destruct y1 as [g2 v2].
    simpl in *. pose proof (G.Equal_equiv). destruct H as [r s t]. 
    pose proof (G.compare g1 g2). destruct H.
    - apply LT. unfold lt. simpl in *. destruct (G.Equal_dec g1 g2). apply G.lt_not_eq in l. 
      contradiction. apply l.
    - case_eq (Nat.compare (D.f_time None g1 v1) (D.f_time None g2 v2)); intro; simpl in *.
      + apply EQ. unfold eq. simpl in *. destruct (G.Equal_dec g1 g2). apply nat_compare_eq in H. omega.
        contradiction.
      + apply GT. unfold lt. simpl in *. destruct (G.Equal_dec g2 g1). apply nat_compare_lt in H. omega.
        apply s in e. contradiction.
      + apply LT. unfold lt. simpl in *. destruct (G.Equal_dec g1 g2). apply nat_compare_gt in H. omega.
        contradiction.
    - apply GT. unfold lt. simpl in *. destruct (G.Equal_dec g2 g1). apply G.lt_not_eq in l. contradiction.
      apply l.
  Qed.

 Lemma eq_dec : forall x y : t, { eq x y } + { ~ eq x y }.
  Proof.
    intros. pose proof (compare x y). destruct H. right. intro. apply lt_not_eq in l. contradiction.
    left. apply e. right. intro. apply lt_not_eq in l. apply eq_sym in H. contradiction.
  Qed.

End ReverseFTime.

 Parameter Inline t : Type.
 Definition eq := @eq t.
 Parameter Inline lt : t -> t -> Prop.
 Definition eq_refl := @eq_refl t.
 Definition eq_sym := @eq_sym t.
 Definition eq_trans := @eq_trans t.
 Axiom lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
 Axiom lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
 Parameter compare : forall x y : t, Compare lt eq x y.
 Parameter eq_dec : forall x y : t, { eq x y } + { ~ eq x y }.

*)
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
    (*WOOO *)
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
(*
Next Obligation.
case_eq (Nat.compare (D1.f_time None g x) (D1.f_time None g y)); intro; simpl in *.
- apply EQ. unfold O.eq. eapply D1.f_times_unique. apply H. apply H0. apply Nat.compare_eq in H1. apply H1.
- apply GT. simpl. apply nat_compare_Lt_lt in H1. omega.
- apply LT. simpl. apply nat_compare_Gt_gt in H1. omega.
Defined.*)

Section SecondPass.
  Variable g' : G.graph.
  Definition gt := G.get_transpose g'.
  Definition lt := (fun v1 v2 => D1.f_time None g' v2 <? D1.f_time None g' v1).
(*Just a test - ok figure this out tomorrow - can either do backtracking with nats (or more likely for now -
  just pass a function*)
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


(*For any two trees in the DFS forest, if the root of t1 finishes before the root of t2, then there
  is no edge rom t1 to t2*)

Lemma get_tree_in_graph: forall g lt H o v t,
  InA S.Equal t (F.get_trees (D2.dfs_forest g lt H o)) ->
  S.In v t ->
  G.contains_vertex g v = true.
Proof.
  intros. eapply F.get_trees_root in H0. destruct H0. destruct_all. destruct (O.eq_dec v x).
  unfold O.eq in e. subst. eapply D2.same_vertices. apply F.is_root_5. apply H0.
  rewrite H3 in H1. apply F.desc_in_forest in H1. eapply D2.same_vertices. apply H1. auto.
Qed.

Lemma no_edge_to_later_tree: forall g lt H o v1 v2 r1 r2 t1 t2 (E: S.equal t1 t2 = false),
  InA S.Equal t1 (F.get_trees (D2.dfs_forest g lt H o)) ->
  InA S.Equal t2 (F.get_trees (D2.dfs_forest g lt H o)) ->
  S.In r1 t1 ->
  S.In v1 t1 ->
  S.In r2 t2 ->
  S.In v2 t2 ->
  F.is_root (D2.dfs_forest g lt H o) r1 = true ->
  F.is_root (D2.dfs_forest g lt H o) r2 = true ->
  D2.f_time g lt H o r1 < D2.f_time g lt H o r2 ->
  G.contains_edge g v1 v2 = false.
Proof.
  intros. destruct (G.contains_edge g v1 v2) eqn : ?.
  - assert (G.contains_vertex g r1 = true). { eapply D2.same_vertices. 
    apply F.is_root_5. apply H6. } 
    assert (Hr: G.contains_vertex g r2 = true). { eapply D2.same_vertices. 
    apply F.is_root_5. apply H7. } pose proof (D2.discovery_exists g lt0 H o r1 H9).
    destruct H10 as [sr1]. assert (forall v, S.In v t1 -> v <> r1 -> D2.white g lt0 H o sr1 v = true). { intros.
    assert (A:= H0).
    apply F.get_trees_root in H0. destruct H0. assert (x = r1). { eapply F.tree_root_unique.
    apply A. apply H0. apply H6. destruct_all. apply H13. apply H2. } subst.
    destruct_all. clear H0. clear H13. rewrite D2.white_def. rewrite Nat.ltb_lt. rewrite H10.
    eapply D2.descendant_iff_interval. apply H9. eapply get_tree_in_graph. apply A. apply H11.
    apply H14. auto. apply H11. }
    assert (forall v, S.In v t2 -> D2.white g lt0 H o sr1 v = true). { intros.
    assert (r1 <> r2). intro. subst. omega.
    assert (D2.d_time g lt0 H o r1 < D2.d_time g lt0 H o r2). { 
    assert ((D2.d_time g lt0 H o r1 < D2.d_time g lt0 H o r2) \/ (D2.d_time g lt0 H o r1 = D2.d_time g lt0 H o r2)
    \/ (D2.d_time g lt0 H o r1 > D2.d_time g lt0 H o r2)) by omega. destruct H14. apply H14. destruct H14.
    assert (r1 = r2). eapply D2.d_times_unique. apply H9. apply Hr. apply H14. contradiction. 
    pose proof (D2.parentheses_theorem g lt0 H o r1 r2 H9 Hr H13). destruct H15. omega. destruct H15.
    destruct_all. assert (F.desc (D2.dfs_forest g lt0 H o) r2 r1). { eapply D2.descendant_iff_interval; try(assumption);
    try(omega). } rewrite F.root_no_desc in H6. specialize (H6 r2). contradiction. apply F.is_root_5. apply H6.
    omega. } destruct (O.eq_dec v r2). unfold O.eq in e. subst. rewrite D2.white_def. rewrite Nat.ltb_lt. rewrite H10.
    apply H14. assert (F.desc (D2.dfs_forest g lt0 H o) r2 v). assert (A:= H1). apply F.get_trees_root in H1. destruct_all.
    assert (x = r2). eapply F.tree_root_unique. apply A. all: try(eassumption). subst.
    apply H16. auto. apply H12. rewrite D2.descendant_iff_interval in H15. rewrite D2.white_def.
    rewrite Nat.ltb_lt. omega. apply Hr. eapply get_tree_in_graph. apply H1. apply H12. }
    assert (F.desc (D2.dfs_forest g lt0 H o) r1 v2). { eapply D2.white_path_theorem. apply H9.
    intros. assert (s = sr1). eapply D2.state_time_unique. omega. subst. assert (A:= H0).
    apply F.get_trees_root in H0. destruct_all. assert ( x = r1). eapply F.tree_root_unique. apply A.
    all: try(assumption). subst. destruct (O.eq_dec r1 v1). unfold O.eq in e. subst.
    exists nil. rewrite D2.P.path_list_ind_rev. simplify.
    assert (F.desc (D2.dfs_forest g lt0 H o) r1 v1). {
    apply H15. intro. subst. apply n. reflexivity. assumption. }
    rewrite D2.white_path_theorem in H16. specialize (H16 sr1 H13). destruct H16.
    exists (v1 :: x). rewrite D2.P.path_list_ind_rev. rewrite D2.P.path_list_ind_rev in H16.
    destruct_all.  simpl. simplify. subst. apply H18. apply H9. } 
    assert (v2 <> r1). { intro. subst. rewrite F.root_no_desc in H6. specialize (H6 r1). contradiction.
    apply F.is_root_5; assumption. } assert (S.In v2 t1). assert (A:= H0). apply F.get_trees_root in H0.
    destruct_all. assert (x = r1). eapply F.tree_root_unique; try(apply A); try(assumption). subst.
    apply H16. auto. apply H13. pose proof (F.get_trees_partition ((D2.dfs_forest g lt0 H o))).
    unfold F.P.partition in H16. destruct_all.  unfold F.P.disjoint in H17. specialize (H17 
    t1 t2 E H0 H1 v2). exfalso. apply H17; split; assumption.
  - reflexivity.
Qed. 

(*One final lemma before the algorithm: get_trees is a partition according to G.contains_vertex*)
Lemma get_trees_partition_graph : forall g lt H o,
  Pa.partition G.contains_vertex g (F.get_trees (D2.dfs_forest g lt H o)). 
Proof.
  intros. unfold Pa.partition. pose proof (F.get_trees_partition (D2.dfs_forest g lt0 H o)).
  unfold F.P.partition in H0. destruct_all. split. intros. apply H0.
  apply D2.same_vertices. apply H2. apply H1.
Qed.

(** Kosaraju's Strongly Connected Components Algorithm **)
Search F.desc.

(*TODO; maybe move this, maybe dont be so lazy also with assumptions*)

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
Require Import Wellfounded.

(*Let's try with induction*)


Lemma strong_ind_trees: forall (P: S.t -> Prop)

Lemma all_trees_strongly_connected: forall t1,
  InA S.Equal t1 (F.get_trees (D2.dfs_forest gt lt (reverseF g') None)) ->
  scc t1 gt.
Proof.
  intros. assert (A:= H). apply F.get_trees_root in H. destruct_all.
  clear H1. clear H0. remember (D1.f_time None g' x) as n. induction x using (@well_founded_induction G.vertex 
                        (fun x y : G.vertex => D1.f_time None g' x < D1.f_time None g' y)
                       (wf_inverse_image _ nat _ (@D1.f_time None g' )
                          PeanoNat.Nat.lt_wf_0)).



Lemma all_trees_strongly_connected: forall t1,
  InA S.Equal t1 (F.get_trees (D2.dfs_forest gt lt (reverseF g') None)) ->
  strongly_connected t1 gt.
Proof.
  intros. destruct (strongly_connected_dec t1 gt). apply s.
  assert (A:= H). apply F.get_trees_root in H. destruct_all.
  pose proof (vertex_in_scc gt x). assert (G.contains_vertex gt x = true).
   unfold gt in A. unfold lt in A. eapply get_tree_in_graph in A. apply A.
  apply H0. specialize (H2 H3). destruct H2 as [C]. destruct_all.
  
  assert (forall x0 : S.elt,
      S.In x0 t1 ->
      x0 <> x ->
      exists l : list G.vertex, Pa.path_list_rev gt x x0 l = true /\ (forall y : G.vertex, In y l -> S.In y t1)). {
  intros. apply H1 in H5. assert (x <> x0) by auto. rewrite <- F.desc_list_iff_desc in H5.
  destruct H5 as [l']. assert (B:= H5). eapply (desc_path _ _ _  H7) in H5. exists l'. simplify.
  destruct (O.eq_dec y x). unfold O.eq in e. subst. assumption. apply H1. auto.
  eapply F.desc_list_all_desc. apply B. apply H8. auto. }
  assert ((forall x : S.elt, S.In x t1 -> G.contains_vertex gt x = true)). { intros.
  eapply get_tree_in_graph. apply A. apply H6. } 
     pose proof (scc_vertex x t1 C gt H5 H6 n H2 H4 H0). clear H5.
  destruct H7 as [v]. destruct H5 as [C']. destruct_all. 
  (*Now we have another SCC, either every vertex in t1 or in a different one - if in a tree before, then v is
    descendant so in wrong tree. If it comes after, then that vertex should be in this tree. So it is entirely
    within t1, but it has a later finish time, which contradicts transpose corollary and root largest finish time
    so it must actually be strongly connected.
  *)
   pose proof (find_max_scc_exists (D1.f_time None g') gt C H2).
   pose proof (find_max_scc_exists (D1.f_time None g') gt C' H8).
   destruct H12 as [fC]. destruct H13 as [fC'].
   assert (forall y, S.In y C -> S.In y t1). {
   pose proof (get_trees_partition_graph gt lt (reverseF g') None).
   pose proof (scc_partition_1 _ _ _ _ _ H2 H14 A H4 H0). destruct H15. apply H15.
   pose proof (scc_partition_2 _ _ _ _ _ H2 H14 A H4 H0). destruct H16. apply H16.
   destruct_all. 
     

   assert (G.contains_vertex gt fC = true). unfold scc in H2. destruct H2. unfold strongly_connected in H2.
    apply H2. eapply max_elt_set_in_set. apply H12. pose proof (get_trees_partition_graph gt lt (reverseF g') None).
    unfold Pa.partition in H15. destruct_all. assert (FC:=H15). specialize (FC _ H14). destruct FC as [fCt FC].
    destruct FC. assert (S.equal t1 fCt = true). { destruct (S.equal t1 fCt) eqn : ?. reflexivity.
    
    
   assert (fC = x). destruct (O.eq_dec fC x). apply e. assert (B:= H12). apply max_elt_set_finds_max with (y:= x) in H12.
   assert (F.desc (D2.dfs_forest gt lt (reverseF g') None) x fC). { apply H1. auto. eapply max_elt_set_in_set.
   apply B.
  
  
  apply not_strongly_connected_vertex in n. 
  



End SecondPass.


End SCCAlg.








