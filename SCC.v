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
(*Require Import DerivedProofs.*)

Module SCC(O: UsualOrderedType)(S: FSetInterface.Sfun O)(G: Graph O S)(F: Forest O S G)(D: DFSBase).

  Module Pa := (Path.PathTheories O S G).
  Module P2 := FSetProperties.WProperties_fun O S.
  Module O2 := OrderedTypeFacts O.
  Module SN := Helper.SetNeq O S.
  (*Module De := (DerivedProofs.DerivedProofs O S G F D).*)

  (*A set of vertices is strongly connected if every vertex in the set is in the graph and if there is a path
    between any two vertices in the set*)
  Definition strongly_connected(C: S.t)(g: G.graph) :=
    S.is_empty C = false /\
    (forall x, S.In x C -> G.contains_vertex g x = true) /\
    (forall x y, S.In x C -> S.In y C -> x <> y -> Pa.path g x y).
  
  (*A strongly connected component is a maximal strongly connected set*)
  Definition scc(C: S.t) (g: G.graph) :=
    strongly_connected C g /\ (forall x, ~ S.In x C -> ~strongly_connected (S.add x C) g).

  Lemma add_empty: forall x s,
    S.is_empty (S.add x s) = false.
  Proof.
    intros. destruct (S.is_empty (S.add x s)) eqn : ?.
    - apply S.is_empty_2 in Heqb. apply P2.empty_is_empty_1 in Heqb. unfold S.Equal in Heqb.
      specialize (Heqb x). assert (S.In x S.empty). apply Heqb. apply S.add_1. reflexivity.
      rewrite P2.Dec.F.empty_iff in H. destruct H.
    - reflexivity.
  Qed.

  (*Any two unequal SCCs are disjoint*)
  Lemma neq_scc_disjoint: forall g C1 C2,
    scc C1 g ->
    scc C2 g ->
    S.equal C1 C2 = false ->
    (forall x, ~(S.In x C1 /\ S.In x C2)).
  Proof.
    intros. intro. destruct H2. apply SN.unequal_sets in H1. unfold scc in H. unfold scc in H0.
    destruct_all. unfold strongly_connected in H. unfold strongly_connected in H0. destruct_all.
    destruct H1; destruct_all.
    - destruct (O.eq_dec x x0). unfold O.eq in e. subst. contradiction.
      assert (strongly_connected (S.add x0 C2) g). { unfold strongly_connected. split. apply add_empty.
      split.
      + intros. destruct (O.eq_dec x0 x1). unfold O.eq in e. subst. apply H8. apply H1.
        rewrite P2.FM.add_neq_iff in H11. apply H6. apply H11. apply n0.
      + intros.  destruct (O.eq_dec x0 y).
        * unfold O.eq in e. subst. rewrite P2.FM.add_neq_iff in H11.
          destruct (O.eq_dec x1 x).
          -- unfold O.eq in e. subst. apply H9; try(assumption).
          -- assert (Pa.path g x1 x). apply H7; try(assumption).
             eapply Pa.path_trans. apply H14. apply H9;try(assumption).
          -- auto.
        * rewrite P2.FM.add_neq_iff in H12. destruct (O.eq_dec x1 x0).
          -- unfold O.eq in e. subst. destruct (O.eq_dec x y).
             ++ unfold O.eq in e. subst. apply H9; try(assumption).
             ++ assert (Pa.path g x0 x). apply H9; try(assumption). auto.
                eapply Pa.path_trans. apply H14. apply H7; try(assumption).
          -- rewrite P2.FM.add_neq_iff in H11. apply H7; try(assumption). auto.
          -- auto. }
      apply (H4 x0); assumption.
   - destruct (O.eq_dec x x0). unfold O.eq in e. subst. contradiction.
      assert (strongly_connected (S.add x0 C1) g). { unfold strongly_connected. split. apply add_empty. split.
      + intros. destruct (O.eq_dec x0 x1). unfold O.eq in e. subst. apply H6. apply H10.
        rewrite P2.FM.add_neq_iff in H11. apply H8. apply H11. apply n0.
      + intros.  destruct (O.eq_dec x0 y).
        * unfold O.eq in e. subst. rewrite P2.FM.add_neq_iff in H11.
          destruct (O.eq_dec x1 x).
          -- unfold O.eq in e. subst. apply H7; try(assumption).
          -- assert (Pa.path g x1 x). apply H9; try(assumption).
             eapply Pa.path_trans. apply H14. apply H7;try(assumption).
          -- auto.
        * rewrite P2.FM.add_neq_iff in H12. destruct (O.eq_dec x1 x0).
          -- unfold O.eq in e. subst. destruct (O.eq_dec x y).
             ++ unfold O.eq in e. subst. apply H7; try(assumption).
             ++ assert (Pa.path g x0 x). apply H7; try(assumption). auto.
                eapply Pa.path_trans. apply H14. apply H9; try(assumption).
          -- rewrite P2.FM.add_neq_iff in H11. apply H9; try(assumption). auto.
          -- auto. }
      apply (H5 x0); assumption.
  Qed.
  

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
  intros. intro. assert (~S.In u C'). eapply neq_scc_disjoint in H1. intro. apply H1.
  split. apply H2. apply H8. apply H. apply H0.
  assert (strongly_connected (S.add u C') g). {
  unfold scc in H. unfold scc in H0. destruct_all. unfold strongly_connected in H.
  unfold strongly_connected in H0. destruct_all. unfold strongly_connected. split. apply add_empty. split.
  - intros. destruct (O.eq_dec x u). unfold O.eq in e. subst. apply H13. apply H2.
    rewrite P2.FM.add_neq_iff in H15. apply H11. apply H15. auto. 
  - intros. destruct (O.eq_dec x u).
    + unfold O.eq in e. subst. rewrite P2.FM.add_neq_iff in H16.
      destruct (O.eq_dec u' y). unfold O.eq in e. subst. apply H6.
      eapply Pa.path_trans. apply H6. apply H12; try(assumption). apply H17.
    + rewrite P2.FM.add_neq_iff in H15. destruct (O.eq_dec y u).
      * unfold O.eq in e. subst. destruct (O.eq_dec x v'). unfold O.eq in e. subst.
        destruct (O.eq_dec u v). unfold O.eq in e. subst. apply H7.
        eapply Pa.path_trans. apply H7. apply H14; try(assumption). auto.
        eapply Pa.path_trans. apply H12. apply H15. apply H5. auto.
        destruct (O.eq_dec u v). unfold O.eq in e. subst. apply H7.
        eapply Pa.path_trans. apply H7. apply H14; try(assumption). auto.
      * rewrite P2.FM.add_neq_iff in H16. apply H12; try(assumption). auto.
      * auto. }
  unfold scc in H0. destruct H0. apply (H10 u); assumption.
Qed.

(** Results about times of 1st DFS Pass **)
Module D1 := (D O S G F).
Module Der1 := (DerivedProofs.DerivedProofs O S G F D1).

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

(*Definition of discovery time of SCC*)
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

Lemma path_module_equiv: forall g x y,
  Pa.path g x y <-> D1.P.path g x y.
Proof.
  intros. split; intros; induction H.
  - constructor. apply H.
  - eapply D1.P.p_continue. apply IHpath. apply H0.
  - constructor. apply H.
  - eapply Pa.p_continue. apply IHpath. apply H0.
Qed. 

(*TODO: Prove that SCC implies a path entirely within the SCC and a path entirely within with unique vertices
  ie: know unique from derived, then show within because if out, then get bigger SCC*)

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
  unfold scc in Hc. unfold scc in Hc'. destruct Hc. destruct_all.
  unfold strongly_connected in s0. unfold strongly_connected in s. destruct_all.
  assert (G.contains_vertex g x0 = true). apply e0. apply H8. 
  pose proof (D1.discovery_exists None g x0 H9). destruct H10 as [s].
  assert (forall v, S.In v c' -> v <> x0 -> D1.white None g s v = true). { intros.
  rewrite D1.white_def. rewrite Nat.ltb_lt. unfold d_time_scc in H6.
   eapply min_elt_set_finds_min in H6. rewrite <- H10 in H6. apply H6. intros.
  eapply D1.d_times_unique. apply e0. apply H13. apply e0. apply H14. apply H15.
  apply H11. apply H12. }
  assert (forall v, S.In v c' -> v <> x0 -> exists l, D1.P.path_list_ind g x0 v (fun x => D1.white None g s v) l). {
  intros. apply (p x0) in H12. rewrite path_module_equiv in H12. rewrite D1.P.path_path_list_rev in H12.
  destruct H12 as [l]. exists l. rewrite D1.P.path_list_ind_rev. split. apply H12.
  split. intros. apply H11. (*need to know all vertices on path in SCC and might need path with no cycles - can
  prove from reachable I think because that cannot have a cycle*)

(*next steps: do same for max, define f_time, then prove lemma 22.14*)
(*it would be really nice to prove this lemma, although it is ok if I dont finish today*)
  

  








