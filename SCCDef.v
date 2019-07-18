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
Require Import Coq.Program.Wf.

(*Contains the definition of an SCC and general facts about strong connectivity and SCCs*)
Module SCCDef(O: UsualOrderedType)(S: FSetInterface.Sfun O)(G: Graph O S).

  Module Pa := (Path.PathTheories O S G).
  Module P2 := FSetProperties.WProperties_fun O S.
  Module O2 := OrderedTypeFacts O.
  Module SN := Helper.SetNeq O S.

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

(*Any path between 2 vertices in an SCC must consist of vertices entirely within the SCC*)
Lemma scc_path_within: forall g C u v l,
  scc C g ->
  S.In u C ->
  S.In v C ->
  Pa.path_list_rev g u v l = true ->
  (forall x, In x l -> S.In x C).
Proof.
  intros. destruct (P2.In_dec x C). apply i.
  unfold scc in H. destruct H. unfold strongly_connected in H. destruct_all.
  assert (strongly_connected (S.add x C) g). { unfold strongly_connected. split.
  apply add_empty. split.
  - intros. destruct (O.eq_dec x0 x). 
    + unfold O.eq in e. subst. eapply Pa.path_implies_in_graph in H2. destruct_all. apply H9.
      apply H3.
    + apply S.add_3 in H7. apply H5. apply H7. auto.
  - intros. destruct (O.eq_dec x y).
    + unfold O.eq in e. subst. apply S.add_3 in H7.
      apply in_split_app_fst in H3. destruct_all. clear H10. subst.
      apply Pa.path_app in H2. destruct_all.
      destruct (O.eq_dec x0 u). unfold O.eq in e. subst. rewrite Pa.path_path_list_rev.
      exists x1. apply H3. eapply Pa.path_trans. apply (H6 _ u); try(assumption).
      rewrite Pa.path_path_list_rev. exists x1. apply H3. apply O.eq_dec. auto.
    + apply S.add_3 in H8. destruct (O.eq_dec x0 x).
      * unfold O.eq in e. subst. eapply in_split_app_fst in H3. destruct_all. subst. clear H10.
        apply Pa.path_app in H2. destruct_all. destruct (O.eq_dec v y). unfold O.eq in e. subst.
        rewrite Pa.path_path_list_rev. exists x0. apply H2. 
        eapply Pa.path_trans. rewrite Pa.path_path_list_rev. exists x0. apply H2. apply H6; try(assumption).
        apply O.eq_dec.
      * apply S.add_3 in H7. apply H6. apply H7. apply H8. auto. auto.
      * auto. }
  exfalso. apply (H4 x); assumption.
Qed.

(** Existence and Decidability **)

(* We want to prove that every vertex is in a SCC (ie, for every vertex in g, there exists a set C
  such that C is an SCC of g and the vertex is in C. This turns out to be very nontrivial.
   We would also like to show that if a set is strongly connected but is not an SCC, then there is a vertex x
  not in C that can be added and the new set is still strongly connected (basically the law of the excluded middle
  for SCCs. Both claims are very similar, and lead to a number of other results, such as the decidability of SCC-ness
  if a set is strongly connected. This requires several (inefficient) algorithms for checking and constructing
  a strongly connected set *)

(*See if the given vertex has a path to and from every vertex in the given set*)
Definition check_vertex (v: G.vertex) (C: S.t)(g: G.graph) : bool :=
  fold_right (fun x t => if Pa.path_dec g x v then if Pa.path_dec g v x then t else false else false) true (S.elements C).

Lemma check_vertex_all_paths: forall v C g,
  check_vertex v C g = true <-> (forall x, S.In x C -> Pa.path g v x /\ Pa.path g x v).
Proof.
  intros. split; intros.
  - unfold check_vertex in H. assert (forall x l, In x l -> 
    fold_right
      (fun (x : G.vertex) (t : bool) => if Pa.path_dec g x v then if Pa.path_dec g v x then t else false else false)
      true l = true -> Pa.path g v x /\ Pa.path g x v). { intros. induction l; simpl in *.
      - destruct H1.
      - destruct H1. subst. destruct (Pa.path_dec g x0 v). destruct (Pa.path_dec g v x0). simplify.
        inversion H2. inversion H2. destruct (Pa.path_dec g a v). destruct (Pa.path_dec g v a).
        apply IHl. apply H1. apply H2. inversion H2. inversion H2. }
      apply (H1 _ (S.elements C)). rewrite In_InA_equiv. apply S.elements_1. apply H0. apply H.
  - unfold check_vertex. assert (forall l, (forall x, In x l -> Pa.path g v x /\ Pa.path g x v) ->
    fold_right (fun (x : G.vertex) (t : bool) => if Pa.path_dec g x v then if Pa.path_dec g v x then t else false else false)
    true l = true). { intros. induction l; intros; simpl in *.
    + reflexivity. 
    + destruct (Pa.path_dec g a v). destruct (Pa.path_dec g v a). apply IHl. intros. apply H0. right. apply H1.
      specialize (H0 a). destruct H0. left. reflexivity. contradiction. specialize (H0 a). destruct H0.
      left. reflexivity. contradiction. }
    apply H0. intros. rewrite In_InA_equiv in H1. apply S.elements_2 in H1. apply H. apply H1.
Qed.

Lemma check_vertex_true: forall C g v,
  strongly_connected C g ->
  ~S.In v C ->
  G.contains_vertex g v = true ->
  check_vertex v C g = true <-> strongly_connected (S.add v C) g.
Proof.
  intros. split; intros.
  - unfold strongly_connected. split. apply add_empty. split. intros.
    destruct (O.eq_dec x v). unfold O.eq in e. subst. apply H1. 
    rewrite P2.FM.add_neq_iff in H3. unfold strongly_connected in H. apply H. apply H3. auto.
    intros. destruct (O.eq_dec x v). 
    + unfold O.eq in e. subst. rewrite P2.Dec.F.add_neq_iff in H4. 
      eapply check_vertex_all_paths in H2. destruct H2. apply H2. apply H4. apply H5.
    + rewrite P2.Dec.F.add_neq_iff in H3. destruct (O.eq_dec y v).
      * unfold O.eq in e. subst. eapply check_vertex_all_paths in H2. destruct H2. apply H6.
        apply H3. 
      * rewrite P2.Dec.F.add_neq_iff in H4. unfold strongly_connected in H. destruct_all. apply H7;
        try(assumption). auto.
      * auto.
  - rewrite check_vertex_all_paths. intros. unfold strongly_connected in H2. destruct_all.
    split. apply H5. apply S.add_1. reflexivity. apply S.add_2. apply H3. intro. subst. contradiction.
    apply H5. apply S.add_2. apply H3. apply S.add_1. reflexivity. intro. subst. contradiction.
Qed.

(* If a set is strongly connected but not an scc, this finds an additional vertex to add. If a set
  is an scc, it will return none*)
Definition find_additional (C: S.t) (g: G.graph) : option G.vertex :=
  fold_right (fun x t => if P2.In_dec x C then t else if check_vertex x C g then Some x else t) 
  None (G.list_of_graph g).

(*If C is strongly connected, find_additional returns None iff for all vertices, they are either in the set
  or cannot be added to make a strongly connected set*)
Lemma find_additional_none: forall C g,
  strongly_connected C g ->
  find_additional C g = None <-> (forall v, G.contains_vertex g v = true ->
  S.In v C \/ ~strongly_connected (S.add v C) g).
Proof.
  intros. split; intros.
  - unfold find_additional in H0. assert (forall l v, In v l -> G.contains_vertex g v = true ->
    fold_right
      (fun (x : S.elt) (t : option S.elt) => if P2.In_dec x C then t else if check_vertex x C g then Some x else t)
      None l = None -> S.In v C \/ ~strongly_connected (S.add v C) g). { intros. induction l; simpl in *.
      - destruct H2.
      - destruct H2. subst. destruct (P2.In_dec v0 C). left. apply i. destruct (check_vertex v0 C g) eqn : ?.
        inversion H4. right. intro. rewrite <- check_vertex_true in H2. rewrite H2 in Heqb. inversion Heqb.
        apply H. apply n. apply H3. destruct (P2.In_dec a C). apply IHl. apply H2.
        apply H4. destruct (check_vertex a C g) eqn : ?. inversion H4. apply IHl. apply H2. apply H4. }
      apply (H2 (G.list_of_graph g)). apply G.list_of_graph_1. apply H1. apply H1. apply H0.
  - unfold find_additional. assert (forall l, (forall x, In x l -> G.contains_vertex g x = true) ->
    (forall x, G.contains_vertex g x = true -> S.In x C \/  ~ strongly_connected (S.add x C) g) ->
    fold_right
    (fun (x : S.elt) (t : option S.elt) => if P2.In_dec x C then t else if check_vertex x C g then Some x else t)
    None l = None). { intros. induction l; simpl in *.
    - reflexivity.
    - destruct ( P2.In_dec a C). apply IHl. intros. apply H1. right. apply H3. destruct (check_vertex a C g) eqn : ?.
      rewrite check_vertex_true in Heqb. assert (G.contains_vertex g a = true). apply H1. left. reflexivity.
       exfalso. apply H2 in H3. destruct H3; contradiction. apply H. apply n. apply H1. left. reflexivity.
        apply IHl. intros. apply H1. right. apply H3. } apply H1.
     intros. apply G.list_of_graph_1 in H2. apply H2. apply H0.
Qed. 

(*In contrast, if C is strongly connected, then if find_additional gives Some x, this gives a vertex not in C
  which still results in a strongly connected set when added*)
Lemma find_additional_some: forall C g x,
  strongly_connected C g ->
  find_additional C g = Some x ->
  ~S.In x C /\ strongly_connected (S.add x C) g.
Proof.
  intros. unfold find_additional in H0. assert (forall l x,
  (forall x, In x l -> G.contains_vertex g x = true) ->
   fold_right
       (fun (x : S.elt) (t : option S.elt) => if P2.In_dec x C then t else if check_vertex x C g then Some x else t)
       None l= Some x ->
    ~ S.In x C /\ strongly_connected (S.add x C) g). { intros. induction l; simpl in *.
    - inversion H2.
    - destruct (P2.In_dec a C). apply IHl. intros. apply H1. right. apply H3. apply H2.
      destruct (check_vertex a C g) eqn : ?.
      rewrite check_vertex_true in Heqb. inversion H2; subst. simplify. apply H. apply n. apply H1. left.
      reflexivity. apply IHl. intros. apply H1. right. apply H3. apply H2. } apply (H1 (G.list_of_graph g)).
      intros. apply G.list_of_graph_1 in H2. apply H2. apply H0.
Qed.

(*This implies that a strongly connected set is an SCC iff find_additional returns None*)
Lemma find_additional_scc: forall C g,
  strongly_connected C g ->
  scc C g <-> find_additional C g = None.
Proof.
  intros. split; intros.
  - destruct (find_additional C g) eqn : ?.
    + apply find_additional_some in Heqo. unfold scc in H0. destruct H0. exfalso. apply (H1 v); apply Heqo.
      apply H.
    + reflexivity.
  - rewrite find_additional_none in H0. unfold scc. split. apply H.
    intros. intro. destruct (G.contains_vertex g x) eqn : ?.
    + apply H0 in Heqb. destruct Heqb; contradiction.
    + unfold strongly_connected in H2. destruct_all. rewrite H3 in Heqb. inversion Heqb. apply S.add_1. 
      reflexivity.
    + apply H.
Qed.

(*Thus, if we have a strongly connected set, scc-ness is decidable*)
Lemma scc_dec_weak: forall C g,
  strongly_connected C g ->
  {scc C g} + {~scc C g}.
Proof.
  intros. destruct (find_additional C g) eqn : ?.
  - right. intro. rewrite find_additional_scc in H0. rewrite H0 in Heqo. inversion Heqo.
    apply H.
  - left. apply find_additional_scc. apply H. apply Heqo.
Qed.

(* If a strongly connected set is not an scc, then there exists an element that we can add to get a larger
  strongly connected set (this is kind of a long way of getting around the lack of law of the excluded
  middle *)
Lemma non_scc_has_another: forall C g,
  strongly_connected C g ->
  ~scc C g ->
  exists v, ~S.In v C /\ strongly_connected (S.add v C) g.
Proof.
  intros. destruct (find_additional C g) eqn : ?.
  + exists v. apply find_additional_some. apply H. apply Heqo.
  + rewrite <- find_additional_scc in Heqo. contradiction. apply H.
Qed.

(*strongly connected sets are subsets of the vertex set of the graph*)
Lemma strongly_connected_subset: forall C g,
  strongly_connected C g ->
  S.Subset C (G.set_of_graph g).
Proof.
  intros. unfold S.Subset. intros. unfold strongly_connected in H. 
  apply G.set_of_graph_1. apply H. apply H0.
Qed.

(*If an strongly connected set is the size of the graph, it must be an SCC*)
Lemma scc_size_of_graph: forall C g,
  strongly_connected C g ->
  S.cardinal C = S.cardinal (G.set_of_graph g) ->
  scc C g.
Proof.
  intros. unfold scc. split. apply H. intros.
  intro. unfold strongly_connected in H2. destruct_all.
  assert (S.In x (G.set_of_graph g)). apply G.set_of_graph_1. apply H3. apply S.add_1. reflexivity.
  apply strongly_connected_subset in H.
  pose proof (P2.subset_cardinal_lt H H5 H1). omega.
Qed. 

Lemma strongly_connected_size: forall C g,
  strongly_connected C g ->
  S.cardinal C <= S.cardinal (G.set_of_graph g).
Proof.
  intros. apply P2.subset_cardinal. apply strongly_connected_subset. apply H.
Qed.

Lemma subset_add: forall (s : S.t) x,
  S.Subset s (S.add x s).
Proof.
  intros. unfold S.Subset. intros.
  apply S.add_2. apply H.
Qed.

(*We want to show that every vertex is in an SCC. To do this, this function builds an SCC out of any strongly
  connected set*)
Program Fixpoint build_scc (C: S.t) (g:G.graph) (H: strongly_connected C g)
  {measure (S.cardinal (G.set_of_graph g) - S.cardinal C)} : {C': S.t | scc C' g /\
   S.Subset C C'}  :=
  match (find_additional C g) with
  | None => exist _ C _
  | Some y => build_scc (S.add y C) g _
  end.
Next Obligation.
symmetry in Heq_anonymous.
rewrite <- find_additional_scc in Heq_anonymous. split. apply Heq_anonymous. apply P2.subset_refl. apply H.
Defined.
Next Obligation.
symmetry in Heq_anonymous. apply find_additional_some in Heq_anonymous. destruct Heq_anonymous. apply H1.
apply H.
Defined.
Next Obligation.
symmetry in Heq_anonymous. assert (A:=Heq_anonymous). apply find_additional_some in Heq_anonymous. destruct Heq_anonymous. 
rewrite P2.add_cardinal_2. pose proof (strongly_connected_size C g H).
assert ((S.cardinal C < S.cardinal (G.set_of_graph g)) \/ (S.cardinal C = S.cardinal (G.set_of_graph g))) by omega.
destruct H3. omega. apply scc_size_of_graph in H3. rewrite find_additional_scc in H3. rewrite H3 in A. inversion A.
apply H. apply H. apply H0. apply H.
Defined.
Next Obligation.
destruct ((build_scc (S.add y C) g (build_scc_func_obligation_2 C g H y Heq_anonymous)
        (build_scc_func_obligation_3 C g H y Heq_anonymous))). simpl. destruct a. split. apply H0.
assert (S.Subset C (S.add y C)) by (apply subset_add). eapply P2.FM.SubsetSetoid_Transitive.
apply H2. apply H1.
Defined.

(*A few final corollaries*)
Lemma subset_of_scc: forall C g,
  strongly_connected C g ->
  exists C', scc C' g /\ S.Subset C C'.
Proof.
  intros. pose proof (build_scc C g H). destruct X. exists x. apply a.
Qed.

(*What we wanted to prove*)
Lemma vertex_in_scc: forall g v,
  G.contains_vertex g v = true ->
  exists C, scc C g /\ S.In v C.
Proof.
  intros. remember (S.add v S.empty) as s. assert (strongly_connected s g). { subst.
  unfold strongly_connected. split. apply add_empty. split. intros. destruct (O.eq_dec x v).
  unfold O.eq in e. subst. apply H. apply P2.Dec.F.add_neq_iff in H0. rewrite P2.Dec.F.empty_iff in H0.
  destruct H0. auto. intros. destruct (O.eq_dec x v). unfold O.eq in e. subst.
  apply P2.Dec.F.add_neq_iff in H1. rewrite P2.Dec.F.empty_iff in H1. destruct H1. apply H2.
  apply P2.Dec.F.add_neq_iff in H0. rewrite P2.Dec.F.empty_iff in H0. destruct H0. auto. }
  apply subset_of_scc in H0. destruct H0. exists x. split. apply H0. destruct H0.
  subst. unfold S.Subset in H1. apply H1. apply S.add_1. reflexivity.
Qed.

(** More specific facts about SCCs and strong connectedness **)
(*These are useful for proving Kosaraju's algorithm is correct specifically *)

(*Decidability of [strongly_connected]*)

(*Check if nonempty set is strongly connected*)
Definition check_strong_conn (C: S.t) (g: G.graph) : bool :=
  fold_right (fun x t => if G.contains_vertex g x && check_vertex x (S.remove x C) g then t else false)
   true (S.elements C).

Lemma check_strong_conn_spec: forall C g,
  S.is_empty C = false ->
  check_strong_conn C g = true <-> strongly_connected C g.
Proof.
  intros. unfold check_strong_conn. assert (forall l, fold_right
  (fun (x : G.vertex) (t : bool) => if G.contains_vertex g x && check_vertex x (S.remove x C) g then t else false)
  true l = true <-> forall x, In x l -> G.contains_vertex g x = true /\ check_vertex x (S.remove x C) g = true). {
  intros; induction l; split; intros; simpl in *.
  - destruct H1.
  - reflexivity.
  - destruct H1. subst. destruct (G.contains_vertex g x && check_vertex x (S.remove x C) g) eqn : ?.
    + simplify.
    + inversion H0.
    + destruct (G.contains_vertex g a && check_vertex a (S.remove a C) g). apply IHl. apply H0. apply H1.
      inversion H0.
  - destruct (G.contains_vertex g a && check_vertex a (S.remove a C) g) eqn : ?.
    + simplify.
    + simplify. destruct (H0 a). left. reflexivity. rewrite H4 in H3. inversion H3.
      destruct (H0 a). left. reflexivity. rewrite H5 in H3. inversion H3. }
  rewrite H0. split; intros.
  - unfold strongly_connected. split. apply H. split. intros. apply H1. rewrite In_InA_equiv. apply S.elements_1.
    apply H2. intros. specialize (H1 x). destruct H1. rewrite In_InA_equiv. apply S.elements_1.
    apply H2. rewrite check_vertex_all_paths in H5. apply H5. apply S.remove_2. apply H4. apply H3.
  - unfold strongly_connected in H1. destruct_all.  rewrite In_InA_equiv in H2. apply S.elements_2 in H2.
    split. apply H3. apply H2. rewrite check_vertex_all_paths. intros. rewrite P2.FM.remove_iff in H5.
    destruct H5. split; apply H4; try(assumption). auto.
Qed.

(*Strong connectivity is decidable*)
Lemma strongly_connected_dec: forall C g,
  {strongly_connected C g} + {~strongly_connected C g}.
Proof.
  intros. destruct (S.is_empty C) eqn : ?.
  - right. intro. unfold strongly_connected in H. destruct H. rewrite Heqb in H. inversion H.
  - eapply (check_strong_conn_spec _ g) in Heqb. destruct (check_strong_conn C g).
    left. apply Heqb. reflexivity. right. intro. apply Heqb in H. inversion H.
Qed.

(*Not sure if I need this, but it is interesting to know*)
Lemma scc_dec: forall C g,
  {scc C g} + {~scc C g}.
Proof.
  intros. destruct (strongly_connected_dec C g). apply scc_dec_weak. apply s. right. intro.
  unfold scc in H. intuition.
Qed. 

(** A few more specific results **)

(*If u and v are in different sccs but there is a path from u to v, then there is a point along
  the path such that we move out of u's scc into a new one*)
Lemma scc_path: forall u v g l c c',
  G.contains_vertex g u = true ->
  G.contains_vertex g v = true ->
  scc c g ->
  scc c' g ->
  S.In u c ->
  S.In v c' ->
  S.equal c c' = false ->
  Pa.path_list_rev g u v l = true ->
  exists l1 l2, l = l1 ++ l2 /\ (forall x, In x l2 -> S.In x c) /\ (forall x, In x l1 -> ~S.In x c).
Proof.
  intros. generalize dependent v. generalize dependent c'. induction l; intros; simpl in *.
  - exists nil. exists nil. split. reflexivity. split; intros; inversion H7.
  - simplify. assert (G.contains_vertex g a = true). eapply G.contains_edge_1. apply H7.
    destruct (P2.In_dec a c). exists nil. exists (a:: l).  split. simpl. reflexivity.
    split. intros. simpl in H9. destruct H9. subst. apply i.
    eapply scc_path_within. apply H1. apply H3. apply i. apply H8. apply H9. intros. inversion H9.
    pose proof (vertex_in_scc g a H6). destruct H9 as [c'']. destruct H9.
    destruct (S.equal c c'') eqn : ?. apply P2.Dec.F.equal_iff in Heqb. rewrite <- Heqb in H10.
    contradiction.
    specialize (IHl c''  H9 Heqb a H6 H10 H8). destruct IHl as [l1]. destruct H11 as [l2].
    destruct_all. exists (a :: l1). exists l2. split. subst. simpl. reflexivity. split.
    apply H12. intros. simpl in H14. destruct H14. subst. contradiction. eapply H13; eassumption.
Qed.

Definition all_paths_from (v: G.vertex) (C: S.t) (g: G.graph) :=
  fold_right (fun x t => if O.eq_dec x v then t else if Pa.path_dec g x v then t else Some x) None (S.elements C).

Lemma all_paths_from_none: forall v C g,
  all_paths_from v C g = None <-> (forall x, S.In x C -> v <> x -> Pa.path g x v).
Proof.
  intros. unfold all_paths_from. assert (forall l, fold_right (fun (x : O.t) (t : option O.t) => if O.eq_dec x v then t else if Pa.path_dec g x v then t else Some x)
  None l = None <-> (forall x, In x l -> v <> x -> Pa.path g x v)). {
  intros. induction l; split; intros; simpl in *.
  - destruct H0.
  - reflexivity.
  - destruct H0. subst. destruct (O.eq_dec x v). unfold O.eq in e. subst. contradiction.
    destruct ( Pa.path_dec g x v). apply p. inversion H. destruct (O.eq_dec a v).
    apply IHl. apply H. apply H0. apply H1.
    destruct ( Pa.path_dec g a v). apply IHl. apply H. apply H0. apply H1. inversion H.
  - destruct (O.eq_dec a v). unfold O.eq in e. subst. apply IHl. intros. apply H. right. apply H0. apply H1.
    destruct ( Pa.path_dec g a v). apply IHl. intros. apply H. right. apply H0. apply H1.
    specialize (H a). assert (Pa.path g a v). apply H. left. reflexivity. auto. contradiction. }
  rewrite H. setoid_rewrite In_InA_equiv. setoid_rewrite P2.FM.elements_iff. reflexivity.
Qed.

Lemma all_paths_from_none_strong_conn: forall v C g,
  S.In v C ->
  (forall x, S.In x C -> Pa.path g v x) ->
  all_paths_from v C g = None ->
  strongly_connected C g.
Proof.
  intros. rewrite all_paths_from_none in H1. unfold strongly_connected. split.
  destruct (S.is_empty C) eqn : ?. apply S.is_empty_2 in Heqb. apply P2.empty_is_empty_1 in Heqb.
  rewrite Heqb in H. rewrite P2.Dec.F.empty_iff in H. inversion H. reflexivity. split.
  intros. apply H0 in H2. rewrite Pa.path_path_list_rev in H2. destruct H2. apply Pa.path_implies_in_graph in H2.
  intuition. intros. destruct (O.eq_dec v x). unfold O.eq in e. subst.
  apply H0. apply H3. destruct (O.eq_dec v y). unfold O.eq in e. subst.
  apply H1. apply H2. auto. eapply Pa.path_trans. apply H1. apply H2. auto. apply H0. apply H3.
Qed.

Lemma all_paths_from_some: forall C v g x,
  all_paths_from v C g = Some x ->
  v <> x /\ ~Pa.path g x v /\ S.In x C.
Proof.
  intros. unfold all_paths_from in H. assert (forall l,  fold_right
      (fun (x : O.t) (t : option O.t) => if O.eq_dec x v then t else if Pa.path_dec g x v then t else Some x) None
      l = Some x -> v <> x /\ ~Pa.path g x v /\ In x l). intros. induction l; simpl in *.
    - inversion H0.
    - destruct (O.eq_dec a v). unfold O.eq in e. subst. apply IHl in H0. simplify. 
      destruct (Pa.path_dec g a v). simplify. inversion H0; subst. simplify.
    - setoid_rewrite P2.FM.elements_iff.  rewrite <- In_InA_equiv. eapply H0. apply H.
Qed.

Lemma not_strongly_connected_vertex: forall u g c c1,
  (forall x, S.In x c -> Pa.path g u x) ->
  (forall x, S.In x c -> G.contains_vertex g x = true) ->
  ~strongly_connected c g ->
  scc c1 g ->
  S.In u c1 ->
  S.In u c ->
  exists v c2, S.In v c /\ S.In v c2 /\ scc c2 g /\ S.equal c1 c2 = false.
Proof.
  intros. destruct(all_paths_from u c g) eqn : ?.
  - exists t. apply all_paths_from_some in Heqo. destruct_all. assert (G.contains_vertex g t = true) by
    (apply H0; assumption).  apply vertex_in_scc in H8. destruct H8. exists x. split.
    apply H7. split. apply H8. split. apply H8. destruct (S.equal c1 x) eqn : ?.
    rewrite <- P2.FM.equal_iff in Heqb. destruct H8. rewrite <- Heqb in H9.
    unfold scc in H2. destruct H2. unfold strongly_connected in H2. destruct_all. 
    assert (Pa.path g t u). apply H12. apply H9. apply H3. auto. contradiction. reflexivity.
  - apply all_paths_from_none_strong_conn in Heqo. contradiction. apply H4. apply H.
Qed.

(*What we want to show- if u is a source vertex in a subset of the graph and has paths to all others in the set,
  then if the set is not strongly connected, there is another vertex in the set in a different SCC such that
  there is an edge from u's SCC to v's SCC*)
Lemma scc_vertex: forall u C c1 g,
  (forall x, S.In x C -> exists l, Pa.path_list_rev g u x l = true /\ forall y, In y l -> S.In y C) ->
  (forall x, S.In x C -> G.contains_vertex g x = true) ->
  ~strongly_connected C g ->
  scc c1 g ->
  S.In u c1 ->
  S.In u C ->
  exists v c2, S.In v C /\ S.In v c2 /\ scc c2 g /\ S.equal c1 c2 = false /\ exists x, S.In x c1 /\ G.contains_edge g x v = true.
Proof.
  intros. assert (A: forall x, S.In x C -> Pa.path g u x). intros. specialize (H x H5).
  destruct H. destruct H. rewrite Pa.path_path_list_rev. exists x0. apply H.
   pose proof (not_strongly_connected_vertex u g C c1 A H0 H1 H2 H3 H4). destruct H5 as [v].
  destruct H5 as [c']. destruct_all. assert (exists l, Pa.path_list_rev g u v l = true /\ forall y, In y l ->
  S.In y C). apply H. apply H5. destruct_all.
  assert (G.contains_vertex g u = true).
  apply H0. apply H4. assert (G.contains_vertex g v = true). apply H0. apply H5.
  pose proof (scc_path u v g x c1 c' H11 H12 H2 H7 H3 H6 H8 H9). destruct H13 as [l1]. destruct H13 as [l2].
  destruct_all. pose proof (nil_or_end _ l1). destruct H16.
  - subst. simpl in H9. destruct l2.
    + simpl in H9. exists v. exists c'. simplify. exists u. simplify.
    + simpl in H9. simplify. exists v. exists c'. simplify. exists v0. simplify.
  - destruct_all; subst. assert ((x1 ++ x0 :: nil) ++ l2 = x1 ++ x0 :: l2). rewrite <- app_assoc.
    simpl. reflexivity. rewrite H13 in H9. clear H13. apply Pa.path_app in H9. simplify.
    destruct l2. 
    + simpl in *. exists x0. assert (G.contains_vertex g x0 = true). 
      eapply Pa.path_implies_in_graph in H13. simplify. 
      eapply vertex_in_scc in H9. destruct H9. exists x. simplify. apply H10. solve_in.
      destruct (S.equal c1 x) eqn : ?.
      * apply S.equal_2 in Heqb. rewrite <- Heqb in H18. exfalso. apply (H15 x0). solve_in. apply H18.
      * reflexivity.
      * exists u. simplify.
    + simpl in *. simplify. exists x0. assert (G.contains_vertex g x0 = true). eapply G.contains_edge_2.
      apply H9. eapply vertex_in_scc in H16. destruct H16. exists x. simplify. apply H10. solve_in.
      destruct (S.equal c1 x) eqn : ?.
      * apply S.equal_2 in Heqb. rewrite <- Heqb in H19. exfalso. apply (H15 x0). solve_in. apply H19.
      * reflexivity.
      *  exists v0. simplify.
Qed.

(** SCCs of transpose graph **)
Lemma scc_transpose: forall C g,
  scc C g <-> scc C (G.get_transpose g).
Proof.
  intros. split; intros; unfold scc in *; destruct_all; simpl.
  - unfold strongly_connected in H. split.
    + unfold strongly_connected. split; try(simplify).
      * rewrite <- G.transpose_vertices. apply H. apply H2.
      * rewrite <- Pa.path_transpose. apply H3; simplify.
    + intros. intro. unfold strongly_connected in H2. destruct_all. setoid_rewrite <- Pa.path_transpose in H4.
      assert (strongly_connected (S.add x C) g). unfold strongly_connected; split. apply H2.
      split. intros. rewrite G.transpose_vertices. apply H3. apply H7. intros.
      apply H4; simplify. apply H0 in H1. contradiction.
  - unfold strongly_connected in H. destruct_all. split.
    + unfold strongly_connected; split; simplify.
      * setoid_rewrite <- G.transpose_vertices in H1. apply H1. apply H3.
      * setoid_rewrite <- Pa.path_transpose in H2. apply H2; simplify.
    + intros. intro. assert (strongly_connected (S.add x C) (G.get_transpose g)). {
      unfold strongly_connected in H4; destruct_all. unfold strongly_connected. split. apply H4.
      split; intros. rewrite <- G.transpose_vertices. apply H5. apply H7.
      rewrite <- Pa.path_transpose. apply H6; simplify. }
      apply H0 in H3. contradiction.
Qed.
      

End SCCDef.

