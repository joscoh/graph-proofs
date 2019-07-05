Require Import Graph.
Require Import Helper.

Require Import Coq.FSets.FMapInterface.

Require Import Coq.FSets.FSetProperties.
Require Import Coq.FSets.FMapFacts.

Module AdjacencyMap(O: UsualOrderedType)(S: FSetInterface.Sfun O)(M: FMapInterface.Sfun O) <: (Graph O S).

  Import Graph.

  Module P := FSetProperties.WProperties_fun O S.
  Module P' := FMapFacts.WProperties_fun O M.

  (*We represent graphs as a map from vertices to sets of edges (neighbors). However, we want to make sure that
    the map is well-formed (mainly this means that if an edge exists in the graph, then both endpoints must
    exist. So we define a wf predicate and instantiate the graph as a dependent type*)
  
  Definition graph_all := M.t (S.t).
  
  Definition contains_vertex_all (g: graph_all) v := M.mem v g.

  Definition add_vertex_all (g: graph_all) v := if (contains_vertex_all g v) then g else M.add v (S.empty) g.

  Definition empty_all : graph_all := (M.empty (S.t)).

  Definition add_edge_all (g: graph_all) u v := 
    match (M.find u g) with
    | None => g
    | Some s => match (M.find v g) with
                | None => g 
                | _ => M.add u (S.add v s) g
                end
    end.

  Inductive wf_graph : graph_all -> Prop :=
  | emp: wf_graph empty_all
  | addv: forall g v, wf_graph g -> wf_graph (add_vertex_all g v)
  | adde: forall g u v, wf_graph g -> wf_graph (add_edge_all g u v).

  Definition graph := {g: graph_all | wf_graph g}.

  Definition vertex := O.t.

  Definition empty : graph := (exist _ empty_all emp).

  Definition contains_vertex (g: graph) (v: vertex) : bool :=
    contains_vertex_all (proj1_sig g) v.

  Definition contains_edge (g: graph) (u v : vertex) : bool :=
    match (M.find u (proj1_sig g)) with
    | None => false
    | Some s => S.mem v s
    end.

  Definition add_vertex (g: graph)(v: vertex) : graph.
    unfold graph. econstructor. apply (addv (proj1_sig g) v). unfold graph in g.
    destruct g. simpl. apply w. 
  Defined.

  Definition add_edge (g: graph)( u v: vertex) : graph. 
    unfold graph in *. econstructor. apply (adde (proj1_sig g) u v). destruct g. simpl. apply w.
  Defined.

  Definition neighbors_list (g: graph) (v: vertex) : option (list vertex) :=
    match (M.find v (proj1_sig g)) with
    | None => None
    | Some s => Some (S.elements s)
    end.

  Definition neighbors_set (g: graph) (v: vertex) : option (S.t) :=
    M.find v (proj1_sig g).

  Definition fst_list {A B} (l : list (A * B)) : list A :=
    fold_right (fun (x : A * B) t => let (a,b) := x in a ::t) nil l.

  Definition list_of_graph (g: graph) : list vertex :=
    fst_list (M.elements (proj1_sig g)).

  (*Couldn't find a better function in the interface, so have to add each element*)
  Definition set_of_graph (g: graph) : S.t :=
    fold_right (fun x t => S.add x t) S.empty (list_of_graph g).

  (*Theories*)

  Ltac unfold_all:=
  repeat(match goal with
         | [ H: _ |- _] => progress (unfold contains_vertex in *; simpl)
         | [ H: _ |- _] => progress (unfold contains_vertex_all in *; simpl)
         | [ H: _ |- _] => progress (unfold empty in *; simpl)
         | [ H: _ |- _] => progress (unfold add_vertex in *; simpl)
         | [ H: _ |- _] => progress (unfold add_vertex_all in *; simpl)
         | [ H: _ |- _] => progress (unfold add_edge in *; simpl)
         | [ H: _ |- _] => progress (unfold add_edge_all in *; simpl)
         | [ H: _ |- _] => progress (unfold contains_edge in *; simpl)
         | [ H: _ |- _] => progress (unfold empty_all in *; simpl)
         end). 

  Lemma empty_1: forall v,
    contains_vertex empty v = false.
  Proof.
   intros. unfold_all. apply P'.F.empty_a.
  Qed.

  Lemma empty_2: forall u v,
    contains_edge empty u v = false.
  Proof.
    intros. unfold_all. rewrite P'.F.empty_o. reflexivity.
  Qed.

  Lemma add_vertex_1: forall g v,
    contains_vertex (add_vertex g v) v = true.
  Proof.
    intros. unfold_all. destruct g. simpl. destruct (M.mem v x) eqn : ?.
    - apply Heqb.
    - apply M.mem_1. unfold M.In. exists S.empty. apply M.add_1. reflexivity.
  Qed.
  
  Lemma contains_edge_1: forall g u v,
    contains_edge g u v = true ->
    contains_vertex g u = true.
  Proof.
    intros. unfold_all. destruct g; simpl in *. 
    destruct (M.find u x) eqn : ?.
    - rewrite P'.F.mem_find_b. rewrite Heqo. reflexivity.
    - inversion H.
  Qed.

  Lemma contains_edge_2: forall g u v,
    contains_edge g u v = true ->
    contains_vertex g v = true.
  Proof.
    intros. unfold_all; destruct g; simpl in *. destruct (M.find u x) eqn : ?. generalize dependent t.
     induction w; intros; try(unfold_all).
    - rewrite P'.F.empty_o in Heqo. inversion Heqo.
    - destruct (M.mem v0 g) eqn : ?.
      + eapply IHw. apply Heqo. apply H.
      + destruct (O.eq_dec u v0).
        * unfold O.eq in e. subst. rewrite P'.F.add_eq_o in Heqo. inversion Heqo; subst.
          rewrite P.Dec.F.empty_b in H. inversion H. reflexivity.
        * rewrite P'.F.add_neq_o in Heqo. rewrite P'.F.add_b. apply orb_true_iff.
          right. eapply IHw. apply Heqo. apply H. auto.
    - destruct (M.find u0 g) eqn : ?.
      + destruct (M.find v0 g) eqn : ?. destruct (O.eq_dec u u0). unfold O.eq in e. subst.
        rewrite P'.F.add_eq_o in Heqo. inversion Heqo; subst. destruct (O.eq_dec v v0). unfold O.eq in e.
        subst. destruct (O.eq_dec v0 u0). unfold O.eq in e. subst. rewrite P'.F.add_b.
        apply orb_true_iff. left. unfold P'.F.eqb. destruct (O.eq_dec u0 u0). reflexivity. exfalso.
        apply n. reflexivity. rewrite P'.F.add_b. apply orb_true_iff. right.
        rewrite P'.F.mem_find_b. rewrite Heqo1. reflexivity.
        rewrite P.Dec.F.add_neq_b in H. rewrite P'.F.add_b. apply orb_true_iff. right. eapply IHw.
        apply Heqo0. apply H. auto. reflexivity. rewrite P'.F.add_neq_o in Heqo. 
        rewrite P'.F.add_b. apply orb_true_iff. right. eapply IHw. apply Heqo. apply H. auto.
        eapply IHw. apply Heqo. apply H.
      + eapply IHw. apply Heqo. apply H.
    - inversion H.
  Qed.

  Lemma add_edge_1: forall g u v,
    contains_vertex g v = true ->
    contains_vertex g u = true ->
    contains_edge (add_edge g u v) u v = true.
  Proof.
    intros. unfold_all. destruct g; simpl in *. rewrite P'.F.mem_find_b in H.
    rewrite P'.F.mem_find_b in H0. destruct (M.find v x) eqn : ?.
    destruct (M.find u x) eqn : ?. rewrite P'.F.add_eq_o. rewrite P.FM.add_b.
    apply orb_true_iff. left. unfold P.FM.eqb. destruct (O.eq_dec v v). reflexivity.
    exfalso. apply n. reflexivity. reflexivity. inversion H0. inversion H.
  Qed. 

  Lemma add_edge_2: forall g u v a b,
    contains_edge g a b = true ->
    contains_edge (add_edge g u v) a b = true.
  Proof.
    intros. assert (contains_vertex g a = true) by (eapply contains_edge_1; eassumption).
    assert (contains_vertex g b = true) by (eapply contains_edge_2; eassumption).
     unfold_all. destruct g; simpl in *. destruct (M.find a x) eqn : ?.
    - destruct (M.find u x) eqn : ?.
      + destruct (O.eq_dec a u) eqn : ?.
        * unfold O.eq in e. subst. destruct (O.eq_dec v b).
          -- unfold O.eq in e. subst. rewrite P'.F.mem_find_b in H1. destruct (M.find b x) eqn : ?.
             ++ rewrite P'.F.add_eq_o. rewrite P.Dec.F.add_b. apply orb_true_iff. left.
                unfold P.Dec.F.eqb. destruct (O.eq_dec b b). reflexivity. exfalso. apply n. reflexivity.
                reflexivity.
             ++ inversion H1.
          -- rewrite Heqo0 in Heqo. inversion Heqo; subst. destruct (M.find v x) eqn : ?.
             rewrite P'.F.add_eq_o. rewrite P.FM.add_b. apply orb_true_iff. right. apply H. reflexivity.
             rewrite P'.F.mem_find_b in H0. destruct (M.find u x) eqn : ?. inversion Heqo0; subst.
             apply H. inversion H0.
        * clear Heqs. destruct (M.find v x) eqn : ?. rewrite P'.F.add_neq_o. 
          rewrite P'.F.mem_find_b in H0. destruct (M.find a x). inversion Heqo; subst. apply H. inversion H0.
          auto. rewrite P'.F.mem_find_b in H0. destruct (M.find a x). inversion Heqo; subst. apply H. inversion Heqo.
      +  rewrite P'.F.mem_find_b in H0. destruct (M.find a x). inversion Heqo; subst. apply H. inversion Heqo.
    - inversion H.
  Qed.
 
  Lemma add_edge_3: forall g u v a b,
    u <> a \/ v <> b ->
    (contains_edge g a b = contains_edge (add_edge g u v) a b).
  Proof.
    intros. unfold_all;destruct g; simpl in *. destruct (M.find u x) eqn : ?.
    destruct (M.find v x) eqn : ?. destruct H.
    rewrite P'.F.add_neq_o. reflexivity. apply H. destruct (O.eq_dec u a).
    unfold O.eq in e. subst. rewrite P'.F.add_eq_o. rewrite Heqo. rewrite P.Dec.F.add_neq_b.
    reflexivity. apply H. reflexivity. rewrite P'.F.add_neq_o. reflexivity. auto.
    reflexivity. reflexivity.
  Qed.

  Lemma neighbors_list_1: forall g v,
    contains_vertex g v = false <-> neighbors_list g v = None.
  Proof.
    intros. unfold_all; destruct g; simpl in *. unfold neighbors_list. simpl in *. split; intros.
    - destruct (M.find v x) eqn : ?. apply M.find_2 in Heqo.
      assert (M.In v x). unfold M.In. exists t. assumption.
      apply M.mem_1 in H0. rewrite H0 in H. inversion H. reflexivity.
    - destruct (M.find v x) eqn : ?. inversion H. destruct (M.mem v x) eqn : ?.
      apply M.mem_2 in Heqb. unfold M.In in Heqb. destruct Heqb.
      apply M.find_1 in H0. rewrite H0 in Heqo. inversion Heqo. reflexivity.
Qed.

  Lemma neighbors_list_2: forall g u v l,
    neighbors_list g u = Some l ->
    contains_edge g u v = true <-> In v l.
  Proof.
    intros. unfold_all; unfold neighbors_list in *; destruct g; simpl in *. 
    destruct (M.find u x) eqn : ?.
    - inversion H; subst. split; intros. 
      + apply S.mem_2 in H0. apply S.elements_1 in H0. rewrite <- In_InA_equiv in H0. assumption.
      + apply S.mem_1. apply S.elements_2. rewrite <- In_InA_equiv. assumption.
    - inversion H.
  Qed.

  Lemma neighbors_list_3: forall g v l,
    neighbors_list g v = Some l ->
    StronglySorted (O.lt) l. 
  Proof.
    intros. unfold neighbors_list in H; destruct g; simpl in *. destruct (M.find v x).
    - inversion H; subst. apply Sorted_StronglySorted. unfold Relations_1.Transitive.
      intros. eapply O.lt_trans. apply H0. apply H1. apply S.elements_3.
    - inversion H.
  Qed.

  Lemma neighbors_set_1: forall g v,
    neighbors_set g v = None <-> neighbors_list g v = None.
  Proof.
    intros. unfold neighbors_set. unfold neighbors_list. destruct g; simpl in *. 
    destruct (M.find v x).
    - split; intros H; inversion H.
    - split; intros; reflexivity. 
  Qed.

  Lemma neighbors_set_2: forall g u v s,
    neighbors_set g u = Some s ->
    contains_edge g u v = true <-> S.In v s.
  Proof.
    intros. unfold_all. unfold contains_edge. unfold neighbors_set in H. destruct g; simpl in *.
    rewrite H.
    split; intros. apply S.mem_2. assumption. apply S.mem_1. assumption.
  Qed.

  Lemma in_fst_list: forall (A B : Type) (x: A) (l : list (A * B)),
    (exists y, In (x,y) l) <-> In x (fst_list l).
  Proof.
    intros. induction l; split; intros.
    - simpl. simpl in H. destruct H. destruct H.
    - simpl in H. destruct H.
    - simpl. destruct a. simpl in H. destruct H. destruct H; simpl.
      + inversion H. left. reflexivity.
      + right. apply IHl. exists x0. apply H.
    - simpl. simpl in H. destruct a. simpl in H. destruct H.
      + exists b. left. subst. reflexivity.
      + apply IHl in H. destruct H. exists x0. right. apply H.
  Qed. 

  Lemma list_of_graph_1: forall g v,
    contains_vertex g v = true <-> In v (list_of_graph g).
  Proof.
    intros. unfold_all. unfold list_of_graph. destruct g; simpl in *. split; intros.
    - apply in_fst_list. apply M.mem_2 in H. unfold M.In in H.
      destruct H. exists x0. apply M.elements_1 in H.
      unfold M.eq_key_elt in H. induction (M.elements x).
      + rewrite InA_nil in H. destruct H.
      + simpl. rewrite InA_cons in H. destruct H.
        * destruct H. simpl in *. left. subst. destruct a. simpl. reflexivity.
        * right. apply IHl. apply H.
    - rewrite <- in_fst_list in H. destruct H. 
      assert (InA (M.eq_key_elt (elt:=S.t)) (v, x0) (M.elements x)). { induction (M.elements x).
      - simpl in H. destruct H.
      - simpl in H. destruct H.
        + destruct a. inversion H; subst. apply InA_cons. left. 
          unfold M.eq_key_elt. split; reflexivity.
        + apply InA_cons. right. apply IHl. apply H. }
        apply M.elements_2 in H0. apply M.mem_1. unfold M.In. exists x0. apply H0.
Qed.

  Lemma fst_list_preserves_sorting: forall l,
    StronglySorted (M.lt_key (elt:= S.t)) l ->
    StronglySorted (O.lt) (fst_list l).
  Proof.
    intros. unfold M.lt_key in H. induction H.
    - apply SSorted_nil.
    - simpl. destruct a. apply SSorted_cons. apply IHStronglySorted.
       rewrite Forall_forall in H0. rewrite Forall_forall. intros.
      rewrite <- in_fst_list in H1. destruct H1. apply H0 in H1. simpl in H1. apply H1.
  Qed.

  Lemma list_of_graph_2: forall g,
    StronglySorted (O.lt) (list_of_graph g).
  Proof.
    intros. unfold list_of_graph. destruct g; simpl. apply fst_list_preserves_sorting. apply Sorted_StronglySorted.
    - unfold Relations_1.Transitive. intros. destruct x0. destruct y. destruct z.
      eapply O.lt_trans. unfold M.lt_key in *. apply H. apply H0.
    - apply M.elements_3.
  Qed. 

  Lemma set_of_graph_1: forall g v,
    contains_vertex g v = true <-> S.In v (set_of_graph g).
  Proof.
    intros. assert (S.In v (set_of_graph g) <-> In v (list_of_graph g)). {
      unfold set_of_graph. induction (list_of_graph g).
      - simpl. split; intros. rewrite P.FM.empty_iff in H. destruct H. destruct H.
      - simpl. split; intros. apply P.FM.add_iff in H. destruct H. 
        + left. apply H.
        + right. apply IHl. apply H.
        + apply P.FM.add_iff. destruct H. left. apply H. right. apply IHl. apply H. }
        rewrite list_of_graph_1. rewrite H. reflexivity.
  Qed.

End AdjacencyMap. 
