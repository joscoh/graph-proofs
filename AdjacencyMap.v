Require Import Graph.

Require Import Coq.FSets.FMapInterface.

Require Import Coq.FSets.FSetProperties.

Module AdjacencyMap(O: UsualOrderedType)(S: FSetInterface.Sfun O)(M: FMapInterface.Sfun O) <: (Graph O S).

  Import Graph.

  Module P := FSetProperties.WProperties_fun O S.

  (*We represent graphs as a map from vertices to sets of edges (neighbors)*)
  Definition graph := M.t (S.t).

  Definition vertex := O.t.

  Definition contains_vertex (g: graph)(v: vertex) : bool := M.mem v g.

  Definition contains_edge (g: graph)(u v: vertex): bool :=
    match (M.find u g) with
    | None => false
    | Some s => S.mem v s
    end.

  Definition add_vertex (g: graph)(v: vertex) : graph :=
    M.add v (S.empty) g.

  Definition add_edge (g: graph)( u v: vertex) : graph :=
    match (M.find u g) with
    | None => g
    | Some s => M.add u (S.add v s) g
    end.

  Definition neighbors_list (g: graph) (v: vertex) : option (list vertex) :=
    match (M.find v g) with
    | None => None
    | Some s => Some (S.elements s)
    end.

  Definition neighbors_set (g: graph) (v: vertex) : option (S.t) :=
    M.find v g.

  Definition fst_list {A B} (l : list (A * B)) : list A :=
    fold_right (fun (x : A * B) t => let (a,b) := x in a ::t) nil l.

  Definition list_of_graph (g: graph) : list vertex :=
    fst_list (M.elements g).

  (*Couldn't find a better function in the interface, so have to add each element*)
  Definition set_of_graph (g: graph) : S.t :=
    fold_right (fun x t => S.add x t) S.empty (list_of_graph g).

(*Theories*)
  Lemma add_vertex_1: forall g v,
    contains_vertex (add_vertex g v) v = true.
  Proof.
    intros. unfold contains_vertex. unfold add_vertex. apply M.mem_1. unfold M.In.
    exists S.empty. apply M.add_1. reflexivity.
  Qed. 

  Lemma add_edge_1: forall g u v,
    contains_vertex g v = true ->
    contains_vertex g u = true ->
    contains_edge (add_edge g u v) u v = true.
  Proof.
    intros. unfold contains_vertex in *. unfold contains_edge. unfold add_edge. apply M.mem_2 in H0.
    unfold M.In in H0. destruct H0. apply M.find_1 in H0. rewrite H0.
    assert ( M.MapsTo u (S.add v x) (M.add u (S.add v x) g)). { 
    apply M.add_1. reflexivity. } apply M.find_1 in H1. rewrite H1.
    apply S.mem_1. apply S.add_1. reflexivity.
  Qed.

  Lemma add_edge_2: forall g u v a b,
    contains_edge g a b = true ->
    contains_edge (add_edge g u v) a b = true.
  Proof.
    intros. unfold contains_edge in *. unfold add_edge. destruct (M.find a g) eqn : ?.
    - destruct (M.find u g) eqn : ?.
      + destruct (O.eq_dec a u) eqn : ?.
        * setoid_rewrite e. setoid_rewrite e in Heqo.
          rewrite Heqo0 in Heqo. inversion Heqo; subst.
          assert (M.MapsTo u (S.add v t) (M.add u (S.add v t) g)). apply M.add_1. reflexivity.
          apply M.find_1 in H0. rewrite H0. apply S.mem_1. apply S.mem_2 in H.
          apply S.add_2. apply H.
        * assert (M.MapsTo a t (M.add u (S.add v t0) g)). apply M.add_2. intro. subst.
          apply n. apply eq_refl. apply M.find_2. apply Heqo. apply M.find_1 in H0.
          rewrite H0. apply H.
      + rewrite Heqo. apply H.
  - inversion H.
  Qed. 

  Lemma add_edge_3: forall g u v a b,
    u <> a \/ v <> b ->
    (contains_edge g a b = contains_edge (add_edge g u v) a b).
  Proof.
    intros. unfold contains_edge. unfold add_edge. destruct (M.find u g) eqn : ?.
    - destruct (M.find a g) eqn : ?.
      + destruct (O.eq_dec u a).
        * setoid_rewrite e. setoid_rewrite e in Heqo. rewrite Heqo0 in Heqo.
          inversion Heqo; subst. assert (M.MapsTo a (S.add v t) (M.add a (S.add v t) g)).
          apply M.add_1. reflexivity. apply M.find_1 in H0. rewrite H0.
          destruct (S.mem b t) eqn : ?.
          -- symmetry. rewrite <- P.Dec.F.mem_iff. apply S.add_2. 
             apply S.mem_2. apply Heqb0.
          -- symmetry. rewrite <- P.FM.not_mem_iff. rewrite <- P.FM.not_mem_iff in Heqb0.
             intro. rewrite P.Dec.F.add_iff in H1. destruct H1.
              ++ subst. destruct H. setoid_rewrite e in H. contradiction. contradiction.
              ++ contradiction.
        * assert (M.MapsTo a t0 (M.add u (S.add v t) g)). apply M.add_2. intro.
          subst. apply n. apply eq_refl. apply M.find_2. apply Heqo0. apply M.find_1 in H0.
          rewrite H0. reflexivity.
      + destruct (O.eq_dec u a).
        * setoid_rewrite e in Heqo. rewrite Heqo0 in Heqo. inversion Heqo.
        * destruct (M.find a (M.add u (S.add v t) g)) eqn : ?.
          -- apply M.find_2 in Heqo1. apply M.add_3 in Heqo1.
            erewrite M.find_1 in Heqo0. inversion Heqo0. apply Heqo1. intro.
            subst. apply n. apply eq_refl.
          -- reflexivity.
   - reflexivity.
  Qed.

  Lemma neighbors_list_1: forall g v,
    contains_vertex g v = false <-> neighbors_list g v = None.
  Proof.
    intros. unfold contains_vertex. unfold neighbors_list. split; intros.
    - destruct (M.find v g) eqn : ?. apply M.find_2 in Heqo.
      assert (M.In v g). unfold M.In. exists t. assumption.
      apply M.mem_1 in H0. rewrite H0 in H. inversion H. reflexivity.
    - destruct (M.find v g) eqn : ?. inversion H. destruct (M.mem v g) eqn : ?.
      apply M.mem_2 in Heqb. unfold M.In in Heqb. destruct Heqb.
      apply M.find_1 in H0. rewrite H0 in Heqo. inversion Heqo. reflexivity.
Qed.

  Lemma In_InA_equiv: forall (x: O.t) l,
    In x l <-> InA eq x l.
  Proof.
    intros. induction l.
    - simpl. split; intros. 
      + destruct H.
      + apply InA_nil in H. destruct H.
    - simpl. split; intros.
      + apply InA_cons. destruct H. left. subst. reflexivity. right. apply IHl. assumption.
      + apply InA_cons in H. destruct H. left. subst. reflexivity. right. apply IHl. assumption.
  Qed.

  Lemma neighbors_list_2: forall g u v l,
    neighbors_list g u = Some l ->
    contains_edge g u v = true <-> In v l.
  Proof.
    intros. unfold contains_edge. unfold neighbors_list in H.
    destruct (M.find u g) eqn : ?.
    - inversion H; subst. split; intros. 
      + apply S.mem_2 in H0. apply S.elements_1 in H0. rewrite <- In_InA_equiv in H0. assumption.
      + apply S.mem_1. apply S.elements_2. rewrite <- In_InA_equiv. assumption.
    - inversion H.
  Qed.

  Lemma neighbors_list_3: forall g v l,
    neighbors_list g v = Some l ->
    StronglySorted (O.lt) l. 
  Proof.
    intros. unfold neighbors_list in H. destruct (M.find v g).
    - inversion H; subst. apply Sorted_StronglySorted. unfold Relations_1.Transitive.
      intros. eapply O.lt_trans. apply H0. apply H1. apply S.elements_3.
    - inversion H.
  Qed.

  Lemma neighbors_set_1: forall g v,
    neighbors_set g v = None <-> neighbors_list g v = None.
  Proof.
    intros. unfold neighbors_set. unfold neighbors_list. 
    destruct (M.find v g).
    - split; intros H; inversion H.
    - split; intros; reflexivity. 
  Qed.

  Lemma neighbors_set_2: forall g u v s,
    neighbors_set g u = Some s ->
    contains_edge g u v = true <-> S.In v s.
  Proof.
    intros. unfold contains_edge. unfold neighbors_set in H. rewrite H.
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
    intros. unfold contains_vertex. unfold list_of_graph. split; intros.
    - apply in_fst_list. apply M.mem_2 in H. unfold M.In in H.
      destruct H. exists x. apply M.elements_1 in H.
      unfold M.eq_key_elt in H. induction (M.elements g).
      + rewrite InA_nil in H. destruct H.
      + simpl. rewrite InA_cons in H. destruct H.
        * destruct H. simpl in *. left. subst. destruct a. simpl. reflexivity.
        * right. apply IHl. apply H.
    - rewrite <- in_fst_list in H. destruct H. 
      assert (InA (M.eq_key_elt (elt:=S.t)) (v, x) (M.elements g)). { induction (M.elements g).
      - simpl in H. destruct H.
      - simpl in H. destruct H.
        + destruct a. inversion H; subst. apply InA_cons. left. 
          unfold M.eq_key_elt. split; reflexivity.
        + apply InA_cons. right. apply IHl. apply H. }
        apply M.elements_2 in H0. apply M.mem_1. unfold M.In. exists x. apply H0.
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
    intros. unfold list_of_graph. apply fst_list_preserves_sorting. apply Sorted_StronglySorted.
    - unfold Relations_1.Transitive. intros. destruct x. destruct y. destruct z.
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
      

     
    