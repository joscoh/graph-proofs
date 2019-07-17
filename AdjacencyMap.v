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
    exist.) So we define a wf predicate and instantiate the graph as a dependent type.
    Additionally, to implement transpose efficiently (in constant time) we store both incoming and outgoing edges.
    This makes add edge less efficient (though it is asympotically equal), but makes transpose MUCH faster
    (O(1) instead of O(nlogn) for a balanced BST map*)
  
  (*outgoing edges, incoming edges*)
  Definition graph_all : Type := (M.t (S.t) *  M.t (S.t)).
  
  Definition contains_vertex_all (g: graph_all) v := M.mem v (fst g).

  Definition add_vertex_all (g: graph_all) v := if (contains_vertex_all g v) then g else 
    (M.add v (S.empty) (fst g), M.add v (S.empty) (snd g)).

  Definition empty_all : graph_all := (M.empty (S.t), M.empty (S.t)).

  Definition add_edge_one (g: M.t (S.t)) u v  : M.t (S.t) :=
    match (M.find u g) with
    | None => g
    | Some s => match (M.find v g) with
                | None => g 
                | _ => M.add u (S.add v s) g
                end
    end.

  Definition add_edge_all (g: graph_all) u v :=
    (add_edge_one (fst g) u v, add_edge_one (snd g) v u).

  Definition contains_edge_one (g: M.t S.t) u v : bool :=
    match (M.find u g) with
    | None => false
    | Some s => S.mem v s
    end.

  Inductive wf_graph : graph_all -> Prop :=
  | emp: wf_graph empty_all
  | addv: forall g v, wf_graph g -> wf_graph (add_vertex_all g v)
  | adde: forall g u v, wf_graph g -> wf_graph (add_edge_all g u v).

  Lemma find_mem_some: forall {A: Type} m x (y: A),
    M.find x m = Some y ->
    M.mem x m = true.
  Proof.
    intros.  assert (M.find x m <> None). intro. rewrite H0 in H. inversion H.
    eapply P'.F.in_find_iff in H0. apply P'.F.mem_in_iff. apply H0.
  Qed.

  Lemma find_mem_none: forall {A: Type} (m: M.t A) x,
    M.find x m = None <->
    M.mem x m = false.
  Proof.
    intros. setoid_rewrite <- P'.F.not_find_in_iff. apply P'.F.not_mem_in_iff.
  Qed.

(*Two important lemmas that characterize the two different maps*)

  (*Both maps have the same vertices*)
  Lemma wf_graph_vertices: forall (g: graph_all) v,
    wf_graph g ->
    M.mem v (fst g) = true <-> M.mem v (snd g) = true.
  Proof.
    intros. revert v. induction H; intros.
    - simpl in *. rewrite P'.F.empty_a. reflexivity.
    - unfold add_vertex_all. destruct (contains_vertex_all g v) eqn : ?.
      + apply IHwf_graph.
      + simpl. destruct (O.eq_dec v v0). unfold O.eq in e. subst. rewrite P'.F.add_eq_b.
        rewrite P'.F.add_eq_b. reflexivity. reflexivity. reflexivity. 
        rewrite P'.F.add_neq_b. rewrite P'.F.add_neq_b. apply IHwf_graph. auto. auto.
    - unfold add_edge_all. simpl. unfold add_edge_one in *. destruct (M.find u (fst g)) eqn : ?.
      apply find_mem_some in Heqo. destruct (M.find v (fst g)) eqn : ?.
      apply find_mem_some in Heqo0. rewrite IHwf_graph in Heqo0. destruct (M.find v (snd g)) eqn : ?.
      destruct (M.find u (snd g)) eqn : ?. destruct (O.eq_dec v0 u). unfold O.eq in e. subst.
      rewrite P'.F.add_eq_b. split; intros. rewrite P'.F.add_b. apply orb_true_iff. right. apply IHwf_graph.
      apply Heqo. reflexivity. reflexivity. rewrite P'.F.add_neq_b. destruct (O.eq_dec v0 v).
      unfold O.eq in e. subst. rewrite P'.F.add_eq_b. rewrite IHwf_graph. rewrite Heqo0. reflexivity.
      reflexivity. rewrite P'.F.add_neq_b. apply IHwf_graph. auto. auto. 
      apply find_mem_none in Heqo2. apply IHwf_graph in Heqo. rewrite Heqo2 in Heqo. inversion Heqo.
      apply find_mem_none in Heqo1. rewrite Heqo1 in Heqo0. inversion Heqo0.
      rewrite find_mem_none in Heqo0.
      destruct (M.mem v (snd g)) eqn : ?. apply IHwf_graph in Heqb. rewrite Heqb in Heqo0. inversion Heqo0.
      apply find_mem_none in Heqb. rewrite Heqb. apply IHwf_graph.
      destruct (M.find u (snd g)) eqn : ?. apply find_mem_some in Heqo0. apply find_mem_none in Heqo.
      apply IHwf_graph in Heqo0. rewrite Heqo0 in Heqo. inversion Heqo. destruct (M.find v (snd g)); apply IHwf_graph.
Qed.

(*An edge (u,v) is in the first map iff (v,u) is in the second map (this is why transpose is very efficient)*)
  Lemma wf_graph_edges: forall g u v,
    wf_graph g ->
    contains_edge_one (fst g) u v = true <-> contains_edge_one (snd g) v u = true.
  Proof.
    intros. revert u. revert v. induction H; intros; unfold contains_edge_one in *; simpl in *.
    - rewrite P'.F.empty_o. rewrite P'.F.empty_o. reflexivity.
    - unfold add_vertex_all. destruct (contains_vertex_all g v) eqn : ?; simpl. apply IHwf_graph.
      destruct (O.eq_dec u v). unfold O.eq in e. subst.
      rewrite P'.F.add_eq_o. destruct (O.eq_dec v0 v). unfold O.eq in e. subst.
      rewrite P'.F.add_eq_o. reflexivity. reflexivity. rewrite P'.F.add_neq_o.
      rewrite <- IHwf_graph. unfold contains_vertex_all in Heqb. apply find_mem_none in Heqb. rewrite Heqb.
      rewrite P.Dec.F.empty_b. reflexivity. auto. reflexivity.
      rewrite P'.F.add_neq_o. unfold contains_vertex_all in Heqb. destruct (O.eq_dec v0 v). unfold O.eq in e.
      subst. rewrite P'.F.add_eq_o. rewrite IHwf_graph.
      destruct (M.mem v (snd g)) eqn : ?.
      apply wf_graph_vertices in Heqb0. rewrite Heqb0 in Heqb. inversion Heqb. apply H.
      apply find_mem_none in Heqb0. rewrite Heqb0. rewrite P.Dec.F.empty_b. reflexivity. reflexivity.
      rewrite P'.F.add_neq_o. apply IHwf_graph. auto. auto.
    - unfold add_edge_one. simpl. destruct (M.find u (fst g)) eqn : ?.
      + assert (exists t, M.find u (snd g) = Some t). { destruct (M.find u (snd g)) eqn : ?.
        exists t0. reflexivity. apply find_mem_some in Heqo. apply wf_graph_vertices in Heqo.
        apply find_mem_none in Heqo0. rewrite Heqo0 in Heqo. inversion Heqo. apply H. }
        destruct_all. rewrite H0. destruct (M.find v (fst g)) eqn : A.
        * assert (exists t, M.find v (snd g) = Some t). { destruct (M.find v (snd g)) eqn : ?.
        exists t1. reflexivity. apply find_mem_some in A. apply wf_graph_vertices in A.
        apply find_mem_none in Heqo0. rewrite Heqo0 in A. inversion A. apply H. }
        destruct_all. rewrite H1. destruct (O.eq_dec u0 u). unfold O.eq in e. subst.
        rewrite P'.F.add_eq_o. destruct (O.eq_dec v v0). unfold O.eq in e. subst.
        rewrite P'.F.add_eq_o. rewrite P.FM.add_b. rewrite P.FM.add_b.
        unfold P.FM.eqb. destruct (O.eq_dec v0 v0). destruct (O.eq_dec u u). reflexivity.
        exfalso. apply n. reflexivity. exfalso. apply n. reflexivity. reflexivity.
        rewrite P'.F.add_neq_o. rewrite P.FM.add_b. rewrite <- IHwf_graph. rewrite Heqo.
        unfold P.FM.eqb. destruct (O.eq_dec v v0). contradiction. simpl. reflexivity.
        auto. reflexivity. rewrite P'.F.add_neq_o. destruct (O.eq_dec v0 v). unfold O.eq in e.
        subst. rewrite P'.F.add_eq_o. rewrite IHwf_graph. rewrite H1. rewrite P.FM.add_b.
        unfold P.FM.eqb. destruct (O.eq_dec u u0). intuition. reflexivity. reflexivity.
        rewrite P'.F.add_neq_o. apply IHwf_graph. auto. auto.
        * assert (M.find v (snd g) = None). { destruct (M.find v (snd g)) eqn : ?.
          apply find_mem_some in Heqo0. apply wf_graph_vertices in Heqo0.
          apply find_mem_none in A. rewrite Heqo0 in A. inversion A. apply H. reflexivity. }
          rewrite H1. apply IHwf_graph.
      + assert (M.find u (snd g) = None). { destruct (M.find u (snd g)) eqn : ?.
          apply find_mem_some in Heqo0. apply wf_graph_vertices in Heqo0.
          apply find_mem_none in Heqo. rewrite Heqo0 in Heqo. inversion Heqo. apply H. reflexivity. }
        rewrite H0. destruct (M.find v (snd g)); apply IHwf_graph.
Qed.

  Definition transpose (g: graph_all) := (snd g, fst g).

  Lemma transpose_wf: forall g,
    wf_graph g ->
    wf_graph (transpose g).
  Proof.
    intros. unfold transpose. induction H; simpl in *.
    - constructor.
    - unfold add_vertex_all. destruct (contains_vertex_all g v) eqn : ?.
      apply IHwf_graph. simpl. eapply addv in IHwf_graph. unfold add_vertex_all in IHwf_graph.
      unfold contains_vertex_all in *. simpl in *. 
      destruct (M.mem v (snd g)) eqn : ?. apply wf_graph_vertices in Heqb0. rewrite Heqb0 in Heqb.
      inversion Heqb. apply H. rewrite Heqb0 in IHwf_graph. apply IHwf_graph.
    - unfold add_edge_one. assert (A:= IHwf_graph). eapply adde in A. unfold add_edge_all in A.
      simpl in *. unfold add_edge_one in A. simpl in *. apply A.
  Qed.

  Definition graph := {g: graph_all | wf_graph g}.

  Definition vertex := O.t.

  Definition empty : graph := (exist _ empty_all emp).

  Definition contains_vertex (g: graph) (v: vertex) : bool :=
    contains_vertex_all (proj1_sig g) v.

  Definition contains_edge (g: graph) (u v : vertex) : bool :=
    contains_edge_one (fst (proj1_sig g)) u v.

  Definition add_vertex (g: graph)(v: vertex) : graph.
  Proof.
    unfold graph. econstructor. apply (addv (proj1_sig g) v). unfold graph in g.
    destruct g. simpl. apply w. 
  Defined.

  Definition add_edge (g: graph)( u v: vertex) : graph.
  Proof. 
    unfold graph in *. econstructor. apply (adde (proj1_sig g) u v). destruct g. simpl. apply w.
  Defined.

  Definition neighbors_list (g: graph) (v: vertex) : option (list vertex) :=
    match (M.find v (fst(proj1_sig g))) with
    | None => None
    | Some s => Some (S.elements s)
    end.

  Definition neighbors_set (g: graph) (v: vertex) : option (S.t) :=
    M.find v (fst(proj1_sig g)).

  Definition fst_list {A B} (l : list (A * B)) : list A :=
    fold_right (fun (x : A * B) t => let (a,b) := x in a ::t) nil l.

  Definition list_of_graph (g: graph) : list vertex :=
    fst_list (M.elements (fst(proj1_sig g))).

  (*Couldn't find a better function in the interface, so have to add each element*)
  Definition set_of_graph (g: graph) : S.t :=
    fold_right (fun x t => S.add x t) S.empty (list_of_graph g).

  Definition get_transpose (g:graph) : graph.
  Proof.
    unfold graph in *. destruct g. apply transpose_wf in w. econstructor. apply w. 
  Defined.

  (*Theories*)

  Ltac unfold_all:=
  repeat(match goal with
         | [ H: _ |- _] => progress (unfold contains_vertex in *; simpl)
         | [ H: _ |- _] => progress (unfold contains_vertex_all in *; simpl)
         | [ H: _ |- _] => progress (unfold empty in *; simpl)
         | [ H: _ |- _] => progress (unfold add_vertex in *; simpl)
         | [ H: _ |- _] => progress (unfold add_vertex_all in *; simpl)
         | [ H: _ |- _] => progress (unfold add_edge_one in *; simpl)
         | [ H: _ |- _] => progress (unfold add_edge in *; simpl)
         | [ H: _ |- _] => progress (unfold add_edge_all in *; simpl)
         | [ H: _ |- _] => progress (unfold contains_edge in *; simpl)
         | [ H: _ |- _] => progress (unfold contains_edge_one in *; simpl)
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
    intros. unfold_all. destruct g. simpl. destruct (M.mem v (fst x)) eqn : ?.
    - apply Heqb.
    - apply M.mem_1. unfold M.In. exists S.empty. apply M.add_1. reflexivity.
  Qed.
  
  Lemma contains_edge_1: forall g u v,
    contains_edge g u v = true ->
    contains_vertex g u = true.
  Proof.
    intros. unfold_all. destruct g; simpl in *. 
    destruct (M.find u (fst x)) eqn : ?.
    - rewrite P'.F.mem_find_b. rewrite Heqo. reflexivity.
    - inversion H.
  Qed.

  Lemma contains_edge_2: forall g u v,
    contains_edge g u v = true ->
    contains_vertex g v = true.
  Proof.
    intros. unfold_all; destruct g; simpl in *. destruct (M.find u (fst x)) eqn : ?. generalize dependent t.
     induction w; intros; try(unfold_all).
    - rewrite P'.F.empty_o in Heqo. inversion Heqo.
    - destruct (M.mem v0 (fst g)) eqn : ?.
      + eapply IHw. apply Heqo. apply H.
      + destruct (O.eq_dec u v0).
        * unfold O.eq in e. subst. simpl in *. rewrite P'.F.add_eq_o in Heqo. inversion Heqo; subst.
          rewrite P.Dec.F.empty_b in H. inversion H. reflexivity.
        * simpl in *. rewrite P'.F.add_neq_o in Heqo. rewrite P'.F.add_b. apply orb_true_iff.
          right. eapply IHw. apply Heqo. apply H. auto.
    - destruct (M.find u0 (fst g)) eqn : ?.
      + destruct (M.find v0 (fst g)) eqn : ?. destruct (O.eq_dec u u0). unfold O.eq in e. subst; simpl in *.
        rewrite P'.F.add_eq_o in Heqo. inversion Heqo; subst. destruct (O.eq_dec v v0). unfold O.eq in e.
        subst. destruct (O.eq_dec v0 u0). unfold O.eq in e. subst. rewrite P'.F.add_b.
        apply orb_true_iff. left. unfold P'.F.eqb. destruct (O.eq_dec u0 u0). reflexivity. exfalso.
        apply n. reflexivity. rewrite P'.F.add_b. apply orb_true_iff. right.
        rewrite P'.F.mem_find_b. rewrite Heqo1. reflexivity.
        rewrite P.Dec.F.add_neq_b in H. rewrite P'.F.add_b. apply orb_true_iff. right. eapply IHw.
        apply Heqo0. apply H. auto. reflexivity. simpl in *. rewrite P'.F.add_neq_o in Heqo. 
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
    rewrite P'.F.mem_find_b in H0. destruct (M.find v (fst x)) eqn : ?.
    destruct (M.find u (fst x)) eqn : ?. rewrite P'.F.add_eq_o. rewrite P.FM.add_b.
    apply orb_true_iff. left. unfold P.FM.eqb. destruct (O.eq_dec v v). reflexivity.
    exfalso. apply n. reflexivity. reflexivity. inversion H0. inversion H.
  Qed. 

  Lemma add_edge_2: forall g u v a b,
    contains_edge g a b = true ->
    contains_edge (add_edge g u v) a b = true.
  Proof.
    intros. assert (contains_vertex g a = true) by (eapply contains_edge_1; eassumption).
    assert (contains_vertex g b = true) by (eapply contains_edge_2; eassumption).
     unfold_all. destruct g; simpl in *. destruct (M.find a (fst x)) eqn : ?.
    - destruct (M.find u (fst x)) eqn : ?.
      + destruct (O.eq_dec a u) eqn : ?.
        * unfold O.eq in e. subst. destruct (O.eq_dec v b).
          -- unfold O.eq in e. subst. rewrite P'.F.mem_find_b in H1. destruct (M.find b (fst x)) eqn : ?.
             ++ rewrite P'.F.add_eq_o. rewrite P.Dec.F.add_b. apply orb_true_iff. left.
                unfold P.Dec.F.eqb. destruct (O.eq_dec b b). reflexivity. exfalso. apply n. reflexivity.
                reflexivity.
             ++ inversion H1.
          -- rewrite Heqo0 in Heqo. inversion Heqo; subst. destruct (M.find v (fst x)) eqn : ?.
             rewrite P'.F.add_eq_o. rewrite P.FM.add_b. apply orb_true_iff. right. apply H. reflexivity.
             rewrite P'.F.mem_find_b in H0. destruct (M.find u (fst x)) eqn : ?. inversion Heqo0; subst.
             apply H. inversion H0.
        * clear Heqs. destruct (M.find v (fst x)) eqn : ?. rewrite P'.F.add_neq_o. 
          rewrite P'.F.mem_find_b in H0. destruct (M.find a (fst x)). inversion Heqo; subst. apply H. inversion H0.
          auto. rewrite P'.F.mem_find_b in H0. destruct (M.find a (fst x)). inversion Heqo; subst. apply H. inversion Heqo.
      +  rewrite P'.F.mem_find_b in H0. destruct (M.find a (fst x)). inversion Heqo; subst. apply H. inversion Heqo.
    - inversion H.
  Qed.
 
  Lemma add_edge_3: forall g u v a b,
    u <> a \/ v <> b ->
    (contains_edge g a b = contains_edge (add_edge g u v) a b).
  Proof.
    intros. unfold_all;destruct g; simpl in *. destruct (M.find u (fst x)) eqn : ?.
    destruct (M.find v (fst x)) eqn : ?. destruct H.
    rewrite P'.F.add_neq_o. reflexivity. apply H. destruct (O.eq_dec u a).
    unfold O.eq in e. subst. rewrite P'.F.add_eq_o. rewrite Heqo. rewrite P.Dec.F.add_neq_b.
    reflexivity. apply H. reflexivity. rewrite P'.F.add_neq_o. reflexivity. auto.
    reflexivity. reflexivity.
  Qed.

  Lemma neighbors_list_1: forall g v,
    contains_vertex g v = false <-> neighbors_list g v = None.
  Proof.
    intros. unfold_all; destruct g; simpl in *. unfold neighbors_list. simpl in *. split; intros.
    - destruct (M.find v (fst x)) eqn : ?. apply M.find_2 in Heqo.
      assert (M.In v (fst x)). unfold M.In. exists t. assumption.
      apply M.mem_1 in H0. rewrite H0 in H. inversion H. reflexivity.
    - destruct (M.find v (fst x)) eqn : ?. inversion H. destruct (M.mem v (fst x)) eqn : ?.
      apply M.mem_2 in Heqb. unfold M.In in Heqb. destruct Heqb.
      apply M.find_1 in H0. rewrite H0 in Heqo. inversion Heqo. reflexivity.
Qed.

  Lemma neighbors_list_2: forall g u v l,
    neighbors_list g u = Some l ->
    contains_edge g u v = true <-> In v l.
  Proof.
    intros. unfold_all; unfold neighbors_list in *; destruct g; simpl in *. 
    destruct (M.find u (fst x)) eqn : ?.
    - inversion H; subst. split; intros. 
      + apply S.mem_2 in H0. apply S.elements_1 in H0. rewrite <- In_InA_equiv in H0. assumption.
      + apply S.mem_1. apply S.elements_2. rewrite <- In_InA_equiv. assumption.
    - inversion H.
  Qed.

  Lemma neighbors_list_3: forall g v l,
    neighbors_list g v = Some l ->
    StronglySorted (O.lt) l. 
  Proof.
    intros. unfold neighbors_list in H; destruct g; simpl in *. destruct (M.find v (fst x)).
    - inversion H; subst. apply Sorted_StronglySorted. unfold Relations_1.Transitive.
      intros. eapply O.lt_trans. apply H0. apply H1. apply S.elements_3.
    - inversion H.
  Qed.

  Lemma neighbors_set_1: forall g v,
    neighbors_set g v = None <-> neighbors_list g v = None.
  Proof.
    intros. unfold neighbors_set. unfold neighbors_list. destruct g; simpl in *. 
    destruct (M.find v (fst x)).
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
      unfold M.eq_key_elt in H. induction (M.elements (fst x)).
      + rewrite InA_nil in H. destruct H.
      + simpl. rewrite InA_cons in H. destruct H.
        * destruct H. simpl in *. left. subst. destruct a. simpl. reflexivity.
        * right. apply IHl. apply H.
    - rewrite <- in_fst_list in H. destruct H. 
      assert (InA (M.eq_key_elt (elt:=S.t)) (v, x0) (M.elements (fst x))). { induction (M.elements (fst x)).
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

  Lemma tranpose_vertices: forall g v,
    contains_vertex g v = true <-> contains_vertex (get_transpose g) v = true.
  Proof.
    intros. unfold_all. unfold get_transpose. destruct g. simpl in *. apply wf_graph_vertices.
    apply w.
  Qed.

  Lemma transpose_edges: forall g u v,
    contains_edge g u v = true <-> contains_edge (get_transpose g) v u = true.
  Proof. 
    intros. unfold_all. unfold get_transpose. destruct g. simpl in *. apply wf_graph_edges. apply w.
  Qed.

  Definition topological_sort l g :=
    (forall v, contains_vertex g v = true <-> In v l) /\ NoDup l /\
    (forall l1 l2 l3 u v, l = l1 ++ u :: l2 ++ v :: l3 -> contains_edge g v u = false).

  Lemma topological_sort_def: forall l g,
    topological_sort l g <-> 
  (forall v, contains_vertex g v = true <-> In v l) /\ NoDup l /\
  (forall l1 l2 l3 u v, l = l1 ++ u :: l2 ++ v :: l3 -> contains_edge g v u = false).
  Proof.
    intros. unfold topological_sort. reflexivity.
  Qed.

End AdjacencyMap. 
