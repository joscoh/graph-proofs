Require Import Queue.
Require Import Coq.Structures.Equalities.
Require Import Lists.List.

Module QueueImpl(T: Typ) <: Queue.

  Definition queue : Type := (list T.t * list T.t).
  Definition t : Type := T.t.
  Definition empty : queue := (nil, nil).

  Definition enqueue (x : t)(q : queue) :=
    match q with
    | (l, l') => (x :: l, l')
    end.

  (*Flips the first stack and puts in the position of the second stack*)
  Fixpoint flip (l1: list t) (l2: list t) : queue :=
    match l1 with
      | nil => (l1, l2)
      | x :: tl => flip tl (x :: l2)
    end.

  Definition flip_queue (q: queue) : queue :=
    match q with
    | (_ :: _, nil) => flip (fst q) nil
    | (_, _) => q
    end.
    

  Definition peek (q: queue) : option t :=
    match (flip_queue q) with
    | (_, x :: _) => Some x
    | (_, _) => None
    end.

  Definition dequeue (q: queue) : queue :=
    match (flip_queue q) with
    | (l1, x :: t) => (l1, t)
    | (_, _) => (nil, nil)
    end.

  Definition is_empty (q: queue) : bool :=
    match q with
    | (nil, nil) => true
    | (_, _) => false
    end.

  Definition size (q: queue) : nat :=
    length (fst q) + length (snd q).

  Definition to_list (q: queue) : list t :=
    snd q ++ rev (fst q).

  Lemma empty_spec: is_empty empty = true.
  Proof.
    unfold empty. reflexivity.
  Qed.
  
  Lemma enqueue_spec: forall q x, 
    to_list (enqueue x q) = (to_list q) ++ (x :: nil).
  Proof.
    intros. unfold to_list. unfold enqueue. destruct q. simpl. rewrite app_assoc. reflexivity.
  Qed. 

  Lemma flip_spec: forall l1 l2,
    flip l1 l2 = (nil, (rev l1) ++ l2).
  Proof.
    intros. generalize dependent l2. induction l1; intros; simpl.
    - reflexivity.
    - rewrite IHl1. assert ((rev l1 ++ a :: nil) ++ l2 = rev l1 ++ a :: l2). {
      rewrite <- app_assoc. simpl. reflexivity. } rewrite H. reflexivity.
  Qed.

  Lemma flip_fst_nil: forall l1 l2 x y,
     (flip l1 l2) = (x, y) -> x = nil.
  Proof.
    intros. generalize dependent l2. induction l1; intros; simpl in H.
    - inversion H; subst; reflexivity.
    - apply (IHl1 (a :: l2)). apply H. 
  Qed.

  Lemma flip_queue_spec: forall q,
    to_list (flip_queue q) = to_list q.
  Proof.
    intros. unfold flip_queue. destruct q. destruct l.
    - reflexivity.
    - destruct l0; simpl.
      + unfold to_list. rewrite flip_spec. simpl. rewrite app_nil_r. reflexivity.
      + reflexivity.
    Qed.

  Lemma peek_spec_some: forall q x,
    peek q = Some x <-> exists l, to_list q = x :: l.
  Proof.
    intros. split; intros.
    - unfold peek in H. destruct (flip_queue q) eqn : A. destruct l0. inversion H.
      inversion H; subst. pose proof (flip_queue_spec). specialize (H0 q). rewrite A in H0.
      unfold to_list at 1 in H0. simpl in H0. exists (l0 ++ rev l). rewrite <- H0. reflexivity.
    - unfold peek. destruct H. pose proof (flip_queue_spec q). rewrite <- H0 in H.
      destruct (flip_queue q) eqn : A. 
      destruct l0. destruct l. unfold to_list in H. simpl in H. inversion H.
      destruct q. simpl in A. destruct l0. inversion A. destruct l1. 
      simpl in A. apply flip_fst_nil in A. inversion A. inversion A. unfold to_list in H.
       simpl in H. inversion H; subst; reflexivity.
  Qed.

  Lemma dequeue_spec_empty: forall q,
    to_list q = nil ->
    to_list (dequeue q) = nil.
  Proof.
    intros. destruct q. unfold to_list in H. simpl in H. destruct l0.
    destruct l. unfold dequeue. simpl. unfold to_list. simpl. reflexivity.
    simpl in H. destruct (rev l); inversion H. inversion H.
  Qed.

  Lemma dequeue_spec_nonempty: forall q h tl,
    to_list q = h :: tl ->
    to_list (dequeue q) = tl.
  Proof.
    intros. pose proof (flip_queue_spec q).
    rewrite H in H0. unfold dequeue. destruct (flip_queue q) eqn : A.
    destruct l0. destruct q. simpl in A. destruct l0. inversion A; subst. unfold to_list in H. simpl in H.
    inversion H. destruct l1. apply flip_fst_nil in A. subst. unfold to_list in H0; simpl in H0; inversion H0.
    inversion A. unfold to_list in H0. simpl in H0.
    destruct q. simpl in A. destruct l1. inversion A; subst. unfold to_list; simpl. simpl in H0.
    inversion H0; subst. reflexivity. destruct l2. apply flip_fst_nil in A. subst. inversion H0; subst.
    unfold to_list. simpl. reflexivity. inversion A; subst. unfold to_list; simpl. unfold to_list in H; simpl in H.
    inversion H; subst. reflexivity.
  Qed.

  Lemma is_empty_spec: forall q,
    is_empty q = true <-> to_list q = nil.
  Proof.
    intros. split; intros; destruct q; destruct l; destruct l0; simpl in *; 
    unfold to_list in *; simpl in H; try(reflexivity); try(inversion H).
    destruct (rev l); inversion H.
  Qed.
    
  Lemma size_spec: forall q,
    size q = length (to_list q).
  Proof.
    intros. unfold size. unfold to_list. rewrite app_length. rewrite rev_length. intuition.
  Qed. 

  Lemma peek_spec_none: forall q,
    peek q = None <-> is_empty q = true.
  Proof.
    intros. setoid_rewrite is_empty_spec. split; intros. 
    - unfold peek in H. pose proof (flip_queue_spec q). destruct (flip_queue q) eqn : A.
      destruct q. simpl in A. destruct l1. destruct l0. inversion A; subst. unfold to_list; reflexivity.
      inversion H. destruct l2. apply flip_fst_nil in A. subst. destruct l0. unfold to_list in H0; simpl in H0.
      destruct (rev l1); inversion H0. inversion H. inversion A; subst. inversion H.
    - unfold to_list in H. destruct q. simpl in *. apply app_eq_nil in H. destruct H. 
      subst. assert (l = nil). destruct l. reflexivity. simpl in H0. destruct (rev l); inversion H0. subst.
      unfold peek. reflexivity. 
  Qed.

End QueueImpl.


  
