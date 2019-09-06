Require Import Coq.Lists.List.
Require Import Coq.Lists.SetoidList.
Require Import Coq.Bool.Bool.
Require Import Omega.
Require Import Coq.Lists.ListDec.
Require Import Coq.FSets.FSetInterface.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties.


Lemma In_InA_equiv: forall A (x : A) l,
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

Lemma bool_prop: forall b b1,
  b = b1 <-> (b = true <-> b1 = true).
Proof.
  intros. destruct b. destruct b1. split; intros; reflexivity.
  split; intros. inversion H.  destruct H. destruct H. reflexivity. reflexivity.
  destruct b1. split; intros. inversion H. destruct H. destruct H0; reflexivity.
  split; intros; reflexivity.
Qed.

Ltac simplify := try(rewrite andb_diag in *); try(rewrite andb_true_iff in *); try(rewrite negb_true_iff in *);
  try(rewrite andb_false_iff in *); try(rewrite negb_false_iff in *); intuition.

(*Ltac for solving statements of the form: In x l, where l may be many lists appended together*) 
Ltac solve_in :=
  match goal with
  | [ H : _ |- In ?x (?l ++ ?r)] => apply in_or_app; solve_in
  | [ H : _ |- In ?x ?s \/ In ?x ?s'] => (right; solve_in) + (left; solve_in) 
  | [ H : _ |- In ?x (?x :: ?l)] => simpl; left; reflexivity
  | [H : _ |- In ?x (?a :: ?l)] => simpl; right; solve_in
  | [ H : _ |- _ ] => try(reflexivity); assumption
end. 

Ltac destruct_all :=
repeat(match goal with
            |[H: (exists _, _) |- _] => destruct H
            |[H: _ /\ _ |- _] => destruct H 
            end; try(rewrite andb_true_iff in *)).

(*Probably proved somewhere*)
Lemma Forall_all: forall A (l1: list A) l2 R,
  Forall R (l1 ++ l2) ->
  Forall R l1 /\ Forall R l2.
Proof.
  intros. generalize dependent l2. induction l1; intros.
  - simpl in H. split. constructor. apply H.
  - simpl in H. inversion H; subst. split.
    constructor. apply H2. apply (IHl1 l2). apply H3. apply (IHl1 l2). apply H3.
Qed.

(*Same as above, if concatenation of lists is sorted, so are both of the lists*)
Lemma sort_app: forall A (l1: list A) l2 R,
  StronglySorted R (l1 ++ l2) ->
  StronglySorted R l1 /\ StronglySorted R l2.
Proof.
  intros. generalize dependent l2. induction l1; intros.
  - simpl in H. split. constructor. apply H.
  - simpl in H. inversion H; subst.
    split. constructor. apply (IHl1 l2). apply H2.
    apply (Forall_all _ _ _ _ H3). apply IHl1. apply H2.
Qed.

Lemma contrapositive: forall (P Q: Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros. intro. apply H in H1. contradiction.
Qed.

Lemma in_split_app_fst: forall (A: Type) (l: list A) (x: A),
  (forall x y : A, {x = y} + {x <> y}) ->
  In x l ->
  exists l1 l2, l = l1 ++ (x :: l2) /\ forall y, In y l1 -> y <> x.
Proof.
  intros. induction l.
  - inversion H.
  - destruct (X x a). subst. exists nil. exists l. split. reflexivity. intros. inversion H0.
    simpl in H. destruct H. subst. contradiction.  apply IHl in H. destruct_all.
    exists (a :: x0). exists x1. split. rewrite H. reflexivity. intros. intro. subst.
    simpl in H1. destruct H1. subst. contradiction. apply H0 in H. contradiction.
Qed.

Lemma in_split_app_snd: forall (A: Type) (l: list A) (x: A),
  (forall x y : A, {x = y} + {x <> y}) ->
  In x l ->
  exists l1 l2, l = l1 ++ (x :: l2) /\ forall y, In y l2 -> y <> x.
Proof.
  intros. induction l.
  - inversion H.
  - simpl in *. destruct H. subst. destruct (in_dec X x l).
    apply IHl in i. destruct_all. exists (x :: x0). exists x1. split.
    simpl. rewrite H. reflexivity. apply H0.
    exists nil. exists l. split. reflexivity. intros. intro. subst.
    contradiction. apply IHl in H. destruct_all. exists (a :: x0). exists x1.
    split. rewrite H. simpl. reflexivity. apply H0.
Qed. 

Lemma no_no_dup: forall (A: Type) (l: list A),
  (forall x y : A, {x = y} + {x <> y}) ->
  ~(NoDup l) <-> (exists w l1 l2 l3, l = l1 ++ w :: l2 ++ w :: l3).
Proof.
  intros. split; intros.
  - induction l.
    + assert (@NoDup A nil). constructor. contradiction.
    + destruct (NoDup_dec X l).
      * assert (In a l). destruct (In_dec X a l). apply i.
        assert (NoDup (a :: l)). constructor. apply n0. apply n. contradiction.
        apply in_split_app_fst in H0. destruct_all. exists a. exists nil. exists x. exists x0.
        rewrite H0. reflexivity. apply X.
      * apply IHl in n. destruct_all. exists x. exists (a :: x0). exists x1. exists x2. rewrite H0.
        reflexivity.
  -  intro. destruct_all.  subst. induction x0; simpl in *.
    + rewrite NoDup_cons_iff in H0. destruct_all. apply H.
    solve_in.
    + simpl in H0. rewrite NoDup_cons_iff in H0. destruct_all. apply IHx0. apply H0.
Qed.

Lemma StronglySorted_NoDup: forall (A: Type) (P: A -> A -> Prop) (l: list A),
  (forall a, ~P a a) ->
  StronglySorted P l ->
  NoDup l.
Proof.
  intros. induction l. 
  - constructor.
  - inversion H0; subst. constructor. intro. 
    rewrite Forall_forall in H4. apply H4 in H1. apply H in H1. destruct H1.
    apply IHl. apply H3.
Qed.

(** ** Dealing with set inequality **)

(*It turns out to be surprisingly involved to prove that if two sets are not equal, then there
  is an element in one but not the other. I prove this by proving an analogous result for sorted lists
  and using S.elements to relate the two*)
Module SetNeq(O: UsualOrderedType) (S: FSetInterface.Sfun O).

  Module O2 := OrderedTypeFacts O.

(*List inequality as a function, since it gives us the element in one list but not the other
  directly*)
Fixpoint list_neq (l1 l2: list O.t) :=
  match l1, l2 with
  | x1 :: t1, x2 :: t2 => if O.eq_dec x1 x2 then list_neq t1 t2 else true
  | nil, nil => false
  | _, _ => true
  end.

(*The above function actually defines list inequality*)
Lemma list_eq_neq: forall l1 l2,
  l1 <> l2 <-> list_neq l1 l2 = true.
Proof.
  intros. split; intros.
  - generalize dependent l2. induction l1; intros.
    + simpl. destruct l2. contradiction. reflexivity.
    + simpl. destruct l2 eqn : ?. reflexivity.
      destruct (O.eq_dec a t).
      * setoid_rewrite e in H. assert (l1 <> l). intro. subst. contradiction.
        apply IHl1. apply H0.
      * reflexivity.
  - intro. subst. induction l2. simpl in H. inversion H. simpl in H.
    destruct (O.eq_dec a a). apply IHl2. apply H. apply n. apply eq_refl.
Qed. 

(*The result for lists: if two sorted lists are unequal, then there is an element in
  one but not the other*)
Lemma list_neq_has_diff_elements: forall (l1 l2: list O.t),
  StronglySorted O.lt l1 ->
  StronglySorted O.lt l2 ->
  l1 <> l2 ->
  (exists x, In x l1 /\ ~In x l2) \/ (exists x, ~In x l1 /\ In x l2).
Proof.
  intros. rewrite list_eq_neq in H1. generalize dependent l2; induction l1; intros.
  - simpl in H1. destruct l2 eqn : ?. inversion H1. right. exists t.
    split. auto. simpl. left. reflexivity.
  - simpl in H1. destruct l2 eqn : ?.
    + left. exists a. split. simpl. left. reflexivity. auto.
    + inversion H0; subst. inversion H; subst. destruct (O.eq_dec a t) eqn : ?. 
      * setoid_rewrite e. apply IHl1 in H4. destruct H4.
        -- destruct H2. destruct H2. assert (O.lt t x). rewrite Forall_forall in H7.
           setoid_rewrite <- e. eapply H7. apply H2. left. exists x. split. simpl.
           right. apply H2. simpl. intro. destruct H8. subst. apply O.lt_not_eq in H4.
           apply H4. apply eq_refl. contradiction.
        -- destruct H2. destruct H2. assert (O.lt t x). rewrite Forall_forall in H5.
           eapply H5. apply H3. right. exists x. split.  simpl. intro. destruct H8.
           subst. apply O.lt_not_eq in H4. apply H4. apply eq_refl. contradiction.
           simpl. right. apply H3.
        -- apply H6.
        -- apply H1.
      * pose proof (O2.lt_total a t). destruct H2.
        -- left. exists a. split. simpl. left. reflexivity. rewrite Forall_forall in H5.
           simpl. intro. destruct H3. subst. apply n. apply eq_refl. apply H5 in H3.
           apply O2.lt_le in H3. contradiction.
        -- destruct H2.
            ** subst. exfalso. apply n. apply eq_refl.
            ** right. exists t. split. simpl. intro. destruct H3. subst. apply n. apply eq_refl.
               rewrite Forall_forall in H7. apply H7 in H3. apply O2.lt_le in H3.
               contradiction. simpl. left. reflexivity.
Qed. 

(*The analogous result for sets*)
Lemma unequal_sets: forall s1 s2,
  S.equal s1 s2 = false ->
  (exists v, S.In v s1 /\ ~S.In v s2) \/ (exists v, ~S.In v s1 /\ S.In v s2).
Proof.
  intros. destruct (list_neq (S.elements s1) (S.elements s2)) eqn : ?.
  - rewrite <- list_eq_neq in Heqb. apply list_neq_has_diff_elements in Heqb.
    destruct Heqb.
    + destruct H0. destruct H0. rewrite In_InA_equiv in *. apply S.elements_2 in H0.
      assert (~S.In x s2). intro. apply S.elements_1 in H2. contradiction.
      left. exists x. split; assumption.
    + destruct H0. destruct H0. rewrite In_InA_equiv in *. apply S.elements_2 in H1.
      assert (~S.In x s1). intro. apply S.elements_1 in H2. contradiction.
      right. exists x. split; assumption.
    + apply Sorted_StronglySorted. unfold Relations_1.Transitive. intros.
      eapply O.lt_trans. apply H0. apply H1. apply S.elements_3.
    + apply Sorted_StronglySorted. unfold Relations_1.Transitive. intros.
      eapply O.lt_trans. apply H0. apply H1. apply S.elements_3.
  - destruct (list_eq_dec O.eq_dec (S.elements s1) (S.elements s2)).
    + assert (forall x, S.In x s1 <-> S.In x s2). { intros.
      split; intros; apply S.elements_1 in H0.  all: apply S.elements_2.
      rewrite <- e. assumption. rewrite e. assumption. }
      assert (~S.Equal s1 s2). intro. apply S.equal_1 in H1. rewrite H1 in H. inversion H.
      assert (S.Equal s1 s2). unfold S.Equal. apply H0. contradiction.
    + rewrite list_eq_neq in n. rewrite n in Heqb. inversion Heqb.
Qed.

End SetNeq.

Lemma nil_or_end: forall (A: Type) (l: list A),
  l = nil \/ exists x l', l = l' ++ x :: nil.
Proof.
  intros. induction l.
  - left. reflexivity.
  - destruct IHl. subst. right. exists a. exists nil. simpl. reflexivity. 
    destruct_all. right. subst. exists x. exists (a :: x0). reflexivity.
Qed.

Module MinMax(O: UsualOrderedType) .

(*Finding the minimum element in a list based on a given function*)
Definition min_elt_list (l: list O.t) (f: O.t -> nat) : option O.t :=
  fold_right (fun x s => match s with
                     | None => Some x
                     | Some y =>  if (f x <? f y) then Some x else s
                     end) None l.

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

(*The same but for max/finish time*)

Definition max_elt_list (l: list O.t) (f: O.t -> nat) : option O.t :=
  fold_right (fun x s => match s with
                     | None => Some x
                     | Some y =>  if (f y <? f x) then Some x else s
                     end) None l.

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

(** Finding the minimum element of a path **)
(*Because a path has the start, end, and intermediate list, this basically boils down to a ton of cases*)
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

End MinMax.

(*Definitions of a partition of a set and disjoint sets*)
Module Partition(O:UsualOrderedType)(S: FSetInterface.Sfun O).

(*Two sets are disjoint if there is no vertex in both*)
Definition disjoint s s' :=
  forall v, ~(S.In v s /\ S.In v s').

(*For ease with graph/forests, we define the partition of all items satisfying a function (can be
  \x y -> true to use all instances of type O.t). A partition is defined as a list of pairwise
  disjoint sets such that every vertex satsifying f is in a set *)
Definition partition {A: Type} (f: A -> O.t -> bool) (x: A) (l: list (S.t)) :=
  (forall v, f x v = true -> exists s, InA S.Equal s l /\ S.In v s) /\
  (forall s s', S.equal s s' = false -> InA S.Equal s l -> InA S.Equal s' l-> disjoint s s').

End Partition.




