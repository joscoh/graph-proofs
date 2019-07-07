Require Import Coq.Lists.List.
Require Import Coq.Lists.SetoidList.
Require Import Coq.Bool.Bool.
Require Import Omega.
Require Import Coq.Lists.ListDec.


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





