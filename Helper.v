Require Import Coq.Lists.List.
Require Import Coq.Lists.SetoidList.


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
