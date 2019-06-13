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
