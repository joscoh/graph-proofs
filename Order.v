Require Import Coq.Classes.RelationClasses.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.Structures.OrderedType.
  Class UsualOrdered (t: Type) := {
 Ueq := @eq t;
 Ult : t -> t -> Prop;
 eq_refl := @eq_refl t;
 eq_sym := @eq_sym t;
 eq_trans := @eq_trans t;
 lt_trans : forall x y z : t, Ult x y -> Ult y z -> Ult x z;
 lt_not_eq : forall x y : t, Ult x y -> ~ Ueq x y;
 compare : forall x y : t, Compare Ult Ueq x y;
 eq_dec : forall x y : t, { Ueq x y } + { ~ Ueq x y }
}.

Module UsualOrderedTypeToClass(O: UsualOrderedType).
  
  Program Instance mod_to_class : UsualOrdered (O.t) := {
    Ult := O.lt
  }.
  Next Obligation.
   eapply O.lt_trans. apply H. apply H0.
  Defined.
  Next Obligation.
    eapply O.lt_not_eq. apply H.
  Defined.
  Next Obligation.
    apply O.compare.
  Defined.
  Next Obligation.
    apply O.eq_dec.
  Defined.
End UsualOrderedTypeToClass.
  


Module Type ClassOrdered <: UsualOrderedType.
  Parameter t : Type.
  Parameter u : UsualOrdered t.

  Definition eq (t1 t2 : t) : Prop.
    pose proof u.  apply Ueq. apply t1. apply t2.
  Defined.

  Definition lt (t1 t2: t) : Prop.
    pose proof u. apply Ult. apply t1. apply t2.
  Defined.

  Definition eq_refl : forall x, eq x x.
  Proof.
    pose proof u. apply eq_refl.
  Defined.

  Definition eq_sym : forall x y : t, x = y -> y = x.
  Proof.
    pose proof u. apply eq_sym.
  Defined.

  Definition eq_trans: forall x y z : t, x = y -> y = z -> x = z.
  Proof.
    pose proof u. apply eq_trans.
  Defined.

  Definition lt_trans: forall x y z, lt x y -> lt y z -> lt x z.
  Proof.
    pose proof u. apply lt_trans.
  Defined.

  Definition lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    pose proof u. apply lt_not_eq.
  Defined.

  Definition compare: forall x y : t, Compare lt eq x y.
  Proof.
    pose proof u. apply compare. 
  Defined.

  Definition eq_dec : forall x y : t, { eq x y } + { ~ eq x y }.
  Proof. 
    pose proof u. apply eq_dec.
  Defined.


End ClassOrdered.