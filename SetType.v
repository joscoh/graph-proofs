Require Import Order.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Lists.SetoidList.
Require Import Helper.

(*Definition of sets using Typeclasses, requiring a UsualOrdered type as the element. This consists of a subset
  of the functionality of the FSetInterface*)

Class SetType (t elt: Type) (H: UsualOrdered elt) := {
    SIn : elt -> t -> Prop;
    Equal s s' := forall a : elt, SIn a s <-> SIn a s';
    Subset s s' := forall a : elt, SIn a s -> SIn a s';
    Empty s := forall a : elt, ~ SIn a s;
    empty : t;
    is_empty : t -> bool;
    mem : elt -> t -> bool;
    add : elt -> t -> t;
    remove : elt -> t -> t;
    Seq : t -> t -> Prop := Equal;
    eq_dec : forall s s', { Seq s s' } + { ~ Seq s s' };
    equal : t -> t -> bool;
    subset : t -> t -> bool;
    cardinal : t -> nat;
    elements : t -> list elt;
    min_elt : t -> option elt;
    fold : forall A : Type, (elt -> A -> A) -> t -> A -> A
 }.

  


Class SetTheories {set e : Type} {He: UsualOrdered e} (H: SetType set e He) := {
  In_1 : forall (x y : e) (s' : set), Ueq x y -> SIn x s' -> SIn y s';
  eq_refl : forall s', Seq s' s';
  eq_sym :forall s' s'', eq s'' s' -> Seq s' s';
  eq_trans : forall s s' s'', Seq s s' -> Seq s' s'' -> Seq s s'';
  mem_1 : forall x s, SIn x s -> mem x s = true;
  mem_2 : forall x s, mem x s = true -> SIn x s;
  equal_1 : forall s s', Equal s s' -> equal s s' = true;
  equal_2 : forall s s', equal s s' = true -> Equal s s';
  subset_1 : forall s s', Subset s s' -> subset s s' = true;
  subset_2 : forall s s', subset s s' = true -> Subset s s';
  empty_1 : Empty empty;
  is_empty_1 : forall s, Empty s -> is_empty s = true;
  is_empty_2 : forall s, is_empty s = true -> Empty s;
  add_1 : forall x y s, Ueq x y -> SIn y (add x s);
  add_2 : forall x y s, SIn y s -> SIn y (add x s);
  add_3 : forall x y s, ~ Ueq x y -> SIn y (add x s) -> SIn y s;
  remove_1 : forall x y s, Ueq x y -> ~ SIn y (remove x s);
  remove_2 : forall x y s, ~ Ueq x y -> SIn y s -> SIn y (remove x s);
  remove_3 : forall x y s, SIn y (remove x s) -> SIn y s;
  cardinal_1 : forall s, cardinal s = length (elements s);
  elements_1 : forall x s, SIn x s -> InA Ueq x (elements s);
  elements_2 : forall x s, InA Ueq x (elements s) -> SIn x s;
  elements_3w : forall s, NoDupA Ueq (elements s);
  elements_3 : forall s, sort Ult (elements s);
  min_elt_1 : forall x s, min_elt s = Some x -> SIn x s;
  min_elt_2 : forall x y s, min_elt s = Some x -> SIn y s -> ~ Ult y x;
  min_elt_3 : forall s, min_elt s = None -> Empty s;
  fold_1 : forall (A : Type) (i : A) (f : e -> A -> A) s,
      fold _ f s i = fold_left (fun a e => f e a) (elements s) i
}.