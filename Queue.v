Require Import Coq.Lists.List.

Module Type Queue.

  Parameter queue : Type.
  Parameter t : Type.
  Parameter empty : queue.

  Parameter enqueue : t -> queue -> queue.
  Parameter peek: queue -> option t.
  Parameter dequeue : queue -> queue.
  Parameter is_empty : queue -> bool.
  Parameter size : queue -> nat.
  Parameter to_list: queue -> list (t).

  Parameter empty_spec: is_empty empty = true.
  Parameter enqueue_spec: forall q x, 
    to_list (enqueue x q) = (to_list q) ++ (x :: nil).
  Parameter peek_spec_none: forall q,
    peek q = None <-> is_empty q = true.
  Parameter peek_spec_some: forall q x,
    peek q = Some x <-> exists l, to_list q = x :: l.
  Parameter dequeue_spec_empty: forall q,
    to_list q = nil ->
    to_list (dequeue q) = nil.
  Parameter dequeue_spec_nonempty: forall q h tl,
    to_list q = h :: tl ->
    to_list (dequeue q) = tl.
  Parameter is_empty_spec: forall q,
    is_empty q = true <-> to_list q = nil.
  Parameter size_spec: forall q,
    size q = length (to_list q). 
End Queue.
    

    