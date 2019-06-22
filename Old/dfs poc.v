

Require Import Coq.FSets.FMapInterface.

Require Import Coq.Program.Wf.

Require Import Coq.Arith.EqNat.

Require Import Coq.Arith.PeanoNat.

Require Import Coq.Lists.List.

Import ListNotations.

Require Import
  Coq.FSets.FMapFacts
  Coq.FSets.FSetFacts
  Coq.FSets.FSetProperties
  Coq.Structures.OrderedTypeEx.

Module DFS (O: UsualOrderedType) (M : FMapInterface.Sfun O)(S: FSetInterface.Sfun O).

Module P := FMapFacts.WProperties_fun O M.
Module F := P.F.
Module P2 := FSetProperties.WProperties_fun O S.

(*A graph is a map from nats to sets of nats (neighbors)*)
Definition graph : Type := M.t (S.t). 

Definition node : Type := O.t * option nat * option nat.

Inductive tree : Type :=
  | t_node: node -> list (tree) -> tree.

(*Maybe make more efficient: the important part is the type, add with *)
Fixpoint add_child (parent: O.t) (child: O.t) (t: tree) : tree :=
  match t with
  |t_node (vertex, a, b ) children => if O.eq_dec vertex parent then t_node (vertex, a, b)
    (t_node (child, None, None) [] :: children) else 
    t_node (vertex, a, b) (fold_right (fun x t => (add_child parent child x) :: t) nil children)
  end. 

(*discover a vertex that is in the graph already*)
Fixpoint discover_vertex (vertex: O.t) (t: tree) (time: nat) : tree :=
  match t with
  | t_node (v, a, b) children => if O.eq_dec vertex v then t_node (v, Some time, b) children else
    t_node (v, a, b) (fold_right (fun x t => (discover_vertex vertex x time) :: t) nil children)
  end.

Fixpoint finish_vertex (vertex : O.t) (t: tree) (time : nat) : tree :=
  match t with
  | t_node (v, a, b) children => if O.eq_dec vertex v then t_node (v, a, Some time) children else
    t_node (v, a, b) (fold_right (fun x t => (discover_vertex vertex x time) :: t) nil children)
  end.

Definition contains (v: O.t) (l: list (O.t)) :=
  fold_right (fun x t =>  if O.eq_dec v x then true else t) false l.

Print fold_left. 
Print length.
(*
Axiom l_l : (list O.t) -> nat.

Require Import FunInd.
Require Import Recdef.

Program Fixpoint dfs_visit (v: O.t) (g: graph) (t: tree) (white: list O.t) (time : nat) {length white} :
  tree * list O.t * nat :=
  match white with
  | nil => (t , white , time)
  | v :: new_white =>
  let new_tree := discover_vertex v t time in
  (*let new_white := S.remove v white in*)
  match M.find v g with
  |None => (*impossible*) (t, new_white, time)
  | Some s =>
    let y := fold_left (fun (tl: tree * list (O.t) * nat) x => if contains x white then
    match tl with
    | (t1, w1, time1) => dfs_visit x g t1 w1 time1
    end else tl) (S.elements s) (new_tree , new_white , (time + 1)) in
    match y with
    | (t2, w2, time2) => 
    ((finish_vertex v t2 time2), w2, (time2 + 1))
    end
  end
  end.
Next Obligation.
apply nat.
Defined.
Next Obligation.
unfold dfs_visit_obligation_1. apply n.



Fixpoint dfs_visit (v: O.t) (g: graph) (t: tree) (white: list (O.t)) (time : nat) {struct white}:
  tree * list O.t * nat :=
  match white with
  | nil => (t , white , time)
  | v :: new_white =>
  let new_tree := discover_vertex v t time in
  (*let new_white := S.remove v white in*)
  match M.find v g with
  |None => (*impossible*) (t, new_white, time)
  | Some s =>
    let x := fold_left (fun (tl: tree * list (O.t) * nat) x => if contains x white then
    match tl with
    | (t1, w1, time1) => dfs_visit x g t1 w1 time1
    end else tl) (S.elements s) (new_tree , new_white , (time + 1)) in
    match x with
    | (t2, w2, time2) => 
    ((finish_vertex v t2 time2), w2, (time2 + 1))
    end
  end
  end.

Fixpoint dfs_visit (v: O.t) (g: graph) (t: tree) (white: S.t) (time : nat) (n : nat) :
  tree * S.t * nat :=
  if (n =? 0) then (t, white, time) else
  let new_tree := discover_vertex v t time in
  let new_white := S.remove v white in
  match M.find v g with
  |None => (*impossible*) (t, white, time)
  | Some s =>
    let x := fold_left (fun (tl: tree * S.t * nat) x => if S.mem x white then
    match tl with
    | (t1, w1, time1, n1) => dfs_visit x g t1 w1 time1
    end else tl) (S.elements s) (new_tree , new_white , (time + 1), n1) in
    match x with
    | (t2, w2, time2) => 
    ((finish_vertex v t2 time2), w2, (time2 + 1))
    end
  end.

 dfs_visit )

Fixpoint 
*)
Definition times : Type := M.t nat.

Definition stack : Type := list (O.t * option O.t).

Definition add_to_stack (vertex: O.t) (g: graph) (remaining: S.t) : stack :=
  match M.find vertex g with
  |None => nil
  |Some s => fold_right (fun v t => if S.mem v remaining then (v, Some vertex) :: t else t) nil (S.elements s)
  end.

Fixpoint pop_off_stack (s: stack) (remaining: S.t) : stack :=
  match s with
  | nil => nil
  | (v,p) :: t => if (negb (S.mem v remaining)) then pop_off_stack t remaining
                  else s
  end.

Lemma top_not_finished:
  forall s remaining x y t,
    ((x, y):: t) = pop_off_stack s remaining ->
    S.mem x remaining = true.
Proof.
  intros. induction s.
  - simpl in H. inversion H.
  - simpl in H. destruct a. destruct (S.mem t0 remaining) eqn : ?.
    + simpl in H. inversion H; subst. assumption.
    + simpl in H. apply IHs. apply H.
Qed.

Require Import Omega.

(*Changed to have 2 remaining sets - those that remain to be started and those that
  remain to be finished. This helps the termination argument, since in each step we either
  start or finish a vertex*)

Program Fixpoint dfs_cc
   (g: graph)(s : stack)(time : nat)(d_times: times)(f_times : times) (remain_start : S.t)
  (remain_finish: S.t)(t: graph) {measure (S.cardinal remain_start + S.cardinal remain_finish)}
   : graph * times * times * nat:=
  match S.min_elt remain_start with
  | None => (t, d_times, f_times, time)
  | Some min => let s_new := pop_off_stack s remain_finish in
      match s_new with
       | nil =>   let new_remaining := S.remove min remain_start in
                  let new_d_times := M.add min time d_times in
                  let new_stack := (add_to_stack min g remain_finish) ++ [(min, None)] in
                        dfs_cc g new_stack (time + 1) new_d_times f_times new_remaining remain_finish t
       | (y, z) :: tl => if bool_dec ( S.mem y remain_start) true then
                       ( let new_remaining := S.remove y remain_start in
                        let new_d_times := M.add y time d_times in
                        let new_stack := (add_to_stack y g remain_finish) ++ s_new in
                        dfs_cc g new_stack (time + 1) new_d_times f_times new_remaining remain_finish t)
                        
                        (*Because of pop_off_stack, if we are in this case, we know that y should
                          be finished*)
                        else let new_f_times := M.add y time f_times in
                             let new_t :=
                             match z with
                              |Some p => match M.find p t with
                                          |None => (*impossible because of DFS*) M.add y S.empty t
                                          | Some s => M.add y S.empty (M.add p (S.add y s) t)
                                          end
                              | None => M.add y S.empty t
                              end in 
                              let new_remaining := S.remove y remain_finish in
                          dfs_cc g tl (time + 1) d_times new_f_times remain_start new_remaining new_t
        end
  end.
Next Obligation.
  symmetry in Heq_anonymous. apply S.min_elt_1 in Heq_anonymous.
  apply P2.remove_cardinal_1 in Heq_anonymous. rewrite <- Heq_anonymous. omega.
Defined.
Next Obligation.
  apply S.mem_2 in H.
  apply P2.remove_cardinal_1 in H. rewrite <- H. omega.
Defined.
Next Obligation.
  apply top_not_finished in Heq_s_new. apply S.mem_2 in Heq_s_new.
  apply P2.remove_cardinal_1 in Heq_s_new. rewrite <- Heq_s_new. omega.
Defined.

Definition set_of_graph (g: graph) : S.t :=
  P2.of_list (fold_right (fun (x: O.t * S.t) t => let (a,b) := x in a :: t) nil (P.to_list g)).

Definition dfs (g: graph) : graph * times * times :=
  match (dfs_cc g nil 0 (M.empty nat) (M.empty nat) (set_of_graph g) (set_of_graph g)(M.empty S.t)) with
  | (t, start, finish, _) => (t, start, finish)
  end.


Definition state : Type := graph * graph * times * times * nat * S.t * S.t * stack.
Print add_to_stack.  

Inductive dfs_step: state -> state -> Prop :=
  | dfs_discover : forall g t f_times d_times time remain_d remain_f x y tl,
    S.mem x remain_d = true ->
    dfs_step (g, t, f_times, d_times, time, remain_d, remain_f, (x, y) :: tl)
    (g, t, f_times, (M.add x time d_times), (time + 1), (S.remove x remain_d), 
    remain_f, (add_to_stack x g remain_d) ++  ((x, y) :: tl))
  | dfs_finish_root : forall g t f_times d_times time remain_d remain_f x tl,
    S.mem x remain_d = false ->
    S.mem x remain_f = true ->
    dfs_step (g, t, f_times, d_times, time, remain_d, remain_f, (x,None) :: tl)
    (g, (M.add x S.empty t), (M.add x time f_times), d_times, (time + 1), remain_d, (S.remove x remain_f), tl)
  | dfs_finish_internal: forall g t f_times d_times time remain_d remain_f x y tl s,
    S.mem x remain_d = false ->
    S.mem x remain_f = true ->
    M.find y t = Some s ->
    dfs_step (g, t, f_times, d_times, time, remain_d, remain_f, (x,Some y) :: tl)
    (g, (M.add x S.empty (M.add y (S.add x s) t)), 
    (M.add x time f_times), d_times, (time + 1), remain_d, (S.remove x remain_f), tl)
  (*| dfs_done_already: forall g t f_times d_times time remain_d remain_f x y tl,
    S.mem x remain_d = false ->
    S.mem x remain_f = false ->
    dfs_step (g, t, f_times, d_times, time, remain_d, remain_f, (x,y) :: tl)
    (g, t, f_times, d_times, time, remain_d, remain_f, tl)*)
  | dfs_new_cc: forall g t f_times d_times time remain_d remain_f min,
      S.min_elt remain_d = Some min ->
     dfs_step (g, t, f_times, d_times, time, remain_d, remain_f, nil)
     (g, t, f_times, d_times, time, remain_d, remain_f, [(min, None)]).

Definition done (s: state) : bool :=
  match s with
  | (_, _, _, _, _, start, finish, _) => S.is_empty start && S.is_empty finish
  end.

(*
Definition eq_state (s1 s2 : state) :=
  match s1 with
  | ()*)


 
(*
OLD VERSION WITH EXTRA DFS STEP
Lemma dfs_step_deterministic : forall s1 s2 s,
  dfs_step s s1 -> dfs_step s s2 -> s1 = s2.
Proof.
  intros.
  generalize dependent s2. induction H; intros.
  - inversion H0; subst.
    + reflexivity.
    + rewrite H12 in H. inversion H.
    + rewrite H12 in H. inversion H.
    + rewrite H12 in H. inversion H.
  - inversion H1; subst.
    + rewrite H13 in H. inversion H.
    + reflexivity.
    + rewrite H14 in H0. inversion H0.
  - inversion H2; subst.
    + rewrite H14 in H. inversion H.
    + rewrite H16 in H1. inversion H1; subst; reflexivity.
    + rewrite H15 in H0. inversion H0.
  - inversion H1; subst.
    + rewrite H13 in H. inversion H.
    + rewrite H14 in H0. inversion H0.
    + rewrite H14 in H0. inversion H0.
    + reflexivity.
  - inversion H0; subst. rewrite H9 in H. inversion H; subst; reflexivity.
Qed.*)

Lemma dfs_step_deterministic : forall s1 s2 s,
  dfs_step s s1 -> dfs_step s s2 -> s1 = s2.
Proof.
  intros.
  generalize dependent s2. induction H; intros.
  - inversion H0; subst.
    + reflexivity.
    + rewrite H12 in H. inversion H.
    + rewrite H12 in H. inversion H.
  - inversion H1; subst.
    + rewrite H13 in H. inversion H.
    + reflexivity.
  - inversion H2; subst.
    + rewrite H14 in H. inversion H.
    + rewrite H16 in H1. inversion H1; subst; reflexivity.
  - inversion H0; subst. rewrite H9 in H. inversion H; subst; reflexivity.
Qed.

Definition time_of_state (s : state) : nat :=
  match s with
  | (_, _, _, _, n, _, _, _) => n
  end.

Definition remain_d_of_state (s: state) : S.t :=
  match s with
  | (_, _, _, _, _, r, _, _) => r
  end.

Definition remain_f_of_state (s: state) : S.t :=
  match s with
  | (_, _, _, _, _, _, f, _) => f
  end.

Definition d_times_of_state (s: state) :=
  match s with
  | (_, _, d, _, _, _, _, _) => d
  end.

Definition f_times_of_state (s : state) :=
  match s with
  | (_, _, _, f, _, _, _, _) => f
  end.

Definition stack_of_state (s: state) :=
  match s with
  | (_, _, _, _, _, _, _, s') => s'
  end.

(*A few test lemmas to see if I can actually prove things*)
Lemma dfs_time_geq: forall s1 s2,
  dfs_step s1 s2 -> time_of_state s1 <= time_of_state s2.
Proof.
  intros.
  inversion H; simpl; omega.
Qed.

Lemma dfs_time_incr_when_vertex_info_changes : forall s1 s2,
  dfs_step s1 s2 ->
  remain_d_of_state s1 <> remain_d_of_state s2 \/
  remain_f_of_state s1 <> remain_f_of_state s2 \/
  d_times_of_state s1 <> d_times_of_state s2 \/
  f_times_of_state s1 <> f_times_of_state s2 ->
  time_of_state s1 + 1 = time_of_state s2.
Proof.
  intros. inversion H; simpl; try (reflexivity); subst; simpl in *;repeat(destruct H0; try(contradiction)).
Qed.


(*From SmallSetp.v*)
Definition relation (X : Type) := X -> X -> Prop.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Theorem multi_R : forall (X : Type) (R : relation X) (x y : X),
    R x y -> (multi R) x y.
Proof.
  intros X R x y H.
  apply multi_step with y. apply H. apply multi_refl.
Qed.

Theorem multi_trans :
  forall (X : Type) (R : relation X) (x y z : X),
      multi R x y ->
      multi R y z ->
      multi R x z.
Proof.
  intros X R x y z G H.
  induction G.
    - (* multi_refl *) assumption.
    - (* multi_step *)
      apply multi_step with y. assumption.
      apply IHG. assumption.
Qed.

(*Now we want to define what dfs is beyond a single step*)

(*The multi step relation*)
Definition dfs_multi (s1 s2 : state):= multi (dfs_step) s1 s2.

(*The valid start state of DFS (for our purposes). We start with a graph, an empty
  map of start and finish times, time=0, all vertices remaining to start and finish, and an empty stack*)
Definition start_state (g: graph) : state :=
  (g, M.empty S.t, M.empty nat, M.empty nat, 0, (set_of_graph g), (set_of_graph g), nil).

(*A state for a given graph is valid if is is the start state or can be reached in 1 step from
  another valid state. This allows us to work only with correct dfs states in proofs (not, for example,
  in the case where the vertices that must be finished is empty but there are vertices to discover*)
Inductive valid_dfs_state: state -> graph -> Prop :=
  | start: forall g, valid_dfs_state (start_state g) g
  | step: forall s1 s2 g,
    valid_dfs_state s1 g ->
    dfs_step s1 s2 ->
    valid_dfs_state s2 g.

(*We can use the above multistep relation as well*)

Lemma multistep_preserves_valid: forall s s' g,
  valid_dfs_state s g ->
  dfs_multi s s' ->
  valid_dfs_state s' g.
Proof.
  intros. induction H0.
  - assumption.
  - apply IHmulti. eapply step. apply H. apply H0.
Qed.

Lemma valid_begins_with_start: forall s g,
  valid_dfs_state s g ->
  dfs_multi (start_state g) s.
Proof.
  intros. induction H.
  - constructor.
  - eapply multi_trans. apply IHvalid_dfs_state. eapply multi_step. apply H0. apply multi_refl.
Qed.

(*This uses the above 2 helper lemmas to prove that the two definitions of valid dfs states are equivalent. 
(I think) the inductive definition will be much more useful in proofs*)
Lemma valid_dfs_multistep: forall s g,
  dfs_multi (start_state g) s <-> valid_dfs_state s g.
Proof.
  intros. split; intros.
  - eapply multistep_preserves_valid. apply start. assumption.
  - apply valid_begins_with_start. assumption.
Qed. 


(*If a vertex still has to be discovered, then it still has to be finished*)
Lemma vertex_in_finish_if_not_discovered: forall s g,
  valid_dfs_state s g ->
  (forall x, 
  S.mem x (remain_d_of_state s) = true ->
  S.mem x (remain_f_of_state s) = true).
Proof.
  intros. induction H.
  - unfold start_state in *; simpl in *. assumption.
  - inversion H1; subst; simpl in *.
    + apply IHvalid_dfs_state. Search S.mem. apply S.mem_1. eapply S.remove_3.
      apply S.mem_2. apply H0.
    + assert (x <> x0). intro. subst. rewrite H2 in H0. inversion H0. apply S.mem_1. apply S.remove_2.
      intro. subst. contradiction. apply S.mem_2. apply IHvalid_dfs_state. apply H0.
    + assert (x <> x0). intro. subst. rewrite H2 in H0. inversion H0. apply S.mem_1. apply S.remove_2.
      intro. subst. contradiction. apply S.mem_2. apply IHvalid_dfs_state. apply H0.
    + apply IHvalid_dfs_state. assumption.
Qed.

(*A non empty set has at least one element*)
Lemma non_empty_set_has_elements: forall (s: S.t),
  (S.is_empty s) = false <-> exists x, S.In x s.
Proof.
  intros. split; intros.
  - assert (~S.Empty s). intro. apply S.is_empty_1 in H0. rewrite H0 in H. inversion H.
    assert (S.cardinal s <> 0). intro. apply P2.cardinal_inv_1 in H1. contradiction.
    apply P2.cardinal_inv_2b in H1. destruct H1. exists x. apply i.
  - destruct H. destruct (S.is_empty s) eqn : ?.
    + apply S.is_empty_2 in Heqb. apply P2.empty_is_empty_1 in Heqb.
      setoid_rewrite Heqb in H. apply P2.Dec.F.empty_iff in H. destruct H.
    + reflexivity.
Qed. 

(*When all vertices are finished, all vertices have been discovered*)
Lemma finish_discover_before_finishing : forall (s: state) g,
  valid_dfs_state s g ->
  S.is_empty (remain_f_of_state s) = true ->
  S.is_empty (remain_d_of_state s) = true.
Proof.
  intros. destruct (S.is_empty (remain_d_of_state s)) eqn : ?.
  + reflexivity.
  + rewrite non_empty_set_has_elements in Heqb. destruct Heqb.
    apply S.mem_1 in H1. eapply vertex_in_finish_if_not_discovered in H1.
    apply S.mem_2 in H1. apply S.is_empty_2 in H0. apply P2.empty_is_empty_1 in H0.
    setoid_rewrite H0 in H1. apply P2.Dec.F.empty_iff in H1. destruct H1. apply H.
Qed.

(*By above, the ending condition of the finishing set being empty is sufficient*)
Definition done' (s: state) : bool :=
  S.is_empty (remain_f_of_state s).

Lemma done_done': forall s g,
  valid_dfs_state s g ->
  done s = done' s.
Proof.
  intros. unfold done. unfold done'. remember s as s'. destruct s. repeat(destruct p).
  simpl. assert (t = remain_f_of_state s'). subst; simpl; reflexivity. rewrite Heqs'.
  simpl. assert (t0 = remain_d_of_state s'). subst; simpl; reflexivity.
  destruct (S.is_empty t) eqn : ?.
  - apply finish_discover_before_finishing in H. rewrite <- H1 in H. rewrite H. reflexivity.
    rewrite <- H0. apply Heqb.
  - destruct (S.is_empty t0); reflexivity.
Qed. 

(*Proving progress: helper lemmas*)

(*First, If a valid state is done, it cannot step. This shows that our choice of the done function
  was a reasonable one*)
Lemma done_cannot_step: forall s g,
  valid_dfs_state s g ->
  done' s = true ->
  (forall s', ~dfs_step s s').
Proof.
  intros. intro. unfold done' in H0. inversion H1; subst; simpl in *.
  - remember ((g0, t, f_times, d_times, time, remain_d, remain_f, (x, y) :: tl)) as s.
    assert (remain_f_of_state s = remain_f). subst; simpl; reflexivity.
    rewrite <- H3 in H0. apply (finish_discover_before_finishing s g H) in H0.
    apply S.is_empty_2 in H0. apply P2.empty_is_empty_1 in H0.
    assert (remain_d_of_state s = remain_d). subst; simpl; reflexivity. 
    rewrite H4 in H0. setoid_rewrite H0 in H2. apply S.mem_2 in H2. apply P2.FM.empty_iff in H2.
    apply H2.
  - apply S.mem_2 in H3. apply S.is_empty_2 in H0. apply P2.empty_is_empty_1 in H0.
    setoid_rewrite H0 in H3. apply P2.FM.empty_iff in H3. apply H3.
  - apply S.mem_2 in H3. apply S.is_empty_2 in H0. apply P2.empty_is_empty_1 in H0.
    setoid_rewrite H0 in H3. apply P2.FM.empty_iff in H3. apply H3.
  - assert (S.is_empty remain_d = false). destruct (S.is_empty remain_d) eqn : ?.
    apply S.is_empty_2 in Heqb. apply S.min_elt_1 in H2. apply P2.empty_is_empty_1 in Heqb.
    setoid_rewrite Heqb in H2. apply P2.FM.empty_iff in H2. destruct H2. reflexivity.
    remember (g0, t, f_times, d_times, time, remain_d, remain_f, []) as s.
    assert (remain_f_of_state  s = remain_f). subst; simpl; reflexivity.
    assert (remain_d_of_state s = remain_d). subst; reflexivity.
    rewrite <- H4 in H0. eapply finish_discover_before_finishing in H0.
    rewrite H5 in H0. rewrite H3 in H0. inversion H0. apply H.
Qed.

Lemma only_add_undiscovered_vertices: forall v s r v' p,
  In (v', p) (add_to_stack v s r) -> S.In v' r.
Proof.
  intros. unfold add_to_stack in H. destruct (M.find v s) eqn : ?.
  - induction (S.elements t); simpl in H. 
    + destruct H.
    + destruct (S.mem a r) eqn : ?.
      * simpl in H. destruct H.
        -- inversion H; subst. apply S.mem_2. apply Heqb.
        -- apply IHl. apply H.
      * apply IHl. apply H.
  - destruct H.
Qed.


Lemma only_correct_vertex_on_stack: forall s g v p,
  valid_dfs_state s g ->
  In (v,p) (stack_of_state s) ->
  S.In v (remain_d_of_state s) \/ S.In v (remain_f_of_state s).
Proof.
  intros. induction H; subst; simpl in *.
  - destruct H0.
  - inversion H1; subst; simpl in *.
    + apply in_app_or in H0. destruct H0.
      * 
(*I think that I need a lemma saying that we only add a vertex to the stack once it has been discovered*)
(*Will probably also need one that once vertex is discovered, it stays discovered*)
apply only_add_undiscovered_vertices in H0. 

 unfold add_to_stack in H0.


(*If the stack is non_empty, we can progress. Note that this is not true if we add the additional condition.
Right now i should be good, because each vertex should only be added to the stack once
WAIT this is not true no wait yes it is because we only add neighbor if it is remaining to be discovered

IDEA: prove: for each state, if vertex is not in remaining, then it is discover/finish times and in resulting graph
then can prove that we see all of the vertices and then start stuff about ordering*)


Lemma empty_stack_when_done: forall s g,
  valid_dfs_state s g ->
  done' s = true ->
  stack_of_state s = [].
Proof.
  intros. inversion H; subst; simpl in *.
  - reflexivity.
  - unfold done' in H0. inversion H2; subst; simpl in *.
    + simpl in *. remember (g0, t, f_times, d_times, time, remain_d, remain_f, (x, y) :: tl) as s.
    assert (remain_d_of_state s = remain_d). subst; reflexivity.
    assert (remain_f_of_state s = remain_f) by (subst; reflexivity).
    rewrite <- H5 in H0. eapply finish_discover_before_finishing in H0. rewrite H4 in H0.
    apply S.is_empty_2 in H0. apply P2.empty_is_empty_1 in H0. setoid_rewrite H0 in H3.
    apply S.mem_2 in H3. apply P2.FM.empty_iff in H3. destruct H3. apply H1.
    + destruct tl eqn : ?.
      * reflexivity.
      * remember (g0, t, f_times, d_times, time, remain_d, remain_f, (x, None) :: p :: l) as s.
        (*Need a lemma saying something like - all elements (or at least the first one) on the stack
          are in at least one of the sets (discovered or finished). Then this case can be proved. Although
          this kind of proves part of stack_implies_progress also*)

(*Overall plan: *)
        assert (dfs_step s (g0, t, f_times, d_times, time, 
  

Lemma stack_implies_progress: forall s g,
  valid_dfs_state s g ->
  stack_of_state s <> [] ->
  (exists s1, dfs_step s s1).
Proof.
  intros. inversion H; subst; simpl in *.
  - contradiction.
  - inversion H2; subst; simpl in *.
    + destruct (add_to_stack x g0 remain_d ++ (x, y) :: tl) eqn : ?.
      * contradiction.
      * destruct p. exists  
    
  
(*What we want to show: If we start with a valid DFS, we can continue or else we are done*)
Lemma dfs_progress: forall s g,
  valid_dfs_state s g ->
  done s = true \/ exists s1, dfs_step s s1.
Proof.
  intros. rewrite (done_done' s g H). inversion H; subst; simpl in *.
  - unfold start_state. unfold done'. simpl. destruct (S.is_empty (set_of_graph g)) eqn : ?.
    + left. reflexivity.
    + right. destruct (S.min_elt (set_of_graph g)) eqn : ?.
      * exists (g, M.empty S.t, M.empty nat, M.empty nat, 0, set_of_graph g, set_of_graph g, [(e, None)]).
        constructor. apply Heqo.
      * apply S.min_elt_3 in Heqo. apply S.is_empty_1 in Heqo. rewrite Heqo in Heqb. inversion Heqb.
  - (*The induction is useless, *) inversion H1; subst; simpl in *.


 unfold state in s. destruct s. repeat(destruct p as [ ]).
  unfold done'. simpl. destruct (S.is_empty t) eqn : ?.
  - simpl. left. reflexivity.
  - 



 Search S.In.


 induction H.
  - unfold start_state in *. simpl in *. assumption.
  - inversion H1.
    + simpl. subst; simpl in *. apply IHvalid_dfs_state in H0. SearchAbout S.is_empty. 
      apply S.is_empty_2 in H0. SearchAbout S.Equal. assert (S.Equal remain_d S.empty).
      SearchAbout S.empty. apply P2.empty_is_empty_1. assumption. setoid_rewrite H3 in H2.
      SearchAbout S.mem. rewrite P2.FM.empty_b in H2. inversion H2.
    + subst; simpl in *.


 unfold valid_dfs_state in H. remember (start_state g) as ss. induction H.
  - unfold start_state in Heqss. rewrite Heqss in *. simpl in *. assumption.
  - 

Lemma dfs_progress: forall s,
  valid_dfs_state ->
  done s = true \/ exists s1, dfs_step s s1.
Proof.
  intros. unfold state in s. destruct s. repeat(destruct p as [ ]).
  unfold done. destruct (S.is_empty t0) eqn : ?.
  - simpl. left. 



(*Well, that was an attempt*)
(*One possible (kind of dumb) way - keep counter tht is the size of both sets and define it with Fixpoint
then I will need to prove that this is the sum of the lengths (which shouldnt be hard*)

Lemma dfs_equiv_general: forall (g g1 g2: graph) start1 start2 finish1 finish2 time1 time2 r_d r_f s,
  dfs_cc g s time1 start1 finish1 r_d r_f g1 = (g2, start2, finish2, time2) <->
  dfs_multi (g, g1, finish1, start1, time1, r_d, r_f, s) (g, g2, finish2, start2, time2, (S.empty), S.empty, nil).
Proof.
  intros. split; intros.
  - generalize dependent r_d. 
    apply (@P2.set_induction (fun se =>
    (dfs_cc g s time1 start1 finish1 se r_f g1 = (g2, start2, finish2, time2) ->
dfs_multi (g, g1, finish1, start1, time1, se, r_f, s) (g, g2, finish2, start2, time2, S.empty, S.empty, [])))).
    + intros. unfold dfs_cc in H0. 


    .  unfold times.
    Check P.map_induction. apply (@P.map_induction nat (fun m => 
    dfs_cc g s time1 m finish1 r_d r_f g1 = (g2, start2, finish2, time2) ->
dfs_multi (g, g1, finish1, m, time1, r_d, r_f, s) (g, g2, finish2, start2, time2, S.empty, S.empty, []))) ; intros.
    + SearchAbout M.Empty.


 unfold dfs_cc in H0. apply  Search existT. unfold dfs_cc_func in H0.
    + 

g : graph) (s : stack) (time : nat) (d_times f_times : times) (remain_start remain_finish : S.t) (t : graph).
(t, d_times, f_times, time, remain_start, remain_finish)
(*This is going to be hard I think*)
Lemma dfs_equiv : forall (g: graph) g1 start finish n,
  dfs g = (g1, start, finish) <->
  dfs_multi (g, (M.empty S.t), (M.empty nat), (M.empty nat), 0, (set_of_graph g), (set_of_graph g), nil)
  (g, g1, start, finish, n, (S.empty), (S.empty), nil).
Proof.
  intros. split; intros.
  - unfold dfs in H. 


Lemma dfs_progress: forall s,
  done s = true \/ exists s1, dfs_step s s1.
Proof.
  intros. destruct s. repeat(destruct p). unfold done.
  
   
  

Lemma parens_1: forall (a b: O.t),
  



Inductive dfs_step: state -> state -> Prop :=
  | dfs_next_component: forall (g: graph) (t: graph) (d_times : map) (f_times: map) (time: nat) (x: nat) tl,
    dfs_step (g, t, d_times, f_times, time, (x :: tl), nil) 
    (g, t, (M.add x time d_times), f_times, time + 1, tl, [(x, None)])
  | dfs
 .

Definition tuple (l : list Type) (base: Type): Type :=
  fold_right prod base l.

Definition state := tuple ([graph; graph; times; times; num; remaining]) stack.

Definition get_start_graph (s: state) : graph :=
  match state with
  | (a, b) => a
  end.

Inductive dfs_step 


Inductive dfs_step: graph -> list (nat * nat) -> nat -> list(nat * nat) -> list (nat * nat) -> list nat -> graph
  -> graph -> list (nat * nat) -> list (nat * nat) -> nat -> Prop :=
| dfs_empty: forall g d_times f_times time t, dfs_step g nil time d_times f-Times nil t.


Fixpoint contains (n : nat) (l : list nat) :=
  match l with
  | nil => false
  | x :: t => (x =? n) || contains n t
  end.

Fixpoint remove (n: nat) (l : list nat) :=
  match l with
  | nil => nil
  | x :: t => if (x =? n) then t else x :: remove n t
  end.

Lemma remove_decr_length: forall

Axiom neighbors: nat -> graph -> list (nat * nat).

Axiom addVertex: nat -> graph -> graph.

Axiom addEdge: nat -> nat -> graph -> graph.


Program Fixpoint dfs (g: graph)(stack: list (nat * nat))(time : nat)(d_times: list (nat * nat))(f_times : list (nat * nat))
  (remaining: list nat)(t: graph) {measure (length remaining)} : graph * list (nat * nat) * list (nat * nat) :=
  match remaining with
  | nil => (t, d_times, f_times)
  | _ =>
    match stack with
    | nil => (t, d_times, f_times)
    | (y, z) :: tl => if contains y remaining then 
                 let new_remaining := remove y remaining in
                 let new_d_times := (y, time) :: d_times in
                 let new_stack := neighbors y g ++ stack in
                 dfs g new_stack (time + 1) new_d_times f_times new_remaining t
                 else 
                 let new_f_times := (y, time) :: f_times in
                 let new_t := addEdge z y (addVertex y t) in
                 dfs g tl (time + 1) d_times new_f_times remaining new_t
    end
  end.
               
