Require Import Graph.
Require Import Tree.
Require Import Coq.FSets.FMapInterface.
Require Import Coq.Lists.List.
Require Import Coq.FSets.FSetInterface.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.FSets.FSetProperties.
Require Import Omega.
Require Import Path.
Require Import Helper.
Require Import Coq.Arith.Wf_nat.

(*In order to perform DFS, we need a lawful Graph (the input), Tree (the output), Set (for keeping
  track of the vertices not yet seen), Map (for storing discover/finish times), and UsualOrderedType
  (for the vertices). Also, we could use different sets for the Graph and Tree instances.*)
Module DFS (O: UsualOrderedType)(M: FMapInterface.Sfun O) (S St: FSetInterface.Sfun O) (G: Graph O S)
            (T: Tree O St S G).

Module P := FMapFacts.WProperties_fun O M.
Module F := P.F.
Module P2 := FSetProperties.WProperties_fun O S.
Module O2 := OrderedTypeFacts O.

(*First, we define the types we will need*)
Definition vertex := O.t.
Definition graph := G.graph.
Definition tree := T.tree.
Definition forest := list tree.
Definition times_map := M.t nat.
(*Each vertex on the stack is pushed along with its parent if it has one*)
Definition stack := list (O.t * (option O.t)).
(*The state of the program at any given iteration: contains the input graph, the current output forest,
  the map of discovery times, the map of finish times, the current timestamp, the set of vertices
  yet to be discovered, the set of vertices yet to be finished, and the stack*)
Definition state : Type := graph * forest * times_map * times_map * nat * S.t * S.t * stack.

(*A preliminary function: add all neighbors of a vertex to a stack unless they have already been
  discovered*)
Definition add_to_stack (vertex: O.t) (g: graph) (remaining: S.t) : stack :=
  match G.neighbors_set g vertex with
    |None => nil
    |Some s => fold_right (fun v t => if S.mem v (S.remove vertex remaining) then (v, Some vertex) :: t else t) nil (S.elements s)
  end.

(** ** The inductive definition **)

(*The inductive definition of DFS. It is simply a relation between two states*)
Inductive dfs_step: state -> state -> Prop :=
  | dfs_discover_root : forall g f f_times d_times time remain_d remain_f x tl,
    S.mem x remain_d = true ->
    dfs_step (g, f, f_times, d_times, time, remain_d, remain_f, (x, None) :: tl)
    (g, (T.singleton x) :: f, f_times, (M.add x (time + 1) d_times), (time + 1), (S.remove x remain_d), 
    remain_f, (add_to_stack x g remain_d) ++  ((x, None) :: tl))
    (*Discover a vertex: add all of its neighbors who have not been discovered to the stack,
      add it to the stack, add it to the discover times with the current time, and remove it from
      remain_d. We also add it to the forest as a new singleton tree*)
  | dfs_discover_child : forall g t f f_times d_times time remain_d remain_f x y tl,
    S.mem x remain_d = true ->
    dfs_step (g, t :: f, f_times, d_times, time, remain_d, remain_f, (x, Some y) :: tl)
    (g, (T.add_child t y x) :: f, f_times, (M.add x (time + 1) d_times), (time + 1), (S.remove x remain_d), 
    remain_f, (add_to_stack x g remain_d) ++  ((x, Some y) :: tl))
    (*The same as the previous except we add the vertex as a child of its parent in the tree*)
  | dfs_finish: forall g f f_times d_times time remain_d remain_f x o tl,
    S.mem x remain_d = false ->
    S.mem x remain_f = true ->
    dfs_step (g, f, f_times, d_times, time, remain_d, remain_f, (x,o) :: tl)
    (g,  f, (M.add x (time + 1) f_times), d_times, (time + 1), remain_d, (S.remove x remain_f), tl)
    (*Finish a vertex by adding it to finish_times whileremoving it from remain_f and the stack*)
  | dfs_done_already: forall g f f_times d_times time remain_d remain_f x y tl s,
    S.mem x remain_d = false ->
    S.mem x remain_f = false ->
    (S.is_empty remain_d && S.is_empty remain_f) = false  ->
    dfs_step (g, f, f_times, d_times, time, remain_d, remain_f, tl) s ->
    dfs_step (g, f, f_times, d_times, time, remain_d, remain_f, (x,y) :: tl) s
    (*If we see a vertex that is already finished, keep stepping until we discover/finish a vertex*)
  | dfs_new_cc: forall g f f_times d_times time remain_d remain_f min s,
      S.min_elt remain_d = Some min ->
     dfs_step (g, f, f_times, d_times, time, remain_d, remain_f, (min, None) :: nil) s ->
     dfs_step (g, f, f_times, d_times, time, remain_d, remain_f, nil) s
    (*If the stack is empty but we still have more vertices to discover, get the minimum element
      of the remaining vertices and start again*).