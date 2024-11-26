Require Import List ssreflect.
Import ListNotations.
Require Import PeanoNat.

Inductive term : Type :=
  (* tm n x [tk; ...; t1] is the term
     \x1...\xn. x t1 ... tk
     where x is the de Bruijn index of a bound variable.
     If the variable is out of bounds, then it is a constant *)
  | tm : nat -> nat -> list term -> term.

(* a path is a list of indices to traverse a term *)


(* Positions in a tree or term are lists of natural numbers. *)
Definition positions := list nat.


(* compute the subterm of [t] at position [p] *)
Fixpoint subterm (t : term) (p : positions) : option term :=
  match t, p with
  | tm n x ts, [] => Some (tm n x ts)
  | tm n x ts, i :: p =>
    match nth_error ts i with
    | Some ti => subterm ti p
    | None => None
    end
  end.


(* as above, but gives also the limit for variables that were bound

   QUESTION: maybe we should use only this definition?
 *)
Fixpoint subterm_bound (t : term) (p : positions) (bound:nat) : option (term*nat) :=
  match t, p with
  | tm n x ts, [] => Some (tm n x ts, bound + n)
  | tm n x ts, i :: p =>
    match nth_error ts i with
    | Some ti => subterm_bound ti p (bound+n)
    | None => None
    end
  end.


Inductive rose_tree (A : Type) : Type :=
| node : A -> list (rose_tree A) -> rose_tree A.

Arguments node {A}.

Fixpoint get_depth (A : Type) (tr: rose_tree A) :=
  match tr with
  | node v children => fold_left (fun acc el => let nacc := (get_depth A el) in
                                                match (acc ?= nacc)  with
                                                | Eq => acc
                                                | Lt => nacc
                                                | Gt => acc
                                                end) children 0%nat
  end.

Arguments get_depth {A}.



(* 
   Intervals are used to designate a segment of roseta tree
   π[i, j] is the sequence of positions πi, ..., πj.

 *)
Inductive intervals : Type :=
    | intvl : positions -> positions -> intervals.

Notation "'pi[' a ',' b ']'" := (intvl a b) (at level 2).

Check (pi[[1; 2], [3; 4]]).



Inductive lookups : Type :=
  | lk : list ((nat * list nat) * lookups) -> lookups.

Definition lookup_contents := list ((nat * list nat) * lookups).


(* Arenas of our game are lists of terms [t, t1, ..., tk] s.t. 
    t t1...tk reduces to rhs of the target equation. *)
Definition arenas  := list term.

(* Arena position picks a term t from an arena and then it is 
   a position in t. *)
Definition arena_pos  := (nat * positions)%type.

Definition game_trees := rose_tree (arena_pos * lookup_contents).

(* Returns the list of nodes in the game tree tr through which the
   interval intv passes.   *)
Fixpoint passthrough_nodes (tr:game_trees) (intv:intervals) (fuel:nat) :=
  match fuel with
  | 0 => None
  | S fuel' =>
      match tr with
      | node (pos, theta) children  =>
          match intv with
          | pi[[], []] => Some [pos]
          | pi[[], hd :: tl] =>
              match nth_error children hd with
              | Some tr' => match (passthrough_nodes tr' pi[[], tl]) fuel' with
                            | Some rest => Some (pos :: rest)
                            | None => None
                            end
              | None => None
              end
          | pi[hd :: tl, rest] => match nth_error children hd with
                                   | Some tr' => passthrough_nodes tr' pi[tl, rest] fuel'
                                   | None => None
                                   end
          end
      end
  end.

(* 
   Intervals [intv1] and [intv2] correspond when they pass through
   the same sequence of nodes in the game tree tr.

   QUESTION: maybe this should be modelled by an inductive predicate?
 *)
Definition corresponding (tr:game_trees) (intv1:intervals) (intv2:intervals) :=
  let dpth := (get_depth tr)+1 in
  let nds1 := passthrough_nodes tr intv1 dpth in
  let nds2 := passthrough_nodes tr intv2 dpth in
  nds1 = nds2.


Section Arenas.

Variable TS: arenas.

(* Gives the porion of the arena [TS] under the position [ap],
   provided that [ap] is an address in the arena. *)
Definition get_subarena ap :=
      let '(i, p) := ap in
      match nth_error TS i with
      | Some t => subterm t p 
      | None => None
      end.


(* The list with [n] elements [v]. *)
Fixpoint const_list (n:nat) (v:nat) :=
  match n with
  | 0 => []
  | S n' => v :: const_list n' v
  end.


Fixpoint level_helper (t:term) (ap:positions) (lvls:list nat) (last:nat) :=
  match t with
  | tm n x args =>
      let nlvls := lvls ++ (const_list n (last+1)) in
      match ap with
      | [] => Some (nth x nlvls 0) (* level of constants is 0 *)
      | hd :: tl => match nth_error args hd with
                    | Some arg => level_helper t tl nlvls (nth x lvls 0) (* in this rendition level of constant is 0 *)
                    | None => None
                    end
      end
  end.

(*

Stirling:

Assume an interpolation tree @tw1 . . . wk. A variable node in this
tree is level 1 if it is bound by the root of t or wq for some q. A
variable node is level j + 1 if it is bound by a successor node of a
level j node.

Here:

Level of a position ap in the interpolation tree TS (aka arena) is 0
is for constants. A variable node is level 1 if it is bound by the
root of any term of the arena TS or by a node with constant in any of
the terms. A variable node is level j + 1 if it is bound by a
successor node of a level j node. 

 *)
Definition level (TS:arenas) (ap:arena_pos) :=
  let (i, pos) := ap in
  match nth_error TS i with
  | Some t => level_helper t pos [] 0
  | None => None
  end.


(* Extend the arena position ap at its end with extension. *)
Definition extend_ap (ap:arena_pos) (extension:positions) :=
  let '(i, p) := ap in
   (i, p ++ extension).



(* Given the range of so far [bound] variables and
   a list of [seen] variables up to the current position
   tell if the given term on the given position has an
   embedded occurrence *)
Inductive embedded_seen  (bound:nat) (seen: list nat) :
  term ->  positions -> Prop :=
| embseen_null n x args:
  In x seen ->
  embedded_seen bound seen (tm n x args) []
| embseen_step n x args nseen nbound t hd tl:
  nseen = x :: (map (fun m => m + n)  seen) ->
  nbound = n + bound ->
  nth_error args hd = Some t ->
  embedded_seen nbound nseen t tl ->
  embedded_seen bound seen (tm n x args) (hd::tl).

                

(* 

Stirling:

Assume n0 ↓ n, n0 ↓ m and n, m are distinct nodes of an interpolation
tree labelled with the same variable. Node m is embedded if m occurs
below n in the tree.

Here:

unpack a term [t] from arena [TS] and check if the
variable at the position [p] has been seen on the path
to the variable. The latter is checked by embedded_seen.

*)
               
Inductive embedded (TS : arenas) (ap:arena_pos) :=
  | embedded_unpack i p t:
    ap = (i, p) ->
    nth_error TS i = Some t ->
    embedded_seen 0 [] t p ->
    embedded TS ap.

(* Given an indication of which variables are [bound] in the given
   term checks if the variable at the given position is a descendant
   under binding of the given variable *)
Inductive descendant_of (bound : nat) : term -> nat -> positions  -> Prop :=
| descendant_term_take x n p m y args m' y' args' z:
  nth_error args n = Some (tm m' y' args') ->
  z < m' ->
  y = x + m -> 
  descendant_of (bound+m) (tm m' y' args') z p  ->
  descendant_of bound (tm m y args) x (n::p) 
| descendant_term_omit x n p m y args t':
  nth_error args n = Some t' ->
  descendant_of (bound+m) t' (x+m) p ->
  descendant_of bound (tm m y args) x (n::p) 
| descendant_term_nil x m y args:
  y = x + m -> 
  descendant_of bound (tm m y args) x [] 
| descendant_term_take_nil x n m y args m' y' args':
  nth_error args n = Some (tm m' y' args') ->
  y' < m' ->
  y = x + m -> 
  descendant_of bound (tm m y args) x [n].

  
(*
Stirling:

Assume n, m are variable nodes of an interpolation tree.  1. n is a
descendant under binding of m (m is an ancestor under binding of n) if
m = n or m0 is a successor of m, m0 ↓ n0 and n is a descendant under
binding of n0 .  2. n and m belong to the same family if they have a
common ancestor under binding.  3. n is end if it has no descendants
under binding except itself.

here:

unpack ap and ap', check that ap is a prefix of ap, i.e. ap' = ap ++
p'' check that the variable in the root of the subterm tp at ap is a
descendant under binging of the variable at p'' respecting the bound
variables.

*)
Inductive descendant_under_binding (ap:arena_pos) (ap':arena_pos) :=
  | descendant_unpack i p i' p' p'' t n x args bound:
    ap = (i, p) ->
    ap' = (i', p') ->
    i = i' ->
    nth_error TS i = Some t ->
    subterm_bound t p 0 = Some (tm n x args, bound) ->
    p' = p ++ p'' ->
    descendant_of bound t x p'' ->
    descendant_under_binding ap ap'.

(*
(* 
  (x, [t1; ...; tk], l, t) is the state
  where x is the de Bruijn index of head symbol
  t1; ...; tk are the arguments of the head symbol
  l is the lookup table
  t is the current right-hand side term
*)
Notation state := (nat * list term * list (term * lookup) * term)%type.
*)
Definition add_lk (ap:arena_pos) (theta : lookup_contents) (j : nat) :=
  let '(i, p) := ap in
    ((i, p ++ [j]), lk theta).

Arguments add_lk /.

End Arenas.

(* for now / for simplicity let us consider rhs which does not contain abstraction
  e.g. f (\x.x) is not allowed as right-hand side
*)

(*
  solved TS i p theta game_tree r
    TS = [t, t1, ..., tk] where t is the solution and t1, ..., tk are arguments
         TS is the game arena
    ap = (i, p) is an arena position in TS
    theta is the lookup table for free variables
    game_tree are positions ((i', p'), theta') in the game
    r is the rhs term (no abstractions)
  means that the game starting at position ((i, p), theta) with the rhs r is solved
*)

Inductive solved (TS : arenas) (ap : arena_pos) (theta : lookup_contents) :
  rose_tree (arena_pos * lookup_contents) ->
  rose_tree nat -> Prop :=
  
    | solved_var n x args nap theta' gt r:
      get_subarena TS ap = Some (tm n x args) ->
      nth_error theta x = Some (nap, lk theta') ->
      solved TS nap ((map (add_lk ap theta) (seq 0 (length args))) ++ theta') gt r ->
      solved TS ap theta (node (ap, theta) [gt]) r

    | solved_const gs n x ts rs:
      get_subarena TS ap = Some (tm n (x + length theta) ts) ->
      length ts = length rs ->
      Forall2 (fun _ t => match t with tm nt _ _ => nt = 0 end) gs ts ->
      (forall g j r, In (g, (j, r)) (combine gs (combine (seq 0 (length rs)) rs)) ->
        solved TS (extend_ap ap [j]) theta g r) ->
      solved TS ap theta (node (ap, theta) gs) (node x rs).

(* t ts = r *)
Definition solved_start g t (ts : list term) (r : rose_tree nat) :=
  match t with
  | tm n x us =>
    length ts = n /\
    solved (t :: ts) (0, []) (map (fun j => ((S j, []), lk [])) (rev (seq 0 (length ts)))) g r
  end.

(* parent_binder_var TODO

Assume that π ∈ G(t, E) and nj is a variable node. The position πi is
the parent of the later position πj if ni ↓ nj and θi (ni ) = θj (ni ). We also say that πj is
a child of πi .

 *)
Inductive parent_binder_var (gt: rose_tree (arena_pos * lookup_contents)) (pi1 : list nat) (pi2 : list nat) :=
  parent_at_binder : parent_binder_var gt pi1 pi2.
(*
| parent_at_binder ap theta further: (* TODO *)
  pi1 = [] ->
  gt = (node (ap, theta) further) ->
  parent_binder_var gt pi1 pi2
| parent_follow
    (further: list (rose_tree (arena_pos * lookup_contents))) (i:nat) pi11 nnode (j:nat) pi21 ap theta :
  pi1 = i :: pi11 ->
  pi2 = j :: pi21 ->
  gt = (node (ap, theta) further) ->
  nth_error further i = Some nnode ->
  parent_binder_var nnode pi11 pi21 ->
  parent_binder_var gt pi1 pi2.
*)


(* parent_var_binder TODO

Assume π ∈ G(t, E) and nj is a lambda node. We define πi the parent
of πj by cases on the label at the node n directly above nj in the interpolation tree:
@: i = 1;
f : i = j − 1;
z: i is such that πi+1 is the parent of πj−1 (according to Definition 21).

 *)

(* parent TODO *)

(* chain TODO

Assume π ∈ G(t, E) and πj is a lambda node. The sequence πj1 , . . . , πj2p
is a chain (of parent child positions) for πj if
1. πj = πj2p ,
2. for 1 ≤ m ≤ p, πj2m−1 is the parent of πj2m ,
3. for 1 ≤ m < p, πj2m is the position preceding πj2m+1 .

 *)


(* complementary intervals TODO
   Czy to ma być w kontekście areny?
 *)

(* recurrence property

Assume π ∈ G(t, E). The chain πj1 , . . . , πj2p for πj has the recurrence
property if for each i : 1 ≤ i ≤ p, if nj2i−1 is a variable node then there is a j < j2i−1 and
a k such that π[j + 1, j + k] and π[m + 1, m + k] are complementary where m = j2i−1
and j2i = m + k + 1.

 *)

(* transformation T1

Assume the game G(t, E) and n is a variable node or a constant node la-
belled with some f : A 6= 0 of t. If for every π ∈ G(t, E) and i, ni 6= n then transformation
T1 is t[b/n].

 *)

(* end arena position TODO

The path m1 , . . . , m2p is end in t if
1. m1 is a variable node,
2. for each i : 1 < i ≤ p, m2i−1 is a variable node whose binder occurs in the path,
3. every variable node below m2p in t is bound by a node that either occurs above m1
or below m2p in t.

 *)

(* path that contributes TODO

Assume π ∈ G(t, E) and nj is a lambda node. The interval π[i, j] con-
tributes if [ri ] 6= [rj ].

*)

(* redundant path TODO

Assume γ = m1 , . . . , m2p is an end path in t.
1. γ is redundant in the interval π[i, k] of π ∈ G(t, E) when: if πj1 , j1 < k, is the first
position after πi with nj1 = m1 then
(a) there is a later position πj , j ≤ k, and a chain πj1 , . . . , πj2p for πj where nj = m2p ,
(b) π[j1 , j] does not contribute, and
(c) γ is redundant in the interval π[j, k].
2. γ is redundant in the game G(t, E) if γ is redundant in every play π[1, l] (where πl is
the final position of π).

 *)

(* transformation T2

Assume the end path m1 , . . . , m2p is redundant in G(t, E). If t0 is the
subterm whose root is the successor node of m2p then transformation T2 is t[t0 /m1 ].

 *)

(*
  example 1
  (\x.x) a = a
*)



Notation "'[-' a ',' b '-]_' TS " := (intvl TS a b) (at level 20).


(* \x.x *)
Definition ex1_0 := tm 1 0 [].
(* a *)
Definition ex1_1 := tm 0 0 [].
(* a as applicative term *)
Definition ex1_rhs := node 0 [].


Lemma solved_ex1 : exists g, solved_start g ex1_0 [ex1_1] ex1_rhs.
Proof.
  eexists.
  cbn. split; [reflexivity|].
  apply: solved_var.
  - cbn. reflexivity.
  - cbn. reflexivity.
  - cbn. apply: solved_const.
    + cbn. reflexivity.
    + cbn. reflexivity.
    + cbn. constructor.
    + cbn. done.
Qed.

(* example Stirling
  constants:
  b := 2
  g := 1
  a := 0
*)

Definition main_solution :=
  tm 2 0 [tm 2 3 [tm 2 5 [tm 2 4 [tm 0 3 []; tm 0 3 []]; tm 0 8 []]; tm 0 1 []]].

Definition arg1 :=
  tm 2 0 [tm 0 1 []; tm 0 1 []].

Definition arg2 :=
  tm 1 0 [tm 2 4 [tm 0 0 []]; tm 0 0 [tm 2 1 []; tm 0 1 []]].

(* g a *)
Definition result :=
  node 1 [node 0 []].

Lemma solved_Stirling : exists g, solved_start g main_solution [arg1; arg2] result.
Proof.
  unfold result.
  eexists.
  cbn. split; [reflexivity|].
  apply: solved_var; [reflexivity..|].
  rewrite [length _]/=. apply: solved_var; [reflexivity..|].
  rewrite [length _]/=. apply: solved_var; [reflexivity..|].
  rewrite [length _]/=. apply: solved_var; [reflexivity..|].
  rewrite [length _]/=. apply: solved_var; [reflexivity..|].
  rewrite [length _]/=. apply: solved_var; [reflexivity..|].
  rewrite [length _]/=. apply: solved_var; [reflexivity..|].

  rewrite [length _]/=. apply: solved_const; [repeat constructor..|].
  move=> > [|]; last done.
  move=> [*]. subst.
  apply: solved_var; [reflexivity..|].
  rewrite [length _]/=. apply: solved_var; [reflexivity..|].
  rewrite [length _]/=. apply: solved_var; [reflexivity..|].
  rewrite [length _]/=. apply: solved_var; [reflexivity..|].
  rewrite [length _]/=. apply: solved_var; [reflexivity..|].
  rewrite [length _]/=. apply: solved_var; [reflexivity..|].
  rewrite [length _]/=. apply: solved_var; [reflexivity..|].
  rewrite [length _]/=. apply: solved_var; [reflexivity..|].
  rewrite [length _]/=. apply: solved_var; [reflexivity..|].
  rewrite [length _]/=. apply: solved_var; [reflexivity..|].
  rewrite [length _]/=. apply: solved_var; [reflexivity..|].
  rewrite [length _]/=. apply: solved_var; [reflexivity..|].
  rewrite [length _]/=. apply: solved_var; [reflexivity..|].
  rewrite [length _]/=. apply: solved_var; [reflexivity..|].


  rewrite [length _]/=. apply: solved_const; [repeat constructor..|].
  done.
Qed.


