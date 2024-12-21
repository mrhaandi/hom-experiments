Require Import List ssreflect.
Import ListNotations.
Require Import PeanoNat.
Require Import Nat.




Inductive term : Type :=
  (* tm n x [tk; ...; t1] is the term
     \x1...\xn. x t1 ... tk
     where x is the de Bruijn index of a bound variable.
     If the variable is out of bounds, then it is a constant *)
  | tm : nat -> nat -> list term -> term.

(* Positions in a tree or term are lists of natural numbers. *)
Definition position := list nat.

Fixpoint get_depth (t : term) :=
  let 'tm n m args := t
  in 1 + fold_left (fun acc el => max acc (get_depth el)) args 0.

(* compute the subterm of [t] at position [p] *)
Fixpoint subterm (t : term) (p : position) : option term :=
  match t, p with
  | tm n x ts, [] => Some (tm n x ts)
  | tm n x ts, i :: p =>
    match nth_error ts i with
    | Some ti => subterm ti p
    | None => None
    end
  end.


(* as above, but gives also the limit for variables that were bound
   above the returned term

   QUESTION: maybe we should use only this definition?
   SEPARATE
 *)
Fixpoint subterm_bound (t : term) (p : position) (bound:nat) : option nat :=
  match t, p with
  | tm n x ts, [] => Some bound
  | tm n x ts, i :: p =>
    match nth_error ts i with
    | Some ti => subterm_bound ti p (bound+n)
    | None => None
    end
  end.


Inductive rose_tree (A : Type) : Type :=
| node : A -> list (rose_tree A) -> rose_tree A.

Arguments node {A}.

Fixpoint get_tdepth (A : Type) (tr: rose_tree A) :=
  match tr with
  | node v children => fold_left (fun acc el => let nacc := (get_tdepth A el) in
                                                match (acc ?= nacc)  with
                                                | Eq => acc
                                                | Lt => nacc
                                                | Gt => acc
                                                end) children 0%nat
  end.

Arguments get_tdepth {A}.




(* Arenas of our game are lists of terms [t, t1, ..., tk] s.t. 
    t t1...tk reduces to rhs of the target equation.
    TODO: get rid of plurals
 *)
Definition arena  := list term.

(* Arena position picks a term t from an arena and then it is 
   a position in t. *)
Definition aposition  := (nat * position)%type.

(* 
   Intervals are used to designate a segment of rose tree
   π[i, j] is the sequence of positions πi,..., πj.

 *)
Inductive interval : Type :=
    | intvl : position -> position -> interval.

Notation "'pi[' a ',' b ']'" := (intvl a b) (at level 2).

(* [3; 4] is a continuation of [1; 2] *)
Check (pi[[1; 2], [3; 4]]).



Definition prefix (ap:aposition) (ap':aposition) :=
  let '(i, p) := ap in
  let '(i', p') := ap' in
  i = i' /\ p = firstn (length p) p'.

(* For a lookup table
     theta = lk [e0,...,en]
   the interpretation of the variable of de Bruijn index i is
   in ei = (ap, theta')
   where
   - ap is the position of the subarena t used to interpret
     the variable,
   - theta' is the interpretation of the free variables in t
*)
Inductive lookup : Type :=
  | lk : list (aposition * lookup) -> lookup.

Definition lookup_contents := list (aposition * lookup).

Definition add_lk (ap:aposition) (theta : lookup_contents) (j : nat) :=
  let '(i, p) := ap in
    ((i, p ++ [j]), lk theta).

Arguments add_lk /.



Definition game_tree := rose_tree (aposition * lookup_contents).

Fixpoint get_game_subtree (gtr : game_tree) (p: position) :=
  match p with
  | [] => Some gtr
  | hd :: tl => let 'node v children := gtr
                in match nth_error children hd with
                   | Some gtr' => get_game_subtree gtr' tl
                   | None => None
                   end
  end.

(* Returns the list of nodes in the game tree tr through which the
   interval intv passes.

   TODO: inductive type
 *)
Inductive passthrough_nodes : game_tree -> interval -> list aposition -> Prop :=
  | passthrouugh_case_nil_nil pos theta children:
      passthrough_nodes (node (pos, theta) children) pi[[], []] [pos]

  | passthrouugh_case_nil_cons pos theta children hd (tl:position) rest tr':
      nth_error children hd = Some tr' ->
      passthrough_nodes tr' pi[[], tl] rest ->
      passthrough_nodes (node (pos, theta) children) pi[ [], (hd :: tl) ] (pos :: rest)

| passthrouugh_case_cons_cons pos theta children hd (tl:position) rest tr' res:
      nth_error children hd = Some tr' ->
      passthrough_nodes tr' pi[tl, rest] res ->
      passthrough_nodes (node (pos, theta) children) pi[ (hd :: tl), rest ] res.


(* 
   Intervals [intv1] and [intv2] correspond when they pass through
   the same sequence of nodes in the game tree tr.

   QUESTION: maybe this should be modelled by an inductive predicate?
 *)
Inductive corresponding (tr:game_tree) (intv1:interval) (intv2:interval) :=
  | corr_case nds1 nds2:
  passthrough_nodes tr intv1 nds1 ->
  passthrough_nodes tr intv2 nds2 ->  
  nds1 = nds2 -> corresponding tr intv1 intv2.


Section Arenas.

Variable TS: arena.

(* Gives the portion of the arena [TS] under the position [ap],
   provided that [ap] is an address in the arena. *)
Definition get_subarena ap :=
      let '(i, p) := ap in
      match nth_error TS i with
      | Some t => subterm t p 
      | None => None
      end.


(* as above, but gives the limit for variables that were bound
   above the returned term

   QUESTION: maybe we should use only this definition?
 *)
Fixpoint get_subarena_bound ap : option nat :=
  let '(i, p) := ap in
  match nth_error TS i with
  | Some t => subterm_bound t p 0
  | None => None
  end.


(* The list with [n] elements [v]. TODO: repeat *)
Fixpoint const_list (n:nat) (v:nat) :=
  match n with
  | 0 => []
  | S n' => v :: const_list n' v
  end.


Fixpoint level_helper (t:term) (ap:position) (lvls:list nat) (last:nat) :=
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

TODO: inductive

 *)
Definition level (TS:arena) (ap:aposition) :=
  let (i, pos) := ap in
  match nth_error TS i with
  | Some t => level_helper t pos [] 0
  | None => None
  end.


(* Extend the arena position ap at its end with extension. *)
Definition extend_ap (ap:aposition) (extension:position) :=
  let '(i, p) := ap in
   (i, p ++ extension).



(* Given the range of so far [bound] variables and
   a list of [seen] variables up to the current position
   tell if the given term on the given position has an
   embedded occurrence *)
Inductive embedded_seen  (bound:nat) (seen: list nat) :
  term ->  position -> Prop :=
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
               
Inductive embedded  :
  aposition -> Prop :=
  | embedded_unpack i p t:
    nth_error TS i = Some t ->
    embedded_seen 0 [] t p ->
    embedded (i, p).

(* Given a variable [x] bound in the context of the current term
   we check if
   - for the current term
   - at the given position in it there is a variable
   - that is a descendant under binding of [x] *)
Inductive descendant_of (x : nat) :
  term -> position -> Prop :=
| descendant_term_use_binding n t p m y args m' z:
  nth_error args n = Some t ->
  z < m' -> (* z is bound in the binder of (tm m' y' args') *)
  y = x + m -> (* y is an occurrence of x *)
  descendant_of z t p  ->
  descendant_of x (tm m y args) (n::p)
                
| descendant_term_skip_binding n p m y args t':
  nth_error args n = Some t' ->
  descendant_of (x+m) t' p -> 
  descendant_of x (tm m y args) (n::p)
                
| descendant_term_nil m y args:
  y = x + m -> (* y is an occurrence of x *)
  descendant_of x (tm m y args) [] 
                
| descendant_term_take_nil n m y args m' y' args':
  nth_error args n = Some (tm m' y' args') -> (* y' is bound in one of arguments of x *)
  y' < m' -> (* y' occurs directly under its binder *)
  y = x + m -> (* y is an occurrence of x *)
  descendant_of x (tm m y args) [n].

  
(* Stirling:

Assume n, m are variable nodes of an interpolation tree.

1. n is a descendant under binding of m (m is an ancestor under
binding of n) if m = n or m0 is a successor of m, m0 ↓ n0 and n is a
descendant under binding of n0 .

2. n and m belong to the same family if they have a common ancestor
under binding.

3. n is end if it has no descendants under binding except itself.

here:

unpack ap and ap', check that ap is a prefix of ap, i.e. ap' = ap ++
p'' check that the variable in the root of the subterm tp at ap is a
descendant under binging of the variable at p'' respecting the bound
variables.

*)
Inductive descendant_under_binding :
  aposition -> aposition -> Prop :=
  | descendant_unpack i p p' t n x args:
    nth_error TS i = Some t ->
    subterm t p = Some (tm n x args) -> (* we take variable at p *)
    descendant_of x (tm n x args) (p ++ p') ->
    descendant_under_binding (i, p) (i, p ++ p').



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
  means that the game
  - represented as game_tree
  - starting at position (ap, theta)
  - with the rhs r
  is solved
*)

Inductive solved (ap : aposition) (theta : lookup_contents) :
  rose_tree (aposition * lookup_contents) ->
  rose_tree nat -> Prop :=
  
    | solved_var n x args nap theta' gt r:
      get_subarena ap = Some (tm n x args) -> (* get subarena at position ap *)
      nth_error theta x = Some (nap, lk theta') -> (* get interpretation of x *)
      solved nap ((map (add_lk ap theta) (seq 0 (length args))) ++ theta') gt r ->
      (* (map (add_lk ap theta) (seq 0 (length args))) - uses arguments of x
         to interpret variables abstracted in the interpretation of x *)
      solved ap theta (node (ap, theta) [gt]) r

    | solved_const gs n x ts rs:
      get_subarena ap = Some (tm n (x + length theta) ts) ->
      length ts = length rs ->
      Forall2 (fun _ t => match t with tm nt _ _ => nt = 0 end) gs ts ->
      (forall g j r, In (g, (j, r)) (combine gs (combine (seq 0 (length rs)) rs)) ->
        solved (extend_ap ap [j]) theta g r) ->
      solved ap theta (node (ap, theta) gs) (node x rs).


(* parent_binder_var: in the game tree TS the game position pi1 is the parent of pi2
   when

  - pi1 is a binder position and pi2 is a variable bound by the binder
  - the interpretation of free variables at pi1 is the same as at pi2


   Stirling:

   Assume that π ∈ G(t, E) and nj is a variable node. The position πi
   is the parent of the later position πj if ni ↓ nj and θi (ni ) = θj
   (ni ). We also say that πj is a child of πi .

 *)

Inductive parent_binder_var (pi1 : position) (pi2 : position) :
  (rose_tree (aposition * lookup_contents)) -> Prop  :=
| parent_at_binder gtr ap ap' theta theta' further further' bound: 
  descendant_under_binding ap ap' ->
  get_game_subtree gtr pi1 = Some (node (ap, theta) further) ->
  get_game_subtree gtr pi2 = Some (node (ap', theta') further') ->
  get_subarena_bound ap = Some bound ->
  theta = skipn ((length theta') - bound) theta' ->
  parent_binder_var pi1 pi2 gtr.


(* parent_var_binder

Assume π ∈ G(t, E) and nj is a lambda node. We define πi the parent
of πj by cases on the label at the node n directly above nj in the interpolation tree:
@: i = 1;
f : i = j − 1;
z: i is such that πi+1 is the parent of πj−1 (according to Definition 21).

 *)
Inductive parent_var_binder (pi1 : position) (pi2 : position) :
  (rose_tree (aposition * lookup_contents)) -> Prop  :=
| parent_at_var gtr ap ap1 ap1' theta theta1 theta1' further further1 further1' n x args bound pi1': 
  get_game_subtree gtr pi1 = Some (node (ap, theta) further) ->
  get_subarena ap = Some (tm n x args) -> (* take var x at ap *)
  get_subarena_bound ap = Some bound -> (* take var x at ap *)
  x < bound + n -> (* check that x at ap is not a constant *)
  nth_error further 0 = Some (node (ap1, theta1) further1) -> (* var nodes have only one successor *)
  parent_binder_var (pi1 ++ [0]) pi1' gtr -> (* find relevant child at pi1' *)
  get_game_subtree gtr pi1' = Some (node (ap1', theta1') further1') ->
  pi2 = pi1' ++ [0] -> (* var nodes have only one successor *)
  parent_var_binder pi1 pi2 gtr.



Inductive chain_condition (gtr: game_tree) : (position * position) * nat -> Prop :=
| chain_case_odd pi pi' n:
 Nat.Odd n ->
  parent_var_binder pi pi' gtr ->
  chain_condition gtr ((pi, pi'), n)
| chain_case_even pi pi' n:
  Nat.Even n ->
  pi = firstn (length pi) pi' ->
  chain_condition gtr ((pi, pi'), n).


(* chain

   For now we do not check the first condition.

  Stirling:
  Assume π ∈ G(t, E) and πj is a lambda node. The sequence πj1 , . . . , πj2p
  is a chain (of parent child positions) for πj if
  1. πj = πj2p ,
  2. for 1 ≤ m ≤ p, πj2m−1 is the parent of πj2m ,
  3. for 1 ≤ m < p, πj2m is the position preceding πj2m+1 .

 *)
Definition chain gtr l  :=
  Forall (chain_condition gtr) (combine (combine l (skipn 1 l)) (seq 0 (length l))).



End Arenas.

(* t ts = r *)
Definition solved_start g t (ts : list term) (r : rose_tree nat) :=
  match t with
  | tm n x us =>
    length ts = n /\
    solved (t :: ts) (0, []) (map (fun j => ((S j, []), lk [])) (rev (seq 0 (length ts)))) g r
  end.






(* complementary intervals TODO
   
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


