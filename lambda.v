Require Import List ssreflect.
Import ListNotations.
Require Import PeanoNat.
Require Import Nat.
Require Import Lia.


Require Export HOM.RoseTree.
Export HOM.RoseTree.


Notation term := (rose_tree (nat * nat)).

(* increment all free variables by k *)
Definition shift_term (k : nat) (t : term) : term :=
  map_tree_dependent (fun l '(n, x) => let bound := list_sum (map fst l) in (n, if bound <=? x then k + x else x)) t.

(* decrement all free variables by k *)
Definition slide_term (k : nat) (t : term) : term :=
  map_tree_dependent (fun l '(n, x) => let bound := list_sum (map fst l) in (n, if bound <=? x then k - x else x)) t.


(* place term t' at position p in t *)
Definition replace_term (t' : term) (p : position) (t : term) : term :=
  let bound := list_sum (map fst (get_branch t p)) in
  replace_subtree (shift_term bound t') p t.




Definition get_depth (t : term) := get_tree_depth t.


(* compute the subterm of [t] at position [p] *)
Definition get_subterm (t : term) (p : position) : term :=
  get_subtree t p.


(* as above, but gives the limit for variables that were bound
   above the (lambdas) of the term at the position, the value is
   accumulated over the parameter bound

 *)
Definition get_subterm_bound (t : term) (p : position) (bound:nat) : nat :=
  fold_left (fun acc el => acc + el) (fst (split (get_branch t p))) bound.

Notation "'tm' n x ts" := (node (n, x) ts) (at level 10, n at next level, x at next level).


(*
  example 1
  (\x.x) a = a
*)

(* \x.x *)
Definition ex1_0 := tm 1 0 [].
(* a *)
Definition ex1_1 := tm 0 0 [].
(* \x.a *)
Definition ex1_2 := tm 1 1 [].



(* example Stirling
  constants:
  b := 2
  g := 1
  a := 0
*)

Definition main_solution :=
  (* \x1 x0.x0 (\x1 x0.  x1+2  (\x1 x0.x1+2+2  (\x1 x0.x0+2+2 (\.x1+2) (\.x1+2) )  (\.x2+0+2+2+2))  (\.x1+0) ) *)
  tm 2 0 [tm 2 3 [tm 2 5 [tm 2 4 [tm 0 3 []; tm 0 3 []]; tm 0 8 []]; tm 0 1 []]].

(* This is the solution from Stirling's paper? *)
Definition main_solution' :=
  (* \x1 x0.x0 (\x1 x0.  x1+2  (\x1 x0.x1+2+2  (\x1 x0.x0+2+2 (\.x1+2) (\.x0+2) )  (\.x2+0+2+2+2))  (\.x1+0) ) *)
  tm 2 0 [tm 2 3 [tm 2 5 [tm 2 4 [tm 0 3 []; tm 0 2 []]; tm 0 8 []]; tm 0 1 []]].

(* This is also some solution. *)
Definition main_solution'' :=
  (* \x1 x0.x0 (\x1 x0.  x1+2  (\x1 x0.x1+2+2  (\x1 x0.x0+2+2 (\.x0+2) (\.x1+2) )  (\.x2+0+2+2+2))  (\.x1+0) ) *)
  tm 2 0 [tm 2 3 [tm 2 5 [tm 2 4 [tm 0 2 []; tm 0 3 []]; tm 0 8 []]; tm 0 1 []]].

(* This is also some solution. *)
Definition main_solution''' :=
  (* \x1 x0.x0 (\x1 x0.  x1+2  (\x1 x0.x1+2+2  (\x1 x0.x0+2+2 (\.x0+2) (\.x1+2) )  (\.x2+0+2+2+2))  (\.x1+0) ) *)
  tm 2 0 [tm 2 3 [tm 2 5 [tm 2 4 [tm 0 2 []; tm 0 2 []]; tm 0 8 []]; tm 0 1 []]].



Definition arg1 :=
  tm 2 0 [tm 0 1 []; tm 0 1 []].

Definition arg2 :=
  tm 1 0 [tm 2 4 [tm 0 0 []]; tm 0 0 [tm 2 1 []; tm 0 1 []]].

Lemma test_get_depth1: (get_depth ex1_0) = 0.
Proof.
  now compute.
Qed.


Lemma test_get_depth2: (get_depth arg2) = 2.
Proof.
  now hnf.
Qed.


Lemma test_get_depth3: (get_depth arg1) = 1.
Proof.
  now compute.
Qed.

Lemma test_subterm1: get_subterm ex1_0 [] = ex1_0.
Proof.
  now compute.
Qed.

Lemma test_subterm2: get_subterm ex1_0 [0] = ex1_0.
Proof.
   now compute.
Qed.

Lemma test_subterm3: get_subterm arg1 [0] = tm 0 1 [].
Proof.
  now compute.
Qed.

Lemma test_subterm4: get_subterm arg2 [0;0] = tm 0 0 [].
Proof.
  now compute.
Qed.

Lemma test_subterm5: get_subterm arg2 [1;1] = tm 0 1 [].
Proof.
  now compute.
Qed.

Lemma test_subterm_bound1: get_subterm_bound ex1_0 [] 0 = 0.
Proof.
  now compute.
Qed.

Lemma test_subterm_bound2: get_subterm_bound ex1_0 [0] 0 = 0.
Proof.
  now compute.
Qed.

Lemma test_subterm_bound3: get_subterm_bound arg2 [0] 0 = 1.
Proof.
  now compute.
Qed.

Lemma test_subterm_bound4: get_subterm_bound arg2 [0;0] 0 = 3.
Proof.
  now compute.
Qed.




(* Arenas of our game are lists of terms [t, t1, ..., tk] s.t. 
    t t1...tk reduces to rhs of the target equation.

  PROPOSAL: (list of lists of terms, list of booleans, list of rhs)
 *)
Definition arena  := list term.


(* Arena position picks a term t from an arena and then it is 
   a position in t. *)
Definition aposition  := (nat * position)%type.

Definition ex_arena0 :=  [ex1_0; ex1_1].
Definition ex_arena1 :=  [main_solution; arg1; arg2].


(* Gives the portion of the arena [TS] under the position [ap],
   provided that [ap] is an address in the arena. *)
Definition get_arena_subterm TS ap :=
      let '(i, p) := ap in
      match nth_error TS i with
      | Some t => Some (get_subterm t p)
      | None => None
      end.



(* as above, but gives the limit for variables that were bound
   above the returned term

 *)
Definition get_arena_subterm_bound TS ap : option nat :=
  let '(i, p) := ap in
  match nth_error TS i with
  | Some t => Some (get_subterm_bound t p 0)
  | None => None
  end.

Lemma test1_subterm_ex_arena1: get_arena_subterm ex_arena1 (0, nil) = Some main_solution.
Proof.
  now compute.
Qed.

(* The result is tm 0 8 [] *)
Lemma test2_subterm_ex_arena1: get_arena_subterm ex_arena1 (0, [0;0;1]) = Some (tm 0 8 []).
Proof.
  now compute.
Qed.

(* Since bound is 6, this tm 0 8 [] is actually tm 0 2 [], which corresponds to the constant b. *)
Lemma test2_subterm_bound_ex_arena1: get_arena_subterm_bound ex_arena1 (0, [0;0;1]) = Some 6.
Proof.
  now compute.
Qed.


(* The result is tm 0 3 [] *)
Lemma test3_subterm_ex_arena1: get_arena_subterm ex_arena1 (0, [0;0;0;1]) = Some (tm 0 3 []).
Proof.
   now compute.
Qed.

(* Since bound is 8, tm 0 8 [] is actually an occurrence of a bound variable. *)
Lemma test3_subterm_bound_ex_arena1: get_arena_subterm_bound ex_arena1 (0, [0;0;0;1]) = Some 8.
Proof.
   now compute.
Qed.


(* 
   Intervals are used to designate a segment of rose tree
   π[i, j] is the sequence of positions πi,..., πj.

 *)
Inductive interval : Type :=
    | intvl : position -> position -> interval.

Notation "'pi[' a ',' b ']'" := (intvl a b) (at level 2).

(* [3; 4] is a continuation of [1; 2] *)
Check (pi[[1; 2], [3; 4]]).


(* ap is a prefix of ap' *)
Definition prefix (ap:aposition) (ap':aposition) :=
  let '(i, p) := ap in
  let '(i', p') := ap' in
  i = i' /\ p = firstn (length p) p'.

Lemma test_prefix: prefix (0,[1;2]) (0,[1;2;3]).
Proof.
  simpl.
  now split.
Qed.

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

Definition get_game_subtree (gtr : game_tree) (p: position) :=
  get_subtree gtr p.

(* Returns the list of nodes in the game tree tr through which the
   interval intv passes.

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
Inductive corresponding (gtr:game_tree) (intv1:interval) (intv2:interval) :=
  | corr_case nds1 nds2:
  passthrough_nodes gtr intv1 nds1 ->
  passthrough_nodes gtr intv2 nds2 ->  
  nds1 = nds2 -> corresponding gtr intv1 intv2.


Inductive is_variable_node (ar:arena) (gtr:game_tree) (p:position) :=
| is_var_case ap cont rest n x args b:
  has_position gtr p = true ->
  get_game_subtree gtr p = node (ap, cont) rest ->
  get_arena_subterm ar ap = Some (tm n x args) ->
  get_arena_subterm_bound ar ap = Some b ->
  x < b ->
  is_variable_node ar gtr p.

Section Arenas.

Variable TS : arena.



(*

The predicate

level_term t p lvl y

holds when the variable at the position p in t has level lvl
provided that y is an ancestor variable of the variable at
p.


*)

(*
by "variable at position p" we mean "the head variable of the term at position p"
*)

(* actual level is  level_term (tm n y ts) p x (repeat 1 n) *)

(* 
level_term t p l l' ls means
- t is the term
- p is the position in the term
- l is the level of the head variable of the subterm at p
- l' is the level of the predecessor od the t
- ls is the list of levels of free variables in the term

usage for closed terms: level_term t p l 0 []
*)
Inductive level_term : term -> position -> nat -> nat -> list nat -> Prop :=
| level_term_nil n x ts l' ls :
    level_term (tm n x ts) [] (nth x ((repeat (S l') n) ++ ls) 0) l' ls
| level_term_cons n x ts i ps t l l' ls:
    nth_error ts i = Some t ->
    level_term t ps l (nth x ((repeat (S l') n) ++ ls) 0) ((repeat (S l') n) ++ ls) ->
    level_term (tm n x ts) (i::ps) l l' ls.

(* level of x in \x.x is 1 *)
Lemma test_level_term_ex1_0: level_term ex1_0 [] 1 0 [].
Proof.
  apply (level_term_nil 1 0 [] 0 []).
Qed.

(* \x.x (\y.x (\z.y)) *)
Definition ex2_0 := tm 1 0 [tm 1 1 [tm 1 1 []]].

(* 
level of y in \x.x (\y.x (\z.y)) is 2 because it is bound as successor of x
*)
Lemma test_level_term_ex2_0: level_term ex2_0 [0; 0] 2 0 [].
Proof.
  econstructor; [reflexivity|].
  cbn.
  econstructor; [reflexivity|].
  cbn.
  apply (level_term_nil 1 1 [] 1 [2; 1]).
Qed.

(*
Inductive level_term : term -> position -> nat -> nat -> Prop :=
(* We reached the position of the variable. *)
| level_term_nil n x ts:
   level_term (tm n x ts) [] 0 x
(* We skip unrelated binder. *)
| level_term_cons_skip n x ts hd tl m y t:
   nth_error ts hd = Some t ->
   level_term t tl m (y+n) -> 
   level_term (tm n x ts) (hd::tl) m y
(* We take into account related binder and position is shallow. *)
| level_term_cons_shallow_parent n x ts n' ts' hd y:
   nth_error ts hd = Some (tm n' y ts') ->
   y < n' -> (* y is bound by the binder in hd's argument of x *)
   level_term (tm n (x+n) ts) [hd] 1 x (* x is the head variable of the current term *)
(* We take into account related binder and position is deep. *)
| level_term_cons_anc n x ts n' x' ts' hd hd' tl m y t':
   nth_error ts hd = Some (tm n' x' ts') ->
   y < n' -> (* y is bound by the binder in hd's argument of x *)
   nth_error ts' hd' = Some t' ->
   level_term t' tl m y -> 
   level_term (tm n (x+n) ts) (hd::hd'::tl) (S m) x. (* x is the head variable of the current term *)
*)
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
Inductive level : arena -> aposition -> nat -> Prop :=
| level_const TS i t pos l:
   nth_error TS i = Some t -> 
   level_term t pos l 0 [] ->
   level TS (i, pos) l.
  (*
| level_var TS i n x ts pos lvl m :
   nth_error TS i = Some (tm n x ts) -> 
   m < n ->
   level_term (tm n x ts) pos lvl m ->
   level TS (i, pos) lvl.
*)




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
| descendant_term_use_binding n t p m args m' z:
  nth_error args n = Some t ->
  z < m' -> (* z is bound in the binder of (tm m' y' args') *)
  descendant_of z t p  ->
  descendant_of x (tm m (x+m) args) (n::p)
                
| descendant_term_skip_binding n p m y args t':
  nth_error args n = Some t' ->
  descendant_of (x+m) t' p -> 
  descendant_of x (tm m y args) (n::p)
                
| descendant_term_nil m args:
  descendant_of x (tm m (x+m) args) [] 
                
| descendant_term_take_nil n m args m' y' args':
  nth_error args n = Some (tm m' y' args') -> (* y' is bound in one of arguments of x *)
  y' < m' -> (* y' occurs directly under its binder *)
  descendant_of x (tm m (x+m) args) [n].

  
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
    has_position t p = true ->
    get_subterm t p = tm n x args -> (* we take variable at p *)
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
      get_arena_subterm TS ap = Some (tm n x args) -> (* get subarena at position ap *)
      nth_error theta x = Some (nap, lk theta') -> (* get interpretation of x *)
      solved nap ((map (add_lk ap theta) (seq 0 (length args))) ++ theta') gt r ->
      (* (map (add_lk ap theta) (seq 0 (length args))) - uses arguments of x
         to interpret variables abstracted in the interpretation of x *)
      solved ap theta (node (ap, theta) [gt]) r

    | solved_const gs n x ts rs:
      get_arena_subterm TS ap = Some (tm n (x + length theta) ts) ->
      length ts = length rs ->
      Forall2 (fun _ t => match t with tm nt _ _ => nt = 0 end) gs ts ->
      (forall g j r, In (g, (j, r)) (combine gs (combine (seq 0 (length rs)) rs)) ->
        solved (extend_ap ap [j]) theta g r) ->
      solved ap theta (node (ap, theta) gs) (node x rs).


(* Holds when the position is final in the game tree. *)
Inductive is_final : position -> game_tree -> Prop :=
| position_nil_rose_nil v:
  is_final [] (node v [])
| position_some_rose_do hd tl v l t':
  nth_error l hd = Some t' ->
  is_final tl t' ->
  is_final (hd::tl) (node v l).

    
  
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
  has_position gtr pi1 = true ->
  has_position gtr pi2 = true ->
  get_game_subtree gtr pi1 = node (ap, theta) further ->
  get_game_subtree gtr pi2 = node (ap', theta') further' ->
  get_arena_subterm_bound TS ap = Some bound ->
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
  has_position gtr pi1 = true ->
  get_game_subtree gtr pi1 = node (ap, theta) further ->
  get_arena_subterm TS ap = Some (tm n x args) -> (* take var x at ap *)
  get_arena_subterm_bound TS ap = Some bound -> (* take var x at ap *)
  x < bound + n -> (* check that x at ap is not a constant *)
  nth_error further 0 = Some (node (ap1, theta1) further1) -> (* var nodes have only one successor *)
  parent_binder_var (pi1 ++ [0]) pi1' gtr -> (* find relevant child at pi1' *)
  has_position gtr pi1' = true ->
  get_game_subtree gtr pi1' = node (ap1', theta1') further1' ->
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
  1. π_j = πj2p ,
  2. for 1 ≤ m ≤ p, πj2m−1 is the parent of πj2m ,
  3. for 1 ≤ m < p, πj2m is the position preceding πj2m+1 .

 *)
Definition chain (gtr : game_tree) (l : list position)  :=
  Forall (chain_condition gtr) (combine (combine l (skipn 1 l)) (seq 0 (length l))).



End Arenas.

(* [t] [ts] = [r] by means of [g] *)
Definition solved_start (g : game_tree) (t : term) (ts : list term) (r : rose_tree nat) :=
  match t with
  | tm n x us =>
    length ts = n /\
    solved (t :: ts) (0, []) (map (fun j => ((S j, []), lk [])) (rev (seq 0 (length ts)))) g r
  end.





Inductive same_variable_at_start (ar : arena) (gtr : game_tree) : interval -> interval -> Prop :=
| svar_case j jend m mend ap1 tht1 chldrn1 n1 x1 ts1 b1 ap2 tht2 chldrn2 n2 x2 ts2 b2:
  has_position gtr j = true ->
  has_position gtr m = true ->
  get_game_subtree gtr j = node (ap1, tht1) chldrn1 ->
  get_game_subtree gtr m = node (ap2, tht2) chldrn2 ->
  get_arena_subterm ar ap1 = Some (tm n1 x1 ts1)  ->
  get_arena_subterm_bound ar ap1 = Some b1 ->
  get_arena_subterm ar ap2 = Some (tm n2 x2 ts2)  ->
  get_arena_subterm_bound ar ap2 = Some b2 ->
  b1 + n2 = b2 + n1 -> (* n1 and n2 are the same variables *)
  same_variable_at_start ar gtr  pi[j, jend] pi[m, mend].

Definition last_step gtr pos := get_game_subtree gtr pos.
            
(* complementary intervals 

Stirling:

Assume π ∈ G(t, E), π_i is the parent of π_j and π_m , j < m, n_j , n_m are
both labelled with the same variable and n_j <> n_m. There is a k such that 
π[j + 1, j + k] and π[m + 1, m + k] correspond and
1. (a) π_j is the parent of π_j+k+1 and π_m is the parent of π_m+k+1, and 
   (b) n_j+k+1 is the p-th successor of n_j iff n_m+k+1 is the p-th successor of n_m , or
2. n_j+k is labelled with a constant and 
   (a) π_m+k is the final position of π or  (implication?)
   (b) n_j+k+1 <> n_m+k+1 .


Assume π ∈ G(t, E) and n_j, n_m are both labelled with the same variable
for j < m. We say that π[j + 1, j + k] and π[m + 1, m + k] are complementary intervals
if 1 or 2 of Proposition 24 holds.


Here:

We need pi_j and pi_{j+k+1} anyway so it is better to consider complementary intervals
to be π[j, j + k + 1] and π[m, m + k + 1] in the notation above.

*)
Inductive complementary (ar : arena) (gtr : game_tree) : interval -> interval -> Prop :=
| compl_var j jpke jpkp1r m mpke mpkp1r:
  same_variable_at_start ar gtr pi[j, (jpke :: jpkp1r)] pi[m, mpke :: mpkp1r] ->
  corresponding gtr pi[j ++ [jpke], removelast jpkp1r] pi[m ++ [mpke], removelast mpkp1r] ->
  (* intervals correspond *)
  parent_var_binder ar j (j++(jpke :: jpkp1r)) gtr ->
  (* π_j is the parent of π_j+k+1 *)
  parent_var_binder ar m (m++(mpke :: mpkp1r)) gtr ->
  (* π_m is the parent of π_m+k+1 *)
  has_position gtr (j++(jpke :: jpkp1r)) = true ->
  has_position gtr (m++(mpke :: mpkp1r)) = true ->
  last_step gtr (j++(jpke :: jpkp1r)) = last_step gtr (m++(mpke :: mpkp1r)) ->
  (* last step is the same successor *)
  complementary ar gtr  pi[j, (jpke :: jpkp1r)] pi[m, mpke :: mpkp1r]
| compl_const_final j jpkp1 m mpkp1 ap1 tht1 chldrn1 ap2 tht2 chldrn2 n1 b1 x1 ts1 n2 b2 x2 ts2:
  has_position gtr (j++(removelast jpkp1)) = true ->
  has_position gtr (m++(removelast mpkp1)) = true ->
  get_game_subtree gtr (j++(removelast jpkp1)) = node (ap1, tht1) chldrn1 ->
  get_game_subtree gtr (m++(removelast mpkp1)) = node (ap2, tht2) chldrn2 ->
  get_arena_subterm ar ap1 = Some (tm n1 x1 ts1)  ->
  get_arena_subterm_bound ar ap1 = Some b1 ->
  get_arena_subterm ar ap2 = Some (tm n2 x2 ts2)  ->
  get_arena_subterm_bound ar ap2 = Some b2 ->
  (b1 + n2 = b2 + n1 -> is_final (m++(removelast mpkp1)) gtr) ->
  complementary ar gtr  pi[j, jpkp1] pi[m, mpkp1].





(* if n_{j_2i−1} is a variable node then there is a
   j < j_2i−1 and a k such that π[j + 1, j + k] and π[m + 1, m + k] are complementary where m = j_2i−1
   and j_2i = m + k + 1. *)
Inductive recurrence_for_pos ar gtr pos : Prop :=
| rec_pos_case:
  is_variable_node ar gtr pos ->
  (exists pos' lend, pos' <> pos /\ firstn (length pos') pos = pos' /\ complementary ar gtr pi[pos', lend] pi[pos, lend]) ->
  recurrence_for_pos ar gtr pos.
    
(* recurrence property

Assume π ∈ G(t, E). The chain π_j1,..., π_j2p for πj has the recurrence
property if for each i : 1 ≤ i ≤ p, if n_{j_2i−1} is a variable node then there is a j < j_2i−1 and
a k such that π[j + 1, j + k] and π[m + 1, m + k] are complementary where m = j_2i−1
and j_2i = m + k + 1.

 *)
Inductive recurrence_property ar gtr lpos :=
| rec_case:
  chain ar gtr lpos ->
  Forall  (recurrence_for_pos ar gtr) lpos ->
  recurrence_property ar gtr lpos.

(* transformation T1

Assume the game G(t, E) and n is a variable node or a constant node labelled with some
f : A ≠ 0 of t. If for every π ∈ G(t, E) and i, n_i ≠ n then transformation
T1 is t[b/n].

TODO: restate as an application of substitution
 *)

Fixpoint trans_T1 (t:term) (p:position) (b:nat) : option term :=
  match p with
  | [] => match t with
          | tm n _ _ => Some (tm n (n+b) [])
          end
  | hd :: tl => match t with
                | tm n x args => 
                    match nth_error args hd with
                    | Some el =>
                        let start := firstn hd args in
                        let rest := skipn (hd+1) args in
                        match trans_T1 el tl (b+n) with
                        | Some transres =>
                            Some (tm n x (start ++ (transres :: rest)))
                        | None => None
                        end
                    | None => None
                    end
                end
  end.

(* TODO: lemma s.t. we replace with any term

If we have a game tree for an arena s.t. position n does not occur in
g.tr. then if we replace n with any term, the resulting 

 *)

Lemma test_trans_T1_ex1_0: trans_T1 ex1_0 [] 0 = Some ex1_2.
Proof.
  now simpl.
Qed.

Lemma test_trans_T1_main_solution_1: trans_T1 main_solution [] 0 = Some (tm 2 2 []).
Proof.
  now simpl.
Qed.

Lemma test_trans_T1_main_solution_2: trans_T1 main_solution [0] 0 = Some (tm 2 0 [tm 2 4 []]).
Proof.
  now simpl.
Qed.

Lemma test_trans_T1_main_solution_3: trans_T1 main_solution [0;0] 70 = Some (tm 2 0 [tm 2 3 [tm 2 76 []; tm 0 1 []]]).
Proof.
 now simpl.
Qed.


(* Assuming that variables in the range [b1, b2] were bound above the term at hand,
   check that none of the variables in the term are from the range.
*)
Inductive vars_outside_range (b1:nat) (b2:nat) : term -> Prop :=
| vars_outside_range_local (n:nat) (x:nat) (ts : list term):
    x < b2 + n  ->
    Forall (fun st => vars_outside_range (b1+n) (b2+n) st) ts ->
    vars_outside_range b1 b2 (tm n x ts)
| vars_outside_range_external (n:nat) (x:nat) (ts : list term):
    x >= b1 + n  ->
    Forall (fun st => vars_outside_range (b1+n) (b2+n) st) ts ->
    vars_outside_range b1 b2 (tm n x ts).



Lemma test_vars_outside_range:
  vars_outside_range (8+(8-6)) 8 (get_subterm main_solution' [0; 0; 0]).
Proof.
  repeat constructor.
Qed.

(* Checks if the given variable does not occur is absent in the given term. *)
Inductive var_outside x : term -> Prop :=
| var_outside_before n y ts:
  y < x + n ->
  Forall (fun nt => var_outside (x+n) nt) ts ->
  var_outside x (tm n y ts)
| var_outside_after n y ts:
  y > x + n ->
  Forall (fun nt => var_outside (x+n) nt) ts ->
  var_outside x (tm n y ts).

Lemma test_var_outside:
  var_outside 5 (get_subterm main_solution' [0; 0; 0]).
Proof.
  repeat constructor.
Qed.


(* Alternative definition of the predicate which assuming that
   variables in the range [b1, b2] were bound above the term at hand,
   checks that none of the variables in the term are from the range.
   *)
Definition vars_outside_range' (b1:nat) (b2:nat) (t:term) : Prop :=
  Forall (fun var => var_outside var t) (seq b2 (b1-b2)).

Lemma test_vars_outside_range':
  vars_outside_range' (8+(8-6)) 8 (get_subterm main_solution' [0; 0; 0]).
Proof.
  repeat constructor.
Qed.

(* Two versions of vars_outside_range are equivalent. *)
Lemma vars_outside_range_and_prime:
  forall t b1 b2,
    b1 > b2 ->
    vars_outside_range b1 b2 t <-> vars_outside_range' b1 b2 t.
Proof.
  induction t using rose_tree_ind'.
  intros.
  assert (forall r, In r l -> forall b1 b2 : nat, b1 > b2 -> vars_outside_range b1 b2 r <-> vars_outside_range' b1 b2 r).
  {
    intros.
    eapply  (Forall_forall (fun r : term => forall b1 b2 : nat, b1 > b2 -> vars_outside_range b1 b2 r <-> vars_outside_range' b1 b2 r) l) in H;eauto 1.
  } 
  split.
  * intro.
    assert (forall n, Forall (fun st : term => vars_outside_range (b1 + n) (b2 + n) st) l -> forall r, In r l -> vars_outside_range (b1 + n) (b2 + n) r) as Ff.
    { intros.
      eapply (Forall_forall (fun st : term => vars_outside_range (b1 + n) (b2 + n) st) l) in H4;eauto 1.
    }
    inversion H2;subst ts.
    **
         unfold vars_outside_range'.
         apply Forall_forall.
         intros.
         apply in_seq in H4.
         constructor; try lia.
         apply Forall_forall.
         intros.
         generalize H6;intro.
         eapply Ff in H8;eauto 1.
         eapply H1 in H8; try lia; auto.
         unfold vars_outside_range' in H8.
         eapply Forall_forall in H8; [eauto 1|apply in_seq; try lia].
    **
      unfold vars_outside_range'.
      apply Forall_forall.
      intros.
      apply in_seq in H4.
      constructor 2; try lia.
      apply Forall_forall.
      intros.
      generalize H6;intro.
      eapply Ff in H8; eauto 1.
      eapply H1 in H8; try lia; auto.
      unfold vars_outside_range' in H8.
      eapply Forall_forall in H8; [eauto 1|apply in_seq; try lia].
  * intro.
    destruct v as [n x].
    generalize H2; intro vor'.
    unfold vars_outside_range' in H2.
    assert (forall y, In y (seq b2 (b1 - b2)) -> var_outside y (tm n x l)). {
      intros.
      eapply Forall_forall in H2;eauto.
    }
    destruct (Compare_dec.le_lt_dec (b2+n) x).
    ** destruct (Compare_dec.le_lt_dec (b1+n) x).
       *** constructor 2;try lia.
           apply Forall_forall.
           intros.
           apply H1;auto; try lia.
           unfold vars_outside_range'.
           apply Forall_forall.
           intros.
           assert (In (x1-n) (seq b2 (b1 - b2))). {
             apply in_seq.
             apply in_seq in H5.
             lia.
           }
           apply H3 in H6.
           inversion H6; subst n0 y ts.
           ****
             replace (x1 - n + n) with x1 in H11 by lia.
             eapply Forall_forall in H11;eauto 1.
           **** replace (x1 - n + n) with x1 in H11.
                eapply Forall_forall in H11;eauto 1.
                apply in_seq in H5.
                lia.
       ***  
         assert (b2 <= x - n < b2 + (b1 - b2) ) by lia.
         apply in_seq in H4.
         apply H3 in H4.
         inversion H4;  subst n0 y ts;try lia.
    ** constructor 1; try lia.
       apply Forall_forall.
       intros.
       apply H1;auto; try lia.
       unfold vars_outside_range'.
       apply Forall_forall.
       intros.
       assert (In (x1-n) (seq b2 (b1 - b2))). {
         apply in_seq.
         apply in_seq in H5.
         lia.
       }
       apply H3 in H6.
       apply in_seq in H5.
       inversion H6; subst n0 y ts.
       **** replace (x1 - n + n) with x1 in H11; try lia.
            eapply Forall_forall in H11;eauto 1.
       **** replace (x1 - n + n) with x1 in H11; try lia.
Qed.

(* Checks if variables up to the given position in the term, 
   are bound below the given bound [x]. *)
Inductive only_internal_vars_to (x:nat) : term -> position -> Prop :=
| only_internal_vars_to_nil t:
  only_internal_vars_to x t []
| only_internal_vars_to_cons n y ts hd tl t':
  nth_error ts hd = Some t' ->
  y < x+n ->
  only_internal_vars_to (x+n) t' tl ->
  only_internal_vars_to x (tm n y ts) (hd :: tl).


(* Checks if variables in the given interval, except the first one,
   are bound only within the same interval *)                        
Inductive only_in_interval (t:term) : interval -> Prop :=
| only_in_interval_witness from btw to n x ts t':
  get_subterm t from = tm n x ts -> (* the first variable is bound outside the interval *)
  nth_error ts btw = Some t' -> (* we reach to the beginning of the segment of interest *)
  only_internal_vars_to 0 t' to -> (* bindings up to [to] are local *)
  only_in_interval t pi[from, btw :: to].

(* end arena position TODO

Stirling:

The path m_1,..., m_2p is end in t if
1. m1 is a variable node,
2. for each i : 1 < i ≤ p, m2i−1 is a variable node whose binder occurs in the path,
3. every variable node below m_2p in t is bound by a node that either occurs above m1
or below m2p in t.

Here: in our represenation conditions 1 and 2 are for free since paths always point to a
subterm of the form \ xs.y[...]
 *)
Inductive end_path (t:term)  : interval -> Prop :=
| end_path_witness from btw to bf bt:
  has_position t (from ++ btw :: to) = true ->
  bf = get_subterm_bound t (from ++ [btw]) 0%nat ->
  bt = get_subterm_bound t (from ++ btw :: to) 0%nat ->
  only_in_interval t pi[from, btw :: to] ->
  vars_outside_range bf bt (get_subterm t (from++ btw :: to)) ->
  end_path t (pi[from, btw :: to]).

Lemma test_end_path:
  end_path main_solution' pi[[0;0], [0]].
Proof.
  repeat econstructor.
Qed.

Lemma test1_end_path:
  end_path main_solution' pi[[0;0], [1]].
Proof.
  repeat econstructor;lia.
Qed.


(* path that contributes TODO

Assume π ∈ G(t, E) and n_j is a lambda node. The interval π[i, j] contributes if [r_i] ≠ [r_j].
 *)
Inductive non_contributes : arena -> game_tree -> interval -> Prop :=
| contributes_helper_case a ap1 theta1 ap2 theta2 gtr gtrs1 gtrs2 from to r:
  get_subtree gtr from = (node (ap1, theta1) gtrs1) ->
  get_subtree gtr to = (node (ap2, theta2) gtrs2) ->
  solved a ap1 theta1 (node (ap1, theta1) gtrs1) r -> 
  solved a ap2 theta2 (node (ap2, theta2) gtrs2) r -> 
  non_contributes a gtr pi[from, to].

(* get all prefixes of the given list *)
Fixpoint list_prefixes {A : Type} (l : list A) : list (list A) :=
  match l with
  | [] => [[]]
  | a :: l' => [] :: map (cons a) (list_prefixes l')
  end.

Compute (list_prefixes [0;1;2]).

(* Get from the interval pi[startg, endg] position in the game tree gtr
   with the arena position (0, [pos]) *)
Definition find_position_in_game_tree_int (gtr:game_tree) startg endg pos :=
  find (fun pref =>
          let 'node ((tno, p), theta) chlds :=
            get_subtree gtr (startg ++ pref) in
          (tno =? 0) &&
            (forallb (fun '(x, y) => x =? y) (combine p pos)))%bool
    (list_prefixes endg).



(* redundant path in interval

TODO

- we assume that check that γ is an end_path is done outside this predicate

Stirling: 
Assume γ = m1 , . . . , m2p is an end path in t.

1. γ is redundant in the interval π[i, k] of π ∈ G(t, E) when:
(0) if π_j1 , j1 < k, is the first position after π_i with n_j1 = m_1 then
(a) there is a later position π_j, j ≤ k, and a chain π_j1,..., π_j_2p for πj where n_j = m_2p ,
(b) π[j_1 , j] does not contribute, and
(c) γ is redundant in the interval π[j, k].

 *)
Inductive redundant_path_interval (a : arena) (gtr : game_tree) : interval -> interval -> Prop :=
| redundant_interval_case  gtr' from_t to_t from_g to_g pos posend:
  get_subtree gtr from_g = gtr' ->
  find_position_in_game_tree_int gtr from_g to_g from_t = Some pos -> (* (0) *)
  find_position_in_game_tree_int gtr pos to_g (from_t ++ to_t) = Some posend -> (* (a) *)
  non_contributes a gtr pi[pos, posend] -> (* (b) *)
  redundant_path_interval a gtr pi[from_t, to_t] pi[posend, to_g] -> (* (c) *)
  redundant_path_interval a gtr pi[from_t, to_t] pi[from_g, to_g].

(*
2. γ is redundant in the game G(t, E) if γ is redundant in every play π[1, l] (where π_l is
the final position of π).
*)
Inductive redundant_path (a : arena) (gtr : game_tree) (t:term)  : interval -> Prop :=
| redundant_path_case from_t to_t:
  end_path t pi[from_t, to_t] ->
  (forall fp,                       (* TODO: maybe get all final positions, these are leaves *)
      is_final fp gtr -> 
      redundant_path_interval a gtr pi[from_t, to_t] pi[[], fp]) ->
  redundant_path a gtr t pi[from_t, to_t].
                 
(* transformation T2

Assume the end path m_1,..., m_2p is redundant in G(t, E). If t_0 is the
subterm whose root is the successor node of m_2p then transformation T2 is t[t_0/m_1].
 *)

Fixpoint trans_T2 (t:term) (intv : interval) (b:nat) : term :=
  let 'pi[m1, m2p] := intv in
  let 'tm n x ts := get_subterm t m1 in
  let 'tm m y ts' := get_subterm t (m1 ++ m2p) in
  let bound := get_subterm_bound (tm n x ts) m2p 0 in
  let ts'' := map (slide_term bound) ts' in
  replace_term (tm n (y-bound) ts'') m1 t.

(* let r be the rhs of
   t ts = r

  fragment is a term

  \x1...xn.r'

  where x1,...,xn are of base type,
  such that there are positions p0,p1,...,pn
  such that
  get_subtree r p0 = r'[x1 := get_subtree r p1,...,xn := get_subtree r pn]

  Main Theorem:

  Each subterm in t under the reduction of t ts normalizes to a fragment.
 *)

Notation "'pi[' a ',' b ']_' TS " := (intvl TS a b) (at level 20).

(* a as applicative term *)
Definition ex1_rhs := node 0 [].

(* g a *)
Definition result :=
  node 1 [node 0 []].


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



Lemma solved_Stirling' : exists g, solved_start g main_solution' [arg1; arg2] result.
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


Lemma solved_Stirling'' : exists g, solved_start g main_solution'' [arg1; arg2] result.
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



Lemma solved_Stirling''' : exists g, solved_start g main_solution''' [arg1; arg2] result.
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


