Require Import List ssreflect.
Import ListNotations.
Require Import PeanoNat.
Require Import Nat Lia.


Require Import HOM.RoseTree.
Import HOM.RoseTree.


Notation term := (rose_tree (nat * nat)).

(* increment all free variables by k *)
Definition shift_term (k : nat) (t : term) : term :=
  map_tree_dependent (fun l '(n, x) => let bound := list_sum (map fst l) in (n, if bound <=? x then k + x else x)) t.

(* place term t' at position p in t *)
Definition replace_term (t' : term) (p : position) (t : term) : term :=
  let bound := list_sum (map fst (get_branch t p)) in
  replace_subtree (shift_term bound t') p t.




Definition get_depth (t : term) := get_tree_depth t.


(* compute the subterm of [t] at position [p] *)
Definition get_subterm (t : term) (p : position) : term :=
  get_subtree t p.

Definition get_subterm_error (t : term) (p : position) : option term :=
  get_subtree_error t p.

Arguments get_subterm_error /.


(* compute the subterm of [t] at position [p] *)

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


Fixpoint fold_tree_dependent {A B : Type} (f : list A -> A -> list B -> B) (tr : rose_tree A) : B :=
  match tr with
  | node v children => f [] v (map (fold_tree_dependent (fun l => f (v :: l))) children)
  end.

Definition fold_tree {A B : Type} (f : A -> list B -> B) (tr : rose_tree A) : B :=
  fold_tree_dependent (fun _ => f) tr.

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
      | Some t => get_subterm_error t p
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
      length gs = length ts ->
      Forall (fun t => match t with tm nt _ _ => nt = 0 end) ts ->
      (forall g j r, In (g, (j, r)) (combine gs (combine (seq 0 (length rs)) rs)) ->
        solved (extend_ap ap [j]) theta g r) ->
      solved ap theta (node (ap, theta) gs) (node x rs).

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

Definition get_binders (t : term) :=
  match t with node (n, _) _ => n end.

(* t ts = r *)
Definition solved_start g t (ts : list term) (r : rose_tree nat) :=
  length ts = get_binders t /\
  solved (t :: ts) (0, []) (map (fun j => ((S j, []), lk [])) (rev (seq 0 (length ts)))) g r.


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

Definition trans_T1 (t:term) (p:position) (t':term) : term :=
  replace_term t' p t.


Scheme Equality for list.

Definition check_occurrence (p:position) :=
  fun (nd:aposition*lookup_contents) (acc:list bool) => let '((no, p'),_) := nd in 
                                         if (no =? 1) && (list_beq nat eqb p p')
                                         then true
                                         else fold_left (fun bacc el => bacc || el)%bool  acc false.

(* TODO: lemma s.t. we replace with any term

If we have a game tree for an arena s.t. position p does not occur in
g.tr. then if we replace the subterm at p with any term, the resulting
term is a solution.

 *)

Fixpoint get_apositions (gtr: game_tree) : list aposition :=
  match gtr with
  | node (ap, _) children => ap :: flat_map get_apositions children
  end.

Inductive locally_equivalent : option term -> option term -> Prop :=
  | locally_equivalent_Some n_x ts ts' : length ts = length ts' -> locally_equivalent (Some (node n_x ts)) (Some (node n_x ts'))
  | locally_equivalent_None : locally_equivalent None None.

Lemma locally_equivalent_elim ot ot' n x args : 
  locally_equivalent ot ot' ->
  ot = Some (tm n x args) ->
  exists args', length args = length args' /\ ot' = Some (tm n x args').
Proof.
  case=> >; last done.
  move=> ? [*]. subst.
  eexists. by split; last done.
Qed.

Arguments in_combine_l {A B l l' x y}.
Arguments in_split {A x l}.

Lemma get_arena_subterm_extend_ap ts ap n x rs j:
  get_arena_subterm ts ap = Some (tm n x rs) ->
  get_arena_subterm ts (extend_ap ap [j]) = nth_error rs j.
Proof.
  move: ap => [i p] /=.
  move: (nth_error ts i)=> [t|]; last done.
  rewrite get_subtree_error_app=> -> /=.
  by case: (nth_error rs j).
Qed.

Lemma combine_map {A B A' B' : Type} (f : A -> A') (g : B -> B') (l1 : list A) (l2 : list B) :
  combine (map f l1) (map g l2) = map (fun ab => (f (fst ab), g (snd ab))) (combine l1 l2).
Proof.
  elim: l1 l2; first done.
  move=> a l1 IH [|b l2]; first done.
  by rewrite /= IH.
Qed.

Lemma locally_equivalent_solved ts ts' ap theta gtr res:
  solved ts ap theta gtr res ->
  Forall (fun ap' => locally_equivalent (get_arena_subterm ts ap') (get_arena_subterm ts' ap')) (get_apositions gtr) ->
  solved ts' ap theta gtr res.
Proof.
  move=> H. elim: H ts'.
  - move=> {}ap {}theta n x args nap theta' {}gtr r.
    move=> /locally_equivalent_elim Hap Hx Hgtr IH ts' /=.
    move=> /Forall_cons_iff [/Hap [?] [H'args H'ap]] /Forall_app [/IH] + _.
    rewrite H'args. by apply: solved_var; eassumption.
  - move=> {}ap {}theta gs n x {}rs' rs.
    move=> /[dup] H''ap /locally_equivalent_elim Hap Hlen H'len Hrs' IH' IH ts' /=.
    move=> /Forall_cons_iff [/Hap [rs''] [H'rs'' H'ap]] Hgs.
    apply: solved_const.
    + eassumption.
    + by rewrite -H'rs''.
    + by rewrite -H'rs''.
    + (* the game will continue in subtrees, which are also locally equivalent *)
      have Hrs'': forall g j r,
        In (g, (j, r)) (combine gs (combine (seq 0 (length rs')) rs)) ->
        locally_equivalent (nth_error rs' j) (nth_error rs'' j).
      { move=> g j r. rewrite !Hlen.
        move: H''ap => /get_arena_subterm_extend_ap <-.
        move: H'ap => /get_arena_subterm_extend_ap <-.
        move=> /[dup] Hgjr /IH' {}IH'.
        move: Hgs => /Forall_forall. apply.
        move: (extend_ap ap [j]) IH' => ? IH'.
        move: Hgjr=> /in_combine_l /in_split [?] [?] ?. subst gs.
        rewrite flat_map_app /=.
        apply: in_or_app. right. apply: in_or_app. left.
        by case: IH'=> * /=; left. }
      move: Hrs' Hlen H'len H'rs'' Hrs''. clear=> Hrs'.
      elim: Hrs' rs'' gs rs; first by case.
      move=> [[??]?] ? -> _ IH'' [|[[??]?] ?]; first done.
      move=> [|? gs]; first done.
      move=> [|? rs]; first done.
      move=> /= [/IH'' {}IH''] [/IH'' {}IH''] [/IH'' {}IH''] Hequiv. constructor.
      * move: (Hequiv _ 0 _ (or_introl eq_refl)) => /= H.
        by inversion H.
      * apply: IH'' => ? j ? H. apply: (Hequiv _ (S j) _). right.
        rewrite -seq_shift -(map_id rs) -(map_id gs) !combine_map.
        apply /in_map_iff. eexists. by split; last by eassumption.
    + move=> g j r Hgjr. apply: IH; first done.
      move: Hgjr => /in_combine_l /in_split [?] [?] ?. subst gs.
      rewrite flat_map_app in Hgs.
      by move: Hgs => /Forall_app [?] /= /Forall_app [].
Qed.

Arguments node {A}.

Lemma solved_ap_in_get_apositions ts ap theta gtr res:
  solved ts ap theta gtr res ->
  In ap (get_apositions gtr).
Proof.
  case; by left.
Qed.

Fixpoint get_apositions_lk (l : lookup) : list aposition :=
  match l with
  | lk theta => map fst theta ++ flat_map (fun c => get_apositions_lk (snd c)) theta
  end.

Arguments nth_error_In {A l n x}.

(* list lemma not in stdlib *)
Lemma in_combine_intro_l {A B : Type} {b : B} l1 l2  :
  length l1 = length l2 ->
  In b l2 -> exists (a : A), In a l1 /\ In (a, b) (combine l1 l2).
Proof.
  elim: l1 l2.
  - by case.
  - move=> a l1 IH [|b' l2]; first done.
    move=> /= [] /IH {}IH [|].
    + move=> <-. exists a. split; tauto.
    + move=> /IH [a'] [??]. exists a'. split; tauto.
Qed.

(* list lemma not in stdlib *)
Lemma in_combine_intro_r {A B : Type} {a : A} l1 l2  :
  length l1 = length l2 ->
  In a l1 -> exists (b : B), In b l2 /\ In (a, b) (combine l1 l2).
Proof.
  elim: l2 l1.
  - by case.
  - move=> b l2 IH [|a' l1]; first done.
    move=> /= [] /IH {}IH [|].
    + move=> <-. exists b. split; tauto.
    + move=> /IH [b'] [??]. exists b'. split; tauto.
Qed.

Lemma in_get_apositions_lk_intro ap (theta : lookup_contents) ap' theta':
  In (ap', theta') theta ->
  In ap (get_apositions_lk theta') ->
  In ap (get_apositions_lk (lk theta)).
Proof.
  cbn. move=> /in_split [?] [?] -> ?.
  rewrite map_app flat_map_app /=.
  apply /in_app_iff. right.
  apply /in_app_iff. right.
  apply /in_app_iff. by left.
Qed.

(* an aposition in the game tree is either
   the start,
   occurs the lookup table,
   or its direct prefix occurs in the game tree *)
Lemma solved_ap_cone ts ap (theta : lookup_contents) gtr res ap':
  solved ts ap theta gtr res ->
  In ap' (get_apositions gtr) ->
    ap = ap' \/
    In ap' (get_apositions_lk (lk theta)) \/
    exists ap'' j, ap' = extend_ap ap'' [j] /\ In ap'' (get_apositions gtr).
Proof.
  elim.
  - move=> {}ap > ? Htheta _ IH /= [|]; first by tauto.
    move=> /in_app_iff [|]; last done.
    move=> /IH /= [?|[|]].
    + subst. right. left.
      apply /in_app_iff. left.
      apply /in_map_iff.
      move: Htheta => /nth_error_In ?.
      eexists. by split; last by eassumption.
    + rewrite !map_app flat_map_app. move=> /in_app_iff [/in_app_iff [|]|/in_app_iff [|]].
      * rewrite map_map /=.
        destruct ap. cbn.
        move=> /in_map_iff [?] [<- _]. do 2 right. eexists (n, p), _.
        split; first done. by left.
      * move: Htheta => /nth_error_In ?.   
        move=> ?. right. left.
        apply: in_get_apositions_lk_intro; first by eassumption.
        cbn. apply /in_app_iff. by left.
      * destruct ap. move=> /in_flat_map [?] [/in_map_iff] [?] [<-] _ /=. tauto.
      * move: Htheta => /nth_error_In ?.   
        move=> ?. right. left.
        apply: in_get_apositions_lk_intro; first by eassumption.
        cbn. apply /in_app_iff. by right.
    + rewrite app_nil_r.
      move=> [?] [?] [-> ?]. do 2 right.
      eexists _, _. split; first done. by right.
  - move=> ?????? rs ? Ets Egs ? ? IH /= [|]; first by tauto.
    move=> /in_flat_map [g] [Hg] /IH {}IH.
    move: (Hg)=> /(in_combine_intro_r _ (combine (seq 0 (length rs)) rs)).
    rewrite length_combine length_seq Nat.min_id Egs.
    move=> /(_ Ets) [[??]] [?] /IH /= [?|[?|]].
    + subst. do 2 right. eexists _, _.
      split; first done. by left.
    + tauto.
    + move=> [?] [?] [->] ?. do 2 right. eexists _, _.
      split; first done. right.
      apply /in_flat_map. eexists. by split; last by eassumption.
Qed.

(* apositions form a cone in a full game tree *)
Lemma solved_start_ap_cone ts p (theta : lookup_contents) gtr res :
  solved ts (0, []) theta gtr res ->
  In (0, p) (get_apositions gtr) ->
  Forall (fun ap => fst ap <> 0) (get_apositions_lk (lk theta)) ->
  forall i, In (0, firstn i p) (get_apositions gtr).
Proof.
  move=> /solved_ap_cone Hgtr + /Forall_forall Htheta.
  elim /rev_ind: p.
  - by move=> ? [|?].
  - move=> j {}p IH /[dup] /Hgtr [|[|]].
    + by case: p {IH}.
    + by move=> /Htheta.
    + move=> [[??]] [?] [[]] <- /app_inj_tail_iff [<- _] /IH {}IH ? i.
      have [|]: length (p ++ [j]) <= i \/ i < length (p ++ [j]) by lia.
      * by move=> /firstn_all2 ->.
      * rewrite firstn_app length_app /= => ?.
        have ->: i - length p = 0 by lia.
        rewrite /= app_nil_r.
        apply: IH.
Qed.

Lemma locally_equivalent_refl ot: locally_equivalent ot ot.
Proof.
  move: ot=> [[]|]; by constructor.
Qed.

(* application of locally_equivalent_solved *)
Lemma trans_T1_correct t args gtr res p t':
  solved_start gtr t args res ->
  not (In (0, p) (get_apositions gtr)) -> (* p does not occur in gtr *)
  solved_start gtr (trans_T1 t p t') args res.
Proof.
  move=> /= [Hargs] /[dup] H''gtr /locally_equivalent_solved Hgtr H'gtr.
  split.
  - rewrite Hargs.
    move: p t {Hargs Hgtr} H'gtr H''gtr => [].
    + by move=> ? H /solved_ap_in_get_apositions /H.
    + by move=> ?? [[??]?] /=.
  - apply: Hgtr. apply /Forall_forall=> - [[|i] p'].
    + move: H''gtr => /solved_start_ap_cone /= /[apply] H''gtr.
      have: forall i, firstn i p' <> p.
      { move=> i Hp. apply: H'gtr. subst p.
        apply: H''gtr. apply /Forall_app. split.
        - by apply /Forall_map /Forall_map /Forall_forall=> ? /=.
        - apply /Forall_forall=> - [??] /in_flat_map [?].
          by move=> [/in_map_iff] [?] [<-] ? /=. }
      rewrite /trans_T1 /replace_term.
      elim: p' p t (shift_term _ _) {Hargs H'gtr H''gtr}.
      * move=> [|i p] [[??] ts] {}t' /=; first by move=> /(_ 0).
        move=> /= _. rewrite /get_subterm /replace_term /=.
        constructor. by rewrite length_map_nth.
      * move=> j' p' IH [|j p] [v ts] {}t' /=; first by move=> /(_ 0).
        rewrite /get_subterm /=.
        have [|]: j = j' \/ j <> j' by lia.
        ** move=> <- Hp. rewrite /=. rewrite nth_error_map_nth_eq.
           case: (nth_error ts j)=> /=.
           *** move=> t''. apply: IH.
               move=> i Hi. apply: (Hp (S i)). cbn. by rewrite Hi.
           *** by constructor.
        ** move=> ? _. rewrite nth_error_map_nth_neq; first done.
           case: (nth_error ts j').
           *** move=> ?. by apply: locally_equivalent_refl.
           *** by constructor.
    + move=> ?. by apply: locally_equivalent_refl.
Qed.

Lemma test_trans_T1_ex1_0: trans_T1 ex1_0 [] (tm 1 1 []) = ex1_2.
Proof.
  now compute.
Qed.

Lemma test_trans_T1_main_solution_1: trans_T1 main_solution []  (tm 2 2 []) = (tm 2 2 []).
Proof.
  now simpl.
Qed.

Lemma test_trans_T1_main_solution_2: trans_T1 main_solution [0] (tm 0 0 []) = (tm 2 0 [tm 0 2 []]).
Proof.
  now simpl.
Qed.

Lemma test_trans_T1_main_solution_3: trans_T1 main_solution [0;0] (tm 0 70 []) = (tm 2 0 [tm 2 3 [tm 0 74 []; tm 0 1 []]]).
Proof.
 now simpl.
Qed.



(* end arena position TODO

The path m1 , . . . , m2p is end in t if
1. m1 is a variable node,
2. for each i : 1 < i ≤ p, m2i−1 is a variable node whose binder occurs in the path,
3. every variable node below m2p in t is bound by a node that either occurs above m1
or below m2p in t.

 *)

(* path that contributes TODO

Assume π ∈ G(t, E) and nj is a lambda node. The interval π[i, j] contributes if [ri ] 6= [rj ].

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
  - cbn. apply: (solved_const _ _ _ []).
    + cbn. reflexivity.
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

  rewrite [length _]/=. apply: (solved_const _ _ _ [_]); [repeat constructor..|].
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


  rewrite [length _]/=. apply: (solved_const _ _ _ []); [repeat constructor..|].
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

  rewrite [length _]/=. apply: (solved_const _ _ _ [_]); [repeat constructor..|].
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


  rewrite [length _]/=. apply: (solved_const _ _ _ []); [repeat constructor..|].
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

  rewrite [length _]/=. apply: (solved_const _ _ _ [_]); [repeat constructor..|].
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


  rewrite [length _]/=. apply: (solved_const _ _ _ []); [repeat constructor..|].
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

  rewrite [length _]/=. apply: (solved_const _ _ _ [_]); [repeat constructor..|].
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


  rewrite [length _]/=. apply: (solved_const _ _ _ []); [repeat constructor..|].
  done.
Qed.
