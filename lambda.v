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
  | lk : list (option (aposition * lookup)) -> lookup.

Definition lookup_contents := list (option (aposition * lookup)).

Definition add_lk (ap:aposition) (theta : lookup_contents) (j : nat) :=
  let '(i, p) := ap in
    Some ((i, p ++ [j]), lk theta).

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


Definition get_binders (t : term) :=
  match t with node (n, _) _ => n end.

Definition get_var (t : term) :=
  match t with node (_, x) _ => x end.

Definition get_args (t : term) :=
  match t with node _ args => args end.

(* look up the assignment of a variable *)
Definition lookup_var (theta : lookup_contents) (x : nat) :=
  match nth_error theta x with
  | Some (Some v) => Some v
  | _ => None
  end.

(*
  solved ap theta n game_tree means
  - at position ap in the arena TS
  - with the lookup table theta
  - with n many abstractions
    if there are n + k many abstractions at ap, then then theta is extended by k many free variables
  - the game represented by game_tree is well-formed
*)

(* evaluation semantics *)
(*
Inductive eval : term -> list (option term) -> term -> Prop :=
  | eval_lams x args n theta n' x' args': 
    eval (tm 0 x args) (repeat None (S n) ++ theta) (tm n' x' args') ->
    eval (tm (S n) x args) theta (tm (n' + S n) x' args')
  | eval_var x theta ap theta' n:
    nth_error theta x = Some (Some (tm n' x' args')) ->
    n' = length args ->
    eval (tm 0 x' args') (args ++ theta) r
    eval (tm 0 x args) theta r.

  | eval_var x theta ap theta' n:
    lookup_var theta x = Some (ap', theta') ->
    get_arena_subterm TS ap' = Some (tm n' x' args') ->
    n' = length args ->
    eval (tm 0 x' args') (args ++ theta') r
    eval (tm 0 x args) theta r.
  | eval_const theta x rs args :
    lookup_var theta x = None ->
    length rs = length args ->
    (forall i arg r, nth_error args i = Some arg -> nth_error rs i = Some r -> eval arg theta r) ->
    eval (tm 0 x args) theta (tm 0 x rs).
*)

Inductive solved (ap : aposition) (theta : lookup_contents) :
  nat -> rose_tree (aposition * lookup_contents) -> Prop :=
    | solved_var k n x args ap' theta' g:
      get_arena_subterm TS ap = Some (tm (n + k) x args) -> (* get subarena at position ap *)
      n * k = 0 -> (* there is no partial application *)
      lookup_var (repeat None k ++ theta) x = Some (ap', lk theta') -> (* get interpretation of x *)
      (* check that at ap' there are "length args" many abstractions *)
      solved ap' ((map (add_lk ap (repeat None k ++ theta)) (seq 0 (length args))) ++ theta') (length args) g ->
      (* (map (add_lk ap theta) (seq 0 (length args))) - uses arguments of x
         to interpret variables abstracted in the interpretation of x *)
      solved ap theta n (node (ap, repeat None k ++ theta) [g])

    | solved_const k n x args gs:
      get_arena_subterm TS ap = Some (tm (n + k) x args) ->
      n * k = 0 -> (* there is no partial application *)
      lookup_var (repeat None k ++ theta) x = None ->
      length gs = length args ->
      (forall j g, nth_error gs j = Some g -> solved (extend_ap ap [j]) (repeat None k ++ theta) 0 g) ->
      solved ap theta n (node (ap, repeat None k ++ theta) gs).

(*
theta not option, but left/right
left ~> bound variable
right ~> number of abstractions?
*)

(* TODO maybe wrong *)
Fixpoint compute_const (theta : lookup_contents) (x : nat) : option nat :=
  match theta with
  | [] => Some x
  | None :: theta' =>
    match x with
    | 0 => Some 0
    | S x' => option_map S (compute_const theta' x')
    end
  | Some _ :: theta' =>
    match x with
    | 0 => None
    | S x' => compute_const theta' x'
    end
  end.

Inductive solved_rhs (ap : aposition) (theta : lookup_contents) :
  nat -> rose_tree (aposition * lookup_contents) -> term -> Prop :=
    | solved_rhs_var k n x args ap' theta' g y rs:
      get_arena_subterm TS ap = Some (tm (n + k) x args) -> (* get subarena at position ap *)
      lookup_var (repeat None k ++ theta) x = Some (ap', lk theta') -> (* get interpretation of x *)
      (* check that at ap' there are "length args" many abstractions *)
      solved_rhs ap' ((map (add_lk ap (repeat None k ++ theta)) (seq 0 (length args))) ++ theta') (length args) g (tm 0 y rs) ->
      (* (map (add_lk ap theta) (seq 0 (length args))) - uses arguments of x
         to interpret variables abstracted in the interpretation of x *)
      solved_rhs ap theta n (node (ap, repeat None k ++ theta) [g]) (tm k y rs)

    | solved_rhs_const k n x args gs y rs:
      get_arena_subterm TS ap = Some (tm (n + k) x args) ->
      length gs = length args ->
      length rs = length args ->
      (forall j g r, nth_error gs j = Some g -> nth_error rs j = Some r ->
        solved_rhs (extend_ap ap [j]) (repeat None k ++ theta) 0 g r) ->
      compute_const (repeat None k ++ theta) x = Some y ->
      solved_rhs ap theta n (node (ap, repeat None k ++ theta) gs) (tm k y rs).

(*
Fixpoint get_rhs (gtr : rose_tree (aposition * lookup_contents)) : option term :=
  match gtr with
  | node (ap, theta) gs =>
    match get_arena_subterm TS ap with
    | Some (tm n x ts) =>
      match (S x) - length theta with
      | 0 => (* if x is a variable, continue with the subtree - case "solved_var" *)
        match gs with
        | [g] => get_rhs g
        | _ => None
        end
      | S j => (* if x is a constant, continue with the subtrees - case "solved_const" *)
        match sequence get_rhs gs with
        | Some rs => Some (node j rs)
        | None => None
        end
      end
    | None => None
    end
  end.
*)

(* "is_rhs b gt r" means that the term "r" is the unique rhs corresponding to the game tree "gt"
   the argument "b" specifies whether "r" has abstractions *)

Inductive is_rhs (b : bool): rose_tree (aposition * lookup_contents) -> term -> Prop :=
  | is_rhs_var ap theta n x y args gt rs :
    get_arena_subterm TS ap = Some (tm n x args) ->
    compute_const theta x = None -> (* x points to a variable *)
    is_rhs false gt (tm 0 y rs) ->
    is_rhs b (node (ap, theta) [gt]) (tm (if b then n else 0) y rs)
  | is_rhs_const ap theta n x ts y gs rs :
    get_arena_subterm TS ap = Some (tm n x ts) ->
    compute_const theta x = Some y -> (* x points to a constant *)
    (* TODO is the computed index y correct? need to flatten theta? e.g. what if theta points to a const *)
    (* consider this: the abstractions always come immediately after a constant *)
    (* maybe the game tree needs to contain the number of abstractions as information?
       or do we track this via an argument? *)
    length gs = length rs ->
    (forall j g r, nth_error gs j = Some g -> nth_error rs j = Some r -> is_rhs true g r) ->
    is_rhs b (node (ap, theta) gs) (tm (if b then n else 0) y rs).
    (*
  | is_rhs_inner_var ap theta n x ts gs rs:
    get_arena_subterm TS ap = Some (tm n x ts) ->
    nth_error theta x = Some None -> 
    (* x points to an inner var, bound variable which is not substituted *)
    length gs = length ts ->
    (forall j g r, nth_error gs j = Some g -> is_rhs g r) ->
    is_rhs (node (ap, theta) gs) (tm n rs).
    

*)
(*
Fixpoint sequence {A B} (f : A -> option B) (l : list A) : option (list B) :=
  match l with
  | [] => Some []
  | hd :: tl =>
    match f hd with
    | Some b => match sequence f tl with Some bs => Some (b :: bs) | None => None end
    | None => None
    end
  end.

(* compute the unique rhs from a given game tree *)
Fixpoint get_rhs (gtr : rose_tree (aposition * lookup_contents)) : option (rose_tree nat) :=
  match gtr with
  | node (ap, theta) gs =>
    match get_arena_subterm TS ap with
    | Some (tm n x ts) =>
      match (S x) - length theta with
      | 0 => (* if x is a variable, continue with the subtree - case "solved_var" *)
        match gs with
        | [g] => get_rhs g
        | _ => None
        end
      | S j => (* if x is a constant, continue with the subtrees - case "solved_const" *)
        match sequence get_rhs gs with
        | Some rs => Some (node j rs)
        | None => None
        end
      end
    | None => None
    end
  end.
*)
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

(* t ts = r *)
Definition solved_start g t (ts : list term) :=
  length ts = get_binders t /\
  solved (t :: ts) (0, []) (map (fun j => Some ((S j, []), lk [])) (rev (seq 0 (length ts)))) (length ts) g.

Definition solved_start_full g t (ts : list term) (r : term) :=
  solved_start g t ts /\
  is_rhs (t :: ts) false g r.

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
  fun (nd:aposition*lookup_contents) (acc:list bool) => let '((no, p'),_) :=  nd in 
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

Arguments nth_error_In {A l n x}.

Lemma locally_equivalent_solved ts ts' ap theta n gtr:
  solved ts ap theta n gtr ->
  Forall (fun ap' => locally_equivalent (get_arena_subterm ts ap') (get_arena_subterm ts' ap')) (get_apositions gtr) ->
  solved ts' ap theta n gtr.
Proof.
  move=> H. elim: H ts'.
  - move=> {}ap {}theta k {}n x args nap theta' {}gtr.
    move=> /locally_equivalent_elim Hap Hnk Hx Hgtr IH ts' /=.
    move=> /Forall_cons_iff [/Hap [?] [H'args H'ap]] /Forall_app [/IH] + _.
    rewrite H'args. by apply: solved_var; eassumption.
  - move=> {}ap {}theta k {}n x args gs.
    move=> /[dup] H''ap /locally_equivalent_elim Hap Hnk Hx Hlen IH' IH ts' /=.
    move=> /Forall_cons_iff [/Hap [ts''] [H'ts'' H'ap]] /Forall_flat_map Hgs.
    apply: solved_const.
    + eassumption.
    + done.
    + done.
    + by rewrite -H'ts''.
    + move=> j g /[dup] /nth_error_In ? Hg. apply: IH; first done.
      move: Hgs => /Forall_forall. by apply.
Qed.

Arguments node {A}.

Lemma solved_ap_in_get_apositions ts ap theta n gtr:
  solved ts ap theta n gtr ->
  In ap (get_apositions gtr).
Proof.
  case; by left.
Qed.

Fixpoint get_apositions_lk (l : lookup) : list aposition :=
  match l with
  | lk theta => flat_map (fun c => match c with Some (ap', theta') => ap' :: get_apositions_lk theta' | None => [] end) theta
  end.

Arguments nth_error_In {A l n x}.

Lemma in_get_apositions_lk_intro ap (theta : lookup_contents) ap' theta':
  In (Some (ap', lk theta')) theta ->
  In ap (get_apositions_lk (lk theta')) ->
  In ap (get_apositions_lk (lk theta)).
Proof.
  cbn. move=> /in_split [?] [?] -> ?.
  rewrite flat_map_app /=.
  apply /in_app_iff. right.
  right.
  apply /in_app_iff. by left.
Qed.

Lemma loopup_var_Some k theta x v :
  lookup_var (repeat None k ++ theta) x = Some v ->
  exists n, x = n + k /\ nth_error theta n = Some (Some v).
Proof.
  rewrite /lookup_var.
  have [?|?]: x < k \/ k <= x by lia.
  - rewrite nth_error_app1 ?repeat_length; first done.
    by rewrite nth_error_repeat.
  - rewrite nth_error_app2 ?repeat_length; first done.
    case E: (nth_error theta (x - k)) => [ov|]; last done.
    case E': ov=> [v'|]; last done.
    move=> [<-]. subst.
    eexists. split; last by eassumption.
    lia.
Qed.

Arguments In_nth_error {A l x}.
Arguments repeat_spec {A n x y}.

(* an aposition in the game tree is either
   the start,
   occurs the lookup table,
   or its direct prefix occurs in the game tree *)
Lemma solved_ap_cone ts ap (theta : lookup_contents) n gtr ap':
  solved ts ap theta n gtr ->
  In ap' (get_apositions gtr) ->
    ap = ap' \/
    In ap' (get_apositions_lk (lk theta)) \/
    exists ap'' j, ap' = extend_ap ap'' [j] /\ In ap'' (get_apositions gtr).
Proof.
  elim.
  - move=> {}ap > ?? Htheta _ IH /= [|]; first by tauto.
    move=> /in_app_iff [|]; last done.
    move=> /IH /= [?|[|]].
    + subst. right. left.
      move: Htheta=> /loopup_var_Some [n'] [?] /nth_error_In ?. subst.
      apply /in_flat_map. eexists.
      split; first by eassumption.
      by left.
    + rewrite flat_map_app. move=> /in_app_iff [|].
      * rewrite flat_map_concat_map map_map /= -flat_map_concat_map.
        destruct ap. cbn.
        move=> /in_flat_map [?] [_] /= [?|].
        ** subst. right. right. eexists _, _. by split; last by left.
        ** rewrite flat_map_app. move=> /in_app_iff [|]; last by tauto.
           by move=> /in_flat_map [?] [/repeat_spec] ->.
      * move=> /in_get_apositions_lk_intro H.
        right. left. apply: H.
        move: Htheta=> /loopup_var_Some [n'] [?] /nth_error_In ?. subst.
        by eassumption.
    + rewrite app_nil_r.
      move=> [?] [?] [-> ?]. do 2 right.
      eexists _, _. split; first done. by right.
  - move=> ??????? Ets ? Hx Egs ? IH /= [|]; first by tauto.
    move=> /in_flat_map [g] [Hg] /IH {}IH.
    move: (Hg) => /In_nth_error [j] /IH [?|[|]].
    + subst. do 2 right. eexists _, _.
      split; first done. by left.
    + rewrite /= flat_map_app. move=> /in_app_iff [|]; last by tauto.
      by move=> /in_flat_map [?] [/repeat_spec] ->.
    + move=> [?] [?] [->] ?. do 2 right. eexists _, _.
      split; first done. right.
      apply /in_flat_map. eexists. by split; last by eassumption.
Qed.

(* apositions form a cone in a full game tree *)
Lemma solved_start_ap_cone ts p (theta : lookup_contents) n gtr :
  solved ts (0, []) theta n gtr ->
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
Lemma trans_T1_correct t args gtr p t':
  solved_start gtr t args ->
  not (In (0, p) (get_apositions gtr)) -> (* p does not occur in gtr *)
  solved_start gtr (trans_T1 t p t') args.
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
        apply: H''gtr. apply /Forall_flat_map /Forall_map /Forall_forall=> ? /=.
        by constructor. }
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

(*
Notation "'pi[' a ',' b ']_' TS " := (intvl TS a b) (at level 20).
*)

(* a as applicative term *)
Definition ex1_rhs := tm 0 0 [].

Lemma solved_ex1 : exists g, solved_start_full g ex1_0 [ex1_1] ex1_rhs.
Proof.
  eexists. split.
  { cbn. split; [reflexivity|].
    apply: solved_var.
    - cbn. reflexivity.
    - cbn. reflexivity.
    - cbn. reflexivity.
    - cbn. apply: (solved_const _ _ _ _ _ _ _ []).
      + cbn. reflexivity.
      + cbn. reflexivity.
      + cbn. reflexivity.
      + cbn. reflexivity.
      + cbn. now intros [|?]. }
  cbn. apply: is_rhs_var.
  - cbn. reflexivity.
  - cbn. reflexivity.
  - apply: is_rhs_const.
    + cbn. reflexivity.
    + cbn. reflexivity.
    + cbn. reflexivity.
    + cbn. now intros [|?].
Qed.

(* \xy.x (\p. y p) *)
Definition ex3_0 :=
  tm 2 1 [tm 1 1 [tm 0 0 []]].

(* \z.f (\q. z q) *)
Definition ex3_1 :=
  tm 1 1 [tm 1 1 [tm 0 0 []]].

(* \x.x *)
Definition ex3_2 :=
  tm 1 0 [].

(* f (\x.x) *)
Definition ex3_rhs :=
  tm 0 0 [tm 1 0 []].

Lemma solved_ex3 : exists g, solved_start_full g ex3_0 [ex3_1; ex3_2] ex3_rhs.
Proof.
  eexists. split.
  { split; [reflexivity|].
    apply: solved_var; [reflexivity..|].

    rewrite [length _]/=. apply: (solved_const _ _ _ _ _ _ _ [_]); [reflexivity..|].
    move=> [|[|?]] ?; [|done..] => - [<-].

    apply: solved_var; [reflexivity..|].
    rewrite [length _]/=. apply: solved_var; [reflexivity..|].
    rewrite [length _]/=. apply: solved_var; [reflexivity..|].
    rewrite [length _]/=. apply: solved_var; [reflexivity..|].

    rewrite [length _]/=. apply: (solved_const _ _ _ _ _ _ _ []); [reflexivity..|].
    by case. }

  cbn.
  apply: is_rhs_var; [reflexivity..|].
  apply: is_rhs_const; [reflexivity..|].
  move=> [|[|?]] ??; [|done..] => - [<-] [<-].
  do 4 (apply: is_rhs_var; [reflexivity..|]).
  apply: is_rhs_const; [reflexivity..|].
  by case.
Qed.

(* \s.s (s (s a)) *)
Definition ex4_0 :=
  tm 1 0 [tm 0 0 [tm 0 0 [tm 0 1 []]]].

(* \n.f (\x. n) *)
Definition ex4_1 :=
  tm 1 2 [tm 1 1 []].

(* f (\x1.f (\x2. f (\x3. a))) *)
Definition ex4_rhs :=
  tm 0 1 [tm 1 2 [tm 1 3 [tm 1 4 [tm 0 3 []]]]].

Lemma solved_ex4 : exists g, solved_start_full g ex4_0 [ex4_1] ex4_rhs.
Proof.
  eexists. split.
  { split; [reflexivity|].
    apply: solved_var; [reflexivity..|].

    rewrite [length _]/=. apply: (solved_const _ _ _ _ _ _ _ [_]); [reflexivity..|].
    move=> [|[|?]] ?; [|done..] => - [<-].

    apply: solved_var; [reflexivity..|].
    rewrite [length _]/=. apply: solved_var; [reflexivity..|].

    rewrite [length _]/=. apply: (solved_const _ _ _ _ _ _ _ [_]); [reflexivity..|].
    move=> [|[|?]] ?; [|done..] => - [<-].

    apply: solved_var; [reflexivity..|].
    rewrite [length _]/=. apply: solved_var; [reflexivity..|].

    rewrite [length _]/=. apply: (solved_const _ _ _ _ _ _ _ [_]); [reflexivity..|].
    move=> [|[|?]] ?; [|done..] => - [<-].

    apply: solved_var; [reflexivity..|].
    rewrite [length _]/=. apply: (solved_const _ _ _ _ _ _ _ []); [reflexivity..|].
    by case. }

  cbn.
  apply: is_rhs_var; [reflexivity..|].
  apply: is_rhs_const; [reflexivity..|].
  move=> [|[|?]] ??; [|done..] => - [<-] [<-].

  do 2 (apply: is_rhs_var; [reflexivity..|]).

  apply: is_rhs_const; cbn.
  - reflexivity.
  - cbn. (* wrong index of the free variable *)
Abort.

(* \sz2.s (\z1.s (\z0.s (\x.x) z0) z1) z2 *)
Definition ex5_0 :=
  tm 2 1 [tm 0 0 []; tm 1 2 [tm 0 0 []; tm 1 3 [tm 0 0 []; tm 1 0 []]]].

(* 
  f : (a -> a) -> a
  g : a -> a -> a
*)
(* \ny. f (\x. n (g y x)) *)
Definition ex5_1 :=
  tm 2 2 [tm 1 2 [tm 0 4 [tm 0 0 []; tm 0 1 []]]].

(* h *)
Definition ex5_2 :=
  tm 0 2 [].

(* f (\x2.f (\x1. f (\x0. g (g (g h x2) x1) x0))) *)
Definition ex5_rhs :=
  tm 0 0 [tm 1 1 [tm 1 2 [tm 1 4 [tm 0 0 []; tm 0 4 [tm 0 1 []; tm 0 4 [tm 0 2 []; tm 0 5 []]]]]]].

Lemma solved_ex5 : exists g, solved_start_full g ex5_0 [ex5_1; ex5_2] ex5_rhs.
Proof.
  eexists. split.
  { split; [reflexivity|].
    apply: solved_var; [reflexivity..|cbn].
    apply: (solved_const _ _ _ _ _ _ _ [_]); [reflexivity..|cbn].
    move=> [|[|?]] ?; [|done..] => - [<-].
    apply: solved_var; [reflexivity..|cbn].
    apply: solved_var; [reflexivity..|cbn].
    apply: (solved_const _ _ _ _ _ _ _ [_]); [reflexivity..|cbn].
    move=> [|[|?]] ?; [|done..] => - [<-].
    apply: solved_var; [reflexivity..|cbn].
    apply: solved_var; [reflexivity..|cbn].
    apply: (solved_const _ _ _ _ _ _ _ [_]); [reflexivity..|cbn].
    move=> [|[|?]] ?; [|done..] => - [<-].
    apply: solved_var; [reflexivity..|cbn].
    apply: solved_var; [reflexivity..|cbn].
    apply: (solved_const _ _ _ _ _ _ _ [_; _]); [reflexivity..|cbn].
    move=> [|[|[|?]]] ?; [ | |done..] => - [<-].
    { apply: (solved_const _ _ _ _ _ _ _ []); [reflexivity..|cbn].
      by case. }
    apply: solved_var; [reflexivity..|cbn].
    apply: solved_var; [reflexivity..|cbn].
    apply: (solved_const _ _ _ _ _ _ _ [_; _]); [reflexivity..|cbn].
    move=> [|[|[|?]]] ?; [ | |done..] => - [<-].
    { apply: (solved_const _ _ _ _ _ _ _ []); [reflexivity..|cbn].
      by case. }
    apply: solved_var; [reflexivity..|cbn].
    apply: solved_var; [reflexivity..|cbn].
    apply: (solved_const _ _ _ _ _ _ _ [_; _]); [reflexivity..|cbn].
    move=> [|[|[|?]]] ?; [ | |done..] => - [<-].
    { apply: (solved_const _ _ _ _ _ _ _ []); [reflexivity..|cbn].
      by case. }
    apply: solved_var; [reflexivity..|cbn].
    apply: solved_var; [reflexivity..|cbn].
    apply: (solved_const _ _ _ _ _ _ _ []); [reflexivity..|cbn].
    by case. }
  cbn.
  apply: is_rhs_var; [reflexivity..|].
  apply: is_rhs_const; [reflexivity..|].
  move=> [|[|?]] ??; [|done..] => - [<-] [<-].

  do 2 (apply: is_rhs_var; [reflexivity..|]).

  apply: is_rhs_const; cbn.
  - reflexivity.
  - cbn. (* wrong index of the free variable *)
  admit.
Abort.


(* g a *)
Definition result :=
  tm 0 1 [tm 0 0 []].

Lemma solved_Stirling : exists g, solved_start_full g main_solution [arg1; arg2] result.
Proof.
  unfold result. eexists. split.
  { cbn. split; [reflexivity|].
    apply: solved_var; [reflexivity..|].

    rewrite [length _]/=. apply: solved_var; [reflexivity..|].
    rewrite [length _]/=. apply: solved_var; [reflexivity..|].
    rewrite [length _]/=. apply: solved_var; [reflexivity..|].
    rewrite [length _]/=. apply: solved_var; [reflexivity..|].
    rewrite [length _]/=. apply: solved_var; [reflexivity..|].
    rewrite [length _]/=. apply: solved_var; [reflexivity..|].

    rewrite [length _]/=. apply: (solved_const _ _ _ _ _ _ _ [_]); [repeat constructor..|].
    move=> [|[|?]] ?; [|done..] => - [<-].
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


    rewrite [length _]/=. apply: (solved_const _ _ _ _ _ _ _ []); [repeat constructor..|].
    by case. }
  
  cbn.
  do 7 (apply: is_rhs_var; [reflexivity..|]).

  apply: is_rhs_const; [reflexivity..|].
  move=> [|[|?]] ??; [|done..] => - [<-] [<-].
  
  do 14 (apply: is_rhs_var; [reflexivity..|]).

  apply: is_rhs_const; [reflexivity..|].
  by case.
Qed.

(*
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
*)