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
  map_tree_dependent (fun l '(n, x) => let bound := list_sum (map fst l) in (n, if bound <=? x then x - k else x)) t.


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
  | lk : list ((aposition * lookup) + nat) -> lookup.

Notation lookup_contents := (list ((aposition * lookup) + nat)).

Definition add_lk (ap: aposition) (theta: lookup_contents) (j: nat) : (aposition * lookup) + nat :=
  inl ((fst ap, snd ap ++ [j]), lk theta).

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
Definition extend_ap (ap: aposition) (extension: position) :=
   (fst ap, snd ap ++ extension).



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
Definition lookup_var (theta : lookup_contents) (x : nat) : option (aposition * lookup) :=
  match nth_error theta x with
  | Some (inl v) => Some v
  | _ => None
  end.

(*
  "solved ap theta l ots gt" means
  - at position ap in the arena TS
  - with the lookup table theta
  - l is the total number of prior abstractions 
  - with optional arguments ots
  the game represented by gt is well-formed
*)

Inductive solved (ap : aposition) (theta : lookup_contents) (l : nat):
  option lookup_contents -> rose_tree (aposition * lookup_contents) -> Prop :=
    | solved_abs k x args g:
      get_arena_subterm TS ap = Some (tm k x args) ->
      solved ap theta (k+l) (Some (map inr (seq l k))) g ->
      solved ap theta l None g

    | solved_var ts x args ap' theta' g:
      get_arena_subterm TS ap = Some (tm (length ts) x args) -> (* get subarena at position ap *)
      lookup_var (ts ++ theta) x = Some (ap', lk theta') -> (* get interpretation of x *)
      solved ap' theta' l (Some (map (add_lk ap (ts ++ theta)) (seq 0 (length args)))) g ->
      solved ap theta l (Some ts) (node (ap, ts ++ theta) [g])

    | solved_const ts x args gs:
      get_arena_subterm TS ap = Some (tm (length ts) x args) ->
      lookup_var (ts ++ theta) x = None ->
      length gs = length args ->
      (forall j g, nth_error gs j = Some g -> solved (extend_ap ap [j]) (ts ++ theta) l None g) ->
      solved ap theta l (Some ts) (node (ap, ts ++ theta) gs).

(* compute the actual index for true constant / variable constant *)
Definition compute_const (theta : lookup_contents) (l x : nat) : option nat :=
  match nth_error theta x with
  | Some (inr n) => Some (l-n-1) (* the variable was bound at n abstractions - l is the number of current abstractions *)
  | None => Some (x+l-length theta) (* constant case *)
  |_ => None
  end.

(* TS[0] is solution TS[1..] are arguments *)
Fixpoint construct_game_tree (depth : nat) (ap : aposition) (theta : lookup_contents) (l : nat) (ots : option lookup_contents): game_tree :=
  match depth with
  | 0 => node (ap, theta) []
  | S depth =>
    match get_arena_subterm TS ap with
    | Some (tm m x args) =>
      match ots with
      | Some ts =>
        match lookup_var (ts ++ theta) x with
        | Some (ap', lk theta') => (* bound variable case, see solved_var *)
            node (ap, ts ++ theta)
              [construct_game_tree depth ap' theta' l (Some (map (add_lk ap (ts ++ theta)) (seq 0 (length args))))]
        | None => (* constant case, see solved_const *)
            node (ap, ts ++ theta)
              (map (fun j => construct_game_tree depth (extend_ap ap [j]) (ts ++ theta) l None) (seq 0 (length args)))
        end
      | None => construct_game_tree depth ap theta (m+l) (Some (map inr (seq l m)))
      end
    | None => node (ap, theta) []
    end
  end.

(* "is_rhs l gt on r" means that the term "r" is the unique rhs corresponding to the game tree "gt"
   the argument "on" specifies whether "r" has abstractions *)

Inductive is_rhs (l : nat): rose_tree (aposition * lookup_contents) -> option nat -> term -> Prop :=
  | is_rhs_abs ap theta gs k x args y rs:
    get_arena_subterm TS ap = Some (tm k x args) ->
    is_rhs (k+l) (node (ap, theta) gs) (Some k) (tm 0 y rs) ->
    is_rhs l (node (ap, theta) gs) None (tm k y rs)

  | is_rhs_var n ap theta x args gt r :
    get_arena_subterm TS ap = Some (tm n x args) ->
    compute_const theta l x = None -> (* x points to a variable *)
    is_rhs l gt (Some (length args)) r ->
    is_rhs l (node (ap, theta) [gt]) (Some n) r

  | is_rhs_const n ap theta x ts y gs rs :
    get_arena_subterm TS ap = Some (tm n x ts) ->
    compute_const theta l x = Some y -> (* x points to a constant *)
    length gs = length rs ->
    (forall j g r, nth_error gs j = Some g -> nth_error rs j = Some r -> is_rhs l g None r) ->
    is_rhs l (node (ap, theta) gs) (Some n) (tm 0 y rs).

Lemma is_rhs_Some_binders l n g r:
  is_rhs l g (Some n) r ->
  get_binders r = 0.
Proof.
  move=> H.
  have : Some n <> None by done.
  move: (Some n) H=> on.
  elim; [done| |done].
  move=> > ??? IH ?.
  by apply: IH.
Qed.

Lemma is_rhs_elim l ap theta gs on r:
  is_rhs l (node (ap, theta) gs) on r ->
  match on with
  | None => forall k x args,
      get_arena_subterm TS ap = Some (tm k x args) ->
      exists y rs, r = tm k y rs /\ is_rhs (k+l) (node (ap, theta) gs) (Some k) (tm 0 y rs)
  | Some n => forall m x args,
      get_arena_subterm TS ap = Some (tm m x args) ->
      m = n /\
      match compute_const theta l x with
      | Some y =>
        exists rs, r = tm 0 y rs /\ length gs = length rs /\
          (forall j g r, nth_error gs j = Some g -> nth_error rs j = Some r -> is_rhs l g None r)
      | None =>
        exists gt, gs = [gt] /\ is_rhs l gt (Some (length args)) r
      end
  end.
Proof.
  move E: (node (ap, theta) gs)=> g H.
  case: H E.
  - move=> > + ? [???] >. subst.
    move=> -> [???]. subst.
    do 2 eexists. by split.
  - move=> > ++ ? [???] >. subst.
    move=> -> + [???]. subst.
    move=> ->.
    split; first done.
    by eexists.
  - move=> > ++ ?? [???] >. subst.
    move=> -> + [???]. subst.
    move=> ->.
    split; first done.
    by eexists.
Qed.

(*
  eval ap theta l ots r means that
  the game starting at position ap with lookup table theta,
  l many prior abstractions
  with ots arguments
  evaluates to the term r

  eval does not include the game tree
*)

Inductive eval (ap : aposition) (theta : lookup_contents) (l : nat):
  option lookup_contents -> term -> Prop :=
    | eval_abs k x args y rs:
      get_arena_subterm TS ap = Some (tm k x args) ->
      eval ap theta (k+l) (Some (map inr (seq l k))) (tm 0 y rs) ->
      eval ap theta l None (tm k y rs)

    | eval_var ts x args ap' theta' r:
      get_arena_subterm TS ap = Some (tm (length ts) x args) -> (* get subarena at position ap *)
      lookup_var (ts ++ theta) x = Some (ap', lk theta') -> (* get interpretation of x *)
      eval ap' theta' l (Some (map (add_lk ap (ts ++ theta)) (seq 0 (length args)))) r ->
      eval ap theta l (Some ts) r

    | eval_const ts x args y rs:
      get_arena_subterm TS ap = Some (tm (length ts) x args) ->
      compute_const (ts ++ theta) l x = Some y ->
      length rs = length args ->
      (forall j r, nth_error rs j = Some r -> eval (extend_ap ap [j]) (ts ++ theta) l None r) ->
      eval ap theta l (Some ts) (tm 0 y rs).

(* experiment:
     shift eval to subterms, maybe less bookkeeping? *)
Inductive eval' (x : nat) (theta ts : lookup_contents) (l : nat):
  term -> Prop :=
    | eval'_var args ap' theta' y r:
      lookup_var theta x = Some (ap', lk theta') -> (* get interpretation of x *)
      get_arena_subterm TS ap' = Some (tm (length ts) y args) ->
      eval' y (ts ++ theta') ((map (add_lk ap' (ts ++ theta')) (seq 0 (length args)))) l r ->
      eval' x theta ts l r
    | eval'_const y rs k args:
      compute_const theta l x = Some y ->
      length ts = length rs ->
      (forall j ap' theta' z z' args',
        nth_error ts j = Some (inl (ap', lk theta')) ->
        nth_error rs j = Some (tm k z' args') ->
        get_arena_subterm TS ap' = Some (tm k z args) ->
        eval' z theta' (map inr (seq l k)) (k+l) (tm 0 z' args')) ->
      eval' x theta ts l (tm 0 y rs).

Lemma lookup_var_Some_compute_const_None l theta x v:
  lookup_var theta x = Some v ->
  compute_const theta l x = None.
Proof.
  rewrite /lookup_var /compute_const.
  case: (nth_error theta x); last done.
  by case.
Qed.

Lemma compute_const_Some_lookup_var_None l theta x y:
  compute_const theta l x = Some y ->
  lookup_var theta x = None.
Proof.
  rewrite /lookup_var /compute_const.
  case: (nth_error theta x); last done.
  by case.
Qed.

Lemma lookup_var_None_compute_const_Some l theta x:
  lookup_var theta x = None ->
  exists y, compute_const theta l x = Some y.
Proof.
  rewrite /lookup_var /compute_const.
  case: (nth_error theta x).
  - move=> [|]; first done.
    by eexists.
  - by eexists.
Qed.

(* form a list of elements which satisfy a predicate P *)
Lemma form_list {A B: Type} (P: nat -> A -> B -> Prop) (l: list A):
  (forall i a, nth_error l i = Some a -> exists b, P i a b) ->
  exists l', length l' = length l /\
    (forall i a b, nth_error l i = Some a -> nth_error l' i = Some b -> P i a b).
Proof.
  elim: l P.
  - move=> ? _. exists []. split; first done. by case.
  - move=> a l IH P H.
    have [b Hb] := H 0 a eq_refl.
    have [l' [E Hl']] := IH _ (fun i => H (S i)).
    exists (b :: l'). split.
    + by rewrite /= E.
    + move=> [|i] ?? /=.
      * move=> [<-] [<-]. by apply: Hb.
      * by move=> /Hl' /[apply].
Qed.

Lemma solved_game_tree_value ap theta l ts g:
  solved ap theta l (Some ts) g ->
  get_value g = (ap, ts ++ theta).
Proof.
  intros H. inversion H; by subst.
Qed.

Lemma is_rhs_None_get_binders l g r k x args:
  is_rhs l g None r ->
  get_arena_subterm TS (fst (get_value g)) = Some (tm k x args) ->
  get_binders r = k.
Proof.
  move=> H. inversion H; subst.
  move=> /=. congruence.
Qed.

(* eval is equivalent to existence of a game tree with corresponding rhs *)
Lemma eval_spec ap theta l ots r:
  eval ap theta l ots r <->
    (exists gtr, solved ap theta l ots gtr /\ is_rhs l gtr (option_map (@length _) ots) r).
Proof.
  split.
  - elim.
    + move=> {}ap {}theta {}l k x args y rs.
      move=> ?? [gtr] /= [H1gtr].
      rewrite length_map length_seq=> H2gtr.
      move: (H1gtr) => /solved_game_tree_value H'gtr.
      exists gtr.
      split; first by apply: solved_abs; eassumption.
      move: H'gtr.
      destruct gtr as [[??] ?].
      move=> [*]. subst. 
      by apply: is_rhs_abs; eassumption.
    + move=> {}ap {}theta {}l ts x args ap' theta' {}r Hap.
      move=> /[dup] /(lookup_var_Some_compute_const_None l) H'x Hx ? [gtr] [H1gtr H2gtr].
      rewrite /= length_map length_seq in H2gtr.
      eexists (node (ap, ts ++ theta) [_]). split.
      * apply: solved_var; eassumption.
      * apply: is_rhs_var; eassumption.
    + move=> {}ap {}theta {}l ts x args y rs Hap.
      move=> /[dup] /(compute_const_Some_lookup_var_None l) ????.
      move=> /form_list [gs] [?] IH.
      eexists (node (ap, ts ++ theta) gs). split.
      * apply: solved_const; [eassumption..|lia|].
        move=> j g /[dup] Hj /IH.
        case E: (nth_error rs j) => [?|].
        ** by move=> /(_ _ eq_refl) [].
        ** move: E => /nth_error_None ?.
           suff: j < length gs by lia.
           apply /nth_error_Some. by rewrite Hj.
      * apply: is_rhs_const; [eassumption..|].
        move=> j g r' /[dup] Hj /IH /[apply] - [_]. by apply.
  - move=> [gtr] [H]. elim: H r.
    + move=> {}ap {}theta {}l k x args g Hap Hg /=.
      rewrite length_map length_seq=> IH [[k' y] rs] /= H.
      move: (H) (Hap) => /is_rhs_None_get_binders.
      move: (Hg) => /solved_game_tree_value -> /= /[apply] ?.
      subst k'.
      apply: eval_abs; first by eassumption.
      apply: IH.
      inversion H. by subst.
    + move=> {}ap {}theta {}l ts x args ap' theta' g Hap /=.
      rewrite length_map length_seq.
      move=> /[dup] /(lookup_var_Some_compute_const_None l) Hx ?? IH [[k y] rs] Hr.
      move: Hr (Hap) => /is_rhs_elim /[apply] - [_].
      rewrite Hx=> - [gt] [[<-]] /IH.
      by apply: eval_var; eassumption.
    + move=> {}ap {}theta {}l ts x args gs Hap.
      move=> /[dup] /(lookup_var_None_compute_const_Some l) [y Hy] ??? IH r Hr.
      move: Hr (Hap) => /is_rhs_elim /[apply] - [_].
      rewrite Hy=> - [rs] [->] [Egsrs] H.
      have ?: length rs = length args by lia.
      apply: eval_const; [eassumption..|].
      move=> j r'.
      case E: (nth_error gs j) => [g'|].
      * move: (E) => /H /[apply]. by apply: IH.
      * move: E => /nth_error_None.
        by rewrite Egsrs=> /nth_error_None ->.
Qed.


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

(* [t] [ts] = [r] *)
Definition solved_start g t (ts : list term) :=
  length ts = get_binders t /\
  solved (t :: ts) (0, []) [] 0 (Some (map (fun j => inl ((S j, []), lk [])) (rev (seq 0 (length ts))))) g.

Definition construct_game_tree_start (depth : nat) t (ts : list term) :=
  match t with
  | tm n x us =>
    construct_game_tree (t :: ts) depth (0, []) [] 0 (Some (map (fun j => inl ((S j, []), lk [])) (rev (seq 0 (length ts)))))
  end.

Definition solved_start_full g t (ts : list term) (r : term) :=
  solved_start g t ts /\
  is_rhs (t :: ts) 0 g (Some (length ts)) r.

(* if the game is solved, its game tree is unique and is constructed by construct_game_tree_start *)
Lemma construct_game_tree_start_spec g t ts : solved_start g t ts -> exists depth0, forall depth, depth0 <= depth -> g = construct_game_tree_start depth t ts.
Proof.
  rewrite /solved_start /construct_game_tree_start.
  move: t => [] [? x] args /= [<-].
  move: (Some (map _ _)) => ot's.
  move: (_ :: _) => TS.
  move: (0, []) => ap.
  move: [] => theta.
  move: (0) => l.
  elim.
  - move=> > Hap ? [depth0] IH.
    exists (S depth0) => - [|?] ?; first lia.
    rewrite /= Hap. apply: IH. lia.
  - move=> > Hap Hx _ [depth0] IH.
    exists (S depth0)=> - [|depth] ?; first lia.
    by rewrite /= Hap Hx (IH depth); first lia.
  - move=> {}ap {}theta {}l t's {}x {}args gs Hap Hx Hlen Hgs H'gs.
    suff: exists depth0, forall depth, depth0 <= depth -> gs = (map (fun j => construct_game_tree TS depth (extend_ap ap [j]) (t's ++ theta) l None) (seq 0 (length args))).
    { move=> [depth0] H. exists (S depth0).
      move=> [|depth] ?; first by lia.
      by rewrite /= Hap Hx (H depth); first lia. }
    move: H'gs. rewrite -Hlen.
    elim /rev_ind: gs {Hgs Hlen}.
    + move=> _. by exists 0.
    + move=> g' {}gs IH H.
      have := H (length gs).
      rewrite nth_error_app2 ?Nat.sub_diag; first by lia.
      move=> /(_ _ eq_refl).
      case: IH.
      { move=> j ? Hj.
        apply: H.
        by rewrite nth_error_app1; first apply /nth_error_Some; rewrite Hj. }
      move=> depth1 Hdepth1 [depth2] Hdepth2.
      exists (depth1+depth2).
      move=> depth ?.
      rewrite length_app seq_app map_app. congr app.
      * apply: Hdepth1. lia.
      * congr cons. apply: Hdepth2. lia.
Qed.

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

(* stream cons *)
Definition scons {X: Type} (x : X) (f : nat -> X) :=
  fun n => match n with | 0 => x | S n => f n end.

Definition up (f : nat -> nat) (x : nat) := S (scons 0 f x).

(* rename free variables of a term *)
Fixpoint ren_term (f: nat -> nat) (t: term) : term :=
  match t with
  | tm n x ts => tm n (Nat.iter n up f x) (map (ren_term (Nat.iter n up f)) ts)
  end.

(* do all elements in l satisfy the predicate P *)
Definition all {X: Type} (P: X -> Prop) (l: list X) : Prop :=
  fold_right (fun x p => and (P x) p) True l.

(* assert that P holds on all free variables in t *)
Fixpoint allfv (P: nat -> Prop) (t: term) : Prop :=
  match t with
  | tm n x ts => (Nat.iter n (scons True) P) x /\ all (allfv (Nat.iter n (scons True) P)) ts
  end.

(* arena1 is equivalent to arena2 up to renaming of free variables *)
Inductive up_to_renaming (arena1 arena2: arena) :
  ((aposition * lookup) + nat) -> ((aposition * lookup) + nat) -> Prop :=
  | up_to_renaming_inl ap1 ap2 (theta1 theta2 : lookup_contents) f t:
    get_arena_subterm arena1 ap1 = Some (ren_term f t) ->
    get_arena_subterm arena2 ap2 = Some t ->
    (forall x v, nth_error theta1 (f x) = Some v ->
      exists w, nth_error theta2 x = Some w /\
        up_to_renaming arena1 arena2 v w) ->
    up_to_renaming arena1 arena2 (inl (ap1, lk theta1)) (inl (ap2, lk theta2))
  | up_to_renaming_inr n:
    up_to_renaming arena1 arena2 (inr n) (inr n).

Lemma get_arena_subterm_extend_ap ts ap n x rs j:
  get_arena_subterm ts ap = Some (tm n x rs) ->
  get_arena_subterm ts (extend_ap ap [j]) = nth_error rs j.
Proof.
  move: ap => [i p] /=.
  move: (nth_error ts i)=> [t|]; last done.
  rewrite get_subtree_error_app=> -> /=.
  by case: (nth_error rs j).
Qed.

(*
  two arenas evaluate similarly if they are quivalent up to renaming of free variables

Lemma eval_shift arena arena' ap ap' theta theta' ts ts' l r:
  eval arena ap theta ts l r ->
  up_to_renaming arena arena' (inl (ap, lk theta)) (inl (ap', lk theta')) ->
  Forall2 (up_to_renaming arena arena') ts ts' ->
  eval arena' ap' theta' ts' l r.
Proof.
  move=> H. elim: H ap' theta' ts'.
  - move=> {}ap {}theta {}ts {}l k x args nap ntheta y rs.
    move=> Hap H0 Hx ? IH ap' theta' ts'.
    move Ev: (inl (ap, _)) => v.
    move Ew: (inl (ap', _)) => w H.
    case: H Ev Ew=> ap1 ap2 theta1 theta2; last done.
    move=> f [[m'' x''] args''] Hap1 Hap2 H' [??] [??].
    subst ap1 theta1 ap2 theta2.
    move: (Hap) Hap1 Hap2 => -> /= [<- ? Eargs] Hap'.
    move=> /[dup] /Forall2_length E H''.
    rewrite E in Hap' H0.
    have E'args: length args = length args'' by rewrite Eargs length_map.
    have [nap' [ntheta' [??]]]: exists nap' ntheta',
      lookup_var (map inr (seq l k) ++ ts' ++ theta') x'' = Some (nap', lk ntheta') /\
      up_to_renaming arena arena' (inl (nap, lk ntheta)) (inl (nap', lk ntheta')).
    { subst x. move: Hx.
      have [?|?]: x'' < length ts + k \/ length ts + k <= x'' by lia.
      - have ->: (Nat.iter (length ts + k) up f x'') = x'' by admit.
        admit. (* doable *)
      - have ->: (Nat.iter (length ts + k) up f x'') = (length ts + k) + f (x'' - (length ts + k)) by admit.
        rewrite /lookup_var.
        admit. (* doable *) }
    apply: eval_var; [eassumption..|].
    apply: IH; first done.
    rewrite E'args.
    admit. (* maybe *) 
  - move=> {}ap {}theta {}ts {}l k x args y rs.
    move=> Hap H0 Hx ? ? IH ap' theta' ts'.
    move Ev: (inl (ap, _)) => v.
    move Ew: (inl (ap', _)) => w H.
    case: H Ev Ew=> ap1 ap2 theta1 theta2; last done.
    move=> f [[m'' x''] args''] Hap1 Hap2 H' [??] [??].
    subst ap1 theta1 ap2 theta2.
    move: (Hap) Hap1 Hap2 => -> /= [<- ? Eargs] Hap'.
    move=> /[dup] /Forall2_length E H''.
    rewrite E in Hap' H0.
    have E'args: length args = length args'' by rewrite Eargs length_map.
    have ?: length rs = length args'' by lia.

    have ?: compute_const (map inr (seq l k) ++ ts' ++ theta') l x'' = Some y.
    { admit. }
    apply: eval_const; try eassumption.
    move=> j r' Hj.
    apply: IH; [eassumption| |done].
    admit. (* looks doable *)
Admitted.
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

Lemma combine_map {A B A' B' : Type} (f : A -> A') (g : B -> B') (l1 : list A) (l2 : list B) :
  combine (map f l1) (map g l2) = map (fun ab => (f (fst ab), g (snd ab))) (combine l1 l2).
Proof.
  elim: l1 l2; first done.
  move=> a l1 IH [|b l2]; first done.
  by rewrite /= IH.
Qed.

Arguments nth_error_In {A l n x}.

(* two arenas which agree locally on positions in the game tree are equivalent *)
Lemma locally_equivalent_solved arena arena' ap theta l ots gtr:
  solved arena ap theta l ots gtr ->
  Forall (fun ap' => locally_equivalent (get_arena_subterm arena ap') (get_arena_subterm arena' ap')) (get_apositions gtr) ->
  solved arena' ap theta l ots gtr.
Proof.
  move=> H. elim: H arena'.
  - move=> {}ap {}theta {}l k x args g.
    move=> /locally_equivalent_elim Hap /solved_game_tree_value H'g IH arena' Hg.
    have [? [??]] : exists args', length args = length args' /\ get_arena_subterm arena' ap = Some (tm k x args').
    { move: (g) H'g Hg=> [[??] ?] [-> ->] /=.
      by move=> /Forall_cons_iff [/Hap]. }
    apply: solved_abs; [eassumption|].
    by apply: IH.
  - move=> {}ap {}theta {}l ts x args nap ntheta {}gtr.
    move=> /locally_equivalent_elim Hap Hx Hgtr IH arena' /=.
    move=> /Forall_cons_iff [/Hap [?] [H'args H'ap]] /Forall_app [/IH] + _.
    rewrite H'args. by apply: solved_var; eassumption.
  - move=> {}ap {}theta {}l ts x args gs.
    move=> /[dup] H''ap /locally_equivalent_elim Hap Hx Hlen IH' IH arena' /=.
    move=> /Forall_cons_iff [/Hap [ts''] [H'ts'' H'ap]] /Forall_flat_map Hgs.
    have ?: length gs = length ts'' by lia.
    apply: solved_const; [eassumption..|].
    move=> j g /[dup] /nth_error_In ? Hg. apply: IH; first done.
    move: Hgs => /Forall_forall. by apply.
Qed.

Arguments Forall2_cons_iff {A B R x y}.

Arguments node {A}.

Lemma solved_ap_in_get_apositions arena ap theta l ots gtr:
  solved arena ap theta l ots gtr ->
  In ap (get_apositions gtr).
Proof.
Admitted.

Fixpoint get_apositions_lk (l : lookup) : list aposition :=
  match l with
  | lk theta => flat_map (fun c => match c with inl (ap', theta') => ap' :: get_apositions_lk theta' | _ => [] end) theta
  end.

Arguments get_apositions_lk : simpl never.

Arguments nth_error_In {A l n x}.

Lemma in_get_apositions_lk_intro ap (theta : lookup_contents) ap' theta':
  In (inl (ap', lk theta')) theta ->
  In ap (get_apositions_lk (lk theta')) ->
  In ap (get_apositions_lk (lk theta)).
Proof.
  cbn. move=> /in_split [?] [?] -> ?.
  rewrite /get_apositions_lk flat_map_app /=.
  apply /in_app_iff. right.
  right.
  apply /in_app_iff. by left.
Qed.

Lemma lookup_var_Some theta x v :
  lookup_var theta x = Some v ->
  nth_error theta x = Some (inl v).
Proof.
  rewrite /lookup_var.
  case: (nth_error theta x); last done.
  case; congruence.
Qed.

Arguments In_nth_error {A l x}.
Arguments repeat_spec {A n x y}.

Lemma get_apositions_lk_app theta theta':
  get_apositions_lk (lk (theta ++ theta')) = 
  get_apositions_lk (lk theta) ++ get_apositions_lk (lk theta').
Proof.
  by rewrite /get_apositions_lk -/get_apositions_lk flat_map_app.
Qed.

Lemma in_get_apositions_lk ap theta:
  In ap (get_apositions_lk (lk theta)) ->
  exists ap' theta', In (inl (ap', theta')) theta /\
    In ap (ap' :: get_apositions_lk theta').
Proof.
  move=> /in_flat_map [[[ap' theta']|y]].
  - move=> [??].
    by exists ap', theta'.
  - by case.
Qed.

(* an aposition in the game tree is either
   the start,
   occurs the lookup table,
   or its direct prefix occurs in the game tree *)
Lemma solved_ap_cone arena ap (theta : lookup_contents) l gtr ots ap':
  solved arena ap theta l ots gtr ->
  In ap' (get_apositions gtr) ->
    ap = ap' \/
    In ap' (get_apositions_lk (lk (match ots with Some ts => ts | None => [] end ++ theta))) \/
    exists ap'' j, ap' = extend_ap ap'' [j] /\ In ap'' (get_apositions gtr).
Proof.
  elim.
  - move=> {}ap > ? Htheta /[apply] /=.
    move=> [|[|]]; [tauto| |tauto].
    rewrite get_apositions_lk_app.
    move=> /in_app_iff [|]; last by tauto.
    by move=> /in_flat_map [?] [/in_map_iff] [?] [<-].
  - move=> {}ap > ? Htheta ? /= IH [|]; first by tauto.
    rewrite app_nil_r=> /IH [?|[|]].
    + subst. right. left.
      move: Htheta=> /lookup_var_Some /nth_error_In ?.
      apply /in_flat_map. eexists.
      split; first by eassumption.
      by left.
    + rewrite get_apositions_lk_app.
      move=> /in_app_iff [|].
      * move=> /in_get_apositions_lk [?] [?] /= [].
        move=> /in_map_iff [?] [[<- <-]] _ [<-|]; last by tauto.
        subst. right. right. eexists _, _. by split; last by left.
      * move=> /in_get_apositions_lk_intro H.
        right. left. apply: H.
        move: Htheta=> /lookup_var_Some /nth_error_In. by apply.
    + firstorder done.
  - move=> ???????? Ets ? ? IH /= [|]; first by tauto.
    move=> /in_flat_map [g] [Hg] /IH {}IH.
    move: (Hg) => /In_nth_error [j] /IH [?|[|]] /=.
    + subst. firstorder done.
    + tauto.
    + move=> [?] [?] [->] ?. do 2 right. eexists _, _.
      split; first done. right.
      apply /in_flat_map. eexists. by split; last by eassumption.
Qed.

(* apositions form a cone in a full game tree *)
Lemma solved_start_ap_cone arena p (theta : lookup_contents) l ots gtr :
  solved arena (0, []) theta l ots gtr ->
  In (0, p) (get_apositions gtr) ->
  Forall (fun ap => fst ap <> 0) (get_apositions_lk (lk (match ots with Some ts => ts | None => [] end ++ theta))) ->
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

(* is this helpful? Maybe NO
   difficult to adjust whole game tree
   maybe just adjust eval on the basis of the game tree?

Inductive solved_arena (ap : aposition) (theta ts : lookup_contents) (l : nat):
  rose_tree (arena * aposition * lookup_contents) -> Prop :=
    | solved_arena_var arena k x args ap' theta' g:
      get_arena_subterm arena ap = Some (tm (length ts + k) x args) -> (* get subarena at position ap *)
      length ts * k = 0 -> (* there is no partial application *)
      lookup_var (map inr (seq l k) ++ ts ++ theta) x = Some (ap', lk theta') -> (* get interpretation of x *)
      (* check that at ap' there are "length args" many abstractions *)
      solved_arena ap' theta' (map (add_lk ap (map inr (seq l k) ++ ts ++ theta)) (seq 0 (length args))) (k+l) g ->
      (* (map (add_lk ap theta) (seq 0 (length args))) - uses arguments of x
         to interpret variables abstracted in the interpretation of x *)
      solved_arena ap theta ts l (node (arena, ap, map inr (seq l k) ++ ts ++ theta) [g])

    | solved_arena_const arena k x args gs:
      get_arena_subterm arena ap = Some (tm (length ts + k) x args) ->
      length ts * k = 0 -> (* there is no partial application *)
      lookup_var (map inr (seq l k) ++ ts ++ theta) x = None ->
      length gs = length args ->
      (forall j g, nth_error gs j = Some g -> solved_arena (extend_ap ap [j]) (map inr (seq l k) ++ ts ++ theta) [] (k+l) g) ->
      solved_arena ap theta ts l (node (arena, ap, map inr (seq l k) ++ ts ++ theta) gs).
*)


(* more experiments *)
(*
Lemma eval_equiv ts ap theta n l r ts' ap' theta':
  eval ts ap theta n l r ->
  locally_equivalent (get_arena_subterm ts ap) (get_arena_subterm ts' ap') ->
  Forall2 (fun ap ap' => locally_equivalent (get_arena_subterm ts ap) (get_arena_subterm ts' ap')) (get_apositions_lk (lk theta)) (get_apositions_lk (lk theta')) ->
  eval ts' ap' theta' n l r.
Proof.
  move=> H. elim: H ts' ap' theta'.
  - move=> {}ap {}theta {}n {}l k x args ap'' theta'' y rs.
    move=> Hap ? Hx ? IH ts' ap' theta' E1 E2.
    move: E1 (Hap)=> /locally_equivalent_elim /[apply] - [args'] [Elen] ?.
    move: (E2) (Hx)=> /more_local_equivalence /[apply] - [ap'''] [theta'''] [?] [?] ?.
    apply: eval_var.
    + by eassumption.
    + done.
    + by eassumption.
    + rewrite -Elen. apply: IH.
      * done.
      * rewrite !get_apositions_lk_app.
        apply: Forall2_app; last done.

       cbn. destruct ap. cbn in *. rewrite map_app. cbn.  
*)


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
      rewrite app_nil_r in H''gtr.
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


(* path that contributes TODO

Assume π ∈ G(t, E) and n_j is a lambda node. The interval π[i, j] contributes if [r_i] ≠ [r_j].
 *) 
Inductive non_contributes : arena -> game_tree -> interval -> Prop :=
| contributes_helper_case a ap1 theta1 ap2 theta2 gtr gtrs1 gtrs2 from to (lf:nat) (lt:nat) r:
  get_subtree gtr from = (node (ap1, theta1) gtrs1) ->
  get_subtree gtr to = (node (ap2, theta2) gtrs2) ->
  get_arena_subterm_bound a ap1 = Some lf ->
  get_arena_subterm_bound a ap2 = Some lt ->
  eval a ap1 theta1 lf None r ->
  eval a ap2 theta2 lt None r ->
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
Definition find_position_in_game_tree_int (gtr:game_tree) startg endg pos : option position :=
  find (fun pref =>
          let 'node ((tno, p), theta) chlds :=
            get_subtree gtr (startg ++ pref) in
          (tno =? 0) &&
            (forallb (fun '(x, y) => x =? y) (combine p pos)))%bool
    (list_prefixes endg).

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

(* increase all free variables in t by d starting fround bound *)
Fixpoint shift_vars (d: nat) (bound: nat) (t: term) : term :=
  match t with
  | tm m x ts => tm m ((if x <? bound then 0 else d) + x) (map (shift_vars d (m + bound)) ts)
  end.






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
  (forall fp, is_final fp gtr -> 
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

(*
  Stirling:
  Proposition 32:

Assume t is a smallest solution to E whose goal is u,
m1,..., mp are
+ both embedded and
+ end nodes (Definitions 35 and 36) of t
+ labelled with the same variable
+ bound by a binder at a node n.
+ the node mi+1 occurs below mi for each i : 1 ≤ i ≤ p.then p ≤ depth(u).
 *)


(*
p - order of the instance
q - (maximal) arity of types in the instance
u - right-hand side of equation
N_i - number of nodes on level i
ENE_i - number of embedded non-end nodes of level i

=======================================
In 4th-order matching we have nodes of:
=======================================

---------- LEVEL 1

- non-embedded nodes of level 1 (of order 3 at most)
  --> bounded by q
      : each variable bound on the top of the
      : solution t contributes at most 1 to the number of
      : non-embedded nodes of level 1 and no other
      : source contributes to them.

- embedded non-end nodes of level 1 that contribute (of order 3 at most)
  --> bounded by |u|

- embedded non-end nodes of level 1 that do not contribute (of order 3 at most)
  --> bounded by ENE_1 = 0?
      : Each time we have two embedded non-end nodes n0 above n1
      : that do not contribute (i.e. they do not start a segment that contributes)
      : such that below n1 there is no ther embedded non-end node
      : if there is an occurence n2 of some variable bound at the successor of n0
      : that occurs under n1 then unfold n0 to all variables it binds.
      : in that way the path to n2 after applying T2 will get fewer occurrences of main
      : variables. For all other paths to active variables the number remains the same.

- embedded end nodes of level 1 (of order 3 at most)
  --> bounded by q * depth(u)
      : by Proposition 32

- N_1 <= q + |u| + ENE_1 + q * depth(u)

---------- LEVEL 2

- non-embedded nodes of level 2 (of order 1)
  --> bounded by q * q * N_1
      : each node on level 1 has at most q arguments,
      : every of the q arguments contributes at most
      : q bound variables, each of the bindings
      : contributes at most 1 to non-embedded nodes

- embedded non-end nodes of level 2 that contribute (of order 1)
  --> bounded by |u|

- embedded non-end nodes of level 2 that do not contribute (of order 1)
  --> bounded by ENE_2 = 0
      : each node of order 1 is an end node, because it has
      : no descendant under binding

- embedded end nodes of level 2 (of order 1)
  --> q*q*N_1 * depth(u)
      : by Proposition 32

- N_2 <= q*q*N_1 + |u| + 0 + q*q*N_1 * depth(u)



=======================================
In 5th-order matching we have nodes of:
=======================================

---------- LEVEL 1

- non-embedded nodes of level 1 (of order 4 at most)
  --> bounded by q
      : each variable bound on the top of the
      : solution t contributes at most 1 to the number of
      : non-embedded nodes of level 1 and no other
      : source contributes to them.

- embedded non-end nodes of level 1 that contribute (of order 4 at most)
  --> bounded by |u|

- embedded non-end nodes of level 1 that do not contribute (of order 4 at most)
  --> bounded by ENE_1 = 0?
      : Each time we have two embedded non-end nodes n0 above n1
      : that do not contribute (i.e. they do not start a segment that contributes)
      : such that below n1 there is no ther embedded non-end node
      : if there is an occurence n2 of some variable bound at the successor of n0
      : that occurs under n1 then unfold n0 to all variables it binds.
      : in that way the path to n2 after applying T2 will get fewer occurrences of main
      : variables. For all other paths to active variables the number remains the same.

- embedded end nodes of level 1 (of order 4 at most)
  --> bounded by q * depth(u)
      : by Proposition 32

- N_1 <= q + |u| + ENE_1 + q * depth(u)

---------- LEVEL 2

- non-embedded nodes of level 2 (of order 2 at most)
  --> bounded by q * q * N_1
      : each node on level 1 has at most q arguments,
      : every of the q arguments contributes at most
      : q bound variables, each of the bindings
      : contributes at most 1 to non-embedded nodes

- embedded non-end nodes of level 2 that contribute (of order 2 at most)
  --> bounded by |u|

- embedded non-end nodes of level 2 that do not contribute (of order 2 at most)
  --> bounded by ENE_2 = 0
      : each node of order 2 is an end node, because it has
      : no descendant under binding

- embedded end nodes of level 2 (of order 2 at most)
  --> q*q*N_1 * depth(u)
      : by Proposition 32

- N_2 <= q*q*N_1 + |u| + 0 + q*q*N_1 * depth(u)

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
    - cbn. apply: (solved_const _ _ _ _ _ _ _ []).
      + cbn. reflexivity.
      + cbn. reflexivity.
      + cbn. reflexivity.
      + cbn. now intros [|?]. }
  cbn. apply: is_rhs_var.
  - cbn. reflexivity.
  - cbn. reflexivity.
  - cbn. apply: is_rhs_const.
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
    apply: solved_abs; first done.

    apply: solved_var; [reflexivity..|].
    rewrite [length _]/=. apply: solved_var; [reflexivity..|].
    rewrite [length _]/=. apply: solved_var; [reflexivity..|].
    rewrite [length _]/=. apply: solved_var; [reflexivity..|].

    rewrite [length _]/=. apply: (solved_const _ _ _ _ _ _ _ []); [reflexivity..|].
    by case. }

  apply: is_rhs_var; [reflexivity..|].
  apply: is_rhs_const; [reflexivity..|].
  move=> [|[|?]] ??; [|done..] => - [<-] [<-].
  apply: is_rhs_abs; first done.

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
  tm 0 1 [tm 1 2 [tm 1 3 [tm 1 3 []]]].

Lemma solved_ex4 : exists g, solved_start_full g ex4_0 [ex4_1] ex4_rhs.
Proof.
  eexists. split.
  { split; [reflexivity|].
    apply: solved_var; [reflexivity..|].

    rewrite [length _]/=. apply: (solved_const _ _ _ _ _ _ _ [_]); [reflexivity..|].
    move=> [|[|?]] ?; [|done..] => - [<-].
    apply: solved_abs; [reflexivity..|].

    apply: solved_var; [reflexivity..|].
    rewrite [length _]/=. apply: solved_var; [reflexivity..|].

    rewrite [length _]/=. apply: (solved_const _ _ _ _ _ _ _ [_]); [reflexivity..|].
    move=> [|[|?]] ?; [|done..] => - [<-].
    apply: solved_abs; [reflexivity..|].

    apply: solved_var; [reflexivity..|].
    rewrite [length _]/=. apply: solved_var; [reflexivity..|].

    rewrite [length _]/=. apply: (solved_const _ _ _ _ _ _ _ [_]); [reflexivity..|].
    move=> [|[|?]] ?; [|done..] => - [<-].
    apply: solved_abs; [reflexivity..|].

    apply: solved_var; [reflexivity..|].
    rewrite [length _]/=. apply: (solved_const _ _ _ _ _ _ _ []); [reflexivity..|].
    by case. }

  cbn.
  apply: is_rhs_var; [reflexivity..|].
  apply: is_rhs_const; [reflexivity..|].
  move=> [|[|?]] ??; [|done..] => - [<-] [<-].
  apply: is_rhs_abs; [reflexivity..|].

  do 2 (apply: is_rhs_var; [reflexivity..|]).

  apply: is_rhs_const; [reflexivity..|].
  move=> [|[|?]] ??; [|done..] => - [<-] [<-].
  apply: is_rhs_abs; [reflexivity..|].

  do 2 (apply: is_rhs_var; [reflexivity..|]).

  apply: is_rhs_const; [reflexivity..|].
  move=> [|[|?]] ??; [|done..] => - [<-] [<-].
  apply: is_rhs_abs; [reflexivity..|].

  do 1 (apply: is_rhs_var; [reflexivity..|]).

  apply: is_rhs_const; [reflexivity..|].
  by case.
Qed.

(* Properties of ex5
  + uses true constants
  + uses variable constants
  + distance between binding of a variable constant and use of it is arbitrary
  + number of abstractions is arbitrary
  + number of abstractions for variable constants before using a true constant is arbitrary
  + number of abstractions in the arena is bounded

  - number of abstractions in the solution term is not bounded! (TODO I want this to be bounded!)
*)

(* \s z2.s (\z1.s (\z0.s (\x.x) z0) z1) z2 *)
(* eta expansion of \s.s (s (s (\x.x))) *)
Definition ex5_0 :=
  tm 2 1 [tm 0 0 []; tm 1 2 [tm 0 0 []; tm 1 3 [tm 0 0 []; tm 1 0 []]]].

(* 
  [0] f : (a -> a) -> a
  [1] g : a -> a -> a
*)
(* \n y. f (\x. n (g y x)) *)
Definition ex5_1 :=
  tm 2 2 [tm 1 2 [tm 0 4 [tm 0 0 []; tm 0 1 []]]].

(* [2] h *)
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
    apply: solved_abs; [reflexivity..|cbn].
    apply: solved_var; [reflexivity..|cbn].
    apply: solved_var; [reflexivity..|cbn].
    apply: (solved_const _ _ _ _ _ _ _ [_]); [reflexivity..|cbn].
    move=> [|[|?]] ?; [|done..] => - [<-].
    apply: solved_abs; [reflexivity..|cbn].
    apply: solved_var; [reflexivity..|cbn].
    apply: solved_var; [reflexivity..|cbn].
    apply: (solved_const _ _ _ _ _ _ _ [_]); [reflexivity..|cbn].
    move=> [|[|?]] ?; [|done..] => - [<-].
    apply: solved_abs; [reflexivity..|cbn].
    apply: solved_var; [reflexivity..|cbn].
    apply: solved_var; [reflexivity..|cbn].
    apply: (solved_const _ _ _ _ _ _ _ [_; _]); [reflexivity..|cbn].
    move=> [|[|[|?]]] ?; [ | |done..] => - [<-].
    { apply: solved_abs; [reflexivity..|cbn].
      apply: (solved_const _ _ _ _ _ _ _ []); [reflexivity..|cbn].
      by case. }
    apply: solved_abs; [reflexivity..|cbn].
    apply: solved_var; [reflexivity..|cbn].
    apply: solved_var; [reflexivity..|cbn].
    apply: (solved_const _ _ _ _ _ _ _ [_; _]); [reflexivity..|cbn].
    move=> [|[|[|?]]] ?; [ | |done..] => - [<-].
    { apply: solved_abs; [reflexivity..|cbn].
      apply: (solved_const _ _ _ _ _ _ _ []); [reflexivity..|cbn].
      by case. }
    apply: solved_abs; [reflexivity..|cbn].
    apply: solved_var; [reflexivity..|cbn].
    apply: solved_var; [reflexivity..|cbn].
    apply: (solved_const _ _ _ _ _ _ _ [_; _]); [reflexivity..|cbn].
    move=> [|[|[|?]]] ?; [ | |done..] => - [<-].
    { apply: solved_abs; [reflexivity..|cbn].
      apply: (solved_const _ _ _ _ _ _ _ []); [reflexivity..|cbn].
      by case. }
    apply: solved_abs; [reflexivity..|cbn].
    apply: solved_var; [reflexivity..|cbn].
    apply: solved_var; [reflexivity..|cbn].
    apply: (solved_const _ _ _ _ _ _ _ []); [reflexivity..|cbn].
    by case. }
  cbn.
  apply: is_rhs_var; [reflexivity..|].
  apply: is_rhs_const; [reflexivity..|cbn].
  move=> [|[|?]] ??; [|done..] => - [<-] [<-].
  apply: is_rhs_abs; [reflexivity..|cbn].

  do 2 (apply: is_rhs_var; [reflexivity..|]).
  apply: is_rhs_const; [reflexivity..|cbn].
  move=> [|[|?]] ??; [|done..] => - [<-] [<-].
  apply: is_rhs_abs; [reflexivity..|cbn].

  do 2 (apply: is_rhs_var; [reflexivity..|]).
  apply: is_rhs_const; [reflexivity..|cbn].
  move=> [|[|?]] ??; [|done..] => - [<-] [<-].
  apply: is_rhs_abs; [reflexivity..|cbn].

  do 2 (apply: is_rhs_var; [reflexivity..|]).
  apply: is_rhs_const; [reflexivity..|cbn].
  move=> [|[|[|?]]] ??; [| |done..] => - [<-] [<-].
  { apply: is_rhs_abs; [reflexivity..|cbn].
    apply: is_rhs_const; [reflexivity..|cbn].
    by case. }
  
  apply: is_rhs_abs; [reflexivity..|cbn].
  do 2 (apply: is_rhs_var; [reflexivity..|]).
  apply: is_rhs_const; [reflexivity..|cbn].
  move=> [|[|[|?]]] ??; [| |done..] => - [<-] [<-].
  { apply: is_rhs_abs; [reflexivity..|cbn].
    apply: is_rhs_const; [reflexivity..|cbn].
    by case. }

  apply: is_rhs_abs; [reflexivity..|cbn].
  do 2 (apply: is_rhs_var; [reflexivity..|]).
  apply: is_rhs_const; [reflexivity..|cbn].
  move=> [|[|[|?]]] ??; [| |done..] => - [<-] [<-].
  { apply: is_rhs_abs; [reflexivity..|cbn].
    apply: is_rhs_const; [reflexivity..|cbn].
    by case. }

  apply: is_rhs_abs; [reflexivity..|cbn].
  do 2 (apply: is_rhs_var; [reflexivity..|]).
  apply: is_rhs_const; [reflexivity..|cbn].
  by case.
Qed.



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

(* g a *)
Definition result :=
  tm 0 1 [tm 0 0 []].

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
