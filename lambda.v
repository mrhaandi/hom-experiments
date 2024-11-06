Require Import List ssreflect.
Import ListNotations.

Inductive term : Type :=
  (* tm n x [tk; ...; t1] is the term
     \x1...\xn. x t1 ... tk
     where x is the de Bruijn index of a bound variable.
     If the variable is out of bounds, then it is a constant *)
  | tm : nat -> nat -> list term -> term.

(* a path is a list of indices to traverse a term *)

(* compute the subterm of t at path p *)
Fixpoint subterm (t : term) (p : list nat) : option term :=
  match t, p with
  | tm n x ts, [] => Some (tm n x ts)
  | tm n x ts, i :: p =>
    match nth_error ts i with
    | Some ti => subterm ti p
    | None => None
    end
  end.

Inductive rose_tree (A : Type) : Type :=
  | node : A -> list (rose_tree A) -> rose_tree A.

Arguments node {A}.

Inductive lookup : Type :=
  | lk : list ((nat * list nat) * lookup) -> lookup.
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
Definition add_lk (i : nat) (p : list nat) (theta : list ((nat * list nat) * lookup)) (j : nat) :=
  ((i, p ++ [j]), lk theta).

Arguments add_lk /.

(* for now / for simplicity let us consider rhs which does not contain abstraction
  e.g. f (\x.x) is not allowed as right-hand side
*)

(*
  solved TS i p theta game_tree r
    TS = [t, t1, ..., tk] where t is the solution and t1, ..., tk are arguments
    i is the term index in TS
    p is the path to the subterm in the particular term
    theta is the lookup table for free variables
    game_tree are positions ((i', p'), theta') in the game
    r is the rhs term (no abstractions)
  means that the game starting at position ((i, p), theta) with the rhs r is solved
*)

Inductive solved (TS : list term) (i : nat) (p : list nat) (theta : list ((nat * list nat) * lookup)) :
  rose_tree ((nat * list nat) * list ((nat * list nat) * lookup)) ->
  rose_tree nat -> Prop :=
    | solved_var t n x ts j q theta' r g :
      nth_error TS i = Some t ->
      subterm t p = Some (tm n x ts) ->
      nth_error theta x = Some ((j, q), lk theta') ->
      solved TS j q ((map (add_lk i p theta) (seq 0 (length ts))) ++ theta') g r ->
      solved TS i p theta (node ((i, p), theta) [g]) r
    | solved_const t gs n x ts rs :
      nth_error TS i = Some t ->
      subterm t p = Some (tm n (x + length theta) ts) ->
      length ts = length rs ->
      Forall2 (fun _ t => match t with tm nt _ _ => nt = 0 end) gs ts ->
      (forall g j r, In (g, (j, r)) (combine gs (combine (seq 0 (length rs)) rs)) ->
        solved TS i (p ++ [j]) theta g r) ->
      solved TS i p theta (node ((i, p), theta) gs) (node x rs).

(* t ts = r *)
Definition solved_start g t (ts : list term) (r : rose_tree nat) :=
  match t with
  | tm n x us =>
    length ts = n /\
    solved (t :: ts) 0 [] (map (fun j => ((S j, []), lk [])) (rev (seq 0 (length ts)))) g r
  end.

(*
  example 1
  (\x.x) a = a
*)

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
  - cbn. reflexivity.
  - cbn. apply: solved_const.
    + cbn. reflexivity.
    + cbn. reflexivity.
    + cbn. reflexivity.
    + cbn. constructor.
    + done.
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
