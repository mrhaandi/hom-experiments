Require Import List ssreflect.
Import ListNotations.

Inductive term : Type :=
  (* tm n x [t1; ...; tk] is the term
     \x1...\xn. x t1 ... tk
     where x is the de Bruijn index of a bound variable.
     If the variable is out of bounds, then it is a constant *)
  | tm : nat -> nat -> list term -> term.

Inductive lookup : Type :=
  | lk : list (term * lookup) -> lookup.

(* 
  (x, [t1; ...; tk], l, t) is the state
  where x is the de Bruijn index of head symbol
  t1; ...; tk are the arguments of the head symbol
  l is the lookup table
  t is the current right-hand side term
*)
Notation state := (nat * list term * list (term * lookup) * term)%type.

Definition add_lk (l : list (term * lookup)) (t : term) :=
  (t, lk l).

Arguments add_lk /.

(* for now / for simplicity let us consider rhs which does not contain abstraction
  e.g. f (\x.x) is not allowed as right-hand side
*)

Inductive solved : list (term * lookup) -> nat -> list term -> nat -> list term -> Prop :=
  | solved_var (x y : nat) (m : nat) (ts us : list term) (theta theta' : list (term * lookup))
    (z : nat) (rs : list term) :
    nth_error theta x = Some (tm m y us, lk theta') ->
    solved ((map (add_lk theta) (rev ts)) ++ theta') y us z rs ->
    solved theta x ts z rs
  | solved_const (x : nat) (ts us : list term) (theta : list (term * lookup)) :
    Forall2 (fun t u => match t, u with tm nt _ _, tm nu _ _ => nt = 0 /\ nu = 0 end) ts us ->
    (forall xt tts xu uts, In (tm 0 xt tts, tm 0 xu uts) (combine ts us) ->
      solved theta xt tts xu uts) ->
    solved theta (x + length theta) ts x us.

(* alternative characterization *)
Lemma solved_const' (x : nat) (ts us : list term) (theta : list (term * lookup)) :
  Forall2 (fun t u => match t, u with tm nt xt tts, tm nu xu uts => nt = 0 /\ nu = 0 /\ solved theta xt tts xu uts end) ts us ->
  solved theta (x + length theta) ts x us.
Proof.
  move=> H. apply: solved_const.
  - apply: Forall2_impl H.
    by move=> [] ??? [] ??? [->] [->].
  - elim: H; first done.
    move=> > H' ? IH > /= [].
    + move=> [??]. subst. tauto.
    + by apply: IH.
Qed.

(* t ts = u *)
Definition solved_start t (ts : list term) u :=
  match t, u with
  | tm n x us, tm m z rs => length ts = n /\ m = 0 /\ solved (map (add_lk []) (rev ts)) x us z rs
  end.

(*
  example 1
  (\x.x) a = a
*)

(* \x.x *)
Definition ex1_0 := tm 1 0 [].
(* a *)
Definition ex1_1 := tm 0 0 [].

Lemma solved_ex1 : solved_start ex1_0 [ex1_1] ex1_1.
Proof.
  cbn. split; [|split]; [reflexivity..|].
  apply: solved_var.
  - cbn. reflexivity.
  - cbn. apply: (solved_const 0).
    + constructor.
    + done.
Qed.

(* example Stirling
  constants:
  b := 2
  g := 1
  a := 0
*)

Definition main_solution :=
  tm 2 0 [tm 2 3 [tm 0 1 []; tm 2 5 [tm 0 8 []; tm 2 4 [tm 0 3 []; tm 0 3 []]]]].

Definition arg1 :=
  tm 2 0 [tm 0 1 []; tm 0 1 []].

Definition arg2 :=
  tm 1 0 [tm 0 0 [tm 0 1 []; tm 2 1 []]; tm 2 4 [tm 0 0 []]].

(* g a *)
Definition result :=
  tm 0 1 [tm 0 0 []].

Lemma solved_Stirling : solved_start main_solution [arg1; arg2] result.
Proof.
  unfold main_solution, arg1, arg2, result.
  cbn. split; [|split]; [reflexivity..|].
  apply: solved_var. { reflexivity. }
  apply: solved_var. { reflexivity. }
  apply: solved_var. { reflexivity. }
  apply: solved_var. { reflexivity. }
  apply: solved_var. { reflexivity. }
  apply: solved_var. { reflexivity. }
  apply: solved_var. { reflexivity. }

  apply: (solved_const' 1). constructor; last done.
  split; [done|split; [done|]].

  apply: solved_var. { reflexivity. }
  apply: solved_var. { reflexivity. }
  apply: solved_var. { reflexivity. }
  apply: solved_var. { reflexivity. }
  apply: solved_var. { reflexivity. }
  apply: solved_var. { reflexivity. }
  apply: solved_var. { reflexivity. }
  apply: solved_var. { reflexivity. }
  apply: solved_var. { reflexivity. }
  apply: solved_var. { reflexivity. }
  apply: solved_var. { reflexivity. }
  apply: solved_var. { reflexivity. }
  apply: solved_var. { reflexivity. }
  apply: solved_var. { reflexivity. }

  apply: (solved_const' 0). constructor.
Qed.
