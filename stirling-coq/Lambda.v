(** * The lambda calculus, interpolation equations, solutions.
    [S, Sections 2.1-2.2]. *)

From Coq Require Import List Arith Bool Lia Relations.
From HOM Require Import Syntax.
Import ListNotations.

(** ** Raw de Bruijn terms with beta-reduction *)

Inductive tm : Type :=
  | tvar (n : nat)
  | tcst (c : cst)
  | tapp (s t : tm)
  | tlam (A : ty) (s : tm).

Fixpoint shift (d c : nat) (t : tm) : tm :=
  match t with
  | tvar n => if c <=? n then tvar (n + d) else tvar n
  | tcst x => tcst x
  | tapp a b => tapp (shift d c a) (shift d c b)
  | tlam A a => tlam A (shift d (S c) a)
  end.

(** [subst k u t]: replace variable [k] of [t] by [u] (which lives
    outside the [k] binders) and lower the variables above [k]. *)
Fixpoint subst (k : nat) (u t : tm) : tm :=
  match t with
  | tvar n => if n =? k then shift k 0 u
              else if k <? n then tvar (n - 1) else tvar n
  | tcst x => tcst x
  | tapp a b => tapp (subst k u a) (subst k u b)
  | tlam A a => tlam A (subst (S k) u a)
  end.

Inductive beta : tm -> tm -> Prop :=
  | beta_redex A s t : beta (tapp (tlam A s) t) (subst 0 t s)
  | beta_appl s s' t : beta s s' -> beta (tapp s t) (tapp s' t)
  | beta_appr s t t' : beta t t' -> beta (tapp s t) (tapp s t')
  | beta_lam A s s' : beta s s' -> beta (tlam A s) (tlam A s').

Definition red := clos_refl_trans tm beta.

Definition apps (h : tm) (l : list tm) : tm := fold_left tapp l h.

Fixpoint lams (As : list ty) (b : tm) : tm :=
  match As with [] => b | A :: As' => tlam A (lams As' b) end.

(** ** Embedding lnf into raw terms
    [lens] lists the numbers of variables bound by the enclosing
    lambdas, innermost first. *)

Definition var_index (lens : list nat) (k i : nat) : nat :=
  list_sum (firstn k lens) + (nth k lens 0 - 1 - i).

Fixpoint emb (lens : list nat) (t : lnf) : tm :=
  match t with
  | Lam As h args =>
      let lens' := length As :: lens in
      let hd := match h with
                | HVar k i => tvar (var_index lens' k i)
                | HCst c => tcst c
                end in
      lams As (apps hd (map (emb lens') args))
  end.

Fixpoint fo2tm (r : fo) : tm :=
  match r with
  | FApp f l => apps (tcst (Cst f (Ty (repeat base (length l))))) (map fo2tm l)
  end.

(** ** Interpolation equations  [S, Def. 9]
    [x w1 ... wk = u] with [x : (A1,...,Ak,0)]. *)

Record ieq : Type := IEq {
  eq_args : list ty;      (* A1 ... Ak *)
  eq_ws   : list lnf;     (* w1 ... wk *)
  eq_goal : fo            (* u *)
}.

Definition eq_ty (E : ieq) : ty := Ty (eq_args E).

Definition wf_eq (E : ieq) : Prop :=
  Forall2 (fun w A => wt [] w A = true) (eq_ws E) (eq_args E).

(** A candidate: a closed lnf of the type of [x]. *)
Definition cand (E : ieq) (t : lnf) : Prop := wt [] t (eq_ty E) = true.

(** [t] solves [E].  The paper asks [t w =βη u]; for lnf [t], [w] and
    a goal without binders this is equivalent to [t w ->β* u]
    [S, Prop. 4]; we take the latter as the definition. *)
Definition solves (E : ieq) (t : lnf) : Prop :=
  cand E t /\
  red (apps (emb [] t) (map (emb []) (eq_ws E))) (fo2tm (eq_goal E)).

(** ** The constants C_E  [S, Def. 10] *)

Fixpoint fo_consts (r : fo) : list cst :=
  match r with
  | FApp f l => Cst f (Ty (repeat base (length l))) :: flat_map fo_consts l
  end.

Fixpoint fo_names (r : fo) : list nat :=
  match r with FApp f l => f :: flat_map fo_names l end.

(** The fresh constant [b : 0]. *)
Definition cb (E : ieq) : cst := Cst (S (list_max (fo_names (eq_goal E)))) base.

Definition CE (E : ieq) : list cst := cb E :: fo_consts (eq_goal E).

Definition in_CE (E : ieq) (t : lnf) : Prop :=
  forall c, In c (consts t) -> In c (CE E).

(** Solutions in T_A(C_E).  By [S, Fact 6] (substitute [λ y. b] for
    constants outside C_E) nothing is lost by this restriction; we do
    not formalize that reduction. *)
Definition solution (E : ieq) (t : lnf) : Prop := solves E t /\ in_CE E t.

Definition solvable (E : ieq) : Prop := exists t, solution E t.

(** ** Background facts (standard; not proved here)

    L1. Decidability of [solves].  It follows from strong
    normalisation and confluence of the simply typed lambda calculus
    [S, Fact 1]: compute the normal form of [t w] and compare it with
    [u].  We state only the consequence that is used. *)
Axiom L1_solves_dec : forall E t, {solves E t} + {~ solves E t}.

Lemma in_CE_dec : forall E t, {in_CE E t} + {~ in_CE E t}.
Proof.
  intros E t. unfold in_CE.
  assert (Hd : forall c d : cst, {c = d} + {c <> d}).
  { intros c d. destruct (cst_eqb c d) eqn:H.
    - left. now apply cst_eqb_eq.
    - right. intro e. apply cst_eqb_eq in e. congruence. }
  induction (consts t) as [|c l IH].
  - left. intros c [].
  - destruct (in_dec Hd c (CE E)) as [Hc|Hc].
    + destruct IH as [IH|IH].
      * left. intros d [<-|Hd']; auto.
      * right. intro H. apply IH. intros d Hd'. apply H. now right.
    + right. intro H. apply Hc, H. now left.
Defined.

Lemma solution_dec : forall E t, {solution E t} + {~ solution E t}.
Proof.
  intros E t. unfold solution.
  destruct (L1_solves_dec E t); destruct (in_CE_dec E t); tauto.
Defined.
