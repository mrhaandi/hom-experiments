(** * Syntax: simple types, first-order goal terms, long normal forms.

    Formalization of C. Stirling, "An introduction to decidability of
    higher-order matching" (Section 2).  Restrictions (R1) single base
    type and (R2) goal without bound variables are built into the
    syntax: the goal is a first-order term [fo]. *)

From Coq Require Import List Arith Bool Lia Relations.
Import ListNotations.

(** ** Types  [S, Defs. 1-2]
    [Ty [A1;...;An]] is (A1,...,An,0); [Ty []] is the base type 0. *)

Inductive ty : Type := Ty (args : list ty).

Definition base : ty := Ty [].

Fixpoint ord (A : ty) : nat :=
  match A with Ty l => S (list_max (map ord l)) end.

Fixpoint ar (A : ty) : nat :=
  match A with Ty l => Nat.max (length l) (list_max (map ar l)) end.

Fixpoint ty_eqb (A B : ty) : bool :=
  match A, B with
  | Ty l1, Ty l2 =>
      (fix go (l1 l2 : list ty) : bool :=
         match l1, l2 with
         | [], [] => true
         | a :: r1, b :: r2 => ty_eqb a b && go r1 r2
         | _, _ => false
         end) l1 l2
  end.

Lemma ty_eqb_eq : forall A B, ty_eqb A B = true <-> A = B.
Proof.
  fix IH 1. intros [l1] [l2]. simpl.
  revert l2. induction l1 as [|a r1 IHr]; intros [|b r2]; simpl;
    try (split; intro H; congruence).
  rewrite andb_true_iff, IH, IHr. split.
  - intros [-> H]. now inversion H.
  - intro H. inversion H. subst. auto.
Qed.

Definition ty_eq_dec (A B : ty) : {A = B} + {A <> B}.
Proof.
  destruct (ty_eqb A B) eqn:E.
  - left. now apply ty_eqb_eq.
  - right. intro H. apply ty_eqb_eq in H. congruence.
Defined.

(** ** Constants
    A constant carries its name and its type. *)

Record cst : Type := Cst { cname : nat; ctyp : ty }.

Definition cst_eqb (c d : cst) : bool :=
  Nat.eqb (cname c) (cname d) && ty_eqb (ctyp c) (ctyp d).

Lemma cst_eqb_eq : forall c d, cst_eqb c d = true <-> c = d.
Proof.
  intros [n A] [m B]. unfold cst_eqb. simpl.
  rewrite andb_true_iff, Nat.eqb_eq, ty_eqb_eq.
  split; [intros [-> ->]; reflexivity | intro H; inversion H; auto].
Qed.

(** ** First-order goal terms  [S, Def. 11] *)

Inductive fo : Type := FApp (f : nat) (args : list fo).

Fixpoint fo_eqb (r s : fo) : bool :=
  match r, s with
  | FApp f l1, FApp g l2 =>
      Nat.eqb f g &&
      (fix go (l1 l2 : list fo) : bool :=
         match l1, l2 with
         | [], [] => true
         | a :: r1, b :: r2 => fo_eqb a b && go r1 r2
         | _, _ => false
         end) l1 l2
  end.

Lemma fo_eqb_eq : forall r s, fo_eqb r s = true <-> r = s.
Proof.
  fix IH 1. intros [f l1] [g l2]. simpl. rewrite andb_true_iff, Nat.eqb_eq.
  assert (H : (fix go (l1 l2 : list fo) : bool :=
         match l1, l2 with
         | [], [] => true
         | a :: r1, b :: r2 => fo_eqb a b && go r1 r2
         | _, _ => false
         end) l1 l2 = true <-> l1 = l2).
  { revert l2. induction l1 as [|a r1 IHr]; intros [|b r2]; simpl;
      try (split; intro H; congruence).
    rewrite andb_true_iff, IH, IHr. split.
    - intros [-> ->]. reflexivity.
    - intro H. inversion H. auto. }
  rewrite H. split; [intros [-> ->]; reflexivity | intro E; inversion E; auto].
Qed.

(** Size, depth, number of branches. *)
Fixpoint fo_size (r : fo) : nat :=
  match r with FApp _ l => S (list_sum (map fo_size l)) end.

Fixpoint fo_depth (r : fo) : nat :=
  match r with
  | FApp _ [] => 0
  | FApp _ l => S (list_max (map fo_depth l))
  end.

Fixpoint fo_branches (r : fo) : nat :=
  match r with
  | FApp _ [] => 1
  | FApp _ l => list_sum (map fo_branches l)
  end.

(** Immediate and reflexive-transitive subterm order on [fo]. *)
Inductive fo_child : fo -> fo -> Prop :=
  | fo_child_intro f l s : In s l -> fo_child s (FApp f l).

Definition fo_sub := clos_refl_trans fo fo_child.     (* r ⊑ s *)
Definition fo_psub := clos_trans fo fo_child.          (* r ⊏ s *)

Lemma list_max_ge : forall l x, In x l -> x <= list_max l.
Proof.
  intros l x H. pose proof (list_max_le l (list_max l)) as [H1 _].
  specialize (H1 (le_n _)). rewrite Forall_forall in H1. auto.
Qed.

Lemma fo_child_depth : forall s r, fo_child s r -> fo_depth s < fo_depth r.
Proof.
  intros s r H. destruct H as [f l s Hin]. simpl.
  destruct l as [|a l']; [destruct Hin|].
  apply Nat.lt_succ_r. apply list_max_ge. now apply in_map.
Qed.

Lemma fo_psub_depth : forall s r, fo_psub s r -> fo_depth s < fo_depth r.
Proof.
  intros s r H. induction H as [s r H|s m r _ IH1 _ IH2].
  - now apply fo_child_depth.
  - lia.
Qed.

Lemma fo_sub_depth : forall s r, fo_sub s r -> fo_depth s <= fo_depth r.
Proof.
  intros s r H. induction H as [s r H|r|s m r _ IH1 _ IH2].
  - apply fo_child_depth in H. lia.
  - lia.
  - lia.
Qed.

(** ** Long normal forms  [S, Def. 6]
    An lnf is [Lam As h args]: a lambda node binding variables of types
    [As] (possibly none: a dummy lambda), whose body is the head [h]
    applied to [args].  Variables are de Bruijn pairs [HVar k i]: the
    [i]-th variable (from 0) of the [k]-th enclosing lambda (0 = the
    lambda of this very node).  This is exactly the tree representation
    of [S, Section 3.1] with dummy lambdas. *)

Inductive head : Type :=
  | HVar (k i : nat)
  | HCst (c : cst).

Inductive lnf : Type := Lam (binders : list ty) (h : head) (args : list lnf).

(** Typing.  A context is the list of binder lists, innermost first. *)
Definition ctx := list (list ty).

Definition head_ty (G : ctx) (h : head) : option ty :=
  match h with
  | HVar k i => match nth_error G k with
                | Some As => nth_error As i
                | None => None
                end
  | HCst c => Some (ctyp c)
  end.

Fixpoint wt (G : ctx) (t : lnf) (A : ty) {struct t} : bool :=
  match t with
  | Lam As h args =>
      ty_eqb A (Ty As) &&
      match head_ty (As :: G) h with
      | Some (Ty Bs) =>
          (fix go (l : list lnf) (Bs : list ty) : bool :=
             match l, Bs with
             | [], [] => true
             | a :: l', B :: Bs' => wt (As :: G) a B && go l' Bs'
             | _, _ => false
             end) args Bs
      | None => false
      end
  end.

(** Constants occurring in a term. *)
Fixpoint consts (t : lnf) : list cst :=
  match t with
  | Lam _ h args =>
      (match h with HCst c => [c] | _ => [] end) ++ flat_map consts args
  end.

(** Size (number of tree nodes, dummy lambdas included) and depth
    (number of nodes on a longest path). *)
Fixpoint size (t : lnf) : nat :=
  match t with Lam _ _ args => 2 + list_sum (map size args) end.

Fixpoint depth (t : lnf) : nat :=
  match t with Lam _ _ args => 2 + list_max (map depth args) end.

(** Number of variable nodes. *)
Fixpoint nvars (t : lnf) : nat :=
  match t with
  | Lam _ h args =>
      (match h with HVar _ _ => 1 | HCst _ => 0 end) + list_sum (map nvars args)
  end.
