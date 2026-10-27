(** * Interpolation trees  [S, Section 3.1, Defs. 12, 34-36]

    Nodes are addresses (lists of positive integers).  The root [[]]
    is labelled [@]; [[1]] is the root of [t] and [[q+1]] the root of
    [w_q].  Below a lambda node the only successor (index 1) is the
    head node; below a head node the successors [1..m] are the lambda
    nodes of its arguments.  Lambda nodes have odd length. *)

From Coq Require Import List Arith Bool Lia.
From HOM Require Import Syntax Lambda.
Import ListNotations.

Definition node := list nat.

Fixpoint node_eqb (m n : node) : bool :=
  match m, n with
  | [], [] => true
  | a :: m', b :: n' => Nat.eqb a b && node_eqb m' n'
  | _, _ => false
  end.

Lemma node_eqb_eq : forall m n, node_eqb m n = true <-> m = n.
Proof.
  induction m as [|a m IH]; intros [|b n]; simpl;
    try (split; intro H; congruence).
  rewrite andb_true_iff, Nat.eqb_eq, IH.
  split; [intros [-> ->]; reflexivity | intro H; inversion H; auto].
Qed.

Definition succ (n : node) (i : nat) : node := n ++ [i].
Definition succs (n : node) (p : nat) : list node := map (succ n) (seq 1 p).

(** [m] is above [n] (reflexive). *)
Definition above (m n : node) : Prop := exists w, n = m ++ w.
Definition strictly_above (m n : node) : Prop := above m n /\ m <> n.

(** What sits at a node. *)
Inductive item : Type :=
  | ILam (t : lnf)      (* the lambda node of [t] *)
  | IHead (t : lnf).    (* the head node of [t] *)

Inductive ritem : Type := RApp | RIt (it : item).

Fixpoint walk (it : item) (p : list nat) : option item :=
  match p with
  | [] => Some it
  | i :: p' =>
      match it with
      | ILam t => if i =? 1 then walk (IHead t) p' else None
      | IHead (Lam _ _ args) =>
          if i =? 0 then None
          else match nth_error args (i - 1) with
               | Some a => walk (ILam a) p'
               | None => None
               end
      end
  end.

(** Labels  [S, Def. 12]. *)
Inductive label : Type :=
  | LApp
  | LLam (As : list ty)
  | LVar (k i : nat) (nargs : nat)   (* the variable HVar k i *)
  | LCst (c : cst) (nargs : nat).

Definition ilabel (o : option item) : option label :=
  match o with
  | Some (ILam (Lam As _ _)) => Some (LLam As)
  | Some (IHead (Lam _ (HVar k i) args)) => Some (LVar k i (length args))
  | Some (IHead (Lam _ (HCst c) args)) => Some (LCst c (length args))
  | None => None
  end.

Section Tree.
  Variable E : ieq.
  Variable t : lnf.

  Definition comps : list lnf := t :: eq_ws E.

  Definition item_at (n : node) : option ritem :=
    match n with
    | [] => Some RApp
    | j :: p =>
        if j =? 0 then None
        else match nth_error comps (j - 1) with
             | Some c => option_map RIt (walk (ILam c) p)
             | None => None
             end
    end.

  Definition label_at (n : node) : option label :=
    match item_at n with
    | Some RApp => Some LApp
    | Some (RIt it) => ilabel (Some it)
    | None => None
    end.

  Definition is_node (n : node) : Prop := label_at n <> None.

  Definition lam_node (n : node) : Prop := exists As, label_at n = Some (LLam As).
  Definition binding_node (n : node) : Prop :=
    exists As, label_at n = Some (LLam As) /\ As <> [].
  Definition var_node (n : node) : Prop :=
    exists k i a, label_at n = Some (LVar k i a).
  Definition cst_node (n : node) : Prop :=
    exists c a, label_at n = Some (LCst c a).
  Definition pos_cst_node (n : node) : Prop :=
    exists c a, label_at n = Some (LCst c a) /\ 0 < a.

  (** The binder of the variable [HVar k i] at head node [n]: [k]
      lambda nodes up from the lambda node directly above [n]. *)
  Definition binder (n : node) (k : nat) : node :=
    firstn (length n - 1 - 2 * k) n.

  (** [m ↓ n]: [m] binds the variable at [n]. *)
  Definition binds (m n : node) : Prop :=
    exists k i a, label_at n = Some (LVar k i a) /\ m = binder n k.

  (** Two variable nodes carry the same variable. *)
  Definition same_var (n m : node) : Prop :=
    exists k i a k' a', label_at n = Some (LVar k i a) /\
      label_at m = Some (LVar k' i a') /\ binder n k = binder m k'.

  (** Components. *)
  Definition in_t (n : node) : Prop := exists p, n = 1 :: p.
  Definition in_w (q : nat) (n : node) : Prop := exists p, n = S q :: p.

  (** ** Structural notions  [S, Defs. 34-36] *)

  Inductive level : node -> nat -> Prop :=
    | level_1 n m j : binds m n -> m = [j] -> level n 1
    | level_S n m l j : binds m n -> m = succ l j -> level l j -> level n (S j).

  Definition embedded (m : node) : Prop :=
    exists n, n <> m /\ above n m /\ same_var n m.

  Inductive desc_ub : node -> node -> Prop :=      (* desc_ub n m: n descends from m *)
    | desc_refl n : var_node n -> desc_ub n n
    | desc_step n m i n' : binds (succ m i) n' -> desc_ub n n' -> desc_ub n m.

  Definition same_family (n m : node) : Prop :=
    exists a, desc_ub n a /\ desc_ub m a.

  Definition is_end (n : node) : Prop :=
    var_node n /\ forall n', desc_ub n' n -> n' = n.
End Tree.

(** ** Replacing a subtree at a head node of [t]
    [p] is the address inside [t] (without the leading [1]) of a head
    node; the head and arguments there are replaced by [h'] and [a']. *)

Fixpoint update_nth {A} (i : nat) (f : A -> A) (l : list A) : list A :=
  match l, i with
  | [], _ => []
  | x :: l', 0 => f x :: l'
  | x :: l', S i' => x :: update_nth i' f l'
  end.

Fixpoint repl (t : lnf) (p : list nat) (h' : head) (a' : list lnf) {struct p} : lnf :=
  match t, p with
  | Lam As h args, [1] => Lam As h' a'
  | Lam As h args, 1 :: S i :: p' =>
      Lam As h (update_nth i (fun a => repl a p' h' a') args)
  | _, _ => t
  end.

(** [t[s/n]] for a node [n = 1 :: p] of the t-component and
    [s = Lam [] h' a' : 0]. *)
Definition replace (t : lnf) (n : node) (s : lnf) : lnf :=
  match n, s with
  | 1 :: p, Lam _ h' a' => repl t p h' a'
  | _, _ => t
  end.

(** Lowering de Bruijn levels by [d] for variables bound outside a
    subterm ([c] counts the lambdas entered inside the subterm). *)
Definition lower_head (d c : nat) (h : head) : head :=
  match h with
  | HVar k i => if c <? k then HVar (k - d) i else HVar k i
  | HCst x => HCst x
  end.

Fixpoint lower (d c : nat) (t : lnf) : lnf :=
  match t with
  | Lam As h args => Lam As (lower_head d c h) (map (lower d (S c)) args)
  end.

(** The subterm of [t] at a lambda node [1 :: p]. *)
Definition sub_at (t : lnf) (n : node) : option lnf :=
  match n with
  | 1 :: p => match walk (ILam t) p with Some (ILam s) => Some s | _ => None end
  | _ => None
  end.
