(** * The interpolation game  [S, Section 4]

    Definitions of positions, look-up tables, moves and plays, of
    parents and chains, and the results of Section 4 of the paper as
    axioms G1-G10.  Plays are indexed from 0 (the paper indexes from
    1): paper position [π_{i+1}] is [P pi i] here. *)

From Coq Require Import List Arith Bool Lia Relations.
From HOM Require Import Syntax Lambda ITree.
Import ListNotations.

(** ** States and look-up tables  [S, Defs. 16-17, 24] *)

Inductive state : Type := SR (r : fo) | SAll | SEx.

Inductive table : Type := Tbl (entries : list (node * (list node * table))).

Definition tempty : table := Tbl [].

Definition tlook (th : table) (m : node) : option (list node * table) :=
  match th with
  | Tbl es => match find (fun e => node_eqb (fst e) m) es with
              | Some (_, v) => Some v
              | None => None
              end
  end.

(** [θ{v/m}]: the new entry shadows any old one. *)
Definition tupd (th : table) (m : node) (v : list node * table) : table :=
  match th with Tbl es => Tbl ((m, v) :: es) end.

(** Extensional equality of tables: same domain, same node lists,
    extensionally equal stored tables. *)
Inductive teq : table -> table -> Prop :=
  | teq_intro th1 th2 :
      (forall m, entry_eq (tlook th1 m) (tlook th2 m)) -> teq th1 th2
with entry_eq : option (list node * table) -> option (list node * table) -> Prop :=
  | ee_none : entry_eq None None
  | ee_some ms a b : teq a b -> entry_eq (Some (ms, a)) (Some (ms, b)).

(** [θ ≤ θ']: θ' extends θ. *)
Definition tle (th th' : table) : Prop :=
  forall m v, tlook th m = Some v -> entry_eq (Some v) (tlook th' m).

(** ** Positions and moves  [S, Def. 19, Fig. 5] *)

Record pos : Type := Pos { pnode : node; pst : state; ptab : table }.

Section Game.
  Variable E : ieq.
  Variable t : lnf.

  Definition k_args : nat := length (eq_ws E).

  (** The move depends only on the label at the current node. *)
  Definition step (p : pos) : list pos :=
    match pst p with
    | SR r =>
      match label_at E t (pnode p) with
      | Some LApp =>
          [Pos [1] (SR r)
               (tupd (ptab p) [1] (map (fun j => [j]) (seq 2 k_args), ptab p))]
      | Some (LLam _) => [Pos (succ (pnode p) 1) (SR r) (ptab p)]
      | Some (LCst c 0) =>
          [Pos (pnode p) (if fo_eqb r (FApp (cname c) []) then SEx else SAll) (ptab p)]
      | Some (LCst c (S a')) =>
          match r with
          | FApp f rs =>
              if (f =? cname c) && (length rs =? S a')
              then map (fun jr => Pos (succ (pnode p) (fst jr)) (SR (snd jr)) (ptab p))
                       (combine (seq 1 (length rs)) rs)
              else [Pos (pnode p) SAll (ptab p)]
          end
      | Some (LVar k i a) =>
          match tlook (ptab p) (binder (pnode p) k) with
          | Some (ms, th') =>
              match nth_error ms i with
              | Some mj =>
                  match a with
                  | 0 => [Pos mj (SR r) th']
                  | S _ => [Pos mj (SR r) (tupd th' mj (succs (pnode p) a, ptab p))]
                  end
              | None => []
              end
          | None => []
          end
      | None => []
      end
    | _ => []
    end.

  (** ** Plays  [S, Defs. 18, 20] *)

  Definition init : pos := Pos [] (SR (eq_goal E)) tempty.

  Definition final (p : pos) : Prop :=
    match pst p with SR _ => False | _ => True end.

  Definition P (pi : list pos) (i : nat) : pos := nth i pi init.
  Definition nd pi i := pnode (P pi i).
  Definition th pi i := ptab (P pi i).

  (** A run: a sequence of moves from the initial position. *)
  Definition run (pi : list pos) : Prop :=
    nth_error pi 0 = Some init /\
    (forall i, S i < length pi -> In (P pi (S i)) (step (P pi i)) /\ ~ final (P pi i)).

  Definition play (pi : list pos) : Prop :=
    run pi /\ final (P pi (length pi - 1)).

  Definition forall_loses : Prop :=
    forall pi, play pi -> pst (P pi (length pi - 1)) = SEx.

  (** ** Parents and chains  [S, Defs. 21-23] *)

  Definition parent_var (pi : list pos) (i j : nat) : Prop :=
    i < j /\ j < length pi /\
    binds E t (nd pi i) (nd pi j) /\
    entry_eq (tlook (th pi i) (nd pi i)) (tlook (th pi j) (nd pi i)).

  Definition parent (pi : list pos) (i j : nat) : Prop :=
    parent_var pi i j \/
    (lam_node E t (nd pi j) /\ 0 < j < length pi /\
     let a := removelast (nd pi j) in
     (a = [] /\ i = 0) \/
     (cst_node E t a /\ i = j - 1) \/
     (var_node E t a /\ parent_var pi (S i) (j - 1))).

  (** [chain_ok pi [j1; ...; j2p]]: [π_{j(2m-1)}] is the parent of the
      lambda position [π_{j(2m)}], and [j(2m+1) = j(2m) + 1]. *)
  Fixpoint chain_ok (pi : list pos) (js : list nat) : Prop :=
    match js with
    | [] => True
    | [_] => False
    | a :: b :: rest =>
        parent pi a b /\ lam_node E t (nd pi b) /\
        match rest with
        | [] => True
        | c :: _ => c = S b /\ chain_ok pi rest
        end
    end.

  (** A chain for [π_j]. *)
  Definition chain_for (pi : list pos) (js : list nat) (j : nat) : Prop :=
    chain_ok pi js /\ last js j = j /\ js <> [].

  (** ** Contribution  [S, Def. 40, extended as in the notes] *)
  Definition contributes (pi : list pos) (i j : nat) : Prop :=
    i <= j /\ S j < length pi /\
    exists ri rj, pst (P pi i) = SR ri /\ pst (P pi j) = SR rj /\ ri <> rj.
End Game.


(** ** Axioms for the game part  [S, Section 4]

    In all axioms [E] is well formed and [t] is a candidate. *)

Definition WF (E : ieq) (t : lnf) : Prop := wf_eq E /\ cand E t.

(** G1 [S, Thm. 13]. *)
Axiom G1_characterisation : forall E t, WF E t ->
  (forall_loses E t <-> solves E t).

(** G2 [S, Prop. 12 and corollary of the proof of Thm. 13]: the moves
    are defined at every reachable non-final position, and runs are
    bounded. *)
Axiom G2_total : forall E t pi, WF E t -> run E t pi ->
  ~ final (P E pi (length pi - 1)) -> step E t (P E pi (length pi - 1)) <> [].
Axiom G2_bounded : forall E t, WF E t ->
  exists N, forall pi, run E t pi -> length pi <= N.

(** G3 [S, Fact 10]. *)
Axiom G3_branches : forall E t, WF E t -> solves E t ->
  exists L : list (list pos), NoDup L /\ (forall pi, play E t pi <-> In pi L) /\
    length L = fo_branches (eq_goal E).

(** G4 [S, Fact 11] (0-based: paper index [i+1] is [i] here). *)
Axiom G4_parity : forall E t pi i, WF E t -> play E t pi -> S i < length pi ->
  (Nat.odd i = true -> lam_node E t (nd E pi i)) /\
  (Nat.even i = true -> 0 < i -> var_node E t (nd E pi i) \/ cst_node E t (nd E pi i)).
Axiom G4_last : forall E t pi, WF E t -> play E t pi ->
  cst_node E t (nd E pi (length pi - 1)).
Axiom G4_states : forall E t pi i j ri rj, WF E t -> play E t pi ->
  i < j -> S j < length pi ->
  pst (P E pi i) = SR ri -> pst (P E pi j) = SR rj -> fo_sub rj ri.

(** G5 [S, Prop. 12]. *)
Axiom G5_domain : forall E t pi j n, WF E t -> play E t pi -> j < length pi ->
  (tlook (th E pi j) n <> None <-> binding_node E t n /\ above n (nd E pi j)).
Axiom G5_entry : forall E t pi j m ms th', WF E t -> play E t pi -> j < length pi ->
  tlook (th E pi j) m = Some (ms, th') ->
  (exists As, label_at E t m = Some (LLam As) /\ length As = length ms) /\
  (forall n, tlook th' n <> None <->
     binding_node E t n /\ forall mk, In mk ms -> strictly_above n mk) /\
  exists i, i < j /\ teq th' (th E pi i) /\
    ((i = 0 /\ ms = map (fun q => [q]) (seq 2 (k_args E))) \/
     (var_node E t (nd E pi i) /\ ms = succs (nd E pi i) (length ms))).

(** G6 [S, Prop. 14]. *)
Axiom G6_distinct : forall E t pi i j, WF E t -> play E t pi ->
  i <> j -> i < length pi -> j < length pi -> nd E pi i = nd E pi j ->
  ~ teq (th E pi i) (th E pi j).

(** G7 [S, Prop. 15, Fact 16]. *)
Axiom G7_parent : forall E t pi j, WF E t -> play E t pi -> 0 < j -> S j < length pi ->
  (var_node E t (nd E pi j) \/ lam_node E t (nd E pi j)) ->
  exists i, parent E t pi i j /\ (forall i', parent E t pi i' j -> i' = i) /\ i < j /\
    (lam_node E t (nd E pi j) -> exists s, nd E pi j = succ (nd E pi i) s).

(** G8 [S, Props. 17-18]. *)
Axiom G8_parent_mono : forall E t pi i j, WF E t -> play E t pi ->
  parent E t pi i j -> lam_node E t (nd E pi j) -> tle (th E pi i) (th E pi j).
Axiom G8_chain_mono : forall E t pi js x y, WF E t -> play E t pi -> chain_ok E t pi js ->
  x < y < length js -> tle (th E pi (nth x js 0)) (th E pi (nth y js 0)).
Axiom G8_chain_binds : forall E t pi js x y, WF E t -> play E t pi -> chain_ok E t pi js ->
  x < y < length js -> binds E t (nd E pi (nth x js 0)) (nd E pi (nth y js 0)) ->
  parent E t pi (nth x js 0) (nth y js 0).

(** G9 [S, Prop. 19]. *)
Axiom G9_agree : forall E t pi i j m m', WF E t -> play E t pi ->
  i < length pi -> j < length pi ->
  tlook (th E pi i) m <> None ->
  entry_eq (tlook (th E pi i) m) (tlook (th E pi j) m) ->
  binding_node E t m' -> above m' m ->
  entry_eq (tlook (th E pi i) m') (tlook (th E pi j) m').

(** G10 (used in the proof of [S, Prop. 23]): jumps alternate
    between [t] and the [w_q]. *)
Axiom G10_alternation : forall E t pi j, WF E t -> play E t pi -> S j < length pi ->
  var_node E t (nd E pi j) ->
  lam_node E t (nd E pi (S j)) /\ (in_t (nd E pi j) <-> ~ in_t (nd E pi (S j))).
