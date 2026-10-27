(** * Uniformity properties of plays  [S, Section 6.1]

    Definitions 32, 33, 37 of the paper and its results Prop. 23-29 as
    axioms U1-U7.  In the paper these are derived from the results of
    Section 4 and the move rules; they speak only about plays, so we
    treat them as part of the game layer. *)

From Coq Require Import List Arith Bool Lia.
From HOM Require Import Syntax Lambda ITree Game.
Import ListNotations.

Section Defs.
  Variable E : ieq.
  Variable t : lnf.
  Variable pi : list pos.

  Local Notation nd := (nd E pi).

  (** [S, Def. 32]: [π[i, i+m]] and [π[j, j+m]] correspond. *)
  Definition correspond (i j m : nat) : Prop :=
    forall h, h <= m -> nd (i + h) = nd (j + h).

  (** [S, Def. 33] (with the conditions of [S, Prop. 24]):
      [π[j+1, j+k]] and [π[m+1, m+k]] are complementary. *)
  Definition complementary (j m k : nat) : Prop :=
    j < m /\ 1 <= k /\ same_var E t (nd j) (nd m) /\
    correspond (S j) (S m) (k - 1) /\
    ( (parent E t pi j (j + k + 1) /\ parent E t pi m (m + k + 1) /\
       forall p, nd (j + k + 1) = succ (nd j) p <-> nd (m + k + 1) = succ (nd m) p)
    \/ (cst_node E t (nd (j + k)) /\
        (m + k = length pi - 1 \/ nd (j + k + 1) <> nd (m + k + 1))) ).

  (** [S, Def. 37]: the recurrence property of a chain [js]
      (0-based: the entries at even indices are the [j(2i-1)]). *)
  Definition recurrence (js : list nat) : Prop :=
    forall x, x < length js -> Nat.even x = true ->
      var_node E t (nd (nth x js 0)) ->
      exists j k, j < nth x js 0 /\ complementary j (nth x js 0) k /\
                  nth (S x) js 0 = nth x js 0 + k + 1.

  (** A chain starting at [i] (the empty chain starts anywhere). *)
  Definition chain_from (i : nat) (js : list nat) : Prop :=
    chain_ok E t pi js /\ (js = [] \/ hd_error js = Some i).

  Definition rec_chain_from (i : nat) (js : list nat) : Prop :=
    chain_from i js /\ recurrence js.
End Defs.

(** U1 [S, Prop. 23]. *)
Axiom U1_between : forall E t pi i j m, WF E t -> play E t pi ->
  j < m -> parent E t pi i j -> parent E t pi i m ->
  exists k, j < k < m /\ parent E t pi j k.

(** U2 [S, Prop. 24]. *)
Axiom U2_complementary : forall E t pi i j m, WF E t -> play E t pi ->
  j < m -> parent E t pi i j -> parent E t pi i m ->
  nd E pi j <> nd E pi m -> same_var E t (nd E pi j) (nd E pi m) ->
  exists k, complementary E t pi j m k.

(** U3 [S, Fact 25]. *)
Axiom U3_end_child : forall E t pi i j j', WF E t -> play E t pi ->
  is_end E t (nd E pi i) -> parent E t pi i j -> parent E t pi i j' -> j = j'.

(** U4 [S, Fact 26]. *)
Axiom U4_level1 : forall E t pi j m, WF E t -> play E t pi -> j < m -> m < length pi ->
  in_t (nd E pi j) -> level E t (nd E pi j) 1 -> level E t (nd E pi m) 1 ->
  same_var E t (nd E pi j) (nd E pi m) ->
  exists k, complementary E t pi j m k.

(** U5 [S, Fact 27]. *)
Axiom U5_embedded : forall E t pi n m p j, WF E t -> play E t pi -> j < length pi ->
  same_var E t n m -> above (succ n p) m -> nd E pi j = m ->
  exists i k, i < j /\ nd E pi i = n /\ complementary E t pi i j k /\
    (is_end E t n -> is_end E t m -> pst (P E pi (S i)) = pst (P E pi (i + k)) ->
     nd E pi (j + k + 1) = succ (nd E pi j) p).

(** U6 [S, Prop. 28]. *)
Axiom U6_family : forall E t pi js j q x y, WF E t -> play E t pi ->
  chain_for E t pi js j -> in_w q (nd E pi j) ->
  Nat.even x = true -> Nat.even y = true -> x <= y < length js ->
  in_t (nd E pi (nth x js 0)) -> in_t (nd E pi (nth y js 0)) ->
  same_family E t (nd E pi (nth x js 0)) (nd E pi (nth y js 0)).

(** U7 [S, Prop. 29] with the uniqueness established in its proof: the
    chains with the recurrence property starting at a variable or
    constant position in some [w_q] are all prefixes of a longest one. *)
Axiom U7_longest_chain : forall E t pi i q, WF E t -> play E t pi -> i < length pi ->
  in_w q (nd E pi i) -> (var_node E t (nd E pi i) \/ cst_node E t (nd E pi i)) ->
  exists js, rec_chain_from E t pi i js /\
    forall js', rec_chain_from E t pi i js' -> exists rest, js = js' ++ rest.
