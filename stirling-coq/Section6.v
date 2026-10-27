(** * Section 6 of the paper: T2, partition of plays, partition tree,
    unfolding.  Definitions, the uniqueness of the partition (proved),
    and the remaining steps of the paper stated as named propositions
    (gaps), not assumed. *)

From Coq Require Import List Arith Bool Lia Relations.
From HOM Require Import Syntax Lambda ITree Game GameLemmas Uniformity.
Import ListNotations.

(** ** End paths, redundancy and T2  [S, Defs. 39-42] *)

Definition end_path (E : ieq) (t : lnf) (g : list node) : Prop :=
  (exists p, 1 <= p /\ length g = 2 * p) /\
  (forall x, S x < length g -> exists s, nth (S x) g [] = succ (nth x g []) s) /\
  in_t (nth 0 g []) /\ var_node E t (nth 0 g []) /\
  (forall x, 2 <= x < length g -> Nat.even x = true ->
     var_node E t (nth x g []) /\
     exists y, y < x /\ binds E t (nth y g []) (nth x g [])) /\
  (* every variable strictly below the last node is bound strictly above
     the first node or strictly below the last node (strict reading) *)
  (forall v m, strictly_above (last g []) v -> binds E t m v ->
     strictly_above m (nth 0 g []) \/ strictly_above (last g []) m).

(** [S, Def. 41]: [g] is redundant in the interval [π[i,k]]. *)
Inductive redundant (E : ieq) (t : lnf) (pi : list pos) (g : list node)
  : nat -> nat -> Prop :=
  | red_none i k :
      (forall j1, i <= j1 < k -> nd E pi j1 <> nth 0 g []) -> redundant E t pi g i k
  | red_step i k j1 j js :
      i <= j1 < k -> nd E pi j1 = nth 0 g [] ->
      (forall j', i <= j' < j1 -> nd E pi j' <> nth 0 g []) ->
      j <= k -> chain_ok E t pi js -> hd_error js = Some j1 -> last js 0 = j ->
      map (nd E pi) js = g ->
      ~ contributes E pi j1 j -> redundant E t pi g j k -> redundant E t pi g i k.

Definition redundant_game (E : ieq) (t : lnf) (g : list node) : Prop :=
  forall pi, play E t pi -> redundant E t pi g 0 (length pi - 1).

(** [S, Def. 42]: replace the subtree at [m1] by the one at the
    successor of [m2p], with variables bound above [m1] re-indexed
    ([p] lambdas are removed between them). *)
Definition T2 (E : ieq) (t : lnf) (g : list node) : lnf :=
  match sub_at t (last g []) with
  | Some s => replace t (nth 0 g []) (lower (length g / 2) 0 s)
  | None => t
  end.

(** Gap 1 [S, Prop. 31]: soundness of T2.  The paper's proof needs a
    simulation lemma between plays of [t] and of [T2 t] (see the notes). *)
Definition Gap_T2_sound : Prop :=
  forall E t g, WF E t -> end_path E t g -> redundant_game E t g ->
    solves E t -> solves E (T2 E t g).

(** ** Partition of a play into stages  [S, Def. 43]
    0-based: the paper's stage [π[1,2]] is [[0,1]] here. *)

Definition longest_rec_chain E t pi i js : Prop :=
  rec_chain_from E t pi i js /\
  forall js', rec_chain_from E t pi i js' -> exists rest, js = js' ++ rest.

(** The cut: [p] is the least [p'] in [1..r] such that [π_(j(2p')+2)] is
    a child of [π_i], or [r] if there is none ([j(2p')] is the entry of
    index [2p'-1] of [js]). *)
Definition cut E t pi (i : nat) (js : list nat) (p : nat) : Prop :=
  let r := length js / 2 in
  (r = 0 /\ p = 0) \/
  (1 <= p <= r /\
   (parent E t pi i (nth (2 * p - 1) js 0 + 2) \/ p = r) /\
   forall p', 1 <= p' < p -> ~ parent E t pi i (nth (2 * p' - 1) js 0 + 2)).

Definition stage_end (i : nat) (js : list nat) (p : nat) : nat :=
  if p =? 0 then i + 3 else nth (2 * p - 1) js 0 + 2.

(** [stage E t pi N a b assoc]: stage [N] is [π[a,b]] and [assoc] is its
    associated chain (empty for constant stages and for stage 1). *)
Inductive stage (E : ieq) (t : lnf) (pi : list pos)
  : nat -> nat -> nat -> list nat -> Prop :=
  | stage_1 : stage E t pi 1 0 1 []
  | stage_cst N a b c :
      stage E t pi N a b c -> S b < length pi ->
      cst_node E t (nd E pi (S b)) ->
      stage E t pi (S N) (S b) (S (S b)) []
  | stage_var N a b c js p :
      stage E t pi N a b c -> S b < length pi ->
      var_node E t (nd E pi (S b)) ->
      longest_rec_chain E t pi (S b + 2) js -> cut E t pi (S b) js p ->
      stage E t pi (S N) (S b) (stage_end (S b) js p) (firstn (2 * p) js).

Lemma longest_unique : forall E t pi i js js',
  longest_rec_chain E t pi i js -> longest_rec_chain E t pi i js' -> js = js'.
Proof.
  intros E t pi i js js' [H1 H2] [H1' H2'].
  destruct (H2 js' H1') as [r1 Hr1]. destruct (H2' js H1) as [r2 Hr2].
  assert (Hl : length js = length js' + length r1)
    by (rewrite Hr1, app_length; reflexivity).
  assert (Hl' : length js' = length js + length r2)
    by (rewrite Hr2, app_length; reflexivity).
  destruct r1; [now rewrite app_nil_r in Hr1|simpl in Hl; lia].
Qed.

Lemma cut_unique : forall E t pi i js p p',
  cut E t pi i js p -> cut E t pi i js p' -> p = p'.
Proof.
  intros E t pi i js p p' Hp Hp'. unfold cut in *.
  destruct Hp as [[Hr ->]|[Hb [Hc Hmin]]];
    destruct Hp' as [[Hr' ->]|[Hb' [Hc' Hmin']]]; try lia.
  destruct (lt_eq_lt_dec p p') as [[Hlt|Heq]|Hlt]; auto.
  - exfalso. destruct Hc as [Hc|Hc].
    + apply (Hmin' p); auto. lia.
    + lia.
  - exfalso. destruct Hc' as [Hc'|Hc'].
    + apply (Hmin p'); auto. lia.
    + lia.
Qed.

Lemma cst_var_disjoint : forall E t n, cst_node E t n -> var_node E t n -> False.
Proof.
  intros E t n [c [a Hc]] [k [i [a' Hv]]]. congruence.
Qed.

Lemma stage_ge1 : forall E t pi N a b c, stage E t pi N a b c -> 1 <= N.
Proof. intros E t pi N a b c H. induction H; lia. Qed.

(** [S, Fact 33]: the partition is unique. *)
Theorem stage_unique : forall E t pi N a b c a' b' c',
  stage E t pi N a b c -> stage E t pi N a' b' c' -> a = a' /\ b = b' /\ c = c'.
Proof.
  intros E t pi N a b c a' b' c' H. revert a' b' c'.
  induction H as [|N a b c H IH Hlen Hc|N a b c js p H IH Hlen Hv Hjs Hcut];
    intros a' b' c' H'.
  - inversion H' as [|N0 a0 b0 c0 H0|N0 a0 b0 c0 js0 p0 H0]; subst; auto;
      apply stage_ge1 in H0; lia.
  - inversion H' as [|N0 a0 b0 c0 H0 Hlen0 Hc0|N0 a0 b0 c0 js0 p0 H0 Hlen0 Hv0 Hjs0 Hcut0];
      subst.
    + apply stage_ge1 in H; lia.
    + destruct (IH _ _ _ H0) as [_ [<- _]]. auto.
    + destruct (IH _ _ _ H0) as [_ [<- _]]. exfalso. eapply cst_var_disjoint; eauto.
  - inversion H' as [|N0 a0 b0 c0 H0 Hlen0 Hc0|N0 a0 b0 c0 js0 p0 H0 Hlen0 Hv0 Hjs0 Hcut0];
      subst.
    + apply stage_ge1 in H; lia.
    + destruct (IH _ _ _ H0) as [_ [<- _]]. exfalso. eapply cst_var_disjoint; eauto.
    + destruct (IH _ _ _ H0) as [_ [<- _]].
      pose proof (longest_unique _ _ _ _ _ _ Hjs Hjs0) as <-.
      pose proof (cut_unique _ _ _ _ _ _ _ Hcut Hcut0) as <-. auto.
Qed.

(** [S, Def. 44]. *)
Definition stage_final E pi (b : nat) : Prop := final (P E pi b).

Definition stage_contributes E pi (a b : nat) : Prop :=
  (~ stage_final E pi b /\ contributes E pi a b) \/
  (stage_final E pi b /\ contributes E pi a (b - 1)).

(** ** Combs and paths  [S, Def. 45] *)

Definition in_comb E t pi (a : nat) (n : node) : Prop :=
  n = nd E pi a \/ (exists s, n = succ (nd E pi a) s /\ is_node E t n).

Definition stage_path (E : ieq) (pi : list pos) (a b : nat) (assoc : list nat) : list node :=
  if assoc then [] else
  nd E pi (S a) :: map (nd E pi) assoc ++ [nd E pi (b - 1)].

(** ** Partition tree  [S, Def. 46]
    Stirling's definition: [N+1 -> K] where [K <= N] is the largest stage
    whose comb contains the last node of stage [N] and [N ->* M],
    [K ->* M] for some [M <= N].  Since every stage reaches stage 1, the
    second condition always holds (take [M = 1]), so the definition is
    the following. *)
Definition ptree_edge_S E t pi (N1 K : nat) : Prop :=
  exists N a b c ak bk ck, N1 = S N /\ stage E t pi N a b c /\
    stage E t pi K ak bk ck /\ K <= N /\ in_comb E t pi ak (nd E pi b) /\
    forall K' ak' bk' ck', K < K' <= N -> stage E t pi K' ak' bk' ck' ->
      ~ in_comb E t pi ak' (nd E pi b).

(** Proposed reading: [K] is the stage containing the parent of the last
    position of stage [N]. *)
Definition ptree_edge_P E t pi (N1 K : nat) : Prop :=
  exists N a b c h ak bk ck, N1 = S N /\ stage E t pi N a b c /\
    parent E t pi h b /\ stage E t pi K ak bk ck /\ ak <= h <= bk.

(** Gap 3: the parent is the first position of its stage, and every node
    of [t] visited by a play lies in some comb. *)
Definition Gap_partition_tree : Prop :=
  forall E t pi N a b c h, WF E t -> play E t pi -> solves E t ->
    stage E t pi N a b c -> ~ final (P E pi b) -> parent E t pi h b ->
    exists K bk ck, stage E t pi K h bk ck.

Definition Gap_coverage : Prop :=
  forall E t pi j, WF E t -> play E t pi -> solves E t -> j < length pi ->
    in_t (nd E pi j) ->
    exists N a b c, stage E t pi N a b c /\ in_comb E t pi a (nd E pi j).

(** ** Unfolding  [S, Def. 47], conditions (a)-(d)
    [Ns] lists the stages [N1 < ... < Nk] as triples (N, a, b) with
    their associated chains. *)
Definition unfoldable E t pi (Ns : list (nat * nat * nat * list nat)) : Prop :=
  Ns <> [] /\
  (forall x, x < length Ns -> let '(N, a, b, c) := nth x Ns (0, 0, 0, []) in
     stage E t pi N a b c /\ ~ stage_contributes E pi a b) /\
  (forall x y, x < y < length Ns ->
     let '(N, a, b, c) := nth x Ns (0, 0, 0, []) in
     let '(N', a', b', c') := nth y Ns (0, 0, 0, []) in
     N < N' /\ same_family E t (nd E pi a) (nd E pi a') /\
     nd E pi a <> nd E pi a' /\
     stage_path E pi a b c <> stage_path E pi a' b' c') /\
  (* (c): the stage after N_j points to some N_i, i <= j *)
  (forall y, y < length Ns ->
     let '(N, a, b, c) := nth y Ns (0, 0, 0, []) in
     (y = length Ns - 1 /\ final (P E pi b)) \/
     exists x, x <= y /\ let '(K, _, _, _) := nth x Ns (0, 0, 0, []) in
       ptree_edge_P E t pi (S N) K) /\
  (* (d): the root of each later path is a successor of the leaf of an
     earlier path *)
  (forall y, 0 < y < length Ns ->
     let '(_, a', b', c') := nth y Ns (0, 0, 0, []) in
     exists x s, x < y /\ let '(_, a, b, c) := nth x Ns (0, 0, 0, []) in
       nth 0 (stage_path E pi a' b' c') [] =
       succ (last (stage_path E pi a b c) []) s).

(** The construction of the enlarged comb and of the unfolded term, and
    the proof that the unfolded term is again a solution, are not given
    in the paper (Gap 4).  They are subsumed by the hypothesis of
    [Small.v], which is the statement of [S, Thm. 37]. *)
