(** * Unfolding with a linear head  (order <= 5, notes Section 2)

    Raw-term version of Theorem 3 of hom/order5-unfolding.md.  A
    z-node [n = z A1 ... Am] of [t] whose [w_i] has the form
    [λ x̄. x_j B̄] with [x_j] not free in [B̄]; an occurrence
    [ny = y R̄] of a variable bound by the [j]-th argument
    [A_j = λ ȳ. S_j].  The unfolded term replaces [ny] by
    [z A1 ... (λ ȳ'. y' R̄) ... Am].  We prove that [t w̄] and
    [t' w̄] have a common reduct, hence [t'] solves the equation
    whenever [t] does.  No game axiom is used. *)

From Coq Require Import List Arith Bool Lia Relations.
From HOM Require Import Syntax Lambda Confluence.
Import ListNotations.

(** ** Contexts *)

Inductive ctx : Type :=
  | Hole
  | CAppL (C : ctx) (t : tm)
  | CAppR (s : tm) (C : ctx)
  | CLam (A : ty) (C : ctx).

Fixpoint plug (C : ctx) (t : tm) : tm :=
  match C with
  | Hole => t
  | CAppL C' u => tapp (plug C' t) u
  | CAppR s C' => tapp s (plug C' t)
  | CLam A C' => tlam A (plug C' t)
  end.

Fixpoint cdepth (C : ctx) : nat :=
  match C with
  | Hole => 0
  | CAppL C' _ | CAppR _ C' => cdepth C'
  | CLam _ C' => S (cdepth C')
  end.

Lemma red_plug : forall C a b, red a b -> red (plug C a) (plug C b).
Proof.
  induction C as [|C IH u|s C IH|A C IH]; intros a b H; simpl.
  - exact H.
  - apply red_app; [now apply IH|apply rt_refl].
  - apply red_app; [apply rt_refl|now apply IH].
  - apply red_lam. now apply IH.
Qed.

(** ** Simultaneous substitution
    [msubst k l t] replaces the variables [k .. k + |l| - 1] of [t] by
    the terms of [l] (the last element of [l] for variable [k]) and
    lowers the variables above. *)

Fixpoint msubst (k : nat) (l : list tm) (t : tm) : tm :=
  match t with
  | tvar n =>
      if n <? k then tvar n
      else if n <? k + length l then shift k 0 (nth (k + length l - 1 - n) l (tvar 0))
      else tvar (n - length l)
  | tcst x => tcst x
  | tapp a b => tapp (msubst k l a) (msubst k l b)
  | tlam A a => tlam A (msubst (S k) l a)
  end.

Fixpoint cmsubst (k : nat) (l : list tm) (C : ctx) : ctx :=
  match C with
  | Hole => Hole
  | CAppL C' u => CAppL (cmsubst k l C') (msubst k l u)
  | CAppR s C' => CAppR (msubst k l s) (cmsubst k l C')
  | CLam A C' => CLam A (cmsubst (S k) l C')
  end.

Lemma msubst_plug : forall C k l t,
  msubst k l (plug C t) = plug (cmsubst k l C) (msubst (k + cdepth C) l t).
Proof.
  induction C; intros k l t0; simpl; try rewrite IHC; auto.
  - now rewrite Nat.add_0_r.
  - rewrite Nat.add_succ_r. reflexivity.
Qed.

Lemma msubst_apps : forall k l h ts,
  msubst k l (apps h ts) = apps (msubst k l h) (map (msubst k l) ts).
Proof.
  intros k l h ts. revert h. unfold apps.
  induction ts as [|a ts IH]; intros h; simpl; auto.
Qed.

Lemma msubst_lams : forall As k l b,
  msubst k l (lams As b) = lams As (msubst (k + length As) l b).
Proof.
  induction As as [|A As IH]; intros k l b; simpl.
  - now rewrite Nat.add_0_r.
  - rewrite IH, Nat.add_succ_r. reflexivity.
Qed.

Lemma shift_apps : forall d c h ts,
  shift d c (apps h ts) = apps (shift d c h) (map (shift d c) ts).
Proof.
  intros d c h ts. revert h. unfold apps.
  induction ts as [|a ts IH]; intros h; simpl; auto.
Qed.

Lemma shift_lams : forall As d c b,
  shift d c (lams As b) = lams As (shift d (c + length As) b).
Proof.
  induction As as [|A As IH]; intros d c b; simpl.
  - now rewrite Nat.add_0_r.
  - rewrite IH, Nat.add_succ_r. reflexivity.
Qed.

Lemma subst_lams : forall As k u b,
  subst k u (lams As b) = lams As (subst (k + length As) u b).
Proof.
  induction As as [|A As IH]; intros k u b; simpl.
  - now rewrite Nat.add_0_r.
  - rewrite IH, Nat.add_succ_r. reflexivity.
Qed.

Lemma msubst_shift_cancel : forall t l d c k, c <= k <= c + d ->
  msubst k l (shift (length l + d) c t) = shift d c t.
Proof.
  induction t as [n|x|a IHa b IHb|A a IHt]; intros l d c k Hk; cbn [shift msubst];
    [ | reflexivity | f_equal; [apply IHa|apply IHb]; lia | f_equal; apply IHt; lia ].
  leb_cases; cbn [msubst]; leb_cases; f_equal; lia.
Qed.

Lemma msubst_cons : forall b k l a,
  msubst k l (subst (k + length l) a b) = msubst k (a :: l) b.
Proof.
  induction b as [n|x|b1 IH1 b2 IH2|A b IHb]; intros k l a; cbn [subst msubst];
    [ | reflexivity | f_equal; auto | f_equal ].
  - change (length (a :: l)) with (S (length l)).
    leb_cases; cbn [msubst]; leb_cases; try (f_equal; lia); try lia.
    + replace (k + length l) with (length l + k) by lia.
      rewrite (msubst_shift_cancel a l k 0 k) by lia.
      replace (k + S (length l) - 1 - n) with 0 by lia. reflexivity.
    + replace (k + S (length l) - 1 - n) with (S (k + length l - 1 - n)) by lia.
      reflexivity.
  - replace (S (k + length l)) with (S k + length l) by lia. apply IHb.
Qed.

Lemma red_apps_head : forall l h h', red h h' -> red (apps h l) (apps h' l).
Proof.
  unfold apps. induction l as [|a l IH]; intros h h' H; simpl; auto.
  apply IH. apply red_app; auto. apply rt_refl.
Qed.

Lemma msubst_nil : forall b k, msubst k [] b = b.
Proof.
  induction b as [n|x|b1 IH1 b2 IH2|A b IHb]; intros k; cbn [msubst length];
    [ | reflexivity | f_equal; auto | f_equal; auto ].
  leb_cases; f_equal; lia.
Qed.

Lemma red_apps_lams : forall As l b, length As = length l ->
  red (apps (lams As b) l) (msubst 0 l b).
Proof.
  induction As as [|A As IH]; intros [|a l] b Hl; simpl in Hl; try discriminate.
  - rewrite msubst_nil. apply rt_refl.
  - cbn [lams]. unfold apps at 1. cbn [fold_left].
    apply rt_trans with (apps (subst 0 a (lams As b)) l).
    + apply red_apps_head. apply rt_step. constructor.
    + rewrite subst_lams. simpl. rewrite <- msubst_cons.
      replace (length As) with (length l) by lia. apply IH. lia.
Qed.

(** ** Bounded free variables *)

Fixpoint bnd (n : nat) (t : tm) : Prop :=
  match t with
  | tvar m => m < n
  | tcst _ => True
  | tapp a b => bnd n a /\ bnd n b
  | tlam _ a => bnd (S n) a
  end.

Lemma bnd_mono : forall t n m, n <= m -> bnd n t -> bnd m t.
Proof.
  induction t as [x|x|a IHa b IHb|A a IHt]; intros n m Hnm H; simpl in *.
  - lia.
  - auto.
  - destruct H; split; eauto.
  - apply (IHt (S n)); auto. lia.
Qed.

Lemma shift_bnd : forall t n d c, n <= c -> bnd n t -> shift d c t = t.
Proof.
  induction t as [x|x|a IHa b IHb|A a IHt]; intros n d c Hc H; simpl in *.
  - leb_cases; f_equal; lia.
  - reflexivity.
  - destruct H. f_equal; eauto.
  - f_equal. apply (IHt (S n)); auto. lia.
Qed.

Lemma msubst_bnd : forall t n k l, n <= k -> bnd n t -> msubst k l t = t.
Proof.
  induction t as [x|x|a IHa b IHb|A a IHt]; intros n k l Hk H; simpl in *.
  - leb_cases; f_equal; lia.
  - reflexivity.
  - destruct H. f_equal; eauto.
  - f_equal. apply (IHt (S n)); auto. lia.
Qed.

Lemma bnd_apps : forall ts n h, bnd n (apps h ts) <-> bnd n h /\ Forall (bnd n) ts.
Proof.
  unfold apps. induction ts as [|a ts IH]; intros n h; simpl.
  - split; [intros H; split; auto|intros [H _]; auto].
  - rewrite IH. simpl. rewrite Forall_cons_iff. tauto.
Qed.

Lemma bnd_lams : forall As n b, bnd n (lams As b) <-> bnd (n + length As) b.
Proof.
  induction As as [|A As IH]; intros n b; simpl.
  - now rewrite Nat.add_0_r.
  - rewrite IH. now rewrite Nat.add_succ_r.
Qed.

(** ** Shifting commutes with substitution *)

Lemma shift_msubst : forall t d c k l, c <= k ->
  shift d c (msubst k l t) = msubst (k + d) l (shift d c t).
Proof.
  induction t as [n|x|a IHa b IHb|A a IHt]; intros d c k l Hk; cbn [shift msubst];
    [ | reflexivity | f_equal; [apply IHa|apply IHb]; lia | f_equal ].
  - leb_cases; cbn [shift msubst]; leb_cases; try (f_equal; lia); try lia.
    rewrite shift_shift_in by lia. f_equal; [lia|].
    f_equal. lia.
  - replace (S (k + d)) with (S k + d) by lia. apply IHt. lia.
Qed.

Lemma msubst_map_shift : forall t d k l, bnd (k + length l) t ->
  msubst k (map (shift d 0) l) t = shift d k (msubst k l t).
Proof.
  induction t as [n|x|a IHa b IHb|A a IHt]; intros d k l H; cbn [shift msubst bnd] in *;
    [ | reflexivity | destruct H; f_equal; auto | f_equal ].
  - rewrite map_length. leb_cases; cbn [shift]; leb_cases; try (f_equal; lia); try lia.
    rewrite shift_shift_in by lia.
    rewrite (nth_indep _ _ (shift d 0 (tvar 0))) by (rewrite map_length; lia).
    rewrite map_nth. rewrite shift_shift_in by lia. f_equal. lia.
  - apply IHt. simpl. now replace (S (k + length l)) with (S k + length l) by lia.
Qed.

(** ** Replacing one element of a list *)

Fixpoint setn {A} (i : nat) (a : A) (l : list A) : list A :=
  match l, i with
  | [], _ => []
  | _ :: l', 0 => a :: l'
  | x :: l', S i' => x :: setn i' a l'
  end.

Lemma setn_length : forall A i (a : A) l, length (setn i a l) = length l.
Proof. induction i; destruct l; simpl; auto. Qed.

Lemma nth_setn_same : forall A i (a d : A) l, i < length l -> nth i (setn i a l) d = a.
Proof.
  intros A i; induction i; intros a d l H; destruct l; simpl in *; try lia; auto.
  apply IHi. lia.
Qed.

Lemma nth_setn_other : forall A i j (a d : A) l, i <> j -> nth j (setn i a l) d = nth j l d.
Proof.
  intros A i; induction i; intros j a d l H; destruct l, j; simpl; auto; try lia;
    try (apply IHi; lia).
Qed.

Lemma map_setn : forall A B (f : A -> B) i a l, map f (setn i a l) = setn i (f a) (map f l).
Proof. induction i; destruct l; simpl; intros; auto. f_equal. auto. Qed.

(** ** Variables that do not occur *)

Fixpoint nocc (m : nat) (t : tm) : Prop :=
  match t with
  | tvar n => n <> m
  | tcst _ => True
  | tapp a b => nocc m a /\ nocc m b
  | tlam _ a => nocc (S m) a
  end.

Lemma msubst_nocc : forall t k l i a, i < length l ->
  nocc (k + (length l - 1 - i)) t -> msubst k (setn i a l) t = msubst k l t.
Proof.
  induction t as [n|x|b1 IH1 b2 IH2|A b IHb]; intros k l i a Hi H;
    cbn [msubst nocc] in *; rewrite ?setn_length.
  - leb_cases; auto. rewrite nth_setn_other; auto. lia.
  - reflexivity.
  - destruct H. f_equal; auto.
  - f_equal. apply IHb; auto.
Qed.

Lemma nth_map_in : forall A B (f : A -> B) l i d d', i < length l ->
  nth i (map f l) d = f (nth i l d').
Proof.
  intros. rewrite (nth_indep _ _ (f d')) by (rewrite ?map_length, ?setn_length; lia). apply map_nth.
Qed.

(** ** The core: one z-node *)

Section Core.
  Variables (Xs Ys : list ty) (jx ly : nat) (Bs As Rs : list tm) (C2 : ctx).

  (** [w_i = λ x̄. x_j B̄], closed. *)
  Let W := lams Xs (apps (tvar jx) Bs).
  Hypothesis HW : bnd 0 W.
  Hypothesis Hjx : jx < length Xs.
  Hypothesis HAs : length As = length Xs.
  Let jpos := length Xs - 1 - jx.
  (** Linearity: [x_j] does not occur in [B̄]. *)
  Hypothesis Hlin : Forall (nocc jx) Bs.

  (** [A_j = λ ȳ. S_j] with [S_j = C2[y_l R̄]]. *)
  Let Sj := plug C2 (apps (tvar (cdepth C2 + ly)) Rs).
  Hypothesis HAj : nth jpos As (tvar 0) = lams Ys Sj.
  Hypothesis HBs : length Bs = length Ys.
  Hypothesis Hly : ly < length Ys.

  (** The copy placed at [ny] and the new [j]-th argument. *)
  Let As2 := setn jpos (lams Ys (apps (tvar ly) (map (shift (length Ys) 0) Rs)))
                  (map (shift (length Ys + cdepth C2) 0) As).
  Let As1 := setn jpos (lams Ys (plug C2 (apps W As2))) As.

  Lemma W_head : forall L, length L = length Xs ->
    red (apps W L) (apps (nth jpos L (tvar 0)) (map (msubst 0 L) Bs)).
  Proof.
    intros L HL. unfold W. eapply rt_trans; [apply red_apps_lams; auto|].
    rewrite msubst_apps. cbn [msubst]. leb_cases; try lia.
    rewrite shift_0. replace (0 + length L - 1 - jx) with jpos by (unfold jpos; lia).
    apply rt_refl.
  Qed.

  Lemma bnd_Bs : Forall (bnd (length Xs)) Bs.
  Proof.
    pose proof HW as H. unfold W in H. apply bnd_lams in H. simpl in H.
    apply bnd_apps in H. tauto.
  Qed.

  Let Bs' := map (msubst 0 As) Bs.

  Theorem core_unfold : exists X, red (apps W As) X /\ red (apps W As1) X.
  Proof.
    assert (Hjpos : jpos < length As) by (unfold jpos; lia).
    exists (msubst 0 Bs' Sj). split.
    - eapply rt_trans; [apply W_head; auto|]. rewrite HAj.
      apply red_apps_lams. unfold Bs'. now rewrite map_length.
    - eapply rt_trans; [apply W_head; unfold As1; now rewrite setn_length|].
      unfold As1 at 1. rewrite nth_setn_same by auto.
      assert (HB1 : map (msubst 0 As1) Bs = Bs').
      { unfold Bs', As1. apply map_ext_in. intros b Hb.
        apply msubst_nocc; auto. rewrite Forall_forall in Hlin.
        replace (0 + (length As - 1 - jpos)) with jx by (unfold jpos; lia). auto. }
      rewrite HB1.
      assert (HlB : length Bs' = length Ys) by (unfold Bs'; now rewrite map_length).
      eapply rt_trans; [apply red_apps_lams; auto|].
      unfold Sj. rewrite !msubst_plug. simpl.
      apply red_plug.
      rewrite msubst_apps. rewrite (msubst_bnd W 0) by (auto; lia).
      set (L := map (msubst (cdepth C2) Bs') As2).
      assert (HL : length L = length Xs)
        by (unfold L, As2; now rewrite map_length, setn_length, map_length).
      eapply rt_trans; [apply W_head; auto|].
      assert (HLj : nth jpos L (tvar 0) =
        lams Ys (apps (tvar ly) (map (shift (length Ys) 0)
                                    (map (msubst (cdepth C2) Bs') Rs)))).
      { unfold L, As2. rewrite map_setn, nth_setn_same
          by (rewrite ?map_length, ?setn_length; lia).
        rewrite msubst_lams, msubst_apps. cbn [msubst]. leb_cases; try lia.
        f_equal. f_equal. rewrite !map_map. apply map_ext. intro r.
        rewrite shift_msubst by lia. reflexivity. }
      rewrite HLj.
      assert (HlB2 : length (map (msubst 0 L) Bs) = length Ys)
        by (rewrite ?map_length, ?setn_length; lia).
      eapply rt_trans; [apply red_apps_lams; auto|].
      rewrite msubst_apps. cbn [msubst]. leb_cases; try lia.
      rewrite map_map.
      replace (map (fun x => msubst 0 (map (msubst 0 L) Bs) (shift (length Ys) 0 x))
                   (map (msubst (cdepth C2) Bs') Rs))
        with (map (msubst (cdepth C2) Bs') Rs).
      2:{ symmetry. rewrite <- (map_id (map (msubst (cdepth C2) Bs') Rs)) at 2.
          apply map_ext. intro r. rewrite <- HlB2.
          rewrite <- (Nat.add_0_r (length (map (msubst 0 L) Bs))).
          rewrite msubst_shift_cancel by lia. apply shift_0. }
      rewrite shift_0. rewrite msubst_apps. cbn [msubst]. leb_cases; try lia.
      f_equal.
      (* The value of [y_l]: the copy sees [B_l] under [L], which agrees
         with [map (shift d2 0) As] off [jpos]. *)
      replace (0 + length (map (msubst 0 L) Bs) - 1 - ly)
        with (length Ys - 1 - ly) by (rewrite map_length; lia).
      replace (cdepth C2 + length Bs' - 1 - (cdepth C2 + ly))
        with (length Ys - 1 - ly) by lia.
      assert (Hlp : length Ys - 1 - ly < length Bs) by lia.
      rewrite (nth_map_in _ _ _ Bs _ _ (tvar 0)) by auto.
      unfold Bs'. rewrite (nth_map_in _ _ _ Bs _ _ (tvar 0)) by auto.
      set (b := nth (length Ys - 1 - ly) Bs (tvar 0)).
      assert (Hb : In b Bs) by (apply nth_In; auto).
      assert (HLs : L = setn jpos (nth jpos L (tvar 0)) (map (shift (cdepth C2) 0) As)).
      { unfold L, As2. rewrite map_setn, map_map.
        rewrite nth_setn_same by (rewrite ?map_length, ?setn_length; lia).
        f_equal. apply map_ext. intro a.
        replace (length Ys + cdepth C2) with (length Bs' + cdepth C2) by lia.
        apply msubst_shift_cancel. lia. }
      rewrite HLs. rewrite msubst_nocc.
      2:{ rewrite map_length. lia. }
      2:{ rewrite map_length. rewrite Forall_forall in Hlin.
          replace (0 + (length As - 1 - jpos)) with jx by (unfold jpos; lia). auto. }
      rewrite msubst_map_shift.
      2:{ pose proof bnd_Bs as H. rewrite Forall_forall in H. simpl. rewrite HAs. auto. }
      apply rt_refl.
  Qed.
End Core.

Lemma cdepth_cmsubst : forall C k l, cdepth (cmsubst k l C) = cdepth C.
Proof. induction C; intros; simpl; auto. Qed.

(** ** The whole term
    [t = λ z̄. C1[z A1 ... Am]] applied to closed [w̄]. *)

Section Global.
  Variables (Zs Xs Ys : list ty) (zz jx ly : nat) (ws As Bs Rs : list tm) (C1 C2 : ctx).

  Hypothesis Hws : Forall (bnd 0) ws.
  Hypothesis HZs : length ws = length Zs.
  Hypothesis Hzz : zz < length Zs.
  Hypothesis HW : nth (length ws - 1 - zz) ws (tvar 0) = lams Xs (apps (tvar jx) Bs).
  Hypothesis Hjx : jx < length Xs.
  Hypothesis HAs : length As = length Xs.
  Let jpos := length Xs - 1 - jx.
  Hypothesis Hlin : Forall (nocc jx) Bs.
  Hypothesis HAj : nth jpos As (tvar 0) =
    lams Ys (plug C2 (apps (tvar (cdepth C2 + ly)) Rs)).
  Hypothesis HBs : length Bs = length Ys.
  Hypothesis Hly : ly < length Ys.

  Let d := length Ys + cdepth C2.
  Let zv := cdepth C1 + zz.

  Definition t_orig : tm := lams Zs (plug C1 (apps (tvar zv) As)).

  Let As2 := setn jpos (lams Ys (apps (tvar ly) (map (shift (length Ys) 0) Rs)))
                  (map (shift d 0) As).

  Definition t_unf : tm :=
    lams Zs (plug C1 (apps (tvar zv)
      (setn jpos (lams Ys (plug C2 (apps (tvar (zv + d)) As2))) As))).

  Let W := lams Xs (apps (tvar jx) Bs).
  Let s1 := msubst (cdepth C1) ws.
  Let C1s := cmsubst 0 ws C1.

  Lemma W_closed : bnd 0 W.
  Proof.
    unfold W. rewrite <- HW. rewrite Forall_forall in Hws. apply Hws.
    apply nth_In. lia.
  Qed.

  Lemma z_value : forall k, cdepth C1 <= k ->
    msubst k ws (tvar (k + zz)) = W.
  Proof.
    intros k Hk. cbn [msubst]. leb_cases; try lia.
    replace (k + length ws - 1 - (k + zz)) with (length ws - 1 - zz) by lia.
    rewrite HW. apply (shift_bnd _ 0); [lia|apply W_closed].
  Qed.

  Lemma red_orig : red (apps t_orig ws) (plug C1s (apps W (map s1 As))).
  Proof.
    unfold t_orig. eapply rt_trans; [apply red_apps_lams; lia|].
    rewrite msubst_plug, msubst_apps, Nat.add_0_l. unfold zv.
    rewrite z_value by lia. apply rt_refl.
  Qed.

  Lemma red_unf : red (apps t_unf ws)
    (plug C1s (apps W (map s1
      (setn jpos (lams Ys (plug C2 (apps (tvar (zv + d)) As2))) As)))).
  Proof.
    unfold t_unf. eapply rt_trans; [apply red_apps_lams; lia|].
    rewrite msubst_plug, msubst_apps, Nat.add_0_l. unfold zv.
    rewrite z_value by lia. apply rt_refl.
  Qed.

  Theorem unfold_sound : forall u, normal u ->
    red (apps t_orig ws) u -> red (apps t_unf ws) u.
  Proof.
    intros u Hu Ho.
    set (C2s := cmsubst (cdepth C1 + length Ys) ws C2).
    set (Rss := map (msubst (cdepth C1 + d) ws) Rs).
    assert (Hjpos : jpos < length As) by (unfold jpos; lia).
    assert (HAj' : nth jpos (map s1 As) (tvar 0) =
      lams Ys (plug C2s (apps (tvar (cdepth C2s + ly)) Rss))).
    { rewrite (nth_map_in _ _ _ As _ _ (tvar 0)) by lia. rewrite HAj.
      unfold s1. rewrite msubst_lams, msubst_plug, msubst_apps.
      unfold C2s. rewrite cdepth_cmsubst. cbn [msubst]. leb_cases; try lia.
      do 3 f_equal. unfold Rss, d. apply map_ext. intro r. f_equal. lia. }
    assert (Hcore := core_unfold Xs Ys jx ly Bs (map s1 As) Rss C2s W_closed Hjx
      ltac:(now rewrite map_length) Hlin HAj' HBs Hly).
    destruct Hcore as [X [H1 H2]].
    assert (HX : red (plug C1s X) u).
    { eapply red_to_normal; eauto. eapply rt_trans; [apply red_orig|].
      now apply red_plug. }
    eapply rt_trans; [apply red_unf|]. eapply rt_trans; [|apply HX].
    apply red_plug. fold W in H2.
    replace (map s1 (setn jpos (lams Ys (plug C2 (apps (tvar (zv + d)) As2))) As))
      with (setn (length Xs - 1 - jx)
              (lams Ys (plug C2s (apps W
                 (setn (length Xs - 1 - jx)
                    (lams Ys (apps (tvar ly) (map (shift (length Ys) 0) Rss)))
                    (map (shift (length Ys + cdepth C2s) 0) (map s1 As))))))
              (map s1 As)); [exact H2|].
    rewrite map_setn. f_equal.
    unfold s1. rewrite msubst_lams, msubst_plug, msubst_apps. f_equal. f_equal.
    unfold C2s. rewrite cdepth_cmsubst. f_equal.
    - unfold zv, d. replace (cdepth C1 + length Ys + cdepth C2)
        with (cdepth C1 + (length Ys + cdepth C2)) by lia.
      replace (cdepth C1 + zz + (length Ys + cdepth C2))
        with ((cdepth C1 + (length Ys + cdepth C2)) + zz) by lia.
      symmetry. apply z_value. lia.
    - unfold As2. rewrite map_setn. f_equal.
      + rewrite msubst_lams, msubst_apps. cbn [msubst]. leb_cases; try lia.
        f_equal. f_equal. unfold Rss. rewrite !map_map. apply map_ext. intro r.
        rewrite shift_msubst by lia. f_equal. unfold d. lia.
      + rewrite !map_map. apply map_ext. intro a. unfold d.
        rewrite shift_msubst by lia. f_equal. lia.
  Qed.
End Global.
