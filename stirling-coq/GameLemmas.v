(** * Consequences of the definitions and of the G-axioms
    (Section 4.2 of the notes). *)

From Coq Require Import List Arith Bool Lia Relations.
From HOM Require Import Syntax Lambda ITree Game.
Import ListNotations.

(** ** States change only at constant nodes of positive arity *)

Lemma step_state_change : forall E t p q r r',
  In q (step E t p) -> pst p = SR r -> pst q = SR r' -> r <> r' ->
  pos_cst_node E t (pnode p) /\ fo_child r' r.
Proof.
  intros E t p q r r' Hin Hp Hq Hne.
  unfold step in Hin. rewrite Hp in Hin. unfold pos_cst_node.
  destruct (label_at E t (pnode p)) as [[|As|k i a|c [|a]]|] eqn:Hl.
  - destruct Hin as [<-|[]]; simpl in Hq; congruence.
  - destruct Hin as [<-|[]]; simpl in Hq; congruence.
  - destruct (tlook (ptab p) (binder (pnode p) k)) as [[ms th']|]; [|destruct Hin].
    destruct (nth_error ms i) as [mj|]; [|destruct Hin].
    destruct a; destruct Hin as [<-|[]]; simpl in Hq; congruence.
  - destruct Hin as [<-|[]]. simpl in Hq. destruct (fo_eqb r _); discriminate.
  - destruct r as [f rs].
    destruct ((f =? cname c) && (length rs =? S a)) eqn:Hc.
    + apply in_map_iff in Hin. destruct Hin as [[j rj] [<- Hjr]].
      simpl in Hq. inversion Hq; subst rj.
      split.
      * exists c, (S a). split; [reflexivity|lia].
      * constructor. now apply in_combine_r in Hjr.
    + destruct Hin as [<-|[]]. simpl in Hq. discriminate.
  - destruct Hin.
Qed.

(** ** Strict descent in the subterm order is bounded by the depth *)

Lemma rt_eq_or_t : forall (A : Type) (R : relation A) x y,
  clos_refl_trans A R x y -> x = y \/ clos_trans A R x y.
Proof.
  intros A R x y H.
  induction H as [x y H|x|x y z _ [<-|IH1] _ [<-|IH2]]; auto.
  - right. now apply t_step.
  - right. now apply t_trans with y.
Qed.

Lemma fo_sub_neq_depth : forall r s, fo_sub r s -> r <> s -> fo_depth r < fo_depth s.
Proof.
  intros r s H Hne. destruct (rt_eq_or_t _ _ _ _ H) as [->|Ht]; [congruence|].
  now apply fo_psub_depth.
Qed.

(** ** Disjoint contributing intervals
    [after b ivs]: the intervals [(i,j)] of [ivs] are sorted, pairwise
    non-overlapping (each starts at or after the end of the previous
    one) and the first starts at or after [b]. *)

Fixpoint after (b : nat) (ivs : list (nat * nat)) : Prop :=
  match ivs with
  | [] => True
  | (i, j) :: rest => b <= i /\ after j rest
  end.

Lemma state_sub : forall E t pi b i rb ri, WF E t -> play E t pi ->
  b <= i -> S i < length pi ->
  pst (P E pi b) = SR rb -> pst (P E pi i) = SR ri -> fo_sub ri rb.
Proof.
  intros E t pi b i rb ri HWF Hpl Hbi Hi Hb Hri.
  destruct (Nat.eq_dec b i) as [->|Hne].
  - rewrite Hb in Hri. inversion Hri. subst. apply rt_refl.
  - apply (G4_states E t pi b i rb ri); auto; lia.
Qed.

Lemma contrib_bound : forall E t pi ivs b rb, WF E t -> play E t pi ->
  after b ivs ->
  Forall (fun ij => contributes E pi (fst ij) (snd ij)) ivs ->
  pst (P E pi b) = SR rb ->
  length ivs <= fo_depth rb.
Proof.
  intros E t pi ivs. induction ivs as [|[i j] ivs IH]; intros b rb HWF Hpl Haft Hall Hb.
  - simpl. lia.
  - destruct Haft as [Hbi Haft]. inversion Hall as [|? ? Hc Hrest]; subst.
    destruct Hc as [Hij [Hlen [ri [rj [Hri [Hrj Hne]]]]]]. simpl in *.
    assert (H1 : fo_sub ri rb) by (apply (state_sub E t pi b i rb ri); auto; lia).
    assert (H2 : fo_sub rj ri) by (apply (state_sub E t pi i j ri rj); auto).
    assert (H3 : fo_depth rj < fo_depth ri) by (apply fo_sub_neq_depth; auto).
    pose proof (fo_sub_depth _ _ H1).
    pose proof (IH j rj HWF Hpl Haft Hrest Hrj). lia.
Qed.

Lemma play_init : forall E t pi, play E t pi -> P E pi 0 = init E.
Proof.
  intros E t pi [[H0 _] _]. unfold P.
  destruct pi; [discriminate|]. simpl in *. now inversion H0.
Qed.

(** In every play, pairwise disjoint contributing intervals number at
    most [depth(u)]  [S, after Def. 44]. *)
Theorem disjoint_contributions : forall E t pi ivs, WF E t -> play E t pi ->
  after 0 ivs ->
  Forall (fun ij => contributes E pi (fst ij) (snd ij)) ivs ->
  length ivs <= fo_depth (eq_goal E).
Proof.
  intros E t pi ivs HWF Hpl Haft Hall.
  eapply contrib_bound; eauto.
  rewrite (play_init E t pi Hpl). reflexivity.
Qed.

(** ** Runs extend to plays (from G2) *)

Lemma run_snoc : forall E t pi q, run E t pi -> pi <> [] ->
  ~ final (P E pi (length pi - 1)) -> In q (step E t (P E pi (length pi - 1))) ->
  run E t (pi ++ [q]).
Proof.
  intros E t pi q [H0 Hs] Hne Hnf Hq. split.
  - destruct pi; [congruence|]. exact H0.
  - intros i Hi. rewrite app_length in Hi. simpl in Hi.
    unfold P in *.
    destruct (Nat.eq_dec (S i) (length pi)) as [Heq|Hneq].
    + rewrite app_nth2 by lia. rewrite app_nth1 by lia.
      replace (S i - length pi) with 0 by lia. simpl.
      replace i with (length pi - 1) by lia. auto.
    + rewrite !app_nth1 by lia. apply Hs. lia.
Qed.

Lemma classic_final : forall p, final p \/ ~ final p.
Proof. intros [n [r| |] th]; unfold final; simpl; tauto. Qed.

Theorem run_extends : forall E t pi, WF E t -> run E t pi -> pi <> [] ->
  exists pi', play E t (pi ++ pi').
Proof.
  intros E t pi HWF Hrun Hne.
  destruct (G2_bounded E t HWF) as [N HN].
  remember (N - length pi) as d eqn:Hd. revert pi Hrun Hne Hd.
  induction d as [d IH] using lt_wf_ind. intros pi Hrun Hne Hd.
  destruct (classic_final (P E pi (length pi - 1))) as [Hf|Hnf].
  - exists []. rewrite app_nil_r. split; auto.
  - pose proof (G2_total E t pi HWF Hrun Hnf) as Hst.
    destruct (step E t (P E pi (length pi - 1))) as [|q qs] eqn:Hstep; [congruence|].
    assert (Hr' : run E t (pi ++ [q])).
    { apply run_snoc; auto. rewrite Hstep. now left. }
    pose proof (HN _ Hr') as Hb. rewrite app_length in Hb. simpl in Hb.
    destruct (IH (N - length (pi ++ [q]))) with (pi := pi ++ [q]) as [pi' Hp]; auto.
    + rewrite app_length. simpl. lia.
    + intro H. apply app_eq_nil in H. destruct H. congruence.
    + exists (q :: pi'). rewrite <- app_assoc in Hp. exact Hp.
Qed.

(** ** Ancestors are visited first  [S, after Def. 23] *)

Lemma step_lam : forall E t p As r,
  label_at E t (pnode p) = Some (LLam As) -> pst p = SR r ->
  step E t p = [Pos (succ (pnode p) 1) (SR r) (ptab p)].
Proof. intros E t p As r Hl Hr. unfold step. now rewrite Hr, Hl. Qed.

Lemma step_final_node : forall E t p q,
  In q (step E t p) -> final q -> pnode q = pnode p.
Proof.
  intros E t p q Hin Hf. unfold step in Hin.
  destruct (pst p) as [r| |]; [|destruct Hin|destruct Hin].
  destruct (label_at E t (pnode p)) as [[|As|k i a|c [|a]]|].
  - destruct Hin as [<-|[]]. destruct Hf.
  - destruct Hin as [<-|[]]. destruct Hf.
  - destruct (tlook (ptab p) (binder (pnode p) k)) as [[ms th']|]; [|destruct Hin].
    destruct (nth_error ms i); [|destruct Hin].
    destruct a; destruct Hin as [<-|[]]; destruct Hf.
  - destruct Hin as [<-|[]]. reflexivity.
  - destruct r as [f rs]. destruct ((f =? cname c) && (length rs =? S a)).
    + apply in_map_iff in Hin. destruct Hin as [jr [<- _]]. destruct Hf.
    + destruct Hin as [<-|[]]. reflexivity.
  - destruct Hin.
Qed.

Lemma above_nil : forall n, above n [] -> n = [].
Proof. intros n [w Hw]. symmetry in Hw. now apply app_eq_nil in Hw. Qed.

Lemma above_snoc : forall n m x, above n (m ++ [x]) -> n <> m ++ [x] -> above n m.
Proof.
  intros n m x [w Hw] Hne.
  destruct w as [|y w'] using rev_ind.
  - rewrite app_nil_r in Hw. congruence.
  - rewrite app_assoc in Hw. apply app_inj_tail in Hw. destruct Hw as [Hw _].
    now exists w'.
Qed.

Lemma run_step : forall E t pi i, run E t pi -> S i < length pi ->
  In (P E pi (S i)) (step E t (P E pi i)) /\ ~ final (P E pi i).
Proof. intros E t pi i [_ H] Hi. now apply H. Qed.

Lemma not_final_SR : forall p, ~ final p -> exists r, pst p = SR r.
Proof. intros [n [r| |] th] H; simpl; [eauto| |]; exfalso; apply H; exact I. Qed.

Theorem ancestors_visited : forall E t pi j n, WF E t -> play E t pi ->
  j < length pi -> above n (nd E pi j) ->
  exists i, i <= j /\ nd E pi i = n.
Proof.
  intros E t pi j. induction j as [j IH] using lt_wf_ind.
  intros n HWF Hpl Hj Hab.
  destruct (list_eq_dec Nat.eq_dec n (nd E pi j)) as [Heq|Hne].
  { exists j. auto. }
  destruct j as [|j'].
  - exfalso. unfold nd in Hab, Hne. rewrite (play_init E t pi Hpl) in Hab, Hne.
    simpl in *. apply above_nil in Hab. congruence.
  - destruct Hpl as [Hrun Hfin] eqn:Hpl'.
    destruct (run_step E t pi j' Hrun Hj) as [Hin Hnf].
    destruct (Nat.eq_dec (S (S j')) (length pi)) as [Hlast|Hnl].
    + (* the final position sits at the node of its predecessor *)
      assert (Hf : final (P E pi (S j'))).
      { replace (S j') with (length pi - 1) by lia. exact Hfin. }
      pose proof (step_final_node E t _ _ Hin Hf) as Hn.
      destruct (IH j' ltac:(lia) n HWF Hpl ltac:(lia)) as [i [Hi Hni]].
      { unfold nd in *. now rewrite <- Hn. }
      exists i. split; [lia|exact Hni].
    + assert (HS : S (S j') < length pi) by lia.
      destruct (Nat.even (S j')) eqn:Hev.
      * (* head node, reached by a lambda move *)
        rewrite Nat.even_succ in Hev.
        destruct (G4_parity E t pi j' HWF Hpl ltac:(lia)) as [Hlam _].
        destruct (Hlam Hev) as [As HAs].
        destruct (not_final_SR _ Hnf) as [r Hr].
        rewrite (step_lam E t _ As r HAs Hr) in Hin.
        destruct Hin as [Hq|[]].
        assert (Hnd : nd E pi (S j') = nd E pi j' ++ [1]).
        { unfold nd. rewrite <- Hq. reflexivity. }
        rewrite Hnd in Hab, Hne.
        destruct (IH j' ltac:(lia) n HWF Hpl ltac:(lia) (above_snoc _ _ _ Hab Hne))
          as [i [Hi Hni]].
        exists i. split; [lia|exact Hni].
      * (* lambda node: go to the parent *)
        assert (Hodd : Nat.odd (S j') = true).
        { rewrite <- Nat.negb_even, Hev. reflexivity. }
        destruct (G4_parity E t pi (S j') HWF Hpl HS) as [Hlam _].
        pose proof (Hlam Hodd) as HL.
        destruct (G7_parent E t pi (S j') HWF Hpl ltac:(lia) HS (or_intror HL))
          as [i [_ [_ [Hij Hsuc]]]].
        destruct (Hsuc HL) as [s Hs]. unfold succ in Hs.
        rewrite Hs in Hab, Hne.
        destruct (IH i Hij n HWF Hpl ltac:(lia) (above_snoc _ _ _ Hab Hne))
          as [i' [Hi' Hni']].
        exists i'. split; [lia|exact Hni'].
Qed.
