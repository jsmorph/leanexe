(* From the big-step termination of the Clight program that clightgen prints
   (after SimplExpr and SimplLocals) to the behavior of the Asm program that ccomp produces
   from the same C program.  CompCert 3.18 proves every step, and this file composes them into
   clight2_bigstep_to_asm.  clight2_bigstep_asm_unique adds, from the determinacy of Asm, that
   the termination is the Asm program's only behavior when its trace has no inputs, and
   clight2_bigstep_asm_reads that the behaviors of a program whose volatile loads read a
   sequence of values are the terminations of a family indexed by those values.  rocq/check.sh
   checks the file against a CompCert 3.18 tree for AArch64 whose proofs are built. *)

From Coq Require Classical ClassicalEpsilon.
Require Import Coqlib Errors AST Integers Linking Events Smallstep Behaviors.
Require Csyntax Clight ClightBigstep Asm.
Require Import Compiler Compopts.
Require SimplExpr SimplLocals Cshmgen Cminorgen Selection RTLgen Tailcall Inlining Renumber.
Require Constprop CSE Deadcode Unusedglob Allocation Tunneling Linearize CleanupLabels.
Require Debugvar Stacking Asmgen.
Require Cshmgenproof Cminorgenproof Selectionproof RTLgenproof Tailcallproof Inliningproof.
Require Renumberproof Constpropproof CSEproof Deadcodeproof Unusedglobproof Allocproof.
Require Tunnelingproof Linearizeproof CleanupLabelsproof Debugvarproof Stackingproof Asmgenproof.

Theorem clight2_to_asm_forward:
  forall p p1 p2 tp,
  SimplExpr.transl_program p = OK p1 ->
  SimplLocals.transf_program p1 = OK p2 ->
  transf_c_program p = OK tp ->
  forward_simulation (Clight.semantics2 p2) (Asm.semantics tp).
Proof.
  intros p p1 p2 tp E1 E2 T.
  unfold transf_c_program, time in T. simpl in T. rewrite E1 in T. simpl in T.
  unfold transf_clight_program, time in T. rewrite ! compose_print_identity in T. simpl in T.
  rewrite E2 in T. simpl in T.
  destruct (Cshmgen.transl_program p2) as [p3|e] eqn:P3; simpl in T; try discriminate.
  destruct (Cminorgen.transl_program p3) as [p4|e] eqn:P4; simpl in T; try discriminate.
  unfold transf_cminor_program, time in T. rewrite ! compose_print_identity in T. simpl in T.
  destruct (Selection.sel_program p4) as [p5|e] eqn:P5; simpl in T; try discriminate.
  destruct (RTLgen.transl_program p5) as [p6|e] eqn:P6; simpl in T; try discriminate.
  unfold transf_rtl_program, time in T. rewrite ! compose_print_identity in T. simpl in T.
  set (p7 := total_if optim_tailcalls Tailcall.transf_program p6) in *.
  destruct (Inlining.transf_program p7) as [p8|e] eqn:P8; simpl in T; try discriminate.
  set (p9 := Renumber.transf_program p8) in *.
  set (p10 := total_if optim_constprop Constprop.transf_program p9) in *.
  set (p11 := total_if optim_constprop Renumber.transf_program p10) in *.
  destruct (partial_if optim_CSE CSE.transf_program p11) as [p12|e] eqn:P12; simpl in T; try discriminate.
  destruct (partial_if optim_redundancy Deadcode.transf_program p12) as [p13|e] eqn:P13; simpl in T; try discriminate.
  destruct (Unusedglob.transform_program p13) as [p14|e] eqn:P14; simpl in T; try discriminate.
  destruct (Allocation.transf_program p14) as [p15|e] eqn:P15; simpl in T; try discriminate.
  set (p16 := Tunneling.tunnel_program p15) in *.
  destruct (Linearize.transf_program p16) as [p17|e] eqn:P17; simpl in T; try discriminate.
  set (p18 := CleanupLabels.transf_program p17) in *.
  destruct (partial_if debug Debugvar.transf_program p18) as [p19|e] eqn:P19; simpl in T; try discriminate.
  destruct (Stacking.transf_program p19) as [p20|e] eqn:P20; simpl in T; try discriminate.
  eapply compose_forward_simulations.
    eapply Cshmgenproof.transl_program_correct. apply Cshmgenproof.transf_program_match; eauto.
  eapply compose_forward_simulations.
    eapply Cminorgenproof.transl_program_correct. apply Cminorgenproof.transf_program_match; eauto.
  eapply compose_forward_simulations.
    eapply Selectionproof.transf_program_correct. apply Selectionproof.transf_program_match; eauto.
  eapply compose_forward_simulations.
    eapply RTLgenproof.transf_program_correct. apply RTLgenproof.transf_program_match; eauto.
  eapply compose_forward_simulations.
    eapply match_if_simulation. apply total_if_match. apply Tailcallproof.transf_program_match.
    exact Tailcallproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply Inliningproof.transf_program_correct. apply Inliningproof.transf_program_match; eauto.
  eapply compose_forward_simulations.
    eapply Renumberproof.transf_program_correct. apply Renumberproof.transf_program_match.
  eapply compose_forward_simulations.
    eapply match_if_simulation. apply total_if_match. apply Constpropproof.transf_program_match.
    exact Constpropproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. apply total_if_match. apply Renumberproof.transf_program_match.
    exact Renumberproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eapply partial_if_match; eauto. apply CSEproof.transf_program_match.
    exact CSEproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eapply partial_if_match; eauto. apply Deadcodeproof.transf_program_match.
    exact Deadcodeproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply Unusedglobproof.transf_program_correct. apply Unusedglobproof.transf_program_match; eauto.
  eapply compose_forward_simulations.
    eapply Allocproof.transf_program_correct. apply Allocproof.transf_program_match; eauto.
  eapply compose_forward_simulations.
    eapply Tunnelingproof.transf_program_correct. apply Tunnelingproof.transf_program_match.
  eapply compose_forward_simulations.
    eapply Linearizeproof.transf_program_correct. apply Linearizeproof.transf_program_match; eauto.
  eapply compose_forward_simulations.
    eapply CleanupLabelsproof.transf_program_correct. apply CleanupLabelsproof.transf_program_match.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eapply partial_if_match; eauto. apply Debugvarproof.transf_program_match.
    exact Debugvarproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply Stackingproof.transf_program_correct with (return_address_offset := Asmgenproof0.return_address_offset).
    exact Asmgenproof.return_address_exists.
    apply Stackingproof.transf_program_match; eauto.
  eapply Asmgenproof.transf_program_correct. apply Asmgenproof.transf_program_match; eauto.
Qed.

Theorem clight2_bigstep_to_asm:
  forall p p1 p2 tp t r,
  SimplExpr.transl_program p = OK p1 ->
  SimplLocals.transf_program p1 = OK p2 ->
  transf_c_program p = OK tp ->
  ClightBigstep.Clight2.bigstep_program_terminates p2 t r ->
  program_behaves (Asm.semantics tp) (Terminates t r).
Proof.
  intros p p1 p2 tp t r E1 E2 T B.
  eapply forward_simulation_same_safe_behavior.
  eapply clight2_to_asm_forward; eauto.
  eapply behavior_bigstep_terminates.
  apply ClightBigstep.Clight2.bigstep_semantics_sound.
  exact B.
  red; auto.
Qed.

(* The behavior of the Asm program is unique.  Asm's semantics is determinate
   (aarch64/Asm.v, semantics_determinate): two steps from one state have traces that
   match_traces relates (common/Events.v, lines 505 to 517), and with equal traces they reach
   one state.  match_traces relates a trace without inputs, a system call or a volatile load,
   only to itself, so every run follows a terminating run whose trace has no inputs, and the
   program has no behavior but that run's. *)

Definition no_inputs (t: trace) : Prop :=
  forall ev, In ev t ->
  match ev with Event_syscall _ _ _ | Event_vload _ _ _ _ => False | _ => True end.

Lemma no_inputs_app:
  forall t1 t2, no_inputs (t1 ** t2) -> no_inputs t1 /\ no_inputs t2.
Proof.
  unfold no_inputs; intros t1 t2 H; split; intros ev IN; apply H; apply in_or_app; auto.
Qed.

Lemma match_traces_no_inputs:
  forall ge t1 t2, match_traces ge t1 t2 -> no_inputs t1 -> t1 = t2.
Proof.
  intros ge t1 t2 M N. inv M; auto; exfalso; exact (N _ (or_introl eq_refl)).
Qed.

Section UNIQUE.

Variable L: semantics.
Hypothesis DET: determinate L.

Lemma star_follows:
  forall s t2 s2, Star L s t2 s2 ->
  forall t s', Star L s t s' -> no_inputs t -> Nostep L s' ->
  exists t3, t = t2 ** t3 /\ Star L s2 t3 s'.
Proof.
  induction 1; intros t' s' K N NS.
  - exists t'; split; auto.
  - inversion K as [s0 | s0 tc sc td s0' tcd STEP STAR EQ]; subst.
    + elim (NS _ _ H).
    + destruct (no_inputs_app _ _ N) as [N1 N2].
      assert (tc = t1) by (eapply match_traces_no_inputs; eauto; eapply sd_determ_1; eauto).
      subst tc.
      assert (sc = s2) by (eapply sd_determ_2; eauto). subst sc.
      destruct (IHstar _ _ STAR N2 NS) as [t4 [A B]].
      exists t4; split; auto. subst. rewrite Eapp_assoc. auto.
Qed.

Lemma star_nostep_inv:
  forall s t s', Star L s t s' -> Nostep L s -> t = E0 /\ s' = s.
Proof.
  intros s t s' S NS. inv S; auto. elim (NS _ _ H).
Qed.

Lemma no_forever_silent:
  forall s t s', Star L s t s' -> Nostep L s' -> ~ Forever_silent L s.
Proof.
  induction 1 as [s | s1 t1 s2 t2 s3 t STEP STAR IH EQ]; intros NS F.
  - inversion F as [s0 s4 STEP0 F0]; subst. elim (NS _ _ STEP0).
  - inversion F as [s0 s4 STEP0 F0]; subst.
    destruct (sd_determ DET _ _ _ _ _ STEP STEP0) as [M E].
    inv M. assert (s2 = s4) by (apply E; auto). subst. apply IH; auto.
Qed.

Lemma no_forever_reactive:
  forall n s t s', (length t <= n)%nat -> Star L s t s' -> no_inputs t -> Nostep L s' ->
  forall T, ~ Forever_reactive L s T.
Proof.
  induction n; intros s t s' LEN S N NS T F;
  inversion F as [s0 s4 t0 T0 STAR0 NE F0]; subst;
  destruct (star_follows _ _ _ STAR0 _ _ S N NS) as [t3 [A B]]; subst;
  assert (L3 : length (t0 ** t3) = (length t0 + length t3)%nat) by (unfold Eapp; apply app_length);
  (destruct t0 as [|ev t0]; [elim NE; reflexivity | rewrite L3 in LEN; simpl in LEN]).
  - lia.
  - destruct (no_inputs_app _ _ N) as [_ N2].
    eapply IHn with (t := t3); eauto. lia.
Qed.

Theorem determinate_unique_behavior:
  forall t r, program_behaves L (Terminates t r) -> no_inputs t ->
  forall beh, program_behaves L beh -> beh = Terminates t r.
Proof.
  intros t r B N beh B'.
  inversion B as [s beh0 INIT SB | NOINIT]; subst.
  inversion SB as [t0 s' r0 STAR FINAL | | |]; subst.
  assert (NS: Nostep L s') by (eapply sd_final_nostep; eauto).
  inversion B' as [s0 beh1 INIT' SB' | NOINIT']; subst.
  - assert (s0 = s) by (eapply sd_initial_determ; eauto). subst s0.
    inversion SB' as [t2 s2 r2 STAR2 FINAL2 | t2 s2 STAR2 SIL | T REACT
                     | t2 s2 STAR2 NS2 NF2]; subst.
    + destruct (star_follows _ _ _ STAR2 _ _ STAR N NS) as [t3 [A B3]].
      destruct (star_nostep_inv _ _ _ B3 (sd_final_nostep DET _ _ FINAL2)) as [C D].
      subst. rewrite E0_right.
      f_equal. eapply sd_final_determ; eauto.
    + destruct (star_follows _ _ _ STAR2 _ _ STAR N NS) as [t3 [A B3]].
      elim (no_forever_silent _ _ _ B3 NS SIL).
    + elim (no_forever_reactive (length t) _ _ _ (le_n _) STAR N NS T REACT).
    + destruct (star_follows _ _ _ STAR2 _ _ STAR N NS) as [t3 [A B3]].
      destruct (star_nostep_inv _ _ _ B3 NS2) as [C D]. subst.
      elim (NF2 _ FINAL).
  - elim (NOINIT' s INIT).
Qed.

(* With inputs, two runs from one state agree until a step at which their events differ, and
   match_traces relates two different events only when both are system calls or both are
   volatile loads, which then differ in the value read.  leaves t t2 holds when the traces t and
   t2 share a prefix followed by two such events. *)

Definition leaves (t t2: trace) : Prop :=
  exists tp e e' u v, t = tp ** e :: u /\ t2 = tp ** e' :: v /\ e <> e' /\
    match_traces (symbolenv L) (e :: nil) (e' :: nil).

Lemma star_follows_or_leaves:
  forall s t2 s2, Star L s t2 s2 ->
  forall t s', Star L s t s' -> Nostep L s' ->
  (exists t3, t = t2 ** t3 /\ Star L s2 t3 s') \/ leaves t t2.
Proof.
  induction 1 as [s | s1 t1 s2 t2 s3 t12 STEP STAR IH EQ]; intros t' s' K NS.
  - left. exists t'; split; auto.
  - inversion K as [s0 | s0 tc sc td s0' tcd STEPC STARC EQC]; subst.
    + elim (NS _ _ STEP).
    + destruct (sd_determ DET _ _ _ _ _ STEPC STEP) as [M E].
      destruct (Classical_Prop.classic (tc = t1)) as [EQ1 | NE1].
      * subst tc. assert (sc = s2) by (apply E; auto). subst sc.
        destruct (IH _ _ STARC NS) as [[t3 [A B]] | [tp [e [e' [u [v [A [B [C D]]]]]]]]].
        { left. exists t3; split; auto. subst. rewrite Eapp_assoc. auto. }
        { right. red. exists (t1 ** tp), e, e', u, v. subst.
          split. rewrite Eapp_assoc. auto.
          split. rewrite Eapp_assoc. auto.
          split; auto. }
      * right. red. inversion M; subst; try (elim NE1; reflexivity);
        exists E0; do 4 eexists;
        (split; [reflexivity | split; [reflexivity | split; [| eassumption]]]);
        intro EQe; apply NE1; rewrite EQe; reflexivity.
Qed.

Lemma no_forever_reactive_leaves:
  forall n s t s', (length t <= n)%nat -> Star L s t s' -> Nostep L s' ->
  forall T, Forever_reactive L s T ->
  exists tp e e' u T', t = tp ** e :: u /\ T = (tp ** e' :: nil) *** T' /\ e <> e' /\
    match_traces (symbolenv L) (e :: nil) (e' :: nil).
Proof.
  induction n; intros s t s' LEN S NS T F;
  inversion F as [s0 s4 t1 T1 STAR1 NE F1]; subst;
  destruct (star_follows_or_leaves _ _ _ STAR1 _ _ S NS)
    as [[t3 [A B]] | [tp [e [e' [u [v [A [B [C D]]]]]]]]].
  - subst.
    assert (L3 : length (t1 ** t3) = (length t1 + length t3)%nat)
      by (unfold Eapp; apply app_length).
    destruct t1 as [|ev t1]; [elim NE; reflexivity | rewrite L3 in LEN; simpl in LEN; lia].
  - exists tp, e, e', u, (v *** T1). subst.
    split. auto. split. rewrite !Eappinf_assoc. reflexivity. split; auto.
  - subst.
    assert (L3 : length (t1 ** t3) = (length t1 + length t3)%nat)
      by (unfold Eapp; apply app_length).
    destruct t1 as [|ev t1]; [elim NE; reflexivity | rewrite L3 in LEN; simpl in LEN].
    destruct (IHn _ _ _ (ltac:(lia) : (length t3 <= n)%nat) B NS _ F1)
      as [tp [e [e' [u [T' [A1 [B1 [C1 D1]]]]]]]].
    exists ((ev :: t1) ** tp), e, e', u, T'. subst.
    split. rewrite Eapp_assoc. auto.
    split. rewrite !Eappinf_assoc. reflexivity.
    split; auto.
  - exists tp, e, e', u, (v *** T1). subst.
    split. auto. split. rewrite !Eappinf_assoc. reflexivity. split; auto.
Qed.

(* A behavior of a program that terminates with t and r is that termination, or it leaves t at
   an input: it begins with a prefix of t followed by an event that differs from the next event
   of t and that match_traces relates to it. *)
Theorem determinate_behavior_leaves:
  forall t r, program_behaves L (Terminates t r) ->
  forall beh, program_behaves L beh ->
  beh = Terminates t r \/
  exists tp e e' u, t = tp ** e :: u /\ e <> e' /\
    match_traces (symbolenv L) (e :: nil) (e' :: nil) /\
    behavior_prefix (tp ** e' :: nil) beh.
Proof.
  intros t r B beh B'.
  inversion B as [s beh0 INIT SB | NOINIT]; subst.
  inversion SB as [t0 s' r0 STAR FINAL | | |]; subst.
  assert (NS: Nostep L s') by (eapply sd_final_nostep; eauto).
  inversion B' as [s0 beh1 INIT' SB' | NOINIT']; subst.
  - assert (s0 = s) by (eapply sd_initial_determ; eauto). subst s0.
    inversion SB' as [t2 s2 r2 STAR2 FINAL2 | t2 s2 STAR2 SIL | T REACT
                     | t2 s2 STAR2 NS2 NF2]; subst.
    + destruct (star_follows_or_leaves _ _ _ STAR2 _ _ STAR NS)
        as [[t3 [A B3]] | [tp [e [e' [u [v [A [A2 [C D]]]]]]]]].
      * left. destruct (star_nostep_inv _ _ _ B3 (sd_final_nostep DET _ _ FINAL2)) as [C D].
        subst. rewrite E0_right. f_equal. eapply sd_final_determ; eauto.
      * right. exists tp, e, e', u. split. auto. split. auto. split. auto.
        exists (Terminates v r2). subst. simpl. rewrite Eapp_assoc. reflexivity.
    + destruct (star_follows_or_leaves _ _ _ STAR2 _ _ STAR NS)
        as [[t3 [A B3]] | [tp [e [e' [u [v [A [A2 [C D]]]]]]]]].
      * elim (no_forever_silent _ _ _ B3 NS SIL).
      * right. exists tp, e, e', u. split. auto. split. auto. split. auto.
        exists (Diverges v). subst. simpl. rewrite Eapp_assoc. reflexivity.
    + right.
      destruct (no_forever_reactive_leaves (length t) _ _ _ (le_n _) STAR NS T REACT)
        as [tp [e [e' [u [T' [A [A2 [C D]]]]]]]].
      exists tp, e, e', u. split. auto. split. auto. split. auto.
      exists (Reacts T'). subst. reflexivity.
    + destruct (star_follows_or_leaves _ _ _ STAR2 _ _ STAR NS)
        as [[t3 [A B3]] | [tp [e [e' [u [v [A [A2 [C D]]]]]]]]].
      * destruct (star_nostep_inv _ _ _ B3 NS2) as [C D]. subst. elim (NF2 _ FINAL).
      * right. exists tp, e, e', u. split. auto. split. auto. split. auto.
        exists (Goes_wrong v). subst. simpl. rewrite Eapp_assoc. reflexivity.
  - elim (NOINIT' s INIT).
Qed.

End UNIQUE.

(** The Asm program of a Clight program that terminates with a trace without inputs has that
    termination as its only behavior. *)
Theorem clight2_bigstep_asm_unique:
  forall p p1 p2 tp t r,
  SimplExpr.transl_program p = OK p1 ->
  SimplLocals.transf_program p1 = OK p2 ->
  transf_c_program p = OK tp ->
  ClightBigstep.Clight2.bigstep_program_terminates p2 t r ->
  no_inputs t ->
  forall beh, program_behaves (Asm.semantics tp) beh <-> beh = Terminates t r.
Proof.
  intros p p1 p2 tp t r E1 E2 T B N beh. split.
  - intros B'. eapply determinate_unique_behavior; eauto.
    apply Asm.semantics_determinate.
    eapply clight2_bigstep_to_asm; eauto.
  - intros; subst. eapply clight2_bigstep_to_asm; eauto.
Qed.

(* Two finite prefixes of one behavior are prefixes of each other, so a behavior has at most one
   k-th volatile load. *)

Lemma behavior_app_cons:
  forall x t b x' t' b',
  behavior_app (x :: t) b = behavior_app (x' :: t') b' ->
  x = x' /\ behavior_app t b = behavior_app t' b'.
Proof.
  intros x t b x' t' b' H.
  destruct b; destruct b'; unfold behavior_app, Eapp in *; simpl in H; try discriminate;
  inversion H; subst; split; auto; congruence.
Qed.

Lemma behavior_prefix_comparable:
  forall t1 b1 t2 b2, behavior_app t1 b1 = behavior_app t2 b2 ->
  (exists q, t2 = t1 ** q) \/ (exists q, t1 = t2 ** q).
Proof.
  induction t1 as [|x t1 IH]; intros b1 t2 b2 H.
  - left. exists t2. reflexivity.
  - destruct t2 as [|x' t2].
    + right. exists (x :: t1). reflexivity.
    + destruct (behavior_app_cons _ _ _ _ _ _ H) as [E H'].
      subst x'.
      destruct (IH _ _ _ H') as [[q Q] | [q Q]].
      * left. exists q. subst. reflexivity.
      * right. exists q. subst. reflexivity.
Qed.

Definition is_vload (ev: event) : bool :=
  match ev with Event_vload _ _ _ _ => true | _ => false end.

Definition count_vloads (t: trace) : nat := length (filter is_vload t).

Lemma count_vloads_app:
  forall t1 t2, count_vloads (t1 ++ t2) = (count_vloads t1 + count_vloads t2)%nat.
Proof.
  intros. unfold count_vloads. rewrite filter_app. apply app_length.
Qed.

Lemma vload_after:
  forall t1 x t2 y q, t2 ** y :: nil = (t1 ** x :: nil) ** q ->
  is_vload x = true -> count_vloads t1 = count_vloads t2 -> x = y.
Proof.
  intros t1 x t2 y q E V C. unfold Eapp in E.
  destruct q as [|z q].
  - rewrite app_nil_r in E. apply app_inj_tail in E. destruct E; congruence.
  - assert (NZ: z :: q <> nil) by discriminate.
    destruct (exists_last NZ) as [q' [a Q]].
    rewrite Q, app_assoc in E. apply app_inj_tail in E. destruct E as [E1 E2].
    exfalso. rewrite E1, !count_vloads_app in C.
    assert (count_vloads (x :: nil) = 1%nat) by (unfold count_vloads; simpl; rewrite V; auto).
    lia.
Qed.

Lemma vload_unique:
  forall beh t1 x b1 t2 y b2,
  beh = behavior_app (t1 ** x :: nil) b1 ->
  beh = behavior_app (t2 ** y :: nil) b2 ->
  is_vload x = true -> is_vload y = true ->
  count_vloads t1 = count_vloads t2 -> x = y.
Proof.
  intros beh t1 x b1 t2 y b2 E1 E2 V1 V2 C.
  rewrite E1 in E2.
  destruct (behavior_prefix_comparable _ _ _ _ E2) as [[q Q] | [q Q]].
  - exact (vload_after _ _ _ _ _ Q V1 C).
  - symmetry. exact (vload_after _ _ _ _ _ Q V2 (eq_sym C)).
Qed.

Lemma match_traces_vload_inv:
  forall ge chunk id ofs res1 e',
  match_traces ge (Event_vload chunk id ofs res1 :: nil) (e' :: nil) ->
  exists res2, e' = Event_vload chunk id ofs res2 /\ eventval_type res1 = eventval_type res2.
Proof.
  intros. inversion H; subst. eauto.
Qed.

(* On AArch64, pointers are 64 bits wide (aarch64/Archi.v, line 22), so an event value of the
   type of int is an integer. *)
Local Transparent Archi.ptr64.

Lemma eventval_type_int:
  forall ev, eventval_type ev = Tint -> exists i, ev = EVint i.
Proof.
  destruct ev; simpl; intros H; try discriminate; eauto.
Qed.

(* reads sigma t: the trace t has no system call, and its k-th volatile load reads the value
   EVint (sigma k). *)
Definition reads (sigma: nat -> int) (t: trace) : Prop :=
  forall tp ev u, t = tp ** ev :: u ->
  match ev with
  | Event_syscall _ _ _ => False
  | Event_vload _ _ _ v => v = EVint (sigma (count_vloads tp))
  | _ => True
  end.

(* kth_vload beh k ev: the k-th volatile load of the behavior beh reads ev.  read_values beh k
   is the integer that the k-th volatile load of beh reads, when there is one. *)
Definition kth_vload (beh: program_behavior) (k: nat) (ev: eventval) : Prop :=
  exists t1 chunk id ofs b1,
    beh = behavior_app (t1 ** Event_vload chunk id ofs ev :: nil) b1 /\ count_vloads t1 = k.

Definition read_values (beh: program_behavior) (k: nat) : int :=
  match ClassicalEpsilon.epsilon (inhabits (EVint Int.zero)) (kth_vload beh k) with
  | EVint i => i
  | _ => Int.zero
  end.

Lemma read_values_kth:
  forall beh tp chunk id ofs i b,
  beh = behavior_app (tp ** Event_vload chunk id ofs (EVint i) :: nil) b ->
  read_values beh (count_vloads tp) = i.
Proof.
  intros beh tp chunk id ofs i b PRE.
  assert (PK: kth_vload beh (count_vloads tp) (EVint i))
    by (red; exists tp, chunk, id, ofs, b; split; auto).
  destruct (ClassicalEpsilon.epsilon_spec (inhabits (EVint Int.zero))
              (kth_vload beh (count_vloads tp)) (ex_intro _ _ PK))
    as [t1 [chunk1 [id1 [ofs1 [b1 [E1 C1]]]]]].
  generalize (vload_unique _ _ _ _ _ _ _ E1 PRE eq_refl eq_refl C1). intro U.
  unfold read_values.
  set (x := ClassicalEpsilon.epsilon (inhabits (EVint Int.zero))
              (kth_vload beh (count_vloads tp))) in *.
  assert (V: x = EVint i) by congruence.
  rewrite V. reflexivity.
Qed.

(* Q holds of a sequence sigma of values and of a termination when the termination's trace reads
   sigma, and of a determinate semantics with such a termination for every sigma, every behavior
   is one of them.  For a behavior beh, take the termination for read_values beh.  Where beh would
   leave it, beh reads at its k-th volatile load a value other than the k-th of read_values beh,
   which is the value of that load, since kth_vload makes the load unique. *)
Theorem determinate_reads:
  forall L, determinate L ->
  forall (Q: (nat -> int) -> trace -> int -> Prop),
  (forall sigma, exists t r,
     program_behaves L (Terminates t r) /\ reads sigma t /\ Q sigma t r) ->
  forall beh, program_behaves L beh ->
  exists sigma t r, beh = Terminates t r /\ reads sigma t /\ Q sigma t r.
Proof.
  intros L DET Q HB beh B.
  destruct (HB (read_values beh)) as [t [r [BT [HR HQ]]]].
  exists (read_values beh), t, r. split; [|split; auto].
  destruct (determinate_behavior_leaves L DET _ _ BT _ B)
    as [EQ | [tp [e [e' [u [A [NE [M [b' PRE]]]]]]]]]; auto.
  exfalso.
  generalize (HR tp e u A). intro HE.
  destruct e as [name args res | chunk id ofs res1 | chunk id ofs v | txt args]; simpl in HE.
  - exact HE.
  - destruct (match_traces_vload_inv _ _ _ _ _ _ M) as [res2 [E' TY]]. subst e'.
    destruct (eventval_type_int res2) as [i2 EV].
    { rewrite <- TY, HE. reflexivity. }
    subst res2.
    apply NE. rewrite HE, (read_values_kth _ _ _ _ _ _ _ PRE). reflexivity.
  - inversion M; subst. elim NE; reflexivity.
  - inversion M; subst. elim NE; reflexivity.
Qed.

(** For a Clight program with a termination that reads sigma and satisfies Q for every sequence
    sigma of values, the Asm program has such a termination for every sigma, and every behavior
    of the Asm program is one of them. *)
Theorem clight2_bigstep_asm_reads:
  forall p p1 p2 tp (Q: (nat -> int) -> trace -> int -> Prop),
  SimplExpr.transl_program p = OK p1 ->
  SimplLocals.transf_program p1 = OK p2 ->
  transf_c_program p = OK tp ->
  (forall sigma, exists t r,
     ClightBigstep.Clight2.bigstep_program_terminates p2 t r /\ reads sigma t /\ Q sigma t r) ->
  (forall sigma, exists t r,
     program_behaves (Asm.semantics tp) (Terminates t r) /\ reads sigma t /\ Q sigma t r) /\
  (forall beh, program_behaves (Asm.semantics tp) beh ->
     exists sigma t r, beh = Terminates t r /\ reads sigma t /\ Q sigma t r).
Proof.
  intros p p1 p2 tp Q E1 E2 TR H.
  assert (HA: forall sigma, exists t r,
     program_behaves (Asm.semantics tp) (Terminates t r) /\ reads sigma t /\ Q sigma t r).
  { intros sigma. destruct (H sigma) as [t [r [B [HR HQ]]]].
    exists t, r. split; auto. eapply clight2_bigstep_to_asm; eauto. }
  split; auto.
  intros beh B'. eapply determinate_reads; eauto.
  apply Asm.semantics_determinate.
Qed.

Print Assumptions clight2_bigstep_to_asm.
Print Assumptions clight2_bigstep_asm_unique.
Print Assumptions clight2_bigstep_asm_reads.
