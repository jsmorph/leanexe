(* From the big-step termination of the Clight program that clightgen prints
   (after SimplExpr and SimplLocals) to the behavior of the Asm program that ccomp produces
   from the same C program.  CompCert 3.18 proves every step, and this file composes them into
   clight2_bigstep_to_asm.  clight2_bigstep_asm_unique adds, from the determinacy of Asm, that
   the termination is the Asm program's only behavior when its trace has no inputs.
   rocq/check.sh checks the file against a CompCert 3.18 tree whose proofs are built. *)

Require Import Coqlib Errors AST Linking Events Smallstep Behaviors.
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

Print Assumptions clight2_bigstep_to_asm.
Print Assumptions clight2_bigstep_asm_unique.
