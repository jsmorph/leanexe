(* From the big-step termination of the Clight program that clightgen prints
   (after SimplExpr and SimplLocals) to the behavior of the Asm program that ccomp produces
   from the same C program.  CompCert 3.18 proves every step, and this file composes them into
   clight2_bigstep_to_asm.  clight2_bigstep_asm_unique adds, from the determinacy of Asm, that
   the termination is the Asm program's only behavior when its trace has no inputs, and
   clight2_bigstep_asm_reads that the behaviors of a program whose volatile loads read a
   sequence of values are the terminations of a family indexed by those values.
   clight2_loop_to_asm carries a main that runs an initialization and then a loop forever, each
   iteration with a nonempty trace, to the reactive behaviors of the Asm program, one for each
   sequence of values read, and shows that every behavior of the Asm program is bisimilar to one
   of them.  The uniqueness halves of clight2_bigstep_asm_reads and clight2_loop_to_asm take the
   premise int_loads, which holds of every behavior when pointers are 64 bits wide, and the
   corollaries clight2_bigstep_asm_reads_ptr64 and clight2_loop_to_asm_ptr64 state them without
   it.  rocq/check.sh checks the file against a CompCert 3.18 tree whose proofs are built, configured
   for AArch64 or for ARMv7-M. *)

From Coq Require Classical ClassicalEpsilon.
Require Import Coqlib Errors AST Integers Linking Values Memory Globalenvs Events Smallstep.
Require Import Behaviors Determinism.
Require Csyntax Ctypes Clight ClightBigstep Asm.
Import (coercions) Ctypes Clight.
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
   (semantics_determinate in the Asm.v of each back end): two steps from one state have traces
   that match_traces relates (common/Events.v, lines 505 to 517), and with equal traces they
   reach one state.  match_traces relates a trace without inputs, a system call or a volatile load,
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

(* An event value of the type of int is an integer EVint or, when pointers are 32 bits wide and
   Tptr is Tint (common/AST.v), a pointer EVptr_global, which ev_match_ptr (common/Events.v)
   lets a volatile load of a chunk of that type read for every public symbol.  The Lean copy of
   Clight omits ev_match_ptr, so the traces of its executions have no pointer events, and the
   uniqueness theorems below consider the behaviors in which no such load reads a pointer.
   int_loads beh holds when every volatile load of beh whose value has the type of int reads an
   integer.  With 64-bit pointers it holds of every behavior (int_loads_ptr64).  Every behavior
   that the uniqueness theorems describe satisfies it (reads_int_loads, reacts_int_loads), so the
   premise excludes only behaviors that no such theorem describes and is the weakest premise on
   behaviors under which they hold.  A premise about the program would have to rule out pointer
   events by the chunks of its volatile loads or by its public symbols, but the input program
   and the controller load Mint8unsigned, whose type is int, and clightgen makes main public. *)
Definition int_loads (beh: program_behavior) : Prop :=
  forall t chunk id ofs ev,
  behavior_prefix (t ** Event_vload chunk id ofs ev :: nil) beh ->
  eventval_type ev = Tint -> exists i, ev = EVint i.

Lemma int_loads_ptr64: Archi.ptr64 = true -> forall beh, int_loads beh.
Proof.
  intros P beh t chunk id ofs ev _ TY.
  destruct ev; simpl in TY; try (unfold Tptr in TY; rewrite P in TY); try discriminate TY; eauto.
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

Lemma reads_int_loads:
  forall sigma t r, reads sigma t -> int_loads (Terminates t r).
Proof.
  intros sigma t r R tp chunk id ofs ev [b E] _.
  destruct b as [u r1 | u | U | u]; simpl in E; try discriminate. inv E.
  exists (sigma (count_vloads tp)).
  exact (R tp (Event_vload chunk id ofs ev) u ltac:(rewrite Eapp_assoc; reflexivity)).
Qed.

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

(* A behavior beh with int_loads cannot leave a trace that reads read_values beh: where the
   trace has the event e after the prefix tp, beh cannot have a different event e' that
   match_traces relates to e.  Both would be volatile loads, e' would read a value of the type of
   int, which int_loads makes an integer, and e reads the value of the load of beh, since
   kth_vload makes that load unique. *)
Lemma read_values_leaves:
  forall ge tp e e' b beh,
  int_loads beh ->
  match e with
  | Event_syscall _ _ _ => False
  | Event_vload _ _ _ v => v = EVint (read_values beh (count_vloads tp))
  | _ => True
  end ->
  match_traces ge (e :: nil) (e' :: nil) -> e <> e' ->
  beh = behavior_app (tp ** e' :: nil) b -> False.
Proof.
  intros ge tp e e' b beh IL HE M NE PRE.
  destruct e as [name args res | chunk id ofs res1 | chunk id ofs v | txt args]; simpl in HE.
  - exact HE.
  - destruct (match_traces_vload_inv _ _ _ _ _ _ M) as [res2 [E' TY]]. subst e'.
    destruct (IL tp chunk id ofs res2) as [i2 EV].
    { exists b. exact PRE. }
    { rewrite <- TY, HE. reflexivity. }
    subst res2.
    apply NE. rewrite HE, (read_values_kth _ _ _ _ _ _ _ PRE). reflexivity.
  - inversion M; subst. elim NE; reflexivity.
  - inversion M; subst. elim NE; reflexivity.
Qed.

(* Q holds of a sequence sigma of values and of a termination when the termination's trace reads
   sigma, and of a determinate semantics with such a termination for every sigma, every behavior
   with int_loads is one of them.  For a behavior beh, take the termination for read_values beh,
   which beh cannot leave by read_values_leaves. *)
Theorem determinate_reads:
  forall L, determinate L ->
  forall (Q: (nat -> int) -> trace -> int -> Prop),
  (forall sigma, exists t r,
     program_behaves L (Terminates t r) /\ reads sigma t /\ Q sigma t r) ->
  forall beh, program_behaves L beh -> int_loads beh ->
  exists sigma t r, beh = Terminates t r /\ reads sigma t /\ Q sigma t r.
Proof.
  intros L DET Q HB beh B IL.
  destruct (HB (read_values beh)) as [t [r [BT [HR HQ]]]].
  exists (read_values beh), t, r. split; [|split; auto].
  destruct (determinate_behavior_leaves L DET _ _ BT _ B)
    as [EQ | [tp [e [e' [u [A [NE [M [b' PRE]]]]]]]]]; auto.
  exfalso. exact (read_values_leaves _ _ _ _ _ _ IL (HR tp e u A) M NE PRE).
Qed.

(** For a Clight program with a termination that reads sigma and satisfies Q for every sequence
    sigma of values, the Asm program has such a termination for every sigma, and every behavior
    of the Asm program with int_loads is one of them. *)
Theorem clight2_bigstep_asm_reads:
  forall p p1 p2 tp (Q: (nat -> int) -> trace -> int -> Prop),
  SimplExpr.transl_program p = OK p1 ->
  SimplLocals.transf_program p1 = OK p2 ->
  transf_c_program p = OK tp ->
  (forall sigma, exists t r,
     ClightBigstep.Clight2.bigstep_program_terminates p2 t r /\ reads sigma t /\ Q sigma t r) ->
  (forall sigma, exists t r,
     program_behaves (Asm.semantics tp) (Terminates t r) /\ reads sigma t /\ Q sigma t r) /\
  (forall beh, program_behaves (Asm.semantics tp) beh -> int_loads beh ->
     exists sigma t r, beh = Terminates t r /\ reads sigma t /\ Q sigma t r).
Proof.
  intros p p1 p2 tp Q E1 E2 TR H.
  assert (HA: forall sigma, exists t r,
     program_behaves (Asm.semantics tp) (Terminates t r) /\ reads sigma t /\ Q sigma t r).
  { intros sigma. destruct (H sigma) as [t [r [B [HR HQ]]]].
    exists t, r. split; auto. eapply clight2_bigstep_to_asm; eauto. }
  split; auto.
  intros beh B' IL. eapply determinate_reads; eauto.
  apply Asm.semantics_determinate.
Qed.

(** With 64-bit pointers, as on AArch64, every behavior of the Asm program is one of the
    terminations. *)
Corollary clight2_bigstep_asm_reads_ptr64:
  Archi.ptr64 = true ->
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
  intros P p p1 p2 tp Q E1 E2 TR H.
  destruct (clight2_bigstep_asm_reads p p1 p2 tp Q E1 E2 TR H) as [A U].
  split; auto. intros beh B. apply U; auto. apply int_loads_ptr64; auto.
Qed.

(* loop_entry s init body post holds when the statement s runs init and then the loop Sloop body
   post, through sequences that precede or follow the loop.  loop_reacts p t0 W, the twin of the
   Lean definition LoopReacts, holds when main runs init with the trace t0 and then the loop
   forever, its n-th iteration running body and post with the nonempty trace W n.  The iterations
   follow from an invariant Inv that holds after init and that every iteration preserves. *)

Inductive loop_entry:
  Clight.statement -> Clight.statement -> Clight.statement -> Clight.statement -> Prop :=
  | loop_entry_loop: forall body post,
      loop_entry (Clight.Sloop body post) Clight.Sskip body post
  | loop_entry_seq_after: forall s init body post rest,
      loop_entry s init body post ->
      loop_entry (Clight.Ssequence s rest) init body post
  | loop_entry_seq_before: forall s init body post pre,
      loop_entry s init body post ->
      loop_entry (Clight.Ssequence pre s) (Clight.Ssequence pre init) body post.

Definition loop_reacts (p: Clight.program) (t0: trace) (W: nat -> trace) : Prop :=
  (forall n, W n <> E0) /\
  exists (b: block) (f: Clight.function) (m0 m1: mem) (e: Clight.env) (le0: Clight.temp_env)
    (init body post: Clight.statement) (Inv: nat -> Clight.temp_env -> mem -> Prop),
    Genv.init_mem p = Some m0 /\
    Genv.find_symbol (Clight.globalenv p) p.(Ctypes.prog_main) = Some b /\
    Genv.find_funct_ptr (Clight.globalenv p) b = Some (Ctypes.Internal f) /\
    Clight.type_of_function f = Ctypes.Tfunction nil Ctypes.type_int32s cc_default /\
    loop_entry f.(Clight.fn_body) init body post /\
    Clight.function_entry2 (Clight.globalenv p) f nil m0 e le0 m1 /\
    (exists le m, ClightBigstep.Clight2.exec_stmt (Clight.globalenv p) e le0 m1 init t0 le m
                    ClightBigstep.Out_normal /\ Inv O le m) /\
    forall n le m, Inv n le m -> exists le' m',
      ClightBigstep.Clight2.exec_stmt (Clight.globalenv p) e le m (Clight.Ssequence body post)
        (W n) le' m' ClightBigstep.Out_normal /\
      Inv (n + 1)%nat le' m'.

(* windows W n is the trace W 0 ** ... ** W (n - 1) of the first n iterations, and concat W NE
   is the infinite trace of all iterations, built through traceinf' as Vélus's mk_trace is
   (src/Traces.v at commit 27ba860c). *)

Fixpoint windows (W: nat -> trace) (n: nat) : trace :=
  match n with
  | O => E0
  | S k => windows W k ** W k
  end.

CoFixpoint concat' (W: nat -> trace) (NE: forall n, W n <> E0) (n: nat) : traceinf' :=
  Econsinf' (W n) (concat' W NE (S n)) (NE n).

Definition concat_from (W: nat -> trace) (NE: forall n, W n <> E0) (n: nat) : traceinf :=
  traceinf_of_traceinf' (concat' W NE n).

Definition concat (W: nat -> trace) (NE: forall n, W n <> E0) : traceinf := concat_from W NE O.

Lemma concat_from_unfold:
  forall W NE n, concat_from W NE n = W n *** concat_from W NE (S n).
Proof.
  intros. unfold concat_from.
  rewrite (unroll_traceinf' (concat' W NE n)). simpl.
  apply traceinf_traceinf'_app.
Qed.

Lemma concat_windows:
  forall W NE t0 n, t0 *** concat W NE = (t0 ** windows W n) *** concat_from W NE n.
Proof.
  induction n; simpl.
  - rewrite E0_right. reflexivity.
  - rewrite IHn, concat_from_unfold, !Eappinf_assoc. reflexivity.
Qed.

Lemma windows_length:
  forall W, (forall n, W n <> E0) -> forall n, (n <= length (windows W n))%nat.
Proof.
  intros W NE. induction n; simpl.
  - lia.
  - unfold Eapp. rewrite app_length.
    destruct (W n) eqn:WN.
    + elim (NE n). rewrite WN. reflexivity.
    + simpl. lia.
Qed.

Lemma Eappinf_prefix:
  forall t1 T1 t2 T2, t1 *** T1 = t2 *** T2 -> (length t1 <= length t2)%nat ->
  exists u, t2 = t1 ** u.
Proof.
  induction t1 as [|x t1 IH]; intros T1 t2 T2 E LEN.
  - exists t2. reflexivity.
  - destruct t2 as [|y t2]; simpl in LEN. lia.
    change (Econsinf x (t1 *** T1) = Econsinf y (t2 *** T2)) in E.
    injection E as EX ET. subst y.
    destruct (IH T1 t2 T2 ET ltac:(lia)) as [u U].
    exists u. subst t2. reflexivity.
Qed.

(* Every finite prefix of t0 *** concat W NE is a prefix of t0 ** windows W n for some n, so
   the infinite trace reads sigma when every t0 ** windows W n does. *)
Lemma windows_reads:
  forall sigma t0 W NE,
  (forall n, reads sigma (t0 ** windows W n)) ->
  forall tp ev T', t0 *** concat W NE = (tp ** ev :: nil) *** T' ->
  match ev with
  | Event_syscall _ _ _ => False
  | Event_vload _ _ _ v => v = EVint (sigma (count_vloads tp))
  | _ => True
  end.
Proof.
  intros sigma t0 W NE R tp ev T' E.
  rewrite (concat_windows W NE t0 (S (length tp))) in E.
  destruct (Eappinf_prefix _ _ _ _ (eq_sym E)) as [u U].
  { generalize (windows_length W NE (S (length tp))).
    unfold Eapp. rewrite !app_length. simpl. lia. }
  apply (R (S (length tp)) tp ev u).
  rewrite U, Eapp_assoc. reflexivity.
Qed.

Lemma traceinf_sim_app_inv:
  forall t T1 T2, traceinf_sim (t *** T1) T2 -> exists T2', T2 = t *** T2'.
Proof.
  induction t as [|e t IH]; intros T1 T2 S.
  - exists T2. reflexivity.
  - change ((e :: t) *** T1) with (Econsinf e (t *** T1)) in S.
    inversion S as [e' T1' T2' S' E1 E2]; subst.
    destruct (IH _ _ S') as [T U]. exists T. subst. reflexivity.
Qed.

Lemma reacts_int_loads:
  forall sigma t0 W NE beh,
  (forall n, reads sigma (t0 ** windows W n)) ->
  same_behaviors beh (Reacts (t0 *** concat W NE)) -> int_loads beh.
Proof.
  intros sigma t0 W NE beh R S tp chunk id ofs ev [b E] _.
  destruct beh as [u r | u | T | u]; simpl in S; try contradiction.
  destruct b as [u r | u | T' | u]; simpl in E; try discriminate. inv E.
  destruct (traceinf_sim_app_inv _ _ _ S) as [T2 E].
  exists (sigma (count_vloads tp)).
  exact (windows_reads sigma t0 W NE R tp (Event_vload chunk id ofs ev) T2 E).
Qed.

(* One iteration in small steps: step_loop enters body, the steps of body end in Sskip,
   step_skip_or_continue_loop1 enters post, the steps of post end in Sskip, and step_skip_loop2
   returns to the loop with the same continuation. *)

Lemma exec_seq_normal:
  forall ge e le m s1 s2 t le' m',
  ClightBigstep.exec_stmt Clight.function_entry2 ge e le m (Clight.Ssequence s1 s2) t le' m'
    ClightBigstep.Out_normal ->
  exists t1 le1 m1 t2, t = t1 ** t2 /\
    ClightBigstep.exec_stmt Clight.function_entry2 ge e le m s1 t1 le1 m1
      ClightBigstep.Out_normal /\
    ClightBigstep.exec_stmt Clight.function_entry2 ge e le1 m1 s2 t2 le' m'
      ClightBigstep.Out_normal.
Proof.
  intros. inversion H; subst.
  - do 4 eexists. split. reflexivity. split; eassumption.
  - congruence.
Qed.

Lemma exec_star:
  forall p e le m s t le' m' f k,
  ClightBigstep.exec_stmt Clight.function_entry2 (Clight.globalenv p) e le m s t le' m'
    ClightBigstep.Out_normal ->
  Star (Clight.semantics2 p) (Clight.State f s k e le m) t
       (Clight.State f Clight.Sskip k e le' m').
Proof.
  intros p e le m s t le' m' f k EX.
  destruct (ClightBigstep.exec_stmt_steps Clight.function_entry2 p _ _ _ _ _ _ _ _ EX f k)
    as [S [ST OSM]].
  inversion OSM; subst. exact ST.
Qed.

Lemma window_star:
  forall p f e body post k le m t le' m',
  ClightBigstep.Clight2.exec_stmt (Clight.globalenv p) e le m (Clight.Ssequence body post)
    t le' m' ClightBigstep.Out_normal ->
  Star (Clight.semantics2 p) (Clight.State f (Clight.Sloop body post) k e le m) t
       (Clight.State f (Clight.Sloop body post) k e le' m').
Proof.
  intros p f e body post k le m t le' m' EX.
  destruct (exec_seq_normal _ _ _ _ _ _ _ _ _ EX) as [t1 [le1 [m1 [t2 [T [EX1 EX2]]]]]].
  subst t.
  replace (t1 ** t2) with (E0 ** t1 ** E0 ** t2 ** E0) by traceEq.
  eapply star_step; [apply Clight.step_loop | | reflexivity].
  eapply star_trans; [apply exec_star; eexact EX1 | | reflexivity].
  eapply star_step; [apply Clight.step_skip_or_continue_loop1; auto | | reflexivity].
  eapply star_trans; [apply exec_star; eexact EX2 | | reflexivity].
  apply star_one. apply Clight.step_skip_loop2.
Qed.

(* From a statement s with loop_entry s init body post, the steps reach the loop with the trace of
   init.  step_seq and step_skip_seq pass the sequences before the loop, whose first statements
   make up init, and step_seq enters the sequences after it, whose second statements the loop
   never reaches. *)
Lemma entry_star:
  forall p f e s init body post, loop_entry s init body post ->
  forall k le m t le' m',
  ClightBigstep.Clight2.exec_stmt (Clight.globalenv p) e le m init t le' m'
    ClightBigstep.Out_normal ->
  exists k', Star (Clight.semantics2 p) (Clight.State f s k e le m) t
                  (Clight.State f (Clight.Sloop body post) k' e le' m').
Proof.
  intros p f e s init body post LE.
  induction LE as [body post | s init body post rest LE IH | s init body post pre LE IH];
    intros k le m t le' m' EX.
  - exists k. inversion EX; subst. apply star_refl.
  - destruct (IH (Clight.Kseq rest k) le m t le' m' EX) as [k' ST].
    exists k'. replace t with (E0 ** t) by traceEq.
    eapply star_step; [apply Clight.step_seq | exact ST | reflexivity].
  - destruct (exec_seq_normal _ _ _ _ _ _ _ _ _ EX) as [t1 [le1 [m1 [t2 [T [EX1 EX2]]]]]].
    destruct (IH k le1 m1 t2 le' m' EX2) as [k' ST].
    exists k'. subst t.
    replace (t1 ** t2) with (E0 ** t1 ** E0 ** t2) by traceEq.
    eapply star_step; [apply Clight.step_seq | | reflexivity].
    eapply star_trans; [apply exec_star; eexact EX1 | | reflexivity].
    eapply star_step; [apply Clight.step_skip_seq | exact ST | reflexivity].
Qed.

(* From a state of the invariant at iteration n, the loop is Forever_reactive with the trace of
   the iterations from n on, by cofixpoint as in Vélus's reactive_loop
   (src/ObcToClight/Correctness.v at commit 27ba860c). *)
Lemma loop_forever_reactive:
  forall p f e body post k (Inv: nat -> Clight.temp_env -> mem -> Prop) W
         (NE: forall n, W n <> E0),
  (forall n le m, Inv n le m -> exists le' m',
     ClightBigstep.Clight2.exec_stmt (Clight.globalenv p) e le m (Clight.Ssequence body post)
       (W n) le' m' ClightBigstep.Out_normal /\
     Inv (n + 1)%nat le' m') ->
  forall n le m, Inv n le m ->
  Forever_reactive (Clight.semantics2 p) (Clight.State f (Clight.Sloop body post) k e le m)
    (concat_from W NE n).
Proof.
  intros p f e body post k Inv W NE WIN.
  cofix COINDHYP. intros n le m I.
  destruct (WIN n le m I) as [le' [m' [EX I']]].
  replace (n + 1)%nat with (S n) in I' by lia.
  rewrite concat_from_unfold.
  econstructor.
  - apply window_star. exact EX.
  - apply NE.
  - exact (COINDHYP (S n) le' m' I').
Qed.

Theorem loop_reacts_clight:
  forall p t0 W (NE: forall n, W n <> E0), loop_reacts p t0 W ->
  program_behaves (Clight.semantics2 p) (Reacts (t0 *** concat W NE)).
Proof.
  intros p t0 W NE [_ [b [f [m0 [m1 [e [le0 [init [body [post [Inv
    [IM [FS [FF [TY [LE [FE [[le [m [EI I0]]] WIN]]]]]]]]]]]]]]]]]].
  destruct (entry_star p f e _ _ _ _ LE Clight.Kstop le0 m1 t0 le m EI) as [k ST].
  eapply program_runs.
  - eapply Clight.initial_state_intro; eauto.
  - apply state_reacts.
    eapply star_forever_reactive.
    + replace t0 with (E0 ** t0) by traceEq.
      eapply star_step;
        [eapply Clight.step_internal_function; eexact FE | exact ST | reflexivity].
    + unfold concat. eapply loop_forever_reactive; eauto.
Qed.

(* Two runs of a determinate semantics from one state, one of them reactive with the trace T,
   agree until a step at which their events differ, which match_traces allows only at a pair of
   system calls or of volatile loads.  A run that agrees with the reactive run at every step
   cannot stop or diverge silently, and a reactive run that agrees with it at every step has a
   trace bisimilar to T. *)

Section REACTIVE.

Variable L: semantics.
Hypothesis DET: determinate L.

Lemma star_reactive_follows_or_leaves:
  forall s t2 s2, Star L s t2 s2 ->
  forall T, Forever_reactive L s T ->
  (exists T', T = t2 *** T' /\ Forever_reactive L s2 T') \/
  exists tp e e' u T', t2 = tp ** e' :: u /\ T = (tp ** e :: nil) *** T' /\ e <> e' /\
    match_traces (symbolenv L) (e :: nil) (e' :: nil).
Proof.
  induction 1 as [s | s1 t1 s2 t2 s3 t12 STEP STAR IH EQ]; intros T F.
  - left. exists T. split; auto.
  - inversion F as [s0 s4 ta T1 STARA NEA FA EQT]; subst.
    inversion STARA as [s0 | s0 tx sx ty s0' txy STEPX STARX EQX]; subst.
    + elim NEA; auto.
    + destruct (sd_determ DET _ _ _ _ _ STEPX STEP) as [M E].
      destruct (Classical_Prop.classic (tx = t1)) as [EQ1 | NE1].
      * subst tx. assert (sx = s2) by (apply E; auto). subst sx.
        destruct (IH _ (star_forever_reactive STARX FA))
          as [[T' [A B]] | [tp [e [e' [u [T' [A [B [C D]]]]]]]]].
        { left. exists T'. split; auto. rewrite !Eappinf_assoc, A. reflexivity. }
        { right. exists (t1 ** tp), e, e', u, T'. subst.
          split. rewrite Eapp_assoc. reflexivity.
          split. rewrite !Eappinf_assoc, B, !Eappinf_assoc. reflexivity.
          split; auto. }
      * right.
        assert (X: exists e e', tx = e :: nil /\ t1 = e' :: nil)
          by (inversion M; subst; first [elim NE1; reflexivity | do 2 eexists; split; reflexivity]).
        destruct X as [e [e' [X1 X2]]]. subst tx t1.
        exists E0, e, e', t2, (ty *** T1).
        split. reflexivity.
        split. rewrite Eappinf_assoc. reflexivity.
        split; auto. intro EE. apply NE1. rewrite EE. reflexivity.
Qed.

Lemma nostep_not_reactive:
  forall s T, Nostep L s -> ~ Forever_reactive L s T.
Proof.
  intros s T NS F. inversion F as [s0 s1 t T1 STAR NE F1]; subst.
  inversion STAR; subst.
  - elim NE; auto.
  - eapply NS; eauto.
Qed.

Lemma star_forever_silent_E0:
  forall s t s', Star L s t s' -> Forever_silent L s -> t = E0.
Proof.
  induction 1 as [s | s1 t1 s2 t2 s3 t STEP STAR IH EQ]; intros F; auto.
  inversion F as [s0 s4 STEP0 F0]; subst.
  destruct (sd_determ DET _ _ _ _ _ STEP STEP0) as [M E].
  inv M. assert (s2 = s4) by (apply E; auto). subst.
  rewrite IH; auto.
Qed.

Lemma forever_silent_not_reactive:
  forall s T, Forever_silent L s -> ~ Forever_reactive L s T.
Proof.
  intros s T FS F. inversion F as [s0 s1 t T1 STAR NE F1]; subst.
  elim NE. eapply star_forever_silent_E0; eauto.
Qed.

(* leaves_inf T T2: the infinite traces T and T2 share a prefix followed by two different events
   that match_traces relates. *)
Definition leaves_inf (T T2: traceinf) : Prop :=
  exists tp e e' T' T2', T = (tp ** e :: nil) *** T' /\ T2 = (tp ** e' :: nil) *** T2' /\
    e <> e' /\ match_traces (symbolenv L) (e :: nil) (e' :: nil).

Lemma leaves_inf_app:
  forall t T T2, leaves_inf T T2 -> leaves_inf (t *** T) (t *** T2).
Proof.
  intros t T T2 [tp [e [e' [T' [T2' [A [B [C D]]]]]]]].
  exists (t ** tp), e, e', T', T2'. subst. rewrite !Eappinf_assoc. auto.
Qed.

Lemma reactive_inv2:
  forall s t1 s1, Star L s t1 s1 ->
  forall t2 s2 T1 T2,
  Star L s t2 s2 -> t1 <> E0 -> t2 <> E0 ->
  Forever_reactive L s1 T1 -> Forever_reactive L s2 T2 ->
  ~ leaves_inf (t1 *** T1) (t2 *** T2) ->
  exists s' t T1' T2', t <> E0 /\ Forever_reactive L s' T1' /\ Forever_reactive L s' T2' /\
    t1 *** T1 = t *** T1' /\ t2 *** T2 = t *** T2'.
Proof.
  induction 1 as [s | s ta sa tb s1 t1 STEPA STARA IH EQA];
    intros t2 s2 T1 T2 S2 NE1 NE2 F1 F2 NL.
  - elim NE1; auto.
  - inversion S2 as [s0 | s0 tc sc td s2' t2' STEPC STARC EQC]; subst.
    + elim NE2; auto.
    + destruct (sd_determ DET _ _ _ _ _ STEPA STEPC) as [M E].
      destruct (Classical_Prop.classic (ta = tc)) as [EQ | NEQ].
      * subst tc. assert (sc = sa) by (symmetry; apply E; auto). subst sc.
        destruct ta as [|ev ta].
        { eapply IH; eauto. }
        { exists sa, (ev :: ta), (tb *** T1), (td *** T2).
          split. discriminate.
          split. eapply star_forever_reactive; eauto.
          split. eapply star_forever_reactive; eauto.
          split; apply Eappinf_assoc. }
      * elim NL.
        assert (X: exists e e', ta = e :: nil /\ tc = e' :: nil)
          by (inversion M; subst; first [elim NEQ; reflexivity | do 2 eexists; split; reflexivity]).
        destruct X as [e [e' [X1 X2]]]. subst ta tc.
        exists E0, e, e', (tb *** T1), (td *** T2).
        split. rewrite Eappinf_assoc. reflexivity.
        split. rewrite Eappinf_assoc. reflexivity.
        split; auto. intro EE. apply NEQ. rewrite EE. reflexivity.
Qed.

Lemma reactive_sim':
  forall s T T2, Forever_reactive L s T -> Forever_reactive L s T2 -> ~ leaves_inf T T2 ->
  traceinf_sim' T T2.
Proof.
  cofix COINDHYP; intros s T T2 F F2 NL.
  inversion F as [s0 s1 t1 T1 STAR1 NE1 F1]; subst.
  inversion F2 as [s0 s2 t2 T2' STAR2 NE2 F2']; subst.
  destruct (reactive_inv2 _ _ _ STAR1 _ _ _ _ STAR2 NE1 NE2 F1 F2' NL)
    as [s' [t [T1' [T2'' [NE [A [B [C D]]]]]]]].
  assert (NL': ~ leaves_inf T1' T2'').
  { intro LV. apply NL. rewrite C, D. apply leaves_inf_app. exact LV. }
  rewrite C, D. constructor.
  - exact NE.
  - exact (COINDHYP s' T1' T2'' A B NL').
Qed.

Lemma reactive_sim_or_leaves:
  forall s T T2, Forever_reactive L s T -> Forever_reactive L s T2 ->
  traceinf_sim T T2 \/ leaves_inf T T2.
Proof.
  intros s T T2 F F2.
  destruct (Classical_Prop.classic (leaves_inf T T2)) as [LV | NL]; auto.
  left. apply traceinf_sim'_sim. exact (reactive_sim' s T T2 F F2 NL).
Qed.

End REACTIVE.

(* For a determinate semantics with the behavior Reacts (t0 *** concat (W sigma) _) for every
   sequence sigma of values, whose finite prefixes read sigma, every behavior beh with int_loads
   is bisimilar to the one for read_values beh, since beh cannot leave it by
   read_values_leaves. *)
Theorem determinate_reacts_reads:
  forall L, determinate L ->
  forall t0 (W: (nat -> int) -> nat -> trace) (NE: forall sigma n, W sigma n <> E0),
  (forall sigma, program_behaves L (Reacts (t0 *** concat (W sigma) (NE sigma)))) ->
  (forall sigma n, reads sigma (t0 ** windows (W sigma) n)) ->
  forall beh, program_behaves L beh -> int_loads beh ->
  exists sigma, same_behaviors beh (Reacts (t0 *** concat (W sigma) (NE sigma))).
Proof.
  intros L DET t0 W NE HB HR beh B IL.
  exists (read_values beh).
  generalize (HB (read_values beh)).
  generalize (windows_reads _ t0 _ (NE (read_values beh)) (HR (read_values beh))).
  generalize (t0 *** concat (W (read_values beh)) (NE (read_values beh))).
  intros T RT BT.
  assert (X: forall tp e e' T' b, T = (tp ** e :: nil) *** T' -> e <> e' ->
             match_traces (symbolenv L) (e :: nil) (e' :: nil) ->
             beh = behavior_app (tp ** e' :: nil) b -> False)
    by (intros tp e e' T' b A C D PRE;
        exact (read_values_leaves _ _ _ _ _ _ IL (RT _ _ _ A) D C PRE)).
  clear RT HB HR IL.
  inversion BT as [s beh0 INIT SB | NOINIT]; subst.
  inversion SB as [ | | T0 REACT | ]; subst.
  inversion B as [s0 beh1 INIT' SB' | NOINIT']; subst.
  - assert (s0 = s) by (eapply sd_initial_determ; eauto). subst s0.
    inversion SB' as [t2 s2 r2 STAR2 FINAL2 | t2 s2 STAR2 SIL | T2 REACT2
                     | t2 s2 STAR2 NS2 NF2]; subst; simpl.
    + destruct (star_reactive_follows_or_leaves L DET _ _ _ STAR2 _ REACT)
        as [[T' [A F]] | [tp [e [e' [u [T' [A [A2 [C D]]]]]]]]].
      * elim (nostep_not_reactive L _ _ (sd_final_nostep DET _ _ FINAL2) F).
      * apply (X tp e e' T' (Terminates u r2) A2 C D). subst. simpl.
        rewrite Eapp_assoc. reflexivity.
    + destruct (star_reactive_follows_or_leaves L DET _ _ _ STAR2 _ REACT)
        as [[T' [A F]] | [tp [e [e' [u [T' [A [A2 [C D]]]]]]]]].
      * elim (forever_silent_not_reactive L DET _ _ SIL F).
      * apply (X tp e e' T' (Diverges u) A2 C D). subst. simpl.
        rewrite Eapp_assoc. reflexivity.
    + destruct (reactive_sim_or_leaves L DET _ _ _ REACT REACT2)
        as [SIM | [tp [e [e' [T' [T2' [A [A2 [C D]]]]]]]]].
      * apply traceinf_sim_sym. exact SIM.
      * exfalso. apply (X tp e e' T' (Reacts T2') A C D). subst. reflexivity.
    + destruct (star_reactive_follows_or_leaves L DET _ _ _ STAR2 _ REACT)
        as [[T' [A F]] | [tp [e [e' [u [T' [A [A2 [C D]]]]]]]]].
      * elim (nostep_not_reactive L _ _ NS2 F).
      * apply (X tp e e' T' (Goes_wrong u) A2 C D). subst. simpl.
        rewrite Eapp_assoc. reflexivity.
  - elim (NOINIT' s INIT).
Qed.

(** For a Clight program whose main runs an initialization with the trace t0 and then a loop
    forever, with the trace W sigma n in its n-th iteration when the volatile loads read the
    sequence sigma of values, the Asm program has the reactive behavior with the trace t0 ***
    concat (W sigma) (NE sigma) for every sigma, and every behavior of the Asm program with
    int_loads is bisimilar to one of them. *)
Theorem clight2_loop_to_asm:
  forall p p1 p2 tp t0 (W: (nat -> int) -> nat -> trace)
         (NE: forall sigma n, W sigma n <> E0),
  SimplExpr.transl_program p = OK p1 ->
  SimplLocals.transf_program p1 = OK p2 ->
  transf_c_program p = OK tp ->
  (forall sigma, loop_reacts p2 t0 (W sigma)) ->
  (forall sigma n, reads sigma (t0 ** windows (W sigma) n)) ->
  (forall sigma, program_behaves (Asm.semantics tp)
                   (Reacts (t0 *** concat (W sigma) (NE sigma)))) /\
  (forall beh, program_behaves (Asm.semantics tp) beh -> int_loads beh ->
     exists sigma, same_behaviors beh (Reacts (t0 *** concat (W sigma) (NE sigma)))).
Proof.
  intros p p1 p2 tp t0 W NE E1 E2 T LR R.
  assert (HA: forall sigma, program_behaves (Asm.semantics tp)
                              (Reacts (t0 *** concat (W sigma) (NE sigma)))).
  { intros sigma. eapply forward_simulation_same_safe_behavior.
    - eapply clight2_to_asm_forward; eauto.
    - apply loop_reacts_clight. apply LR.
    - red; auto. }
  split; auto.
  intros beh B IL. eapply determinate_reacts_reads; eauto.
  apply Asm.semantics_determinate.
Qed.

(** With 64-bit pointers, as on AArch64, every behavior of the Asm program is bisimilar to one of
    the reactive behaviors. *)
Corollary clight2_loop_to_asm_ptr64:
  Archi.ptr64 = true ->
  forall p p1 p2 tp t0 (W: (nat -> int) -> nat -> trace)
         (NE: forall sigma n, W sigma n <> E0),
  SimplExpr.transl_program p = OK p1 ->
  SimplLocals.transf_program p1 = OK p2 ->
  transf_c_program p = OK tp ->
  (forall sigma, loop_reacts p2 t0 (W sigma)) ->
  (forall sigma n, reads sigma (t0 ** windows (W sigma) n)) ->
  (forall sigma, program_behaves (Asm.semantics tp)
                   (Reacts (t0 *** concat (W sigma) (NE sigma)))) /\
  (forall beh, program_behaves (Asm.semantics tp) beh ->
     exists sigma, same_behaviors beh (Reacts (t0 *** concat (W sigma) (NE sigma)))).
Proof.
  intros P p p1 p2 tp t0 W NE E1 E2 T LR R.
  destruct (clight2_loop_to_asm p p1 p2 tp t0 W NE E1 E2 T LR R) as [A U].
  split; auto. intros beh B. apply U; auto. apply int_loads_ptr64; auto.
Qed.

Print Assumptions clight2_bigstep_to_asm.
Print Assumptions clight2_bigstep_asm_unique.
Print Assumptions clight2_bigstep_asm_reads.
Print Assumptions clight2_bigstep_asm_reads_ptr64.
Print Assumptions clight2_loop_to_asm.
Print Assumptions clight2_loop_to_asm_ptr64.
