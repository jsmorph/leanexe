(* From the big-step termination of the Clight program that clightgen prints
   (after SimplExpr and SimplLocals) to the behavior of the Asm program that ccomp produces
   from the same C program.  CompCert 3.18 proves every step, and this file composes them.
   rocq/check.sh checks it against a CompCert 3.18 tree whose proofs are built. *)

Require Import Coqlib Errors AST Linking Smallstep Behaviors.
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

Print Assumptions clight2_bigstep_to_asm.
