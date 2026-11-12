(* The program with requests around the echo with a deadline deadlineCmsdkTick of
   tests/TestSupport/Bare/Req.lean: from the statement deadline_reacts of the instance that
   clightn/check.sh writes from clightgen's Coq file deadline.v, which Lean proves in
   clightn/lean/Deadline.lean, deadline_asm gives by NInst.reacts_asm windows W of every sequence
   sigma of the values that the volatile loads read such that the Asm program reacts with the
   infinite trace of the windows W sigma, which read sigma, and every behavior of the Asm program
   is bisimilar to one of these. *)
Require Import Coqlib Errors AST Integers Events Smallstep Behaviors Ctypes Clight ClightBigstep.
Require Import Determinism Compiler.
Require SimplExpr SimplLocals Asm.
Require NDeadlineSpec NExport Clight2Asm NInst deadline.

Theorem deadline_asm : NDeadlineSpec.stmt_deadline_reacts ->
  forall p p1 p2 tp,
  SimplExpr.transl_program p = OK p1 ->
  SimplLocals.transf_program p1 = OK p2 ->
  transf_c_program p = OK tp ->
  prog_defs deadline.prog = NExport.export_defs (prog_defs p2) ->
  prog_main p2 = prog_main deadline.prog ->
  prog_public p2 = prog_public deadline.prog ->
  prog_types p2 = prog_types deadline.prog ->
  exists (W : (nat -> int) -> nat -> trace) (NE : forall sigma n, W sigma n <> E0),
    (forall sigma n, Clight2Asm.reads sigma (Clight2Asm.windows (W sigma) n)) /\
    (forall sigma, program_behaves (Asm.semantics tp)
                     (Reacts (Clight2Asm.concat (W sigma) (NE sigma)))) /\
    (forall beh, program_behaves (Asm.semantics tp) beh ->
       exists sigma, same_behaviors beh (Reacts (Clight2Asm.concat (W sigma) (NE sigma)))).
Proof.
  intros H. exact (NInst.reacts_asm _ _ H deadline.prog eq_refl eq_refl).
Qed.
