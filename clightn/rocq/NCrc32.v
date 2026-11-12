(* The bare-metal program of crcCheck 0x3837363534333231 0x39, CRC-32 of 123456789: from the
   statement crc32_terminates of the instance that clightn/check.sh writes from clightgen's Coq
   file crc32.v, which Lean proves in clightn/lean/Crc32.lean, crc32_asm gives by
   NInst.terminates_asm a termination of the Asm program with the trace of the bytes of the
   result and the result 0, or with no event and the code of unreachable. *)
Require Import Coqlib Errors AST Integers Events Smallstep Behaviors Ctypes Clight ClightBigstep.
Require Import Compiler.
Require SimplExpr SimplLocals Asm.
Require NBase NCrc32Spec NExport NInst crc32.

Theorem crc32_asm : NCrc32Spec.stmt_crc32_terminates ->
  forall p p1 p2 tp,
  SimplExpr.transl_program p = OK p1 ->
  SimplLocals.transf_program p1 = OK p2 ->
  transf_c_program p = OK tp ->
  prog_defs crc32.prog = NExport.export_defs (prog_defs p2) ->
  prog_main p2 = prog_main crc32.prog ->
  prog_public p2 = prog_public crc32.prog ->
  prog_types p2 = prog_types crc32.prog ->
  program_behaves (Asm.semantics tp) (Terminates NCrc32Spec.cst_crc32_trace (NBase.r32 0)) \/
  program_behaves (Asm.semantics tp) (Terminates E0 (NBase.r32 1)).
Proof.
  intros [H | H] p p1 p2 tp E1 E2 T D M P C; [left | right];
    exact (NInst.terminates_asm _ _ _ _ H crc32.prog eq_refl eq_refl p p1 p2 tp E1 E2 T D M P C).
Qed.
