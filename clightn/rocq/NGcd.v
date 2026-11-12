(* The bare-metal program of gcd 1071 462: from the statement gcd_terminates of the instance that
   clightn/check.sh writes from clightgen's Coq file gcd.v, which Lean proves in
   clightn/lean/Gcd.lean, gcd_asm gives the termination of the Asm program with the trace of the
   bytes of the result and the result 0 by NInst.terminates_asm. *)
Require Import Coqlib Errors AST Integers Events Smallstep Behaviors Ctypes Clight ClightBigstep.
Require Import Compiler.
Require SimplExpr SimplLocals Asm.
Require NBase NGcdSpec NExport NInst gcd.

Theorem gcd_asm : NGcdSpec.stmt_gcd_terminates ->
  forall p p1 p2 tp,
  SimplExpr.transl_program p = OK p1 ->
  SimplLocals.transf_program p1 = OK p2 ->
  transf_c_program p = OK tp ->
  prog_defs gcd.prog = NExport.export_defs (prog_defs p2) ->
  prog_main p2 = prog_main gcd.prog ->
  prog_public p2 = prog_public gcd.prog ->
  prog_types p2 = prog_types gcd.prog ->
  program_behaves (Asm.semantics tp) (Terminates NGcdSpec.cst_gcd_trace (NBase.r32 0)).
Proof.
  intros H. exact (NInst.terminates_asm _ _ _ _ H gcd.prog eq_refl eq_refl).
Qed.
