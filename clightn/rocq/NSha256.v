(* The bare-metal program of shaCheck 0x636261, the SHA-256 digest of abc: from the statement
   sha256_terminates of the instance that clightn/check.sh writes from clightgen's Coq file
   sha256.v, which Lean proves in clightn/lean/Sha256.lean, sha256_asm gives by
   NInst.terminates_asm a termination of the Asm program with the trace of the bytes of the array
   of the digest's words and the result 0, or with no event and the code of unreachable. *)
Require Import Coqlib Errors AST Integers Events Smallstep Behaviors Ctypes Clight ClightBigstep.
Require Import Compiler.
Require SimplExpr SimplLocals Asm.
Require NBase NSha256Spec NExport NInst sha256.

Theorem sha256_asm : NSha256Spec.stmt_sha256_terminates ->
  forall p p1 p2 tp,
  SimplExpr.transl_program p = OK p1 ->
  SimplLocals.transf_program p1 = OK p2 ->
  transf_c_program p = OK tp ->
  prog_defs sha256.prog = NExport.export_defs (prog_defs p2) ->
  prog_main p2 = prog_main sha256.prog ->
  prog_public p2 = prog_public sha256.prog ->
  prog_types p2 = prog_types sha256.prog ->
  program_behaves (Asm.semantics tp) (Terminates NSha256Spec.cst_sha256_trace (NBase.r32 0)) \/
  program_behaves (Asm.semantics tp) (Terminates E0 (NBase.r32 1)).
Proof.
  intros [H | H] p p1 p2 tp E1 E2 T D M P C; [left | right];
    exact (NInst.terminates_asm _ _ _ _ H sha256.prog eq_refl eq_refl p p1 p2 tp E1 E2 T D M P C).
Qed.
