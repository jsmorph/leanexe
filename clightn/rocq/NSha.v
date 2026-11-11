(* The program with input around the export sha256 of the hashing library: from the statement
   sha_reads of the instance that clightn/check.sh writes from clightgen's Coq file sha.v, which
   Lean proves in clightn/lean/Sha.lean, sha_asm gives by NInst.reads_asm that for every sequence
   sigma of the values that its volatile loads read the Asm program terminates with a trace that
   reads sigma, and that every behavior of the Asm program is such a termination. *)
Require Import Coqlib Errors AST Integers Events Smallstep Behaviors Ctypes Clight ClightBigstep.
Require Import Compiler.
Require SimplExpr SimplLocals Asm.
Require NShaSpec NExport Clight2Asm NInst sha.

Theorem sha_asm : NShaSpec.stmt_sha_reads ->
  forall p p1 p2 tp,
  SimplExpr.transl_program p = OK p1 ->
  SimplLocals.transf_program p1 = OK p2 ->
  transf_c_program p = OK tp ->
  prog_defs sha.prog = NExport.export_defs (prog_defs p2) ->
  prog_main p2 = prog_main sha.prog ->
  prog_public p2 = prog_public sha.prog ->
  prog_types p2 = prog_types sha.prog ->
  (forall sigma, exists t r,
     program_behaves (Asm.semantics tp) (Terminates t r) /\ Clight2Asm.reads sigma t) /\
  (forall beh, program_behaves (Asm.semantics tp) beh ->
     exists sigma t r, beh = Terminates t r /\ Clight2Asm.reads sigma t).
Proof.
  intros H. exact (NInst.reads_asm _ _ H sha.prog eq_refl eq_refl).
Qed.
