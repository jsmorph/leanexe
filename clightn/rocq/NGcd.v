(* The bare-metal program of gcd 1071 462 from the statement gcd_terminates of the instance that
   clightn/check.sh writes from clightgen's Coq file gcd.v: gcd_clight2 carries the statement,
   which Lean proves in clightn/gcd/Gcd.lean, to CompCert's Clight2.bigstep_program_terminates
   of the program inside clightgen, and gcd_asm to the behavior of the Asm program by
   clight2_bigstep_to_asm (rocq/Clight2Asm.v).  The premises on p2 state that clightgen printed
   that program's definitions with stmt of export/ExportClight.ml, and that the two programs have
   one main, one list of public identifiers, and the same composite types, none. *)
Require Import Coqlib Errors AST Integers Events Smallstep Behaviors Ctypes Clight ClightBigstep.
Require Import Compiler.
Require SimplExpr SimplLocals Asm.
Require NBase NSpec NGcdSpec NExec NExport Clight2Asm gcd.

Lemma gcd_defs : NGcdSpec.cst_gcd_defs = prog_defs gcd.prog.
Proof. reflexivity. Qed.

Lemma gcd_main : NGcdSpec.cst_gcd_main = prog_main gcd.prog.
Proof. reflexivity. Qed.

Theorem gcd_clight2 : NGcdSpec.stmt_gcd_terminates ->
  forall p2,
  prog_defs gcd.prog = NExport.export_defs (prog_defs p2) ->
  prog_main p2 = prog_main gcd.prog ->
  prog_public p2 = prog_public gcd.prog ->
  prog_types p2 = prog_types gcd.prog ->
  Clight2.bigstep_program_terminates p2 NGcdSpec.cst_gcd_trace (NBase.r32 0).
Proof.
  intros H p2 D M P T.
  apply (NExport.export_terminates p2 gcd.prog); auto.
  apply NExec.nprog_sound.
  rewrite <- gcd_defs, <- gcd_main.
  exact H.
Qed.

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
  intros H p p1 p2 tp E1 E2 T D M P C.
  eapply Clight2Asm.clight2_bigstep_to_asm; eauto.
  eapply gcd_clight2; eauto.
Qed.
