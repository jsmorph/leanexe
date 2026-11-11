(* The program with input around the export sha256 of the hashing library, from the statement
   sha_reads of the instance that clightn/check.sh writes from clightgen's Coq file sha.v: for
   every sequence sigma of the values that its volatile loads read, N's program judgment holds
   with a trace that reads sigma, which Lean proves in clightn/sha/Sha.lean.  sha_clight2
   carries the statement to CompCert's Clight2.bigstep_program_terminates of the program inside
   clightgen, with reads of Clight2Asm.v, and sha_asm to the Asm program by
   clight2_bigstep_asm_reads_ptr64 (rocq/Clight2Asm.v): for every sigma the Asm program
   terminates with a trace that reads sigma, and every behavior of the Asm program is such a
   termination.  The conclusion leaves out the trivial predicate on the result that
   clight2_bigstep_asm_reads_ptr64 takes.  The premises on p2 state that clightgen printed that
   program's definitions with stmt of export/ExportClight.ml, and that the two programs have one
   main, one list of public identifiers, and the same composite types, none. *)
Require Import Coqlib Errors AST Integers Events Smallstep Behaviors Ctypes Clight ClightBigstep.
Require Import Compiler.
Require SimplExpr SimplLocals Asm.
Require NBase NSpec NShaSpec NExec NExport Clight2Asm sha.

Local Transparent Archi.ptr64.

Lemma sha_defs : NShaSpec.cst_sha_defs = prog_defs sha.prog.
Proof. reflexivity. Qed.

Lemma sha_main : NShaSpec.cst_sha_main = prog_main sha.prog.
Proof. reflexivity. Qed.

Theorem sha_clight2 : NShaSpec.stmt_sha_reads ->
  forall p2,
  prog_defs sha.prog = NExport.export_defs (prog_defs p2) ->
  prog_main p2 = prog_main sha.prog ->
  prog_public p2 = prog_public sha.prog ->
  prog_types p2 = prog_types sha.prog ->
  forall sigma, exists t r,
    Clight2.bigstep_program_terminates p2 t r /\ Clight2Asm.reads sigma t.
Proof.
  intros H p2 D M P T sigma. destruct (H sigma) as (t & r & NP & NR).
  exists t, r. split.
  - apply (NExport.export_terminates p2 sha.prog); auto.
    apply NExec.nprog_sound. rewrite <- sha_defs, <- sha_main. exact NP.
  - apply NExec.nreads_reads. exact NR.
Qed.

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
  intros H p p1 p2 tp E1 E2 TR D M P C.
  destruct (Clight2Asm.clight2_bigstep_asm_reads_ptr64 eq_refl p p1 p2 tp (fun _ _ _ => True)
              E1 E2 TR) as [A U].
  - intros sigma. destruct (sha_clight2 H p2 D M P C sigma) as (t & r & B & R).
    exists t, r. auto.
  - split.
    + intros sigma. destruct (A sigma) as (t & r & B & R & _). eauto.
    + intros beh B. destruct (U beh B) as (sigma & t & r & E & R & _). eauto.
Qed.
