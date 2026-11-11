(* What the Rocq theorems of the instances share.  An instance's statement gives N's judgment of
   the definitions defs and the main of clightgen's file, whose program f the instance names.
   NExec.v carries the judgment to CompCert's Clight2 semantics of f, NExport.v to the program p2
   inside clightgen from which clightgen's exporter printed f, and rocq/Clight2Asm.v to the Asm
   program tp that CompCert compiles from p.  The premises on p2 state that clightgen printed its
   definitions with stmt of export/ExportClight.ml, and that p2 and f have one main, one list of
   public identifiers, and the same composite types.  terminates_asm gives the behavior of a
   termination, reads_asm the terminations of a program with input for every sequence sigma of
   the values that its volatile loads read, with no other behavior, and reacts_asm the reactive
   behaviors of a main that runs forever, one for each sigma, to one of which every behavior is
   bisimilar. *)
Require Import Coqlib Errors AST Integers Events Smallstep Behaviors Ctypes Clight ClightBigstep.
Require Import Determinism Compiler.
Require SimplExpr SimplLocals Asm.
Require NBase NSpec NExec NExport Clight2Asm.

Local Transparent Archi.ptr64.

Theorem terminates_asm : forall defs main t r,
  NSpec.nprog defs main t r ->
  forall (f : Clight.program), defs = prog_defs f -> main = prog_main f ->
  forall p p1 p2 tp,
  SimplExpr.transl_program p = OK p1 ->
  SimplLocals.transf_program p1 = OK p2 ->
  transf_c_program p = OK tp ->
  prog_defs f = NExport.export_defs (prog_defs p2) ->
  prog_main p2 = prog_main f ->
  prog_public p2 = prog_public f ->
  prog_types p2 = prog_types f ->
  program_behaves (Asm.semantics tp) (Terminates t r).
Proof.
  intros defs main t r H f DF MF p p1 p2 tp E1 E2 T D M P C. subst defs main.
  eapply Clight2Asm.clight2_bigstep_to_asm; eauto.
  apply (NExport.export_terminates p2 f); auto.
  apply NExec.nprog_sound. exact H.
Qed.

Theorem reads_asm : forall defs main,
  (forall sigma, exists t r, NSpec.nprog defs main t r /\ NSpec.nreads sigma O t) ->
  forall (f : Clight.program), defs = prog_defs f -> main = prog_main f ->
  forall p p1 p2 tp,
  SimplExpr.transl_program p = OK p1 ->
  SimplLocals.transf_program p1 = OK p2 ->
  transf_c_program p = OK tp ->
  prog_defs f = NExport.export_defs (prog_defs p2) ->
  prog_main p2 = prog_main f ->
  prog_public p2 = prog_public f ->
  prog_types p2 = prog_types f ->
  (forall sigma, exists t r,
     program_behaves (Asm.semantics tp) (Terminates t r) /\ Clight2Asm.reads sigma t) /\
  (forall beh, program_behaves (Asm.semantics tp) beh ->
     exists sigma t r, beh = Terminates t r /\ Clight2Asm.reads sigma t).
Proof.
  intros defs main H f DF MF p p1 p2 tp E1 E2 TR D M P C. subst defs main.
  destruct (Clight2Asm.clight2_bigstep_asm_reads_ptr64 eq_refl p p1 p2 tp (fun _ _ _ => True)
              E1 E2 TR) as [A U].
  - intros sigma. destruct (H sigma) as (t & r & NP & NR).
    exists t, r. split; [| split; auto].
    + apply (NExport.export_terminates p2 f); auto.
      apply NExec.nprog_sound. exact NP.
    + apply NExec.nreads_reads. exact NR.
  - split.
    + intros sigma. destruct (A sigma) as (t & r & B & R & _). eauto.
    + intros beh B. destruct (U beh B) as (sigma & t & r & E & R & _). eauto.
Qed.

(* A function with the recursion equations of windows is windows. *)
Lemma prefix_windows : forall (W P : nat -> trace),
  P O = nil -> (forall n, P (S n) = NBase.app (P n) (W n)) ->
  forall n, P n = Clight2Asm.windows W n.
Proof.
  intros W P P0 PS n. induction n as [| n IH]; simpl.
  - exact P0.
  - rewrite PS, IH. reflexivity.
Qed.

Theorem reacts_asm : forall defs main,
  (exists W P : (nat -> int) -> nat -> trace,
     forall sigma, NSpec.nreacts defs main nil (W sigma) /\ P sigma O = nil /\
       (forall n, P sigma (S n) = NBase.app (P sigma n) (W sigma n)) /\
       (forall n, NSpec.nreads sigma O (P sigma n))) ->
  forall (f : Clight.program), defs = prog_defs f -> main = prog_main f ->
  forall p p1 p2 tp,
  SimplExpr.transl_program p = OK p1 ->
  SimplLocals.transf_program p1 = OK p2 ->
  transf_c_program p = OK tp ->
  prog_defs f = NExport.export_defs (prog_defs p2) ->
  prog_main p2 = prog_main f ->
  prog_public p2 = prog_public f ->
  prog_types p2 = prog_types f ->
  exists (W : (nat -> int) -> nat -> trace) (NE : forall sigma n, W sigma n <> E0),
    (forall sigma n, Clight2Asm.reads sigma (Clight2Asm.windows (W sigma) n)) /\
    (forall sigma, program_behaves (Asm.semantics tp)
                     (Reacts (Clight2Asm.concat (W sigma) (NE sigma)))) /\
    (forall beh, program_behaves (Asm.semantics tp) beh ->
       exists sigma, same_behaviors beh (Reacts (Clight2Asm.concat (W sigma) (NE sigma)))).
Proof.
  intros defs main [W [P H]] f DF MF p p1 p2 tp E1 E2 TR D M Pu C. subst defs main.
  assert (LR : forall sigma, Clight2Asm.loop_reacts p2 E0 (W sigma)).
  { intros sigma. destruct (H sigma) as (R & _ & _ & _).
    apply (NExport.export_reacts p2 f); auto.
    apply NExec.nreacts_sound. exact R. }
  assert (R : forall sigma n, Clight2Asm.reads sigma (E0 ** Clight2Asm.windows (W sigma) n)).
  { intros sigma n. destruct (H sigma) as (_ & P0 & PS & NR).
    change (E0 ** Clight2Asm.windows (W sigma) n) with (Clight2Asm.windows (W sigma) n).
    rewrite <- (prefix_windows (W sigma) (P sigma) P0 PS n).
    apply NExec.nreads_reads. exact (NR n). }
  pose (NE := fun sigma => proj1 (LR sigma)).
  destruct (Clight2Asm.clight2_loop_to_asm_ptr64 eq_refl p p1 p2 tp E0 W NE E1 E2 TR LR R)
    as [A U].
  exists W, NE. split; [| split].
  - intros sigma n. exact (R sigma n).
  - intros sigma. exact (A sigma).
  - intros beh B. exact (U beh B).
Qed.
