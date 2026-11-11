(* The controller program around the step ctlStep of tests/TestSupport/Bare/Ctl.lean, from the
   statement ctl_reacts of the instance that clightn/check.sh writes from clightgen's Coq file
   ctl.v: there are functions W and P of the sequence sigma of the values that the volatile loads
   read such that, for every sigma, N's judgment nreacts holds of the file's program with no event
   before the loop and the trace W sigma n in iteration n, P sigma n is the trace of the first n
   iterations, and P sigma n reads sigma, which Lean proves in clightn/ctl/Ctl.lean.  ctl_clight2
   carries the statement to loop_reacts of rocq/Clight2Asm.v for the program inside clightgen,
   with the reads of every prefix of the windows, and ctl_asm to the Asm program by
   clight2_loop_to_asm_ptr64: for every sigma the Asm program reacts with the infinite trace of
   the windows W sigma, which read sigma, and every behavior of the Asm program is bisimilar to
   one of these.  The premises on p2 state that clightgen printed that program's definitions with
   stmt of export/ExportClight.ml, and that the two programs have one main, one list of public
   identifiers, and the same composite types, none. *)
Require Import Coqlib Errors AST Integers Events Smallstep Behaviors Ctypes Clight ClightBigstep.
Require Import Determinism Compiler.
Require SimplExpr SimplLocals Asm.
Require NBase NSpec NCtlSpec NExec NExport Clight2Asm ctl.

Local Transparent Archi.ptr64.

Lemma ctl_defs : NCtlSpec.cst_ctl_defs = prog_defs ctl.prog.
Proof. reflexivity. Qed.

Lemma ctl_main : NCtlSpec.cst_ctl_main = prog_main ctl.prog.
Proof. reflexivity. Qed.

(* A function with the recursion equations of windows is windows. *)
Lemma prefix_windows : forall (W P : nat -> trace),
  P O = nil -> (forall n, P (S n) = NBase.app (P n) (W n)) ->
  forall n, P n = Clight2Asm.windows W n.
Proof.
  intros W P P0 PS n. induction n as [| n IH]; simpl.
  - exact P0.
  - rewrite PS, IH. reflexivity.
Qed.

Theorem ctl_clight2 : NCtlSpec.stmt_ctl_reacts ->
  forall p2,
  prog_defs ctl.prog = NExport.export_defs (prog_defs p2) ->
  prog_main p2 = prog_main ctl.prog ->
  prog_public p2 = prog_public ctl.prog ->
  prog_types p2 = prog_types ctl.prog ->
  exists W : (nat -> int) -> nat -> trace,
    (forall sigma, Clight2Asm.loop_reacts p2 E0 (W sigma)) /\
    (forall sigma n, Clight2Asm.reads sigma (E0 ** Clight2Asm.windows (W sigma) n)).
Proof.
  intros [W [P H]] p2 D M Pu T. exists W. split.
  - intros sigma. destruct (H sigma) as (R & _ & _ & _).
    apply (NExport.export_reacts p2 ctl.prog); auto.
    apply NExec.nreacts_sound. rewrite <- ctl_defs, <- ctl_main. exact R.
  - intros sigma n. destruct (H sigma) as (_ & P0 & PS & NR).
    change (E0 ** Clight2Asm.windows (W sigma) n) with (Clight2Asm.windows (W sigma) n).
    rewrite <- (prefix_windows (W sigma) (P sigma) P0 PS n).
    apply NExec.nreads_reads. exact (NR n).
Qed.

Theorem ctl_asm : NCtlSpec.stmt_ctl_reacts ->
  forall p p1 p2 tp,
  SimplExpr.transl_program p = OK p1 ->
  SimplLocals.transf_program p1 = OK p2 ->
  transf_c_program p = OK tp ->
  prog_defs ctl.prog = NExport.export_defs (prog_defs p2) ->
  prog_main p2 = prog_main ctl.prog ->
  prog_public p2 = prog_public ctl.prog ->
  prog_types p2 = prog_types ctl.prog ->
  exists (W : (nat -> int) -> nat -> trace) (NE : forall sigma n, W sigma n <> E0),
    (forall sigma n, Clight2Asm.reads sigma (Clight2Asm.windows (W sigma) n)) /\
    (forall sigma, program_behaves (Asm.semantics tp)
                     (Reacts (Clight2Asm.concat (W sigma) (NE sigma)))) /\
    (forall beh, program_behaves (Asm.semantics tp) beh ->
       exists sigma, same_behaviors beh (Reacts (Clight2Asm.concat (W sigma) (NE sigma)))).
Proof.
  intros H p p1 p2 tp E1 E2 TR D M P C.
  destruct (ctl_clight2 H p2 D M P C) as (W & LR & R).
  pose (NE := fun sigma => proj1 (LR sigma)).
  destruct (Clight2Asm.clight2_loop_to_asm_ptr64 eq_refl p p1 p2 tp E0 W NE E1 E2 TR LR R)
    as [A U].
  exists W, NE. split; [| split].
  - intros sigma n. exact (R sigma n).
  - intros sigma. exact (A sigma).
  - intros beh B. exact (U beh B).
Qed.
