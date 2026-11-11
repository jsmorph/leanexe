(* The bare-metal program of the Euler solver on a grid of 16 cells, solve 4: from the statement
   euler_terminates of the instance that clightn/check.sh writes from clightgen's Coq file
   euler.v, which Lean proves in clightn/lean/Euler.lean, euler_asm gives by NInst.terminates_asm
   a termination of the Asm program with the trace of the bytes of the solver's packed result and
   the result 0, or with no event and the code of unreachable.  The theorem assumes the
   floating-point equations of N. *)
Require Import Coqlib Errors AST Integers Events Smallstep Behaviors Ctypes Clight ClightBigstep.
Require Import Compiler.
Require SimplExpr SimplLocals Asm.
Require NBase NEulerSpec NExport NInst euler.

Theorem euler_asm : NEulerSpec.stmt_euler_terminates ->
  forall p p1 p2 tp,
  SimplExpr.transl_program p = OK p1 ->
  SimplLocals.transf_program p1 = OK p2 ->
  transf_c_program p = OK tp ->
  prog_defs euler.prog = NExport.export_defs (prog_defs p2) ->
  prog_main p2 = prog_main euler.prog ->
  prog_public p2 = prog_public euler.prog ->
  prog_types p2 = prog_types euler.prog ->
  program_behaves (Asm.semantics tp) (Terminates NEulerSpec.cst_euler_trace (NBase.r32 0)) \/
  program_behaves (Asm.semantics tp) (Terminates E0 (NBase.r32 1)).
Proof.
  intros [H | H] p p1 p2 tp E1 E2 T D M P C; [left | right];
    exact (NInst.terminates_asm _ _ _ _ H euler.prog eq_refl eq_refl p p1 p2 tp E1 E2 T D M P C).
Qed.
