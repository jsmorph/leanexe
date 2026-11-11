(* The bare-metal program of recursive 1000 of Verified/Examples/Fold.lean, a recursion of depth
   1,000: from the statement depth_terminates of the instance that clightn/check.sh writes from
   clightgen's Coq file depth.v, which Lean proves in clightn/lean/Depth.lean, depth_asm gives by
   NInst.terminates_asm a termination of the Asm program with the trace of the bytes of the result
   and the result 0, or with no event and the code of unreachable.  The program holds the
   module's functions on double, which main does not call. *)
Require Import Coqlib Errors AST Integers Events Smallstep Behaviors Ctypes Clight ClightBigstep.
Require Import Compiler.
Require SimplExpr SimplLocals Asm.
Require NBase NDepthSpec NExport NInst depth.

Theorem depth_asm : NDepthSpec.stmt_depth_terminates ->
  forall p p1 p2 tp,
  SimplExpr.transl_program p = OK p1 ->
  SimplLocals.transf_program p1 = OK p2 ->
  transf_c_program p = OK tp ->
  prog_defs depth.prog = NExport.export_defs (prog_defs p2) ->
  prog_main p2 = prog_main depth.prog ->
  prog_public p2 = prog_public depth.prog ->
  prog_types p2 = prog_types depth.prog ->
  program_behaves (Asm.semantics tp) (Terminates NDepthSpec.cst_depth_trace (NBase.r32 0)) \/
  program_behaves (Asm.semantics tp) (Terminates E0 (NBase.r32 1)).
Proof.
  intros [H | H] p p1 p2 tp E1 E2 T D M P C; [left | right];
    exact (NInst.terminates_asm _ _ _ _ H depth.prog eq_refl eq_refl p p1 p2 tp E1 E2 T D M P C).
Qed.
