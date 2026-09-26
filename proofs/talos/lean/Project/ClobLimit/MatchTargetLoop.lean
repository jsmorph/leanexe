import Project.ClobLimit.MatchLoop
import Project.LocalRegion.Transport

namespace Project.ClobLimit.MatchTargetLoop
open Wasm Project.ClobLimit.MatchInvariant

theorem loop_spec (env : HostEnv Unit) (ctx : Context) (st : Store Unit)
    (source target : Locals) (hRelated : MatchLocals.mapping.Related source target)
    (hInvariant : Invariant ctx st source)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ st1 source1 target1, ExitAt ctx st1 source1 →
      MatchLocals.mapping.Related source1 target1 →
      wp «module» rest Q st1 target1 env) :
    wp «module» (MatchProgram.loop ++ rest) Q st target env := by
  have hSource : wp Project.ClobMatchFuel.«module» MatchProgram.sourceLoop
      (ProofKit.Sequence.Fallthrough (ExitAt ctx)) st source env := by
    simpa only [List.append_nil] using MatchLoop.sourceLoop_spec env ctx st source
      hInvariant (ProofKit.Sequence.Fallthrough (ExitAt ctx)) [] (by
        intro st1 source1 hExit
        simpa [wp_simp, ProofKit.Sequence.Fallthrough] using hExit)
  exact LocalRegion.wp_fallthrough MatchLocals.mapping.frameMap
    SearchRegion.searchShift hRelated MatchProgram.sourceLoop_portable
    MatchProgram.sourceLoop_allowed hSource hDone

#print axioms loop_spec
end Project.ClobLimit.MatchTargetLoop
