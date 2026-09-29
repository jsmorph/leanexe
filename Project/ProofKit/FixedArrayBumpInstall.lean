import Project.ProofKit.FixedArrayBumpPrefix

namespace Project.ProofKit.FixedArrayBump
open Wasm FixedArrayFold

def installProgram (resultLocal topLocal : Nat) : Wasm.Program :=
  [.globalGet 0, .constI64 48, .addI64, .localSet resultLocal,
    .localGet topLocal, .globalSet 0]

theorem installProgram_spec (resultLocal topLocal : Nat)
    (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (base top : UInt64) (hValues : frame.values = [])
    (hTop : frame.get topLocal = some (.i64 top))
    (hResultLower : frame.params.length ≤ resultLocal) (hResultValid : frame.validIndex resultLocal)
    (hTopLower : frame.params.length ≤ topLocal) (hTopValid : frame.validIndex topLocal)
    (hDistinct : topLocal ≠ resultLocal)
    (hGlobal : store.globals.globals[0]? = some (.i64 base))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q
      { store with globals := { globals := store.globals.globals.set 0 (.i64 top) } }
      (resultFrame frame resultLocal (base + 48)) env) :
    wp module_ (installProgram resultLocal topLocal ++ rest) Q store frame env := by
  have hResultNotParam : ¬resultLocal < frame.params.length := by omega
  have hResultBound : resultLocal < frame.params.length + frame.locals.length := hResultValid
  have hTopRead := resultFrame_get_of_ne frame resultLocal topLocal (base + 48) (.i64 top)
    hResultLower hTopLower hTopValid hDistinct hTop
  have hTail : wp module_ (.localGet topLocal :: .globalSet 0 :: rest) Q store
      (resultFrame frame resultLocal (base + 48)) env := by
    simp only [wp_localGet_cons, hTopRead, wp_globalSet_cons, hGlobal, resultFrame_values]
    simpa only [resultFrame] using hNext
  simpa only [installProgram, List.cons_append, List.nil_append, wp_globalGet_cons,
    hGlobal, wp_constI64_cons, wp_addI64_cons, wp_localSet_cons, hValues,
    Locals.set?, hResultNotParam, hResultBound, ite_false, ite_true, resultFrame]
    using hTail

#print axioms installProgram_spec

end Project.ProofKit.FixedArrayBump
