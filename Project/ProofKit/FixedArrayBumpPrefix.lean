import Project.ProofKit.Allocation
import Project.ProofKit.FixedArrayFold
import Project.ProofKit.Frame

namespace Project.ProofKit.FixedArrayBump
open Wasm FixedArrayFold

def prefixProgram (needLocal topLocal pagesLocal : Nat) : Wasm.Program :=
  [.globalGet 0, .constI64 48, .addI64, .localGet needLocal, .addI64,
    .localTee topLocal, .globalGet 0, .ltUI64, .iff 0 0 [.unreachable] [],
    .localGet topLocal, .constI64 1, .subI64, .constI64 65536, .divUI64,
    .constI64 1, .addI64, .localSet pagesLocal]

def prefixFrame (frame : Locals) (topLocal pagesLocal : Nat) (base need : UInt64) : Locals :=
  resultFrame (resultFrame frame topLocal (base + 48 + need)) pagesLocal
    ((base + 48 + need - 1) / 65536 + 1)

theorem prefixProgram_spec (needLocal topLocal pagesLocal : Nat)
    (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (base need : UInt64) (hValues : frame.values = [])
    (hNeed : frame.get needLocal = some (.i64 need))
    (hTopLower : frame.params.length ≤ topLocal) (hTopValid : frame.validIndex topLocal)
    (hPagesLower : frame.params.length ≤ pagesLocal) (hPagesValid : frame.validIndex pagesLocal)
    (hGlobal : store.globals.globals[0]? = some (.i64 base))
    (hFit32 : base.toNat + 48 + need.toNat ≤ 4294967296)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q store (prefixFrame frame topLocal pagesLocal base need) env) :
    wp module_ (prefixProgram needLocal topLocal pagesLocal ++ rest) Q store frame env := by
  have hTopNotParam : ¬topLocal < frame.params.length := by omega
  have hTopBound : topLocal < frame.params.length + frame.locals.length := hTopValid
  have hTopIndex : topLocal - frame.params.length < frame.locals.length := by omega
  have hPagesNotParam : ¬pagesLocal < frame.params.length := by omega
  have hPagesBound : pagesLocal < frame.params.length + frame.locals.length := hPagesValid
  have hNoOverflow := Allocation.top_not_lt_base base need hFit32
  unfold prefixProgram
  simp only [List.cons_append, List.nil_append, wp_globalGet_cons, wp_constI64_cons,
    wp_addI64_cons, wp_localGet_cons, Frame.withValues_get, hNeed, hGlobal,
    hValues, wp_localTee_cons, Locals.set?, hTopNotParam, hTopBound, ite_false, ite_true,
    wp_ltUI64_cons]
  refine wp_iff_cons rfl ?_
  simp only [hNoOverflow, ite_false]
  conv => arg 2; simp
  simpa [wp_simp, prefixFrame, resultFrame, Locals.get, Locals.set?,
    hTopNotParam, hTopBound, hTopIndex, hPagesNotParam, hPagesBound]
    using hNext

#print axioms prefixProgram_spec

end Project.ProofKit.FixedArrayBump
