import Demos.RandomHistogram.Proof
import LeanExe.Pipeline.BytesSize
import Verified.Call
import Verified.Reflect.Command

/-! The verified compiler's module of the pure core.  The call theorems compose the generated
`trapFree` theorems with the programs' equations: from a ready store with room for the generated
bound, export `parseN`, function 3, returns `parseSpec` of a borrowed buffer, export `histogram`,
function 5, returns `histogramSpec` of a borrowed array, and export `render`, function 9, returns
`renderSpec` of a borrowed array, each without a trap.  A buffer that a store holds has fewer than
`2^32` bytes, which `parseN_eq` needs. -/

namespace Demos.RandomHistogram

open LeanExe.Pipeline Library.Numerics.Decimal.Int64Text

verified_compile compiled :=
  [parseStep, parseN, countWord, histogram, digitCount, digitByte, appendLine, render]

theorem exports :
    ({ name := "parseN", funcIdx := 3 } : Wasm.Export) ∈ compiled.module.exports ∧
    ({ name := "histogram", funcIdx := 5 } : Wasm.Export) ∈ compiled.module.exports ∧
    ({ name := "render", funcIdx := 9 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- `parseN` cannot abort and allocates nothing. -/
theorem parseN_bound (args : LeanExe.Bytes) : compiled.parseN.bound args = 0 :=
  compiled.parseN.bound_eq args

/-- `histogram` allocates one block of ten words, 136 bytes. -/
theorem histogram_bound (ws : Array UInt64) : compiled.histogram.bound ws = 136 := by
  rw [compiled.histogram.bound_eq, Verified.blockCost_eq]
  rfl

/-- Function 3, called with a borrowed buffer, returns `parseSpec` of it without a trap. -/
theorem parseN_callSpec :
    Verified.CallSpec compiled.module compiled.tables 3 parseSpec compiled.parseN.bound :=
  (Verified.ImplementsTables.call (.ofA compiled.parseN.trapFree) compiled.tables nofun).spec
    (fun _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ b hb => parseN_eq b (by have := Bytes.size_lt_of_borrowed hb; omega)

/-- Function 5, called with a borrowed array of words, returns `histogramSpec` of it without a
trap. -/
theorem histogram_callSpec :
    Verified.CallSpec compiled.module compiled.tables 5 histogramSpec compiled.histogram.bound :=
  (Verified.ImplementsTables.call (.ofA compiled.histogram.trapFree) compiled.tables nofun).spec
    (fun _ _ _ h => h) (fun _ _ _ _ _ h => h) fun _ _ _ ws _ => histogram_eq ws

/-- Function 9, called with a borrowed array of counts, returns `renderSpec` of it without a trap. -/
theorem render_callSpec :
    Verified.CallSpec compiled.module compiled.tables 9 renderSpec compiled.render.bound :=
  (Verified.ImplementsTables.call (.ofA compiled.render.trapFree) compiled.tables nofun).spec
    (fun _ _ _ h => h) (fun _ _ _ _ _ h => h) fun _ _ _ counts _ => render_eq counts

#print axioms parseN_callSpec
#print axioms histogram_callSpec
#print axioms render_callSpec

end Demos.RandomHistogram
