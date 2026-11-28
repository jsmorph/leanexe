module

public import Demos.RandomHistogram.Proof
public import LeanExe.Pipeline.BytesSize
public import Verified.Call
public import Verified.ChargeFacts
public import Verified.Reflect.Command

@[expose] public section

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

/-- One line of `render` charges a push of 80 bytes for each of at most 20 digits and for its
newline: at most 1,680 bytes. -/
theorem appendLine_cost_le (text : Array UInt64) (c : UInt64) :
    compiled.appendLine.cost (⟨text⟩, c) ≤ 1680 := by
  have hd : (digitCount c).toNat ≤ 20 := by
    rw [digitCount_toNat]
    exact digitWords_length_le _ c.toNat_lt
  have h80 : Verified.paidGrowCost 1 = 80 := by rw [Verified.paidGrowCost_eq]
  rw [compiled.appendLine.cost_eq]
  refine le_trans (Nat.add_le_add_right
    (Verified.loopCost_const_le 80 (fun _ _ => h80.le) _ _ _) _) ?_
  rw [h80]
  omega

/-- `render` charges the empty array's block of 56 bytes and its credit of 16, ten lines of at most
1,680 bytes, and the output buffer of at most 210 bytes, 264 bytes: at most 17,136 bytes. -/
theorem render_bound (counts : Array UInt64) : compiled.render.bound counts ≤ 17136 := by
  have hsize := render_text_size counts
  have htext : Verified.Bytes.allocationCost
      (LeanExe.loop 10 (#[] : Array UInt64)
        fun m t => appendLine t counts[m.toNat]!).size.toUInt64.toNat ≤ 264 := by
    rw [LeanExe.Dialect.size_toUInt64 _ (by omega)]
    exact (Verified.allocationCost_mono hsize).trans (by decide)
  rw [compiled.render.bound_eq, Verified.blockCost_eq]
  refine le_trans (Nat.add_le_add (Nat.add_le_add_left
    (Verified.loopCost_const_le 1680 (fun _ s => appendLine_cost_le s _) _ _ _) _) htext) ?_
  simp only [Verified.creditCost, Array.size_empty, UInt64.reduceToNat]
  omega

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
#print axioms histogram_bound
#print axioms render_bound

end Demos.RandomHistogram
