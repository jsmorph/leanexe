import Library.Numerics.Decimal.Int64Text.Proof
import Verified.Reflect.Command
import Verified.Call

/-! The verified compiler's module of the `Int64` printer and reader.  The compiler translates the
loops of `digitCount`, `digitByte`, and `scanDigits` into loops, so no theorem of the module has a
call-depth premise.  `printInt64`, function 4, allocates the block of its text, and its generated
`compiled.printInt64.trapFree` requires room for that block, which `printInt64_bound` states.
`readInt64`, function 7, allocates nothing, and `compiled.readInt64.trapFree` requires nothing of
the store beyond readiness.  `printInt64_callSpec` and `readInt64_callSpec` compose them with
`printInt64_eq` and `readInt64_eq`. -/

namespace Library.Numerics.Decimal.Int64Text

open Wasm LeanExe.Pipeline

verified_compile compiled := [digitCount, digitByte, printInt64, isDigitW, scanDigits, readInt64]

theorem printInt64_export :
    ({ name := "printInt64", funcIdx := 4 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem readInt64_export :
    ({ name := "readInt64", funcIdx := 7 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- The generated bound of `printInt64` is one block of the text's words. -/
theorem printInt64_bound (x : Int64) :
    compiled.printInt64.bound x = Verified.blockCost (expectedPrint x).size := by
  rw [compiled.printInt64.bound_eq, ← printInt64_eq]
  simp only [printInt64, LeanExe.Dialect.build_size]

/-- A call of `printInt64` raises `top` by at most 216 bytes, a block of 20 words. -/
theorem printInt64_bound_le (x : Int64) : compiled.printInt64.bound x ≤ 216 := by
  rw [printInt64_bound, Verified.blockCost_eq]
  have := expectedPrint_size x
  omega

/-- `readInt64` allocates nothing. -/
theorem readInt64_bound (s : Array UInt64) : compiled.readInt64.bound s = 0 :=
  compiled.readInt64.bound_eq s

/-- `Verified.CallSpec` for function 4 and `expectedPrint`: from a ready store in which `top` can
rise by `compiled.printInt64.bound x` bytes, the call with the word of `x` returns without a trap
an owned array that holds the words of the bytes of `toString x`, leaves a ready store, and raises
`top` by at most that bound. -/
theorem printInt64_callSpec :
    Verified.CallSpec compiled.module compiled.tables 4 expectedPrint compiled.printInt64.bound :=
  (Verified.ImplementsTables.call (.ofA compiled.printInt64.trapFree) compiled.tables nofun).spec
    (fun _ _ _ h => h) (fun _ _ _ _ _ h => h) fun _ _ _ x _ => printInt64_eq x

/-- `Verified.CallSpec` for function 7 and `expectedRead`: from a ready store, the call with the
borrowed array `s` returns without a trap the flag and the word of `expectedRead s`, leaves a
ready store, and raises `top` by at most `compiled.readInt64.bound s`, which is 0. -/
theorem readInt64_callSpec :
    Verified.CallSpec compiled.module compiled.tables 7 expectedRead compiled.readInt64.bound :=
  (Verified.ImplementsTables.call (.ofA compiled.readInt64.trapFree) compiled.tables nofun).spec
    (fun _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ s ⟨_, _, hs⟩ => readInt64_eq s hs.values.size_lt

#print axioms printInt64_bound_le
#print axioms readInt64_bound
#print axioms printInt64_callSpec
#print axioms readInt64_callSpec
#print axioms readInt64_printInt64
#print axioms printInt64_of_read
#print axioms readInt64_reject
#print axioms expectedRead_eq_true_iff

end Library.Numerics.Decimal.Int64Text
