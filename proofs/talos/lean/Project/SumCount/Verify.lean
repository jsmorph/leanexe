import Project.SumCount.Execution
import Project.Encoding.RoundTrip

namespace Project.SumCount

open Project.Pipeline LeanExe.Examples.SumCount

/-- One array object for every input: a 48-byte header and a 24-byte payload
holding the length and two words. -/
def sumNeed (_ : Array UInt64) : Nat := 72

theorem sumModule_implements : Implements sumModule 0 sumCount sumNeed :=
  Execution.implements

/-- The bytes `encode` produces for `sumModule` decode to a module that computes
`sumCount` bit for bit. -/
theorem sumModule_bytes (bytes : ByteArray)
    (success : Wasm.Encoding.encode sumModule = .ok bytes) :
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧ Implements m 0 sumCount sumNeed :=
  ⟨sumModule, Wasm.Encoding.decode_encode sumModule bytes (by decide) success,
    sumModule_implements⟩

/-- The sum of the input words read as two's-complement signed integers. -/
def signedSum (xs : Array UInt64) : Int :=
  (xs.toList.map (·.toBitVec.toInt)).sum

theorem foldl_add_toInt (words : List UInt64) (start : UInt64) :
    (words.foldl (· + ·) start).toBitVec.toInt =
      (start.toBitVec.toInt + (words.map (·.toBitVec.toInt)).sum).bmod (2 ^ 64) := by
  induction words generalizing start with
  | nil =>
      rw [List.foldl_nil, List.map_nil, List.sum_nil, Int.add_zero]
      exact (BitVec.toInt_bmod_cancel _).symm
  | cons word rest ih =>
      rw [List.foldl_cons, ih, UInt64.toBitVec_add, BitVec.toInt_add, Int.bmod_add_bmod,
        List.map_cons, List.sum_cons, Int.add_assoc]

theorem sumCount_meaning (xs : Array UInt64) (hSize : xs.size < 2 ^ 63)
    (hFits : -2 ^ 63 ≤ signedSum xs ∧ signedSum xs < 2 ^ 63) :
    (sumCount xs)[0]!.toBitVec.toInt = signedSum xs ∧
      (sumCount xs)[1]!.toNat = xs.size := by
  have hSum : (xs.foldl (· + ·) 0).toBitVec.toInt = signedSum xs := by
    rw [← Array.foldl_toList, foldl_add_toInt]
    simp only [UInt64.toBitVec_zero, BitVec.toInt_zero, Int.zero_add]
    simp only [signedSum] at hFits
    exact Int.bmod_eq_of_le (by norm_num at hFits ⊢; omega) (by norm_num at hFits ⊢; omega)
  constructor
  · simpa [sumCount] using hSum
  · simp only [sumCount, Nat.toUInt64_eq]
    simp
    omega

theorem sumModule_meaning :
    Satisfies sumModule 0 sumNeed
      (fun xs => xs.size < 2 ^ 63 ∧ -2 ^ 63 ≤ signedSum xs ∧ signedSum xs < 2 ^ 63)
      (fun xs ys => ys[0]!.toBitVec.toInt = signedSum xs ∧ ys[1]!.toNat = xs.size) :=
  sumModule_implements.transfer fun xs ⟨hSize, hLow, hHigh⟩ =>
    sumCount_meaning xs hSize ⟨hLow, hHigh⟩

end Project.SumCount
