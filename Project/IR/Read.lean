import Project.IR.Run
import Project.ProofKit.Array
import Project.ProofKit.F64Convert

/-!
The rule lemma for array reads.  The compiler translates `xs[i.toNat]!`, for an
array variable `xs`, to `Expr.read`, which compares the position with the length
word and loads the element or yields 0.  For an `Array Float`, stored as the bit
patterns of its elements, the read is wrapped in `Expr.ofBits`.
-/

namespace Project.IR

open Wasm Project.ProofKit

theorem element_offset {k : UInt64} {size : Nat} (hk : k.toNat < size)
    (hSize : 8 * (size + 1) ≤ 4294967296) :
    (k + 1) * 8 = UInt64.ofNat (8 * (k.toNat + 1)) := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_mul, UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.reduceToNat]
  omega

/-- The memory part of a read of position `k` in an array laid out at `ptr` gives
`xs[k.toNat]!`: the element when `k` is below the length, and 0 otherwise.
Unfolding `Expr.eval` leaves `Expr.readValue`, so `simp` uses this lemma. -/
theorem Expr.readValue_at {store : Store Unit} {ptr : UInt64} {xs : Array UInt64}
    (hArray : UInt64Array.At store ptr xs) {array : Nat} {k : UInt64} {state : State}
    (hPtr : state.get array = some (.i64 ptr)) :
    Expr.readValue store.mem array k state = some (xs[k.toNat]!, state) := by
  have hFit := hArray.1
  have hSize := hArray.size_lt
  simp only [Expr.readValue, hPtr, Option.bind_eq_bind, Option.bind_some,
    hArray.lengthBound, ite_true, hArray.lengthRead]
  have hLess : k < UInt64.ofNat xs.size ↔ k.toNat < xs.size := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' hSize]
  by_cases hk : k.toNat < xs.size
  · have hOffset := element_offset hk (by omega)
    rw [if_pos (hLess.mpr hk), hOffset, if_pos (hArray.elementBound _ hk),
      hArray.elementRead _ hk, getElem!_pos xs k.toNat hk]
    rfl
  · rw [if_neg (fun h => hk (hLess.mp h)), getElem!_neg xs k.toNat hk]
    rfl

/-- A read of position `k` in an array laid out at `ptr` gives `xs[k.toNat]!`. -/
theorem Expr.read_spec {store : Store Unit} {ptr k : UInt64} {xs : Array UInt64}
    {array scratch : Nat} {position : Expr .u64} {state afterPosition saved : State}
    (hArray : UInt64Array.At store ptr xs)
    (hPosition : position.eval store.mem (scratch + 1) state = some (k, afterPosition))
    (hSet : afterPosition.set? scratch (.i64 k) = some saved)
    (hPtr : saved.get array = some (.i64 ptr)) :
    (Expr.read array position).eval store.mem scratch state = some (xs[k.toNat]!, saved) := by
  simp only [Expr.eval, hPosition, hSet, Option.bind_eq_bind, Option.bind_some]
  exact Expr.readValue_at hArray hPtr

/-- A read of an `Array Float` stored as bit patterns yields the bit pattern of
Lean's read.  Past the end, Lean's default float is `UInt64.toFloat 0`, whose bit
pattern is 0, the value the compiled read yields. -/
theorem getElem!_map_toBits (xs : Array Float) (k : Nat) :
    (xs.map Float.toBits)[k]! = (xs[k]!).toBits := by
  by_cases h : k < xs.size
  · rw [getElem!_pos (xs.map Float.toBits) k (by simpa using h), getElem!_pos xs k h]
    simp
  · rw [getElem!_neg (xs.map Float.toBits) k (by simpa using h), getElem!_neg xs k h]
    change (0 : UInt64) = (UInt64.toFloat 0).toBits
    rw [F64Convert.toBits_toFloat]
    decide +kernel

end Project.IR
