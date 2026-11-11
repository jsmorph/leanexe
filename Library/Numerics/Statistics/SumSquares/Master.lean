import Library.Numerics.Statistics.SumSquares.Compiled
import Library.Numerics.Reductions.Binary64
import Verified.Master

namespace Library.Numerics.Statistics.SumSquares

open CodeLib.IEEE64 (value Finite)

set_option exponentiation.threshold 4096
open LeanExe.ProofKit LeanExe.ProofKit.F64Approx Library.Numerics.Reductions.Binary64

theorem sumSquares_export :
    ({ name := "sumSquares", funcIdx := 2 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- `sumSquares` is a left-to-right sum of `n` rounded squares, within `γ_n Σ x_i ^ 2 + n / 2 ^ 1074`
of the exact sum of squares. -/
theorem sumSquares_spec (xs : Array Float) (hs : xs.size < 2 ^ 52)
    (hf : ∀ x ∈ xs, Finite x.toBits)
    (hS : (xs.toList.map fun x => value x.toBits ^ 2).sum ≤ 2 ^ 1021) :
    Finite (sumSquares xs).toBits ∧
      |value (sumSquares xs).toBits - (xs.toList.map fun x => value x.toBits ^ 2).sum| ≤
        (xs.size : ℝ) / (2 ^ 53 - xs.size) * (xs.toList.map fun x => value x.toBits ^ 2).sum +
          xs.size / 2 ^ 1074 := by
  have habs : (xs.toList.map fun x => |value x.toBits * value x.toBits|) =
      xs.toList.map fun x => value x.toBits ^ 2 := by
    congr 1; funext x; rw [abs_mul_self, sq]
  have hsq : (xs.toList.map fun x => value x.toBits * value x.toBits) =
      xs.toList.map fun x => value x.toBits ^ 2 := by
    congr 1; funext x; rw [sq]
  have hfin : ∀ a ∈ xs.toList, Finite a.toBits := fun a ha => hf a (Array.mem_toList_iff.mp ha)
  have h := dot_bound xs.toList (fun x => x) (fun x => x) hfin hfin
    (by rw [Array.length_toList]; exact hs) (by rw [habs]; exact hS)
  beta_reduce at h
  rw [habs, hsq, Array.length_toList] at h
  unfold sumSquares
  rw [← Array.foldl_toList]
  exact h

/-- The export `sumSquares`, called on an array of `n` finite floats whose squares sum to at most
`2 ^ 1021`, returns a finite float within `γ_n Σ x_i ^ 2 + n / 2 ^ 1074` of the exact sum of
squares, where `γ_k = k / (2 ^ 53 - k)` and the second term covers squares below the normal
range. -/
theorem sumSquares_master :
    Verified.Master compiled.module compiled.tables "sumSquares" compiled.sumSquares.bound
      (fun xs : Array Float => (∀ x ∈ xs, Finite x.toBits) ∧
        (xs.toList.map fun x => value x.toBits ^ 2).sum ≤ 2 ^ 1021)
      (fun xs (y : Float) => Finite y.toBits ∧
        |value y.toBits - (xs.toList.map fun x => value x.toBits ^ 2).sum| ≤
          (xs.size : ℝ) / (2 ^ 53 - xs.size) * (xs.toList.map fun x => value x.toBits ^ 2).sum +
            xs.size / 2 ^ 1074) :=
  .of_trapFree (.ofA compiled.sumSquares.trapFree) nofun sumSquares_export
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ xs ⟨_, _, hxs⟩ hD =>
      sumSquares_spec xs (by have := hxs.values.size_lt_memory32; simp at this; omega) hD.1 hD.2

#print axioms sumSquares_master

end Library.Numerics.Statistics.SumSquares
