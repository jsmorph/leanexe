import Library.Arrays.Word.Compiled
import LeanExe.Dialect.Lemmas
import Verified.Master

namespace Library.Arrays.Word

open LeanExe.Dialect

theorem scaled_export :
    ({ name := "scaled", funcIdx := 2 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- `scaled xs k` multiplies each element of `xs` by `k` modulo `2 ^ 64`, for an array of fewer
than `2 ^ 64` elements. -/
theorem scaled_eq (xs : Array UInt64) (k : UInt64) (h : xs.size < 2 ^ 64) :
    scaled xs k = xs.map (· * k) := by
  have hn : xs.size.toUInt64.toNat = xs.size := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']; omega
  apply Array.ext
  · rw [Array.size_map, scaled, build_size, hn]
  · intro i h1 h2
    have hi : i < xs.size := by simpa using h2
    have hb := build_get (n := xs.size.toUInt64) (f := fun i => xs[i.toNat]! * k) (m := i)
      (by rw [hn]; exact hi)
    beta_reduce at hb
    rw [UInt64.toNat_ofNat_of_lt' (show i < 2 ^ 64 by omega), getElem!_pos xs i hi] at hb
    rw [Array.getElem_map, ← getElem!_pos (scaled xs k) i h1]
    exact hb

/-- The export `scaled`, called on an array of words and a word `k`, returns the array of the
products of its elements with `k` modulo `2 ^ 64`. -/
theorem scaled_master :
    Verified.Master compiled.module compiled.tables "scaled" compiled.scaled.bound (fun _ => True)
      (fun (x : Array UInt64 × UInt64) y => y = x.1.map (· * x.2)) :=
  .of_trapFree (.ofA compiled.scaled.trapFree) nofun scaled_export
    (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, ⟨_, _, hxs⟩, _⟩ _ => scaled_eq x.1 x.2 hxs.values.size_lt

#print axioms scaled_master

end Library.Arrays.Word
