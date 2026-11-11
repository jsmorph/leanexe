import Demos.Rcv.Compiled
import Demos.Rcv.Refinement
import Verified.Call
import Verified.ChargeFacts

/-!
The call of the module's export `count`.  `count_callSpec` composes the generated
`compiled.count.trapFree` with `Demos.Rcv.Refine.count_eq`: for every word array, called from a
ready store with room for the generated bound `compiled.count.bound`, function 22, the export
`count`, returns without a trap the words of `Demos.Rcv.Spec.countArray`, leaves a ready store, and
raises `top` by at most the bound.  `count_bound` closes the bound: at most 481,128 bytes for every
array, the two-word array literal, at most 64 rounds of a block of 68 counters and `n + 9` pushes
of result words, and the push of the winner.
-/

namespace Demos.Rcv.Program

open Wasm LeanExe.Pipeline LeanExe.Runtime

theorem count_export :
    ({ name := "count", funcIdx := 22 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- `Verified.CallSpec` for function 22 and `Demos.Rcv.Spec.countArray`, with the generated bound
as the room: from a ready store in which `top` can rise by `compiled.count.bound ws` bytes, the
call with the borrowed array `ws` returns an owned array that holds `countArray ws`, leaves a ready
store, and raises `top` by at most that bound. -/
theorem count_callSpec :
    Verified.CallSpec compiled.module compiled.tables 22 Demos.Rcv.Spec.countArray
      compiled.count.bound :=
  (Verified.ImplementsTables.call (.ofA compiled.count.trapFree) compiled.tables nofun).spec
    (fun _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ ws ⟨_, _, hws⟩ => Demos.Rcv.Refine.count_eq ws hws.values.size_lt

theorem min_bound {U K L G : Nat} (hP : K + L ≤ 407272) (hG : G ≤ 73856) :
    min U (K + L) + G ≤ 481128 := by
  omega

/-- The generated bound is at most 481,128 bytes for every array: 152 bytes for the result `[0]`
of an invalid array, and for a valid one 232 bytes for the literal `#[1, 0]`, 600 bytes for the
counters and `80 (n + 9)` bytes for the pushes of each of at most 64 rounds, and the move of the
result words, at most 4,610 before the winner's, to a block with room for the winner. -/
theorem count_bound (ws : Array UInt64) (hs : ws.size < 2 ^ 64) :
    compiled.count.bound ws ≤ 481128 := by
  rw [compiled.count.bound_eq]
  split
  · next hv =>
    rw [compiled.countValid.bound_eq]
    have hval := (Demos.Rcv.Refine.validArray_iff ws hs).mp hv
    obtain ⟨-, h2, -⟩ := hval
    rw [Demos.Rcv.Refine.readWords_n] at h2
    simp only [Demos.Rcv.maxIndex] at h2
    have hsize := Demos.Rcv.Refine.rounds_size ws hs hv
    have hfuel : (countedSize ws ws[0]! + 1).toNat ≤ 64 := by
      have hlen : (Demos.Rcv.Refine.countedOfWords ws ws[0]!.toNat).length ≤ 63 :=
        (List.filter_sublist.length_le.trans (by simp)).trans h2
      rw [UInt64.toNat_add, Demos.Rcv.Refine.countedSize_eq ws ws[0]! h2, UInt64.toNat_one,
        Nat.mod_eq_of_lt (by omega)]
      omega
    refine min_bound ?_ ?_
    · refine le_trans (Nat.add_le_add_left (Verified.loopCost_const_le 6360 ?_ _ _ _) _) ?_
      · intro k s
        simp only [compiled.tallyRound.bound_eq, compiled.pushRound.cost_eq,
          Verified.loopCost_const, Verified.blockCost_eq, Verified.paidGrowCost_eq,
          UInt64.reduceToNat]
        omega
      · exact (fun K f hK hf => by omega :
          ∀ K f : Nat, K ≤ 232 → f ≤ 64 → K + f * 6360 ≤ 407272) _ _
          (by norm_num [Verified.blockCost_eq, Verified.growCost_eq, Verified.paidGrowCost_eq])
          hfuel
    · rw [Array.size_set!]
      exact (fun s h => by rw [Verified.growCost_eq]; omega :
        ∀ s, s ≤ 4610 → Verified.growCost (s + 1) 1 ≤ 73856) _ hsize
  · norm_num [Verified.blockCost_eq, Verified.growCost_eq]

#print axioms count_export
#print axioms count_callSpec
#print axioms count_bound
#print axioms Demos.Rcv.Refine.count_eq

end Demos.Rcv.Program
