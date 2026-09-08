import Project.EulerGridScan.Loop

namespace Project.EulerGridScan.Execution
open Wasm
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

def resultValues (input : Array UInt64) : List Value :=
  let result := Project.EulerGridStep.Model.maxSpeedCheckedBits input
  [.i64 result.speed, .i64 result.status]

macro "entry_peel" : tactic => `(tactic|
  repeat
    first
    | wp_run [func11Def, loopFrame, List.set, List.getElem?_cons_zero,
        List.getElem?_cons_succ, reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, *]
    | simp [*, -UInt64.ofNat_mul, -UInt64.ofNat_add, -UInt64.ofNat_div, -UInt64.ofNat_mod]
    | refine ⟨by omega, ?_⟩
    | refine wp_iff_cons rfl ?_
      simp [*, -UInt64.ofNat_mul, -UInt64.ofNat_add, -UInt64.ofNat_div, -UInt64.ofNat_mod])

theorem maxSpeedCheckedBits_exact_in_module {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (pointer : UInt64) (input : Array UInt64)
    (hArray : Project.ProofKit.UInt64Array.At initial pointer input) :
    TerminatesWith env m 11 initial [.i64 pointer]
      (fun final values => final = initial ∧ values = resultValues input) := by
  have hSize64 := hArray.size_lt
  have hSizeNat := UInt64.toNat_ofNat_of_lt' hSize64
  have hLengthBound := hArray.generatedLengthBound
  have hLengthRead := hArray.lengthRead
  have hPointerAddress := hArray.pointerAddress_eq
  have hZero : UInt64.ofNat input.size = 0 ↔ input.size = 0 := by
    constructor
    · intro h
      simpa only [hSizeNat, UInt64.toNat_zero] using congrArg UInt64.toNat h
    · intro h
      simp [h]
  have hDivWord : UInt64.ofNat input.size / 3 = UInt64.ofNat (input.size / 3) :=
    (UInt64.ofNat_div (a := input.size) (b := 3) hSize64 (by decide)).symm
  have hModWord : UInt64.ofNat input.size % 3 = UInt64.ofNat (input.size % 3) :=
    (UInt64.ofNat_mod (a := input.size) (b := 3) hSize64 (by decide)).symm
  have hRemNat := UInt64.toNat_ofNat_of_lt' (show input.size % 3 < UInt64.size by omega)
  have hRemZero : UInt64.ofNat (input.size % 3) = 0 ↔ input.size % 3 = 0 := by
    constructor
    · intro h
      simpa only [hRemNat, UInt64.toNat_zero] using congrArg UInt64.toNat h
    · intro h
      simp [h]
  dsimp only [resultValues]
  generalize hModel : Project.EulerGridStep.Model.maxSpeedCheckedBits input = target
  refine TerminatesWith.of_wp_entry_for (f := func11Def)
    (by simpa [layout.noImports] using layout.scan) ?_ (by simp [layout.noImports])
  change wp m func11 _ initial (func11Def.toLocals [.i64 pointer]) env
  unfold func11
  by_cases hEmpty : input.size = 0
  · have hTarget : target = ⟨1, 0⟩ := by
      rw [← hModel]
      simp [Project.EulerGridStep.Model.maxSpeedCheckedBits, hEmpty]
    entry_peel
  · by_cases hRem : input.size % 3 = 0
    · entry_peel
      have hTarget : target = remaining input (input.size / 3) 0 0 0 := by
        rw [← hModel]
        simp [Project.EulerGridStep.Model.maxSpeedCheckedBits, hEmpty, hRem, remaining]
      apply scan_loop_spec layout env initial pointer input hArray
        (input.size / 3) 0 rfl (by omega) 0 0 0
        { l33 := UInt64.ofNat input.size, l34 := 3, l35 := pointer } target hTarget
      intro firstIndex firstStatus firstSpeed firstScratch hFirst
      entry_peel
      apply scan_loop_spec layout env initial pointer input hArray
        (input.size / 3) 0 rfl (by omega) 0 0 firstStatus
        { firstScratch with l40 := 0 } target hTarget
      intro secondIndex secondStatus secondSpeed secondScratch hSecond
      entry_peel
      have hStatus := congrArg Project.EulerGridStep.Model.CheckedSpeed.status hFirst
      have hSpeed := congrArg Project.EulerGridStep.Model.CheckedSpeed.speed hSecond
      simp_all
    · have hTarget : target = ⟨1, 0⟩ := by
        rw [← hModel]
        simp [Project.EulerGridStep.Model.maxSpeedCheckedBits, hEmpty, hRem]
      entry_peel

#print axioms maxSpeedCheckedBits_exact_in_module
end Project.EulerGridScan.Execution
