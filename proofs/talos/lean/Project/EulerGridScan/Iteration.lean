import Project.EulerGridScan.Indexing

namespace Project.EulerGridScan.Execution
open Wasm
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

macro "scan_peel" : tactic => `(tactic|
  repeat
    first
    | wp_run [func8Def, List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
        reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, *]
    | refine ⟨by omega, ?_⟩
    | refine wp_iff_cons rfl ?_
      simp [*, -UInt64.ofNat_mul, -UInt64.ofNat_add])

theorem scanAt_exact {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (pointer capacity speed : UInt64)
    (input : Array UInt64) (index : Nat)
    (hArray : Project.ProofKit.UInt64Array.At initial pointer input)
    (hi : index < input.size / 3) :
    TerminatesWith env m 8 initial [.i64 speed, .i64 (UInt64.ofNat index), .i64 pointer, .i64 capacity]
      (fun final values => final = initial ∧ values = iterationValues input index speed) := by
  have hSize32 := input_size_lt_32 initial pointer input hArray
  have hSize64 := hArray.size_lt
  have hi32 : index < 4294967296 := by omega
  have hi64 : index < UInt64.size := by omega
  have h0 := cellWord_lt input index 0 hi (by decide)
  have h1 := cellWord_lt input index 1 hi (by decide)
  have h2 := cellWord_lt input index 2 hi (by decide)
  simp only [Nat.add_zero] at h0
  obtain ⟨hj0, he0, hb0, hr0⟩ := arrayRead_facts initial pointer input hArray (3 * index) h0
  obtain ⟨hj1, he1, hb1, hr1⟩ := arrayRead_facts initial pointer input hArray (3 * index + 1) h1
  obtain ⟨hj2, he2, hb2, hr2⟩ := arrayRead_facts initial pointer input hArray (3 * index + 2) h2
  have hNonemptyWord : UInt64.ofNat input.size ≠ 0 := by
    intro hz
    have hn := congrArg UInt64.toNat hz
    rw [UInt64.toNat_ofNat_of_lt' hSize64] at hn
    have : input.size = 0 := hn
    omega
  have hIndexNat := UInt64.toNat_ofNat_of_lt' hi64
  have hOffsetNat := UInt64.toNat_ofNat_of_lt' (show 3 * index < UInt64.size by omega)
  have hMul := triple_mul_word index
  have hAdd1 := (UInt64.ofNat_add (3 * index) 1).symm
  have hAdd2 := (UInt64.ofNat_add (3 * index) 2).symm
  have hAddGuard1 := offset_add_guard (3 * index) 1 (by omega) (by decide)
  have hAddGuard2 := offset_add_guard (3 * index) 2 (by omega) (by decide)
  change UInt64.ofNat (3 * index) + 1 = UInt64.ofNat (3 * index + 1) at hAdd1
  change UInt64.ofNat (3 * index) + 2 = UInt64.ofNat (3 * index + 2) at hAdd2
  change ¬ (UInt64.ofNat (3 * index) + 1 < UInt64.ofNat (3 * index)) at hAddGuard1
  change ¬ (UInt64.ofNat (3 * index) + 2 < UInt64.ofNat (3 * index)) at hAddGuard2
  rw [hAdd1] at hAddGuard1
  rw [hAdd2] at hAddGuard2
  have hLengthBound := hArray.generatedLengthBound
  have hLengthRead := hArray.lengthRead
  have hPointerAddress := hArray.pointerAddress_eq
  have sideProof := Project.EulerConservative.Execution.sideCheckedBits_exact_in_module
    layout.toHelperLayout layout.side env initial (input[3 * index]'h0)
      (input[3 * index + 1]'h1) (input[3 * index + 2]'h2)
  dsimp only [Project.EulerConservative.Execution.resultValues] at sideProof
  generalize hSideModel : Project.EulerConservative.Model.sideCheckedBits
    (input[3 * index]'h0) (input[3 * index + 1]'h1) (input[3 * index + 2]'h2) = side at sideProof
  refine TerminatesWith.of_wp_entry_for (f := func8Def)
    (by simpa [layout.noImports] using layout.scanAt) ?_ (by simp [layout.noImports])
  change wp m func8 _ initial (func8Def.toLocals [.i64 capacity, .i64 pointer, .i64 (UInt64.ofNat index), .i64 speed]) env
  unfold func8
  by_cases hzero : index = 0
  · subst index
    norm_num at he0 he1 he2 hb0 hb1 hb2 hr0 hr1 hr2
    change 0 < input.size at h0
    change 1 < input.size at h1
    change 2 < input.size at h2
    change (2 : UInt64) < UInt64.ofNat input.size at he2
    change Project.EulerConservative.Model.sideCheckedBits input[0] input[1] input[2] = side at hSideModel
    scan_peel
    refine wp_call_tw sideProof ?_
    rintro st values ⟨hst, rfl⟩
    subst st
    by_cases hs : side.status = 0 <;> by_cases hm : speed ≤ side.speed
    all_goals
      scan_peel
      simp [iterationValues, Project.EulerGridStep.Model.scan, Array.getD, h0, h1, h2, hSideModel, hs, hm]
  · have hwordzero : UInt64.ofNat index ≠ 0 := by
      intro hz
      have := congrArg UInt64.toNat hz
      rw [hIndexNat] at this
      exact hzero this
    have hGuard := triple_mul_guard index hi32 (by omega)
    scan_peel
    refine wp_call_tw sideProof ?_
    rintro st values ⟨hst, rfl⟩
    subst st
    by_cases hs : side.status = 0 <;> by_cases hm : speed ≤ side.speed
    all_goals
      scan_peel
      simp [iterationValues, Project.EulerGridStep.Model.scan, Array.getD, h0, h1, h2, hSideModel, hs, hm]

#print axioms scanAt_exact
end Project.EulerGridScan.Execution
