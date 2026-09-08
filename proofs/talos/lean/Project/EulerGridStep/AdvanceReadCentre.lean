import Project.EulerGridStep.AdvanceReadFrames

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit
open Project.EulerGridScan.Execution
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

/-- Exact emitted read4 of the old grid, preserving all memory. -/
theorem advance_read_3_spec (m : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (ratio inputUnused pointer unused output : UInt64) (input : Array UInt64) (index : Nat)
    (hArray : UInt64Array.At initial pointer input) (hi : index < input.size / 3)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp m rest Q initial
      (advanceReadStageFrame ratio inputUnused pointer unused output input index 4) env) :
    wp m ((func35.drop 108).take 13 ++ rest) Q initial
      (advanceReadStageFrame ratio inputUnused pointer unused output input index 3) env := by
  have hSize32 := input_size_lt_32 initial pointer input hArray
  obtain ⟨hL0, hC0, hR0⟩ := neighbor_word_bounds input index 0 hi (by decide)
  obtain ⟨hL1, hC1, hR1⟩ := neighbor_word_bounds input index 1 hi (by decide)
  obtain ⟨hL2, hC2, hR2⟩ := neighbor_word_bounds input index 2 hi (by decide)
  simp only [Nat.add_zero] at hL0 hC0 hR0
  have hBounds := neighbor_word_bounds input index 0 hi (by decide)
  have hBound : 3 * index < input.size := by
    simpa only [Nat.add_zero] using hBounds.2.1
  obtain ⟨hNat, hWord, hMemory, hRead⟩ := arrayRead_facts initial pointer input hArray
    (3 * index) hBound
  have hSafe := Nat.not_lt.mpr hMemory
  have hLengthSafe := Nat.not_lt.mpr hArray.generatedLengthBound
  have hLengthRead := hArray.lengthRead
  have hPointerAddress := hArray.pointerAddress_eq
  advance_single_read_peel
  simpa (discharger := omega) [advanceReadStageFrame, advanceReadIndex, advanceReadOffset, advanceOffsetsFrame,
    advanceEntryFrame, Array.getD, hBound, hL0, hL1, hL2, hC0, hC1, hC2,
    hR0, hR1, hR2, -UInt64.ofNat_mul, -UInt64.ofNat_add] using hNext

#print axioms advance_read_3_spec

/-- Exact emitted read5 of the old grid, preserving all memory. -/
theorem advance_read_4_spec (m : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (ratio inputUnused pointer unused output : UInt64) (input : Array UInt64) (index : Nat)
    (hArray : UInt64Array.At initial pointer input) (hi : index < input.size / 3)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp m rest Q initial
      (advanceReadStageFrame ratio inputUnused pointer unused output input index 5) env) :
    wp m ((func35.drop 121).take 23 ++ rest) Q initial
      (advanceReadStageFrame ratio inputUnused pointer unused output input index 4) env := by
  have hSize32 := input_size_lt_32 initial pointer input hArray
  obtain ⟨hL0, hC0, hR0⟩ := neighbor_word_bounds input index 0 hi (by decide)
  obtain ⟨hL1, hC1, hR1⟩ := neighbor_word_bounds input index 1 hi (by decide)
  obtain ⟨hL2, hC2, hR2⟩ := neighbor_word_bounds input index 2 hi (by decide)
  simp only [Nat.add_zero] at hL0 hC0 hR0
  have hBounds := neighbor_word_bounds input index 1 hi (by decide)
  have hBound : 3 * index + 1 < input.size := by
    simpa only [Nat.add_zero] using hBounds.2.1
  obtain ⟨hNat, hWord, hMemory, hRead⟩ := arrayRead_facts initial pointer input hArray
    (3 * index + 1) hBound
  have hSafe := Nat.not_lt.mpr hMemory
  have hAdd : UInt64.ofNat (3 * index) + 1 = UInt64.ofNat (3 * index + 1) :=
    (UInt64.ofNat_add (3 * index) 1).symm
  have hGuard := neighbor_add_guard (3 * index) 1 (by omega) (by decide)
  change ¬ (UInt64.ofNat (3 * index) + 1 < UInt64.ofNat (3 * index)) at hGuard
  rw [hAdd] at hGuard
  have hLengthSafe := Nat.not_lt.mpr hArray.generatedLengthBound
  have hLengthRead := hArray.lengthRead
  have hPointerAddress := hArray.pointerAddress_eq
  advance_single_read_peel
  simpa (discharger := omega) [advanceReadStageFrame, advanceReadIndex, advanceReadOffset, advanceOffsetsFrame,
    advanceEntryFrame, Array.getD, hBound, hL0, hL1, hL2, hC0, hC1, hC2,
    hR0, hR1, hR2, -UInt64.ofNat_mul, -UInt64.ofNat_add] using hNext

#print axioms advance_read_4_spec

/-- Exact emitted read6 of the old grid, preserving all memory. -/
theorem advance_read_5_spec (m : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (ratio inputUnused pointer unused output : UInt64) (input : Array UInt64) (index : Nat)
    (hArray : UInt64Array.At initial pointer input) (hi : index < input.size / 3)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp m rest Q initial
      (advanceReadStageFrame ratio inputUnused pointer unused output input index 6) env) :
    wp m ((func35.drop 144).take 23 ++ rest) Q initial
      (advanceReadStageFrame ratio inputUnused pointer unused output input index 5) env := by
  have hSize32 := input_size_lt_32 initial pointer input hArray
  obtain ⟨hL0, hC0, hR0⟩ := neighbor_word_bounds input index 0 hi (by decide)
  obtain ⟨hL1, hC1, hR1⟩ := neighbor_word_bounds input index 1 hi (by decide)
  obtain ⟨hL2, hC2, hR2⟩ := neighbor_word_bounds input index 2 hi (by decide)
  simp only [Nat.add_zero] at hL0 hC0 hR0
  have hBounds := neighbor_word_bounds input index 2 hi (by decide)
  have hBound : 3 * index + 2 < input.size := by
    simpa only [Nat.add_zero] using hBounds.2.1
  obtain ⟨hNat, hWord, hMemory, hRead⟩ := arrayRead_facts initial pointer input hArray
    (3 * index + 2) hBound
  have hSafe := Nat.not_lt.mpr hMemory
  have hAdd : UInt64.ofNat (3 * index) + 2 = UInt64.ofNat (3 * index + 2) :=
    (UInt64.ofNat_add (3 * index) 2).symm
  have hGuard := neighbor_add_guard (3 * index) 2 (by omega) (by decide)
  change ¬ (UInt64.ofNat (3 * index) + 2 < UInt64.ofNat (3 * index)) at hGuard
  rw [hAdd] at hGuard
  have hLengthSafe := Nat.not_lt.mpr hArray.generatedLengthBound
  have hLengthRead := hArray.lengthRead
  have hPointerAddress := hArray.pointerAddress_eq
  advance_single_read_peel
  simpa (discharger := omega) [advanceReadStageFrame, advanceReadIndex, advanceReadOffset, advanceOffsetsFrame,
    advanceEntryFrame, Array.getD, hBound, hL0, hL1, hL2, hC0, hC1, hC2,
    hR0, hR1, hR2, -UInt64.ofNat_mul, -UInt64.ofNat_add] using hNext

#print axioms advance_read_5_spec

end Project.EulerGridStep.Execution
