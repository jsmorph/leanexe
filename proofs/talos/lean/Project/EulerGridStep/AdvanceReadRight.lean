import Project.EulerGridStep.AdvanceReadFrames

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit
open Project.EulerGridScan.Execution
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

/-- Exact emitted read7 of the old grid, preserving all memory. -/
theorem advance_read_6_spec (m : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (ratio inputUnused pointer unused output : UInt64) (input : Array UInt64) (index : Nat)
    (hArray : UInt64Array.At initial pointer input) (hi : index < input.size / 3)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp m rest Q initial
      (advanceReadStageFrame ratio inputUnused pointer unused output input index 7) env) :
    wp m ((func35.drop 167).take 13 ++ rest) Q initial
      (advanceReadStageFrame ratio inputUnused pointer unused output input index 6) env := by
  have hSize32 := input_size_lt_32 initial pointer input hArray
  obtain ⟨hL0, hC0, hR0⟩ := neighbor_word_bounds input index 0 hi (by decide)
  obtain ⟨hL1, hC1, hR1⟩ := neighbor_word_bounds input index 1 hi (by decide)
  obtain ⟨hL2, hC2, hR2⟩ := neighbor_word_bounds input index 2 hi (by decide)
  simp only [Nat.add_zero] at hL0 hC0 hR0
  have hBounds := neighbor_word_bounds input index 0 hi (by decide)
  have hBound : nextOffset input.size index < input.size := by
    simpa only [Nat.add_zero] using hBounds.2.2
  obtain ⟨hNat, hWord, hMemory, hRead⟩ := arrayRead_facts initial pointer input hArray
    (nextOffset input.size index) hBound
  have hSafe := Nat.not_lt.mpr hMemory
  have hLengthSafe := Nat.not_lt.mpr hArray.generatedLengthBound
  have hLengthRead := hArray.lengthRead
  have hPointerAddress := hArray.pointerAddress_eq
  advance_single_read_peel
  simpa (discharger := omega) [advanceReadStageFrame, advanceReadIndex, advanceReadOffset, advanceOffsetsFrame,
    advanceEntryFrame, Array.getD, hBound, hL0, hL1, hL2, hC0, hC1, hC2,
    hR0, hR1, hR2, -UInt64.ofNat_mul, -UInt64.ofNat_add] using hNext

#print axioms advance_read_6_spec

/-- Exact emitted read8 of the old grid, preserving all memory. -/
theorem advance_read_7_spec (m : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (ratio inputUnused pointer unused output : UInt64) (input : Array UInt64) (index : Nat)
    (hArray : UInt64Array.At initial pointer input) (hi : index < input.size / 3)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp m rest Q initial
      (advanceReadStageFrame ratio inputUnused pointer unused output input index 8) env) :
    wp m ((func35.drop 180).take 23 ++ rest) Q initial
      (advanceReadStageFrame ratio inputUnused pointer unused output input index 7) env := by
  have hSize32 := input_size_lt_32 initial pointer input hArray
  obtain ⟨hL0, hC0, hR0⟩ := neighbor_word_bounds input index 0 hi (by decide)
  obtain ⟨hL1, hC1, hR1⟩ := neighbor_word_bounds input index 1 hi (by decide)
  obtain ⟨hL2, hC2, hR2⟩ := neighbor_word_bounds input index 2 hi (by decide)
  simp only [Nat.add_zero] at hL0 hC0 hR0
  have hBounds := neighbor_word_bounds input index 1 hi (by decide)
  have hBound : nextOffset input.size index + 1 < input.size := by
    simpa only [Nat.add_zero] using hBounds.2.2
  obtain ⟨hNat, hWord, hMemory, hRead⟩ := arrayRead_facts initial pointer input hArray
    (nextOffset input.size index + 1) hBound
  have hSafe := Nat.not_lt.mpr hMemory
  have hAdd : UInt64.ofNat (nextOffset input.size index) + 1 = UInt64.ofNat (nextOffset input.size index + 1) :=
    (UInt64.ofNat_add (nextOffset input.size index) 1).symm
  have hGuard := neighbor_add_guard (nextOffset input.size index) 1 (by omega) (by decide)
  change ¬ (UInt64.ofNat (nextOffset input.size index) + 1 < UInt64.ofNat (nextOffset input.size index)) at hGuard
  rw [hAdd] at hGuard
  have hLengthSafe := Nat.not_lt.mpr hArray.generatedLengthBound
  have hLengthRead := hArray.lengthRead
  have hPointerAddress := hArray.pointerAddress_eq
  advance_single_read_peel
  simpa (discharger := omega) [advanceReadStageFrame, advanceReadIndex, advanceReadOffset, advanceOffsetsFrame,
    advanceEntryFrame, Array.getD, hBound, hL0, hL1, hL2, hC0, hC1, hC2,
    hR0, hR1, hR2, -UInt64.ofNat_mul, -UInt64.ofNat_add] using hNext

#print axioms advance_read_7_spec

/-- Exact emitted read9 of the old grid, preserving all memory. -/
theorem advance_read_8_spec (m : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (ratio inputUnused pointer unused output : UInt64) (input : Array UInt64) (index : Nat)
    (hArray : UInt64Array.At initial pointer input) (hi : index < input.size / 3)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp m rest Q initial
      (advanceReadStageFrame ratio inputUnused pointer unused output input index 9) env) :
    wp m ((func35.drop 203).take 23 ++ rest) Q initial
      (advanceReadStageFrame ratio inputUnused pointer unused output input index 8) env := by
  have hSize32 := input_size_lt_32 initial pointer input hArray
  obtain ⟨hL0, hC0, hR0⟩ := neighbor_word_bounds input index 0 hi (by decide)
  obtain ⟨hL1, hC1, hR1⟩ := neighbor_word_bounds input index 1 hi (by decide)
  obtain ⟨hL2, hC2, hR2⟩ := neighbor_word_bounds input index 2 hi (by decide)
  simp only [Nat.add_zero] at hL0 hC0 hR0
  have hBounds := neighbor_word_bounds input index 2 hi (by decide)
  have hBound : nextOffset input.size index + 2 < input.size := by
    simpa only [Nat.add_zero] using hBounds.2.2
  obtain ⟨hNat, hWord, hMemory, hRead⟩ := arrayRead_facts initial pointer input hArray
    (nextOffset input.size index + 2) hBound
  have hSafe := Nat.not_lt.mpr hMemory
  have hAdd : UInt64.ofNat (nextOffset input.size index) + 2 = UInt64.ofNat (nextOffset input.size index + 2) :=
    (UInt64.ofNat_add (nextOffset input.size index) 2).symm
  have hGuard := neighbor_add_guard (nextOffset input.size index) 2 (by omega) (by decide)
  change ¬ (UInt64.ofNat (nextOffset input.size index) + 2 < UInt64.ofNat (nextOffset input.size index)) at hGuard
  rw [hAdd] at hGuard
  have hLengthSafe := Nat.not_lt.mpr hArray.generatedLengthBound
  have hLengthRead := hArray.lengthRead
  have hPointerAddress := hArray.pointerAddress_eq
  advance_single_read_peel
  simpa (discharger := omega) [advanceReadStageFrame, advanceReadIndex, advanceReadOffset, advanceOffsetsFrame,
    advanceEntryFrame, Array.getD, hBound, hL0, hL1, hL2, hC0, hC1, hC2,
    hR0, hR1, hR2, -UInt64.ofNat_mul, -UInt64.ofNat_add] using hNext

#print axioms advance_read_8_spec

end Project.EulerGridStep.Execution
