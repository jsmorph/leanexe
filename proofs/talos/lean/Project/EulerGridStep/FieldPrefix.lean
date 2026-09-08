import Project.EulerGridStep.FieldIndexing
import Project.EulerGridStep.Program

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

def fieldParameters (unused pointer : UInt64) (index field : Nat) (value : UInt64) : List Value :=
  [.i64 unused, .i64 pointer, .i64 (UInt64.ofNat index), .i64 (UInt64.ofNat field), .i64 value]

def fieldEntryFrame (unused pointer : UInt64) (index field : Nat) (value : UInt64) : Locals :=
  { params := fieldParameters unused pointer index field value,
    locals := List.replicate 20 (.i64 0), values := [] }

def fieldPrefixFrame (unused pointer : UInt64) (count index field : Nat) (value : UInt64) : Locals :=
  { params := fieldParameters unused pointer index field value,
    locals := [.i64 pointer, .i64 (UInt64.ofNat (1 + 6 * index + field)), .i64 0, .i64 0, .i64 0,
      .i64 pointer, .i64 (UInt64.ofNat (1 + 6 * index + field)), .i64 (UInt64.ofNat count), .i64 1,
      .i64 (UInt64.ofNat (6 * index)), .i64 (UInt64.ofNat (1 + 6 * index)), .i64 value,
      .i64 (UInt64.ofNat index), .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
    values := [.i32 1] }

/-- Exact checked-index setup and array-header read, ending with a true in-bounds test. -/
theorem field_prefix_spec (m : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (unused pointer : UInt64) (input : Array UInt64) (index field : Nat) (value : UInt64)
    (hArray : UInt64Array.At initial pointer input)
    (hi : 1 + 6 * index + field < input.size)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp m rest Q initial (fieldPrefixFrame unused pointer input.size index field value) env) :
    wp m (func27.take 44 ++ rest) Q initial (fieldEntryFrame unused pointer index field value) env := by
  have hSize32 : input.size < 4294967296 := by have := hArray.1; omega
  have hIndex32 : index < 4294967296 := by omega
  have hIndex64 : index < UInt64.size := by change index < 18446744073709551616; omega
  have hSize64 := hArray.size_lt
  have hWord0 : UInt64.ofNat index = 0 ↔ index = 0 := by
    constructor
    · intro h
      simpa only [UInt64.toNat_ofNat_of_lt' hIndex64, UInt64.toNat_zero] using congrArg UInt64.toNat h
    · intro h
      simp [h]
  have hMul : (6 : UInt64) * UInt64.ofNat index = UInt64.ofNat (6 * index) :=
    (UInt64.ofNat_mul 6 index).symm
  have hAdd : (1 : UInt64) + UInt64.ofNat (6 * index) = UInt64.ofNat (1 + 6 * index) :=
    (UInt64.ofNat_add 1 (6 * index)).symm
  have hAddField : UInt64.ofNat (1 + 6 * index) + UInt64.ofNat field =
      UInt64.ofNat (1 + 6 * index + field) := (UInt64.ofNat_add _ _).symm
  have hFirstGuard := small_add_guard 1 (6 * index) (by omega)
  have hSecondGuard := small_add_guard (1 + 6 * index) field (by omega)
  have hInBounds : UInt64.ofNat (1 + 6 * index + field) < UInt64.ofNat input.size := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' (by omega : 1 + 6 * index + field < UInt64.size),
      UInt64.toNat_ofNat_of_lt' hSize64]
    exact hi
  have hOffset64 : 1 + 6 * index < UInt64.size := by omega
  have hDestination64 : 1 + 6 * index + field < UInt64.size := by omega
  have hOffsetNZ : UInt64.ofNat (1 + 6 * index) ≠ 0 := by
    intro h
    have hNat := congrArg UInt64.toNat h
    rw [UInt64.toNat_ofNat_of_lt' hOffset64, UInt64.toNat_zero] at hNat
    omega
  have hDestinationNZ : UInt64.ofNat (1 + 6 * index + field) ≠ 0 := by
    intro h
    have hNat := congrArg UInt64.toNat h
    rw [UInt64.toNat_ofNat_of_lt' hDestination64, UInt64.toNat_zero] at hNat
    omega
  have hOffsetRawNZ : (1 : UInt64) + 6 * UInt64.ofNat index ≠ 0 := by
    rwa [hMul, hAdd]
  have hDestinationRawNZ : (1 : UInt64) + 6 * UInt64.ofNat index + UInt64.ofNat field ≠ 0 := by
    rwa [field_index_word]
  have hEncodedGuard : ¬ UInt64.ofNat (1 + 6 * index + field) < UInt64.ofNat (1 + 6 * index) := by
    simpa only [hAddField] using hSecondGuard
  have hLengthBound := hArray.generatedLengthBound
  have hPointerAddress := hArray.pointerAddress_eq
  have hLengthRead := hArray.lengthRead
  by_cases hZero : index = 0
  · subst index
    have hZeroFieldNZ : (1 : UInt64) + UInt64.ofNat field ≠ 0 := by
      simpa using hDestinationRawNZ
    have hZeroInBounds : (1 : UInt64) + UInt64.ofNat field < UInt64.ofNat input.size := by
      simpa using hInBounds
    repeat first
      | wp_run [func27, List.take, fieldEntryFrame, fieldParameters]
      | simp [*, -UInt64.ofNat_mul, -UInt64.ofNat_add, -UInt64.ofNat_div, -UInt64.ofNat_mod]
      | rw [ite_eq_right (Nat.not_lt.mpr hLengthBound)]
      | refine wp_iff_cons rfl ?_
        simp [*, -UInt64.ofNat_mul, -UInt64.ofNat_add, -UInt64.ofNat_div, -UInt64.ofNat_mod]
    simpa [fieldPrefixFrame, fieldParameters] using hNext
  · have hMulGuard := six_mul_guard index hIndex32 (by omega)
    repeat first
      | wp_run [func27, List.take, fieldEntryFrame, fieldParameters]
      | simp [*, -UInt64.ofNat_mul, -UInt64.ofNat_add, -UInt64.ofNat_div, -UInt64.ofNat_mod]
      | rw [ite_eq_right (Nat.not_lt.mpr hLengthBound)]
      | refine wp_iff_cons rfl ?_
        simp [*, -UInt64.ofNat_mul, -UInt64.ofNat_add, -UInt64.ofNat_div, -UInt64.ofNat_mod]
    simpa [fieldPrefixFrame, fieldParameters] using hNext

#print axioms field_prefix_spec
end Project.EulerGridStep.Execution
