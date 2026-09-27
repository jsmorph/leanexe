import Project.Validate.Loop
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Call

/-!
# Specification for `validateGeneric`

The generated export takes a byte-array pointer and length, scans the input
bytes in linear memory, and returns `1` when every byte is an ASCII digit and
`0` otherwise.  The theorem quantifies over the store, the pointer, and the
byte list; the `BytesAt` hypothesis states what the host wrote into memory.
-/

namespace Project.Validate.Spec

open Wasm
open Project.Common
open LeanExe.Examples.AsciiDigits

set_option maxHeartbeats 64000000

/-- The generated export `validateGeneric` returns `1` exactly when every input
byte is an ASCII digit. -/
def wasmRunsTo (bytes : List UInt8) (output : UInt64) : Prop :=
  ∀ (env : HostEnv Unit) (st : Store Unit) (ptr : UInt64),
    bytes.length + 1 < UInt64.size →
    BytesAt st ptr bytes →
    TerminatesWith (m := «module») (id := 3) (initial := st) (env := env)
      [.i64 (UInt64.ofNat bytes.length), .i64 ptr]
      (fun _ vs => vs = [.i64 output])

@[spec_of "lean" "LeanExe.Examples.AsciiDigits.validateGeneric"]
def ValidateGenericSpec : Prop :=
  ValidateSpec wasmRunsTo

@[proves Project.Validate.Spec.ValidateGenericSpec]
theorem validateGeneric_correct : ValidateGenericSpec := by
  unfold ValidateGenericSpec ValidateSpec wasmRunsTo
  intro bytes env st ptr hLen hBytes
  apply TerminatesWith.of_wp_entry_for (f := func3Def)
  · simp [«module»]
  · change wp «module» func3 _ st
      { params := [.i64 ptr, .i64 (UInt64.ofNat bytes.length)],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0],
        values := [] }
      env
    unfold func3
    have hadd1 : (UInt64.ofNat bytes.length + 1).toNat = bytes.length + 1 := by
      rw [toNat_add_one]
      · rw [toNat_ofNat_lt (by omega)]
      · rw [toNat_ofNat_lt (by omega)]
        omega
    have hsucc_no_wrap :
        ¬ (UInt64.ofNat bytes.length + 1 < UInt64.ofNat bytes.length) := by
      rw [UInt64.lt_iff_toNat_lt, hadd1, toNat_ofNat_lt (by omega)]
      omega
    have hplus : UInt64.ofNat bytes.length + 1 = UInt64.ofNat (bytes.length + 1) := by
      apply UInt64.toNat.inj
      rw [hadd1, toNat_ofNat_lt (by omega)]
    wp_run
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp [hsucc_no_wrap])]
    wp_run
    rw [hplus]
    apply wp_call_tw (func2_terminates env st 0 ptr bytes hLen hBytes)
    rintro st2 vs ⟨rfl, rfl⟩
    wp_run
    simp [func3Def]

end Project.Validate.Spec
