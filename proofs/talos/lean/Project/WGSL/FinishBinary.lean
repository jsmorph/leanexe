import Project.Artifact.Binary.Proof.Decode
import Project.Artifact.Binary.Proof.Validate
import Project.Artifact.Binary.Proof.Translate
import Project.Artifact.Binary.Evidence
import Project.WGSL.Precision
import Project.ProofKit.FixedFrame
import Lean.Elab.Tactic.Cbv

namespace Project.WGSL.FinishBinary
open Wasm Wasm.Binary

/-- The exact bias-addition artifact. Promotion is supplied as explicit input;
the artifact itself adds the two binary64 words and returns the result bits. -/
def bytes : ByteArray := [0, 97, 115, 109, 1, 0, 0, 0, 1, 7, 1, 96, 2, 126, 126,
  1, 126, 3, 2, 1, 0, 5, 3, 1, 0, 1, 7, 19, 2, 6, 109, 101, 109, 111, 114, 121,
  2, 0, 6, 102, 105, 110, 105, 115, 104, 0, 0, 10, 12, 1, 10, 0, 32, 0, 191,
  32, 1, 191, 160, 189, 11].toByteArray

def raw : RawModule :=
  { sections := [.type, .function, .memory, .export, .code]
    types := [⟨[.i64, .i64], [.i64]⟩]
    functionTypeIndices := [0]
    memories := [⟨⟨1, none⟩⟩]
    globals := []
    exports := [⟨⟨[109, 101, 109, 111, 114, 121], "memory"⟩, .memory 0⟩,
      ⟨⟨[102, 105, 110, 105, 115, 104], "finish"⟩, .func 0⟩]
    codes := [⟨[], [.localGet 0, .f64ReinterpretI64, .localGet 1, .f64ReinterpretI64,
      .f64Add, .i64ReinterpretF64]⟩] }

theorem parsed : decode bytes = .ok raw := by cbv
theorem validation_test : (validate raw).toOption.isSome = true := by cbv
theorem validated : ∃ checked, validate raw = .ok checked :=
  ok_exists_of_toOption_isSome validation_test
theorem core_valid : CoreValid raw := by
  obtain ⟨checked, h⟩ := validated
  exact Proof.validate_sound h

def body : Wasm.Program := [.localGet 0, .f64ReinterpretI64, .localGet 1,
  .f64ReinterpretI64, .f64Add, .i64ReinterpretF64]
def function : Wasm.Function :=
  { params := [.i64, .i64], locals := [], body := body, results := [.i64], typeIdx := some 0 }
def module : Wasm.Module := Translation.module raw

theorem exact (env : HostEnv Unit) (initial : Store Unit) (x bias : UInt64) :
    TerminatesWith env module 0 initial [.i64 bias, .i64 x]
      (fun final values => final = initial ∧ values = [.i64 (Wasm.IEEE64.add x bias)]) := by
  refine TerminatesWith.of_wp_entry_for (f := function) rfl ?_ (by decide)
  change wp module body _ initial (function.toLocals [.i64 x, .i64 bias]) env
  unfold body
  wp_fixed_frame [function]
  simp [Wasm.f64Add]

/-- Exact decoding and validation are part of the execution claim. -/
theorem artifact_exact (env : HostEnv Unit) (initial : Store Unit) (x bias : UInt64) :
    ∃ decoded checked, decode bytes = .ok decoded ∧ validate decoded = .ok checked ∧
      CoreValid decoded ∧ TerminatesWith env checked.toTalos 0 initial [.i64 bias, .i64 x]
        (fun final values => final = initial ∧ values = [.i64 (Wasm.IEEE64.add x bias)]) := by
  obtain ⟨checked, h⟩ := validated
  refine ⟨raw, checked, parsed, h, core_valid, ?_⟩
  rw [ValidatedModule.toTalos, Proof.validate_raw_eq h]
  exact exact env initial x bias

#print axioms parsed
#print axioms core_valid
#print axioms artifact_exact
end Project.WGSL.FinishBinary
