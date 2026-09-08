import Project.EulerGridStep.InitializationShape
import Project.EulerGridStep.FillLoop
import Project.EulerGridStep.HeaderMemory

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit
open Project.ProofKit.FixedArrayCopy

/-- Exact initialized logical array and the complete frame outside its length/payload. -/
structure InitializedArray (initial final : Store Unit) (target : UInt64) (count : Nat) : Prop where
  arrayAt : UInt64Array.At final target (Array.replicate count 0)
  pages : final.mem.pages = initial.mem.pages
  frame : { final with mem := initial.mem } = initial
  outside : ∀ address, address < target.toNat ∨ target.toNat + 8 * (count + 1) ≤ address →
    final.mem.bytes address = initial.mem.bytes address

theorem initial_fill_program_shape : (gridValidBody.drop 71).take 7 =
    [.localGet 34, .wrapI64, .localGet 33, .store64 0] ++ fillProgram 34 33 35 36 := rfl

/-- The actual length store and zero loop initialize an allocated array from arbitrary payload bytes. -/
theorem initial_fill_spec (m : Wasm.Module) (env : HostEnv Unit)
    (initial : Store Unit) (frame : Locals) (target : UInt64) (count : Nat)
    (hCounter : frame.validIndex 35) (hValues : frame.values = [])
    (hTarget : frame.get 34 = some (.i64 target))
    (hCount : frame.get 33 = some (.i64 (UInt64.ofNat count)))
    (hValue : frame.get 36 = some (.i64 0))
    (hFit32 : target.toNat + 8 * (count + 1) ≤ 4294967296)
    (hFitMemory : target.toNat + 8 * (count + 1) ≤ initial.mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final, InitializedArray initial final target count →
      wp m rest Q final (counterFrame frame 35 count hCounter) env) :
    wp m ((gridValidBody.drop 71).take 7 ++ rest) Q initial frame env := by
  have hTargetNat : target.toUInt32.toNat = target.toNat := by
    simpa [UInt64Array.wordAddress] using UInt64Array.wordAddress_toNat hFit32 (by omega : 0 < count + 1)
  have hHeaderBound : target.toUInt32.toNat + 8 ≤ initial.mem.pages * 65536 := by
    rw [hTargetNat]
    omega
  rw [initial_fill_program_shape]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  simp only [wp_localGet_cons, copyFrame_get_withValues, hTarget, hCount, hValues,
    wp_wrapI64_cons, wp_store64_cons]
  have hWrap : UInt32.ofNat (target.toNat % (2 ^ 32)) = target.toUInt32 :=
    (Memory.toUInt32_eq_ofNat target).symm
  rw [hWrap]
  simp only [UInt32.add_zero, UInt32.toNat_zero, Nat.add_zero]
  rw [ite_eq_right (Nat.not_lt.mpr hHeaderBound)]
  change wp m (fillProgram 34 33 35 36 ++ rest) Q (writeLength initial target count)
    { params := frame.params, locals := frame.locals } env
  rw [copyFrame_ofParts frame hValues]
  apply fill_loop_spec 34 33 35 36 m env (writeLength initial target count) frame target 0
    (payloadSnapshot initial target count) hCounter (by decide) (by decide) (by decide) hValues hTarget
    (by simpa only [payloadSnapshot, Array.size_ofFn] using hCount) hValue
    (writeLength_array initial target count hFit32 hFitMemory) Q rest
  intro final result hFill
  have hArray := hFill.arrayAt
  rw [hFill.complete] at hArray
  have hInitialized : InitializedArray initial final target count := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [payloadSnapshot, Array.size_ofFn] using hArray
    · simpa only [writeLength, Mem.write64_pages] using hFill.pages
    · have h := congrArg (fun s : Store Unit => { s with mem := initial.mem }) hFill.frame
      simpa only [writeLength] using h
    · intro address hOutside
      rw [hFill.outside address (by simp only [payloadSnapshot, Array.size_ofFn]; omega)]
      exact writeLength_bytes_outside initial target count address hFit32 (by omega)
  simpa only [payloadSnapshot, Array.size_ofFn] using hNext final hInitialized

#print axioms initial_fill_program_shape
#print axioms initial_fill_spec
end Project.EulerGridStep.Execution
