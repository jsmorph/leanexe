import Project.EulerCertificate.OutputAppendCopy
import Project.ProofKit.FixedArrayFrame

namespace Project.EulerCertificate.Execution
open Wasm Project.ProofKit FixedArrayFold FixedArrayResult FixedArrayCopy

def outputAppendDataProgram : Wasm.Program :=
  (func15.drop 314).take 12

theorem output_append_data_shape : outputAppendDataProgram =
    resultProgram 64 55 ++ lengthStoreLocalProgram 55 52 ++ outputAppendCopyProgram := rfl

theorem output_append_data_spec (env : HostEnv Unit)
    (initial : Store Unit) (frame : Locals) (source upper target : UInt64)
    (left right : Array UInt64) (hParams : frame.params.length = 17)
    (hLocals : frame.locals.length = 48) (hCounter : frame.validIndex 56)
    (hValues : frame.values = [])
    (hSource : frame.get 48 = some (.i64 source))
    (hUpper : frame.get 49 = some (.i64 upper))
    (hTarget : frame.get 64 = some (.i64 target))
    (hTotalCount : frame.get 52 = some (.i64 (UInt64.ofNat (left.size + right.size))))
    (hLeftCount : frame.get 53 = some (.i64 (UInt64.ofNat left.size)))
    (hRightCount : frame.get 54 = some (.i64 (UInt64.ofNat right.size)))
    (hLeft : UInt64Array.At initial source left) (hRight : UInt64Array.At initial upper right)
    (hTarget32 : target.toNat + 8 * (left.size + right.size + 1) ≤ 4294967296)
    (hTargetMemory : target.toNat + 8 * (left.size + right.size + 1) ≤ initial.mem.pages * 65536)
    (hSeparateLeft : source.toNat + 8 * (left.size + 1) ≤ target.toNat ∨
      target.toNat + 8 * (left.size + right.size + 1) ≤ source.toNat)
    (hSeparateRight : upper.toNat + 8 * (right.size + 1) ≤ target.toNat ∨
      target.toNat + 8 * (left.size + right.size + 1) ≤ upper.toNat)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final : Store Unit,
      ProofKit.Memory.WritesRange initial final target.toNat
        (target.toNat + 8 * (left.size + right.size + 1)) →
      UInt64Array.At final source left → UInt64Array.At final upper right →
      UInt64Array.At final target (left ++ right) →
      wp module rest Q final (counterFrame (resultFrame frame 55 target) 56 right.size
        (by simpa only [Locals.validIndex, resultFrame_params, resultFrame_locals_length] using hCounter)) env) :
    wp module (outputAppendDataProgram ++ rest) Q initial frame env := by
  have hPointer : target.toUInt32.toNat = target.toNat := by
    rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
  have hLengthBound : target.toUInt32.toNat + 8 ≤ initial.mem.pages * 65536 := by
    rw [hPointer]
    omega
  have hLengthWrites : ProofKit.Memory.WritesRange initial
      (writeLength initial target (UInt64.ofNat (left.size + right.size))) target.toNat
      (target.toNat + 8 * (left.size + right.size + 1)) :=
    ProofKit.Memory.WritesRange.write64 initial target.toUInt32 (UInt64.ofNat (left.size + right.size))
      _ _ (by rw [hPointer]) (by rw [hPointer]; omega)
  have hLeftStored := hLeft.writesRange hLengthWrites hSeparateLeft
  have hRightStored := hRight.writesRange hLengthWrites hSeparateRight
  have hResultValid : frame.validIndex 55 := by simp [Locals.validIndex, hParams, hLocals]
  rw [output_append_data_shape]
  simp only [List.append_assoc]
  apply resultProgram_spec 64 55 module env initial frame target hValues hTarget (by omega) hResultValid
  apply lengthStoreLocal_spec module env initial (resultFrame frame 55 target)
    target (UInt64.ofNat (left.size + right.size)) 55 52
    (resultFrame_get_result frame 55 target (by omega) hResultValid)
    ((resultFrame_get_ne frame 55 52 target (by omega) (by decide)).trans hTotalCount) hLengthBound
  refine output_append_copy_spec env _ (resultFrame frame 55 target) source upper target left right
    (by simpa only [Locals.validIndex, resultFrame_params, resultFrame_locals_length] using hCounter) rfl
    ((resultFrame_get_ne frame 55 48 target (by omega) (by decide)).trans hSource)
    ((resultFrame_get_ne frame 55 49 target (by omega) (by decide)).trans hUpper)
    (resultFrame_get_result frame 55 target (by omega) hResultValid)
    ((resultFrame_get_ne frame 55 53 target (by omega) (by decide)).trans hLeftCount)
    ((resultFrame_get_ne frame 55 54 target (by omega) (by decide)).trans hRightCount)
    hLeftStored hRightStored hTarget32 ?_ (ProofKit.Memory.read64_write64 ..)
    hSeparateLeft hSeparateRight Q rest ?_
  · simpa only [writeLength_pages] using hTargetMemory
  · intro final hWrites hFinalLeft hFinalRight hResult
    exact hNext final (hLengthWrites.trans hWrites) hFinalLeft hFinalRight hResult

#print axioms output_append_data_shape
#print axioms output_append_data_spec

end Project.EulerCertificate.Execution
