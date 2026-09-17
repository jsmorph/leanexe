import Project.TinyGpt2Checked.OutputCode

namespace Project.TinyGpt2Checked.Spec
open Wasm Project.ProofKit

theorem output_copy_spec (env : HostEnv Unit) (initial : Store Unit) (frame : Locals)
    (source target : UInt64) (input : Array UInt64) (value : UInt64)
    (hCounter : frame.validIndex 55) (hValues : frame.values = [])
    (hSource : frame.get 50 = some (.i64 source))
    (hTarget : frame.get 54 = some (.i64 target))
    (hCount : frame.get 52 = some (.i64 (UInt64.ofNat input.size)))
    (hLength : frame.get 51 = some (.i64 (UInt64.ofNat input.size)))
    (hValue : frame.get 56 = some (.i64 value))
    (hInput : UInt64Array.At initial source input)
    (hFit : target.toNat + 8 * (input.size + 2) ≤ 4294967296)
    (hMemory : target.toNat + 8 * (input.size + 2) ≤ initial.mem.pages * 65536)
    (hHeader : initial.mem.read64 target.toUInt32 = UInt64.ofNat (input.size + 1))
    (hSeparate : source.toNat + 8 * (input.size + 1) ≤ target.toNat ∨
      target.toNat + 8 * (input.size + 2) ≤ source.toNat)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final : Store Unit,
      Memory.WritesRange initial final target.toNat (target.toNat + 8 * (input.size + 2)) →
      UInt64Array.At final source input → UInt64Array.At final target (input.push value) →
      wp module rest Q final (FixedArrayCopy.counterFrame frame 55 input.size hCounter) env) :
    wp module ((outputBody.drop 88).take 15 ++ rest) Q initial frame env := by
  rw [output_copy_shape]
  exact UInt64Array.pushCopy_spec 50 54 52 51 55 56 module env initial frame source target input value
    hCounter hValues (by decide) (by decide) (by decide) (by decide) (by decide)
    hSource hTarget hCount hLength hValue hInput hFit hMemory hHeader hSeparate Q rest hNext

#print axioms output_copy_spec
end Project.TinyGpt2Checked.Spec
