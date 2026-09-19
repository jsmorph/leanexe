import Project.Gpt2.PackedShader
import Project.ProofKit.PackedInput

/-! Store effects of allocating an output and copying completed shader words.
This is a transfer/ownership lemma. A theorem for the concrete Wasm caller
must additionally prove that its instructions implement these effects. -/
namespace Project.Gpt2.PackedCall
open Wasm LeanExe.WGSL Project.ProofKit Project.EulerRiemann.Execution

def complete (heap : Heap) (initial : Store Unit) (need : UInt64) (output : ByteArray) : Store Unit :=
  PackedInput.write (heap.allocatePackedStore initial need)
    (allocatedRoot heap.top need heap.nodes).toNat output

theorem biased_contract (text : String) (inner cols : Nat)
    (checked : Statement.Implements text ⟨1, cols, inner, inner * cols + cols⟩
      (Gpt2Packed.biased inner cols))
    (weights input : ByteArray) (weightOffset biasOffset : Nat) (hcols : cols < 4294967296)
    (heap : Heap) (initial : Store Unit) (need : UInt64)
    (hHeap : heap.At initial) (hNeed : 4 * cols ≤ need.toNat)
    (hBump : Project.Runtime.takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat < 4294967296) (hPages : initial.mem.pages ≤ 65536) :
    heap.PackedOutput initial
      (complete heap initial need (PackedBody.biasedBytes text weights input weightOffset biasOffset inner cols))
      need (LeanExe.Models.Gpt2.linearRows weights input weightOffset biasOffset inner cols 1) := by
  rw [PackedBody.biasedBytes_exact text inner cols checked weights input weightOffset biasOffset hcols]
  apply PackedInput.allocated heap initial need _ hHeap _ hBump hPages
  simpa only [Project.Gpt2LinearRows.linearRows_eq, PackedSource.generate_size, Nat.one_mul] using hNeed

theorem vocabulary_contract (leftText rightText : String)
    (leftChecked : Statement.Implements leftText ⟨1, 25129, 768, 768 * 25129⟩ Matrix.Shader.vocabularyLeft.body)
    (rightChecked : Statement.Implements rightText ⟨1, 25128, 768, 768 * 25128⟩ Matrix.Shader.vocabularyRight.body)
    (weights input : ByteArray) (heap : Heap) (initial : Store Unit) (need : UInt64)
    (hHeap : heap.At initial) (hNeed : 201028 ≤ need.toNat)
    (hBump : Project.Runtime.takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat < 4294967296) (hPages : initial.mem.pages ≤ 65536) :
    heap.PackedOutput initial
      (complete heap initial need (PackedBody.vocabularyBytes leftText rightText weights input))
      need (LeanExe.Models.Gpt2.vocabularyHead weights input) := by
  rw [PackedBody.vocabularyBytes_exact leftText rightText leftChecked rightChecked weights input]
  apply PackedInput.allocated heap initial need _ hHeap _ hBump hPages
  simpa only [Project.Gpt2CachedStep.Vocabulary.vocabularyHead_eq, PackedSource.generate_size] using hNeed

/-- The represented bytes plus the complete write frame determine the whole
store, including every non-memory field and bytes outside the output. -/
theorem write_unique (initial final : Store Unit) (base : Nat) (bytes : ByteArray)
    (hWrites : Memory.WritesRange initial final base (base + bytes.size))
    (hBytes : PackedMemory.ByteArrayAt final.mem base bytes) :
    final = PackedInput.write initial base bytes := by
  have hMemory : final.mem = (PackedInput.write initial base bytes).mem := by
    apply congrArg₂ Mem.mk hWrites.2.1
    funext address
    by_cases hi : base ≤ address ∧ address < base + bytes.size
    · have h := hBytes.2.2 (address - base) (by omega)
      simpa [PackedInput.write, hi, Nat.add_sub_of_le hi.1] using h
    · simpa [PackedInput.write, hi] using hWrites.2.2 address (by omega)
  calc
    final = { initial with mem := final.mem } := hWrites.1
    _ = PackedInput.write initial base bytes := by rw [hMemory]; rfl

#print axioms biased_contract
#print axioms vocabulary_contract
#print axioms write_unique

end Project.Gpt2.PackedCall
