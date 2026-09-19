import Project.Gpt2.PackedLinear
import Project.Gpt2.PackedVocabulary
import Project.Gpt2CachedStep.LinearRows.Heap
import Project.Gpt2CachedStep.Vocabulary.Source

/-! Explicit interfaces for controller composition. `Kernels` contains checked
shader semantics. `Code` is checked against the parsed module declarations.
`Host` is the external completed-execution/byte-transfer assumption, limited
to represented, protected input arrays and valid allocation resources. -/
namespace Project.Gpt2.PackedBackend
open Wasm LeanExe.WGSL Project.ProofKit PackedMemory Project.EulerRiemann.Execution

inductive Role where
  | qkv | attention | expansion | projection
  deriving DecidableEq

def Role.inner : Role → Nat
  | .projection => 3072
  | _ => 768

def Role.cols : Role → Nat
  | .qkv => 2304
  | .expansion => 3072
  | _ => 768

structure Kernels where
  text : Role → String
  checked : ∀ role, Statement.Implements (text role)
    ⟨1, role.cols, role.inner, role.inner * role.cols + role.cols⟩ (Gpt2Packed.biased role.inner role.cols)
  leftText : String
  rightText : String
  leftChecked : Statement.Implements leftText ⟨1, 25129, 768, 768 * 25129⟩ Matrix.Shader.vocabularyLeft.body
  rightChecked : Statement.Implements rightText ⟨1, 25128, 768, 768 * 25128⟩ Matrix.Shader.vocabularyRight.body

def linearImport : ImportDecl :=
  { «module» := "wgsl", name := "linear", params := List.replicate 12 .i64 }
def vocabularyImport : ImportDecl :=
  { «module» := "wgsl", name := "vocabulary", params := List.replicate 7 .i64 }

class Code (module_ : Wasm.Module) : Prop where
  linear : module_.funcs[23 - module_.imports.length]? = some PackedWrapper.linear
  linearDefined : module_.imports[23]? = none
  vocabulary : module_.funcs[39 - module_.imports.length]? = some PackedVocabulary.wrapper
  vocabularyDefined : module_.imports[39]? = none
  alloc : module_.funcs[41 - module_.imports.length]? = some (PackedAllocExport.function (some 39))
  allocDefined : module_.imports[41]? = none
  memory : module_.memIs64 = false
  linearImport : module_.imports[0]? = some linearImport
  vocabularyImport : module_.imports[1]? = some vocabularyImport

class Host (module_ : Wasm.Module) (env : HostEnv Unit) (kernels : Kernels) : Prop where
  linear : ∃ host : HostFn Unit, env.funcs[0]? = some host ∧
    ∀ (role : Role) (initial : Store Unit) (heap : Heap)
      (weightsOwner weightsPtr inputOwner inputPtr : UInt64) (weights input : ByteArray)
      (weightOffset biasOffset : Nat),
      heap.At initial → ByteArrayAt initial.mem weightsPtr.toNat weights →
      ByteArrayAt initial.mem inputPtr.toNat input →
      heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size) →
      heap.Protects inputPtr.toNat (inputPtr.toNat + input.size) →
      role.inner * 4 ≤ input.size → (weightOffset + role.inner * role.cols) * 4 ≤ weights.size →
      (biasOffset + role.cols) * 4 ≤ weights.size →
      (Project.Runtime.takeFirstFitFrom 0 (PackedLinear.need role.cols) heap.nodes = none →
        heap.top.toNat + 48 + (PackedLinear.need role.cols).toNat < 4294967296 ∧
        FixedArrayBump.requiredPages heap.top (PackedLinear.need role.cols) ≤ initial.memoryCap module_ 0) →
      initial.mem.pages ≤ 65536 →
      host.invoke (heap.allocatePackedStore initial (PackedLinear.need role.cols))
        (PackedLinear.parameters weightsOwner weightsPtr inputOwner inputPtr weights input
          (UInt64.ofNat weightOffset) (UInt64.ofNat biasOffset) role.inner role.cols ++
          [.i64 (allocatedRoot heap.top (PackedLinear.need role.cols) heap.nodes)]) =
        .Return [] (PackedCall.complete heap initial (PackedLinear.need role.cols)
          (PackedBody.biasedBytes (kernels.text role) weights input weightOffset biasOffset role.inner role.cols))
  vocabulary : ∃ host : HostFn Unit, env.funcs[1]? = some host ∧
    ∀ (initial : Store Unit) (heap : Heap)
      (weightsOwner weightsPtr inputOwner inputPtr : UInt64) (weights input : ByteArray),
      heap.At initial → ByteArrayAt initial.mem weightsPtr.toNat weights →
      ByteArrayAt initial.mem inputPtr.toNat input →
      heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size) →
      heap.Protects inputPtr.toNat (inputPtr.toNat + input.size) →
      3072 ≤ input.size → 154389504 ≤ weights.size →
      (Project.Runtime.takeFirstFitFrom 0 201032 heap.nodes = none →
        heap.top.toNat + 48 + 201032 < 4294967296 ∧
        FixedArrayBump.requiredPages heap.top 201032 ≤ initial.memoryCap module_ 0) →
      initial.mem.pages ≤ 65536 →
      host.invoke (heap.allocatePackedStore initial 201032)
        (PackedVocabulary.parameters weightsOwner weightsPtr inputOwner inputPtr weights input ++
          [.i64 (allocatedRoot heap.top 201032 heap.nodes)]) =
        .Return [] (PackedCall.complete heap initial 201032
          (PackedBody.vocabularyBytes kernels.leftText kernels.rightText weights input))

theorem linear_exact (module_ : Wasm.Module) (env : HostEnv Unit) (kernels : Kernels)
    [Code module_] [Host module_ env kernels]
    (role : Role) (initial : Store Unit) (heap : Heap)
    (weightsOwner weightsPtr inputOwner inputPtr : UInt64) (weights input : ByteArray)
    (weightOffset biasOffset : Nat)
    (hHeap : heap.At initial) (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hInput : ByteArrayAt initial.mem inputPtr.toNat input)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hInputProtected : heap.Protects inputPtr.toNat (inputPtr.toNat + input.size))
    (hInputSize : role.inner * 4 ≤ input.size)
    (hWeightSize : (weightOffset + role.inner * role.cols) * 4 ≤ weights.size)
    (hBiasSize : (biasOffset + role.cols) * 4 ≤ weights.size)
    (hBump : Project.Runtime.takeFirstFitFrom 0 (PackedLinear.need role.cols) heap.nodes = none →
      heap.top.toNat + 48 + (PackedLinear.need role.cols).toNat < 4294967296 ∧
      FixedArrayBump.requiredPages heap.top (PackedLinear.need role.cols) ≤ initial.memoryCap module_ 0)
    (hPages : initial.mem.pages ≤ 65536) :
    TerminatesWith env module_ 23 initial
      (PackedLinear.parameters weightsOwner weightsPtr inputOwner inputPtr weights input
        (UInt64.ofNat weightOffset) (UInt64.ofNat biasOffset) role.inner role.cols).reverse
      (fun final values =>
        values = [.i64 (PackedLinear.bytes role.cols),
          .i64 (allocatedRoot heap.top (PackedLinear.need role.cols) heap.nodes),
          .i64 (allocatedRoot heap.top (PackedLinear.need role.cols) heap.nodes)] ∧
        heap.PackedOutput initial final (PackedLinear.need role.cols)
          (LeanExe.Models.Gpt2.linearRows weights input weightOffset biasOffset role.inner role.cols 1)) := by
  have hWeight64 : weightOffset < UInt64.size := by have := hWeights.1; change weightOffset < 18446744073709551616; omega
  have hBias64 : biasOffset < UInt64.size := by have := hWeights.1; change biasOffset < 18446744073709551616; omega
  obtain ⟨host, hHost, hRun⟩ := Host.linear (module_ := module_) (env := env) (kernels := kernels)
  have h := PackedLinear.exact module_ env Code.linear Code.linearDefined Code.alloc Code.allocDefined Code.memory
    linearImport host Code.linearImport hHost rfl rfl _ role.inner role.cols (kernels.checked role)
    (by cases role <;> decide) initial heap hHeap weightsOwner weightsPtr inputOwner inputPtr weights input
    (UInt64.ofNat weightOffset) (UInt64.ofNat biasOffset) hBump hPages
  simp only [UInt64.toNat_ofNat_of_lt' hWeight64, UInt64.toNat_ofNat_of_lt' hBias64] at h
  exact h (hRun role initial heap weightsOwner weightsPtr inputOwner inputPtr weights input weightOffset biasOffset
    hHeap hWeights hInput hWeightsProtected hInputProtected hInputSize hWeightSize hBiasSize hBump hPages)

theorem linear_owned (module_ : Wasm.Module) (env : HostEnv Unit) (kernels : Kernels)
    [Code module_] [Host module_ env kernels]
    (role : Role) (initial : Store Unit) (heap : Heap)
    (weightsOwner inputOwner weightsPtr inputPtr : UInt64) (weights input : ByteArray)
    (weightOffset biasOffset : Nat)
    (hHeap : heap.At initial) (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hInput : ByteArrayAt initial.mem inputPtr.toNat input)
    (hInputSize : 1 * role.inner * 4 ≤ input.size)
    (hWeightSize : (weightOffset + role.inner * role.cols) * 4 ≤ weights.size)
    (hBiasSize : (biasOffset + role.cols) * 4 ≤ weights.size)
    (hBump : Project.Runtime.takeFirstFitFrom 0 (PackedLinear.need role.cols) heap.nodes = none →
      heap.top.toNat + 48 + PackedCapacity.capacityNat (4 * (1 * role.cols)) < 2^32 ∧
      FixedArrayBump.requiredPages heap.top (PackedLinear.need role.cols) ≤ initial.memoryCap module_ 0)
    (hPages : initial.mem.pages ≤ 65536)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hInputProtected : heap.Protects inputPtr.toNat (inputPtr.toNat + input.size)) :
    let need := PackedLinear.need role.cols
    let node := allocatedNode heap.top need heap.nodes
    let result := LeanExe.Models.Gpt2.linearRows weights input weightOffset biasOffset role.inner role.cols 1
    TerminatesWith env module_ 23 initial
      [.i64 1, .i64 (UInt64.ofNat role.cols), .i64 (UInt64.ofNat role.inner),
       .i64 (UInt64.ofNat biasOffset), .i64 (UInt64.ofNat weightOffset),
       .i64 (UInt64.ofNat input.size), .i64 inputPtr, .i64 inputOwner,
       .i64 (UInt64.ofNat weights.size), .i64 weightsPtr, .i64 weightsOwner]
      (fun final values =>
        values = [.i64 (UInt64.ofNat result.size), .i64 node.root, .i64 node.root] ∧
        (heap.allocate need).At final ∧ (heap.allocate need).OwnsPacked final node result ∧
        heap.Frame initial (heap.allocate need) final ∧ final.mem.pages ≤ 65536 ∧
        final.memoryCap module_ 0 = initial.memoryCap module_ 0) := by
  have hCapacity : (PackedLinear.need role.cols).toNat = PackedCapacity.capacityNat (4 * (1 * role.cols)) := by
    cases role <;> decide
  have hCall := linear_exact module_ env kernels role initial heap weightsOwner weightsPtr inputOwner inputPtr
    weights input weightOffset biasOffset hHeap hWeights hInput hWeightsProtected hInputProtected
    (by simpa using hInputSize) hWeightSize hBiasSize
    (fun h => ⟨by rw [hCapacity]; exact (hBump h).1, (hBump h).2⟩) hPages
  apply hCall.mono
  rintro final values ⟨hValues, hOutput⟩
  refine ⟨?_, hOutput.heapAt, hOutput.owned, hOutput.frame, hOutput.pages, hOutput.memoryCap module_ 0⟩
  simpa [Project.Gpt2LinearRows.linearRows_eq, PackedSource.generate_size,
    PackedLinear.bytes, allocatedNode] using hValues

theorem vocabulary_exact (module_ : Wasm.Module) (env : HostEnv Unit) (kernels : Kernels)
    [Code module_] [Host module_ env kernels]
    (initial : Store Unit) (heap : Heap)
    (weightsOwner inputOwner weightsPtr inputPtr : UInt64) (weights input : ByteArray)
    (hHeap : heap.At initial) (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hInput : ByteArrayAt initial.mem inputPtr.toNat input)
    (hWeightsSize : 50257 * 768 * 4 ≤ weights.size) (hInputSize : 3072 ≤ input.size)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hInputProtected : heap.Protects inputPtr.toNat (inputPtr.toNat + input.size))
    (hBump : Project.Runtime.takeFirstFitFrom 0 201032 heap.nodes = none →
      heap.top.toNat + 48 + 201032 < 4294967296 ∧
      FixedArrayBump.requiredPages heap.top 201032 ≤ initial.memoryCap module_ 0)
    (hPages : initial.mem.pages ≤ 65536) :
    TerminatesWith env module_ 39 initial
      [.i64 (UInt64.ofNat input.size), .i64 inputPtr, .i64 inputOwner,
       .i64 (UInt64.ofNat weights.size), .i64 weightsPtr, .i64 weightsOwner]
      (fun final values =>
        values = [.i64 (UInt64.ofNat (LeanExe.Models.Gpt2.vocabularyHead weights input).size),
          .i64 (allocatedRoot heap.top 201032 heap.nodes), .i64 (allocatedRoot heap.top 201032 heap.nodes)] ∧
        heap.PackedOutput initial final 201032 (LeanExe.Models.Gpt2.vocabularyHead weights input)) := by
  obtain ⟨host, hHost, hRun⟩ := Host.vocabulary (module_ := module_) (env := env) (kernels := kernels)
  simpa [Project.Gpt2CachedStep.Vocabulary.vocabularyHead_eq, PackedSource.generate_size,
    PackedVocabulary.parameters] using
    PackedVocabulary.exact module_ env Code.vocabulary Code.vocabularyDefined Code.alloc Code.allocDefined Code.memory
      vocabularyImport host Code.vocabularyImport hHost rfl rfl _ _ kernels.leftChecked kernels.rightChecked
      initial heap hHeap weightsOwner weightsPtr inputOwner inputPtr weights input hBump hPages
      (hRun initial heap weightsOwner weightsPtr inputOwner inputPtr weights input hHeap hWeights hInput
        hWeightsProtected hInputProtected hInputSize hWeightsSize hBump hPages)

#print axioms linear_exact
#print axioms linear_owned
#print axioms vocabulary_exact
end Project.Gpt2.PackedBackend
