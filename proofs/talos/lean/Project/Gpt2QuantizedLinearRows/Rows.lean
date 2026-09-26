import Project.Gpt2QuantizedLinearRows.Bytes

namespace Project.Gpt2QuantizedLinearRows.QuantizeRows
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized

def scaleNode (heap : Heap) (rows : Nat) : FreeNode := allocatedNode heap.top (scaleNeed rows) heap.nodes

def valueNode (heap : Heap) (width rows : Nat) : FreeNode :=
  let next := heap.allocate (scaleNeed rows)
  allocatedNode next.top (byteNeed width rows) next.nodes

def outputHeap (heap : Heap) (width rows : Nat) : Heap :=
  (heap.allocate (scaleNeed rows)).allocate (byteNeed width rows)

structure Output (heap : Heap) (initial final : Store Unit) (input : ByteArray) (width rows : Nat) : Prop where
  heapAt : (outputHeap heap width rows).At final
  values : (outputHeap heap width rows).OwnsPacked final (valueNode heap width rows)
    (quantizeRows input width rows).values
  scales : (outputHeap heap width rows).OwnsPacked final (scaleNode heap rows)
    (quantizeRows input width rows).scales
  separated : regionsDisjoint (scaleNode heap rows).region (valueNode heap width rows).region
  frame : heap.Frame initial (outputHeap heap width rows) final
  pages : final.mem.pages ≤ 65536
  memoryCap : ∀ (module_ : Wasm.Module) (index : Nat),
    final.memoryCap module_ index = initial.memoryCap module_ index

end Project.Gpt2QuantizedLinearRows.QuantizeRows

namespace Project.Gpt2QuantizedLinearRows
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution QuantizeRows

set_option maxRecDepth 32768 in
theorem quantizeRows_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (owner ptr : UInt64) (input : ByteArray) (width rows : Nat)
    (hHeap : heap.At initial) (hInput : ByteArrayAt initial.mem ptr.toNat input)
    (hInputSize : rows * width * 4 ≤ input.size)
    (hInputProtected : heap.Protects ptr.toNat (ptr.toNat + input.size))
    (hCount : 4 * rows ≤ 2^32)
    (hScaleBump : takeFirstFitFrom 0 (scaleNeed rows) heap.nodes = none →
      heap.top.toNat + 48 + (scaleNeed rows).toNat < 4294967296 ∧
      FixedArrayBump.requiredPages heap.top (scaleNeed rows) ≤ initial.memoryCap «module» 0)
    (hByteBump : let next := heap.allocate (scaleNeed rows)
      takeFirstFitFrom 0 (byteNeed width rows) next.nodes = none →
        next.top.toNat + 48 + (byteNeed width rows).toNat < 4294967296 ∧
        FixedArrayBump.requiredPages next.top (byteNeed width rows) ≤ initial.memoryCap «module» 0)
    (hPages : initial.mem.pages ≤ 65536) :
    TerminatesWith env «module» 3 initial
      [.i64 (UInt64.ofNat rows), .i64 (UInt64.ofNat width),
        .i64 (UInt64.ofNat input.size), .i64 ptr, .i64 owner]
      (fun final values =>
        values = [.i64 (UInt64.ofNat (4 * rows)), .i64 (scaleNode heap rows).root,
          .i64 (scaleNode heap rows).root, .i64 (UInt64.ofNat (rows * width)),
          .i64 (valueNode heap width rows).root, .i64 (valueNode heap width rows).root] ∧
        QuantizeRows.Output heap initial final input width rows) := by
  have hByteCount : rows * width ≤ 2^32 := by have := hInput.1; omega
  have hSplit : func3 = func3.take 49 ++ (func3.drop 49).take 50 ++ func3.drop 99 := rfl
  refine TerminatesWith.of_wp_entry_for (f := func3Def) rfl ?_
  change wp «module» func3 _ initial
    { params := parameters owner ptr input width rows, locals := List.replicate 43 (.i64 0), values := [] } env
  rw [hSplit, List.append_assoc]
  apply scales_spec env initial heap owner ptr input width rows _ hHeap hInput hInputSize
    hInputProtected hCount hScaleBump hPages rfl rfl rfl (I64Values.replicate 43 0)
  intro scaleStore scaleFrame hScaleFrame hScaleOutput
  have hBytesBump : let next := heap.allocate (scaleNeed rows)
      takeFirstFitFrom 0 (byteNeed width rows) next.nodes = none →
        next.top.toNat + 48 + (byteNeed width rows).toNat < 4294967296 ∧
        FixedArrayBump.requiredPages next.top (byteNeed width rows) ≤ scaleStore.memoryCap «module» 0 := by
    dsimp only
    intro h
    exact ⟨(hByteBump h).1, by rw [hScaleOutput.memoryCap]; exact (hByteBump h).2⟩
  apply bytes_spec env scaleStore (heap.allocate (scaleNeed rows)) owner ptr
    (scaleNode heap rows).root input width rows scaleFrame hScaleOutput.heapAt
    (hScaleOutput.frame.packed hInputProtected hInput) hScaleOutput.owned.buffer.values hInputSize
    (hScaleOutput.frame.protects _ _ hInputProtected)
    (by simpa only [quantized_scales_size, scaleNode] using hScaleOutput.owned.payload_protects)
    hByteCount hBytesBump hScaleOutput.pages hScaleFrame
  intro final result hReady hState hByteOutput
  have hScaleFinal := hByteOutput.frame.ownsPacked hByteOutput.heapAt hScaleOutput.owned
  have hSeparated := hScaleOutput.owned.allocation_disjoint (byteNeed width rows)
    (fun h => (hByteBump h).1.le)
  have hOutput : QuantizeRows.Output heap initial final input width rows :=
    ⟨hByteOutput.heapAt, hByteOutput.owned, hScaleFinal, hSeparated,
      hScaleOutput.frame.trans hByteOutput.frame, hByteOutput.pages,
      fun module_ index => (hByteOutput.memoryCap module_ index).trans (hScaleOutput.memoryCap module_ index)⟩
  rcases hState with ⟨hParams, hLocals, hScaleOwner, hScalePtr, hScaleSize, hBytes, hTyped⟩
  have hPointer : result.locals[36]? = some (.i64 (valueNode heap width rows).root) := by
    simpa [Locals.get, hParams, parameters, hLocals, valueNode, allocatedNode] using hReady.2.2.2.1
  simp only [parameters] at hParams
  simp only [func3, List.drop]
  wp_packed_frame [hParams, hLocals, hReady.1, hPointer, hScaleOwner, hScalePtr, hScaleSize, hBytes]
  simpa [func3Def] using hOutput

#print axioms quantizeRows_exact

end Project.Gpt2QuantizedLinearRows
