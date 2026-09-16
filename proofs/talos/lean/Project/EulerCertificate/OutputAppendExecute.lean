import Project.EulerCertificate.OutputAppendPrepare

namespace Project.EulerCertificate.Execution
open Project.EulerRiemann Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.ProofKit FixedArrayFold FixedArrayCopy FixedArrayCapacity

set_option maxRecDepth 4096

def outputAppendProgram : Wasm.Program := (func15.drop 257).take 71

theorem output_append_shape : outputAppendProgram =
    outputAppendPrepareProgram ++ FixedArrayAllocate.program 59 1 ++ outputAppendDataProgram ++
      resultProgram 55 42 := rfl

theorem certificate_word_capacity (size : Nat) (hSize : size ≤ 1280016) :
    (normalizedCapacity (UInt64.ofNat size) 1).toNat = 8 * (size + 1) := by
  have hWord : (UInt64.ofNat size).toNat = size := by
    exact UInt64.toNat_ofNat_of_lt (by change size < 18446744073709551616; omega)
  have hFit : 8 + (UInt64.ofNat size).toNat * (1 : UInt64).toNat * 8 + 7 < UInt64.size := by
    rw [hWord]
    change 8 + size * 1 * 8 + 7 < 18446744073709551616
    omega
  rw [normalizedCapacity_toNat_of_fits _ _ hFit, hWord]
  change 8 + size * 1 * 8 = 8 * (size + 1)
  omega

theorem output_append_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (frame : Locals) (source upper : FreeNode) (left right : Array UInt64)
    (hParams : frame.params.length = 17) (hLocals : frame.locals.length = 48)
    (hValues : frame.values = []) (hScratch : I64LocalRange frame 48 65)
    (hSource : frame.get (outputAppendSourceLocal) = some (.i64 source.root))
    (hUpper : frame.get (outputAppendUpperLocal) = some (.i64 upper.root))
    (hHeap : heap.At store) (hLeft : heap.OwnsWords store source left) (hRight : heap.OwnsWords store upper right)
    (hSize : left.size + right.size ≤ 1280016)
    (hBump : let need := normalizedCapacity (UInt64.ofNat (left.size + right.size)) 1
      takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat < 4294967296 ∧
      bumpPages heap.top need ≤ store.memoryCap module 0)
    (hPages : store.mem.pages ≤ 65536) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : let need := normalizedCapacity (UInt64.ofNat (left.size + right.size)) 1
      let target := allocatedNode heap.top need heap.nodes
      ∀ final result,
      (heap.allocate need).At final →
      (heap.allocate need).OwnsWords final source left →
      (heap.allocate need).OwnsWords final upper right →
      (heap.allocate need).OwnsWords final target (left ++ right) →
      ProofKit.Memory.WritesRange (heap.allocateArrayStore store need 1) final
        target.root.toNat (target.root.toNat + 8 * (left.size + right.size + 1)) →
      result.params.length = 17 → result.locals.length = 48 → result.values = [] →
      I64LocalRange result 48 65 →
      result.get 42 = some (.i64 target.root) →
      (∀ index : Nat, index < 48 → index ≠ 42 → result.get index = frame.get index) →
      wp module rest Q final result env) :
    wp module (outputAppendProgram ++ rest) Q store frame env := by
  let need := normalizedCapacity (UInt64.ofNat (left.size + right.size)) 1
  let prepared := outputAppendPreparedFrame frame source.root upper.root
    (UInt64.ofNat left.size) (UInt64.ofNat right.size)
  have hPreparedParams : prepared.params.length = 17 := hParams
  have hPreparedLocals : prepared.locals.length = 48 := by
    simpa only [prepared, outputAppendPreparedFrame, outputAppendCountsFrame, outputAppendLengthsFrame,
      resultFrame_locals_length] using hLocals
  have hPreparedScratch := output_append_prepared_scratch frame source.root upper.root
    (UInt64.ofNat left.size) (UInt64.ofNat right.size) hParams hLocals hScratch
  change I64LocalRange prepared 48 65 at hPreparedScratch
  have hGets := output_append_prepared_gets frame source.root upper.root
    (UInt64.ofNat left.size) (UInt64.ofNat right.size) hParams hLocals
  rw [← UInt64.ofNat_add] at hGets
  have hSaved : (prepared.locals.take 42).length = 42 := by simp [hPreparedLocals]
  have hTail : (prepared.locals.drop 48).length = 0 := by simp [hPreparedLocals]
  have hStart : prepared.params.length + (prepared.locals.take 42).length = 59 := by omega
  obtain ⟨requested, previous, current, capacity, next, root, hEq⟩ :=
    hPreparedScratch.window 42 (by omega) (by omega) (by omega) rfl
  have hNeedGet := FixedArraySearch.frame_get prepared.params (prepared.locals.take 42)
    (prepared.locals.drop 48) requested previous current capacity next root 0 (by decide)
  simp only [hStart, Nat.add_zero, List.getElem?_cons_zero] at hNeedGet
  rw [← hEq, hGets.2.2.2.2.2] at hNeedGet
  have hRequested : requested = need := (Value.i64.inj (Option.some.inj hNeedGet)).symm
  subst requested
  have hBefore (index : Nat) (hi : index < 59) :
      ({ params := prepared.params, locals := prepared.locals.take 42, values := [] } : Locals).get index =
        prepared.get index := by
    have hGet := FixedArraySearch.frame_get_before prepared.params (prepared.locals.take 42)
      (prepared.locals.drop 48) need previous current capacity next root index (by omega)
    rw [← hEq] at hGet
    exact hGet.symm
  have hNeed : 8 * (left.size + right.size + 1) ≤ need.toNat :=
    (certificate_word_capacity (left.size + right.size) hSize).ge
  rw [output_append_shape]
  simp only [List.append_assoc]
  apply output_append_prepare_spec env store frame source.root upper.root left right
    hParams hLocals hValues hSource hUpper hLeft.buffer.values hRight.buffer.values
  change wp module (FixedArrayAllocate.program 59 1 ++
    (outputAppendDataProgram ++ (resultProgram 55 42 ++ rest))) Q store prepared env
  rw [hEq]
  apply output_append_allocate_spec env store heap prepared.params (prepared.locals.take 42)
    (prepared.locals.drop 48) hPreparedParams hSaved hTail hStart need previous current capacity next root
    source upper left right hHeap hLeft hRight hNeed hBump hPages
    ((hBefore 48 (by decide)).trans hGets.1) ((hBefore 49 (by decide)).trans hGets.2.1)
    ((hBefore 52 (by decide)).trans hGets.2.2.1) ((hBefore 53 (by decide)).trans hGets.2.2.2.1)
    ((hBefore 54 (by decide)).trans hGets.2.2.2.2.1)
  intro previousAfter currentAfter capacityAfter nextAfter final hFinalHeap hLeftOwner hRightOwner hResultOwner hWrites
  let target := allocatedRoot heap.top need heap.nodes
  let allocated := FixedArraySearch.frame prepared.params (prepared.locals.take 42)
    (prepared.locals.drop 48) need previousAfter currentAfter capacityAfter nextAfter target
  let copied := outputAppendAllocationResult prepared.params (prepared.locals.take 42)
    (prepared.locals.drop 48) need previousAfter currentAfter capacityAfter nextAfter target right.size hStart
  have hAllocatedParams : allocated.params.length = 17 := hPreparedParams
  have hAllocatedLocals : allocated.locals.length = 48 := by
    simp [allocated, FixedArraySearch.frame, hSaved, hTail]
  have hAllocatedValid (index : Nat) (hi : index < 65) : allocated.validIndex index := by
    simpa only [Locals.validIndex, hAllocatedParams, hAllocatedLocals] using hi
  have hCopiedParams : copied.params.length = 17 := by
    simpa only [copied, outputAppendAllocationResult, counterFrame_params_length, resultFrame_params]
      using hAllocatedParams
  have hCopiedLocals : copied.locals.length = 48 := by
    simpa only [copied, outputAppendAllocationResult, counterFrame_locals_length, resultFrame_locals_length]
      using hAllocatedLocals
  have hAllocatedScratch : I64LocalRange allocated 48 65 := by
    have hOriginal := hPreparedScratch
    rw [hEq] at hOriginal
    exact hOriginal.search need previousAfter currentAfter capacityAfter nextAfter target
  have hCopiedScratch : I64LocalRange copied 48 65 :=
    (hAllocatedScratch.result 55 target (by omega) (hAllocatedValid 55 (by decide))).counter 56 right.size _
  have hTarget : copied.get 55 = some (.i64 target) := by
    dsimp only [copied, outputAppendAllocationResult]
    rw [counterFrame_get_ne _ _ _ _ _ (by decide)]
    exact resultFrame_get_result allocated 55 target (by omega) (hAllocatedValid 55 (by decide))
  have hReturnValid : copied.validIndex 42 := by simp [Locals.validIndex, hCopiedParams, hCopiedLocals]
  apply resultProgram_spec 55 42 module env final copied target rfl hTarget (by omega) hReturnValid
  apply hNext final (resultFrame copied 42 target) hFinalHeap hLeftOwner hRightOwner hResultOwner hWrites
  · exact hCopiedParams
  · simpa only [resultFrame_locals_length] using hCopiedLocals
  · rfl
  · exact hCopiedScratch.result 42 target (by omega) hReturnValid
  · exact resultFrame_get_result copied 42 target (by omega) hReturnValid
  · intro index hi hResultLocal
    rw [resultFrame_get_ne copied 42 index target (by omega) hResultLocal]
    dsimp only [copied, outputAppendAllocationResult]
    rw [counterFrame_get_ne _ _ _ _ _ (by omega),
      resultFrame_get_ne _ 55 index target (by change allocated.params.length ≤ 55; omega) (by omega)]
    have hAllocatedGet := FixedArraySearch.frame_get_before prepared.params (prepared.locals.take 42)
      (prepared.locals.drop 48) need previousAfter currentAfter capacityAfter nextAfter target index (by omega)
    exact hAllocatedGet.trans ((hBefore index (by omega)).trans
      (output_append_prepared_get_other frame source.root upper.root (UInt64.ofNat left.size)
        (UInt64.ofNat right.size) index hParams hi))

#print axioms certificate_word_capacity
#print axioms output_append_shape
#print axioms output_append_spec
end Project.EulerCertificate.Execution
