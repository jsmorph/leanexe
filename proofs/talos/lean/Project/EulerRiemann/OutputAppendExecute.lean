import Project.EulerRiemann.OutputAppendPrepare

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.ProofKit FixedArrayFold FixedArrayCopy FixedArrayCapacity

def outputAppendOwnerLocal (header : Bool) : Nat := if header then 31 else 26

def outputAppendProgram (header : Bool) : Wasm.Program :=
  (func99.drop (if header then 280 else 104)).take 73

set_option maxRecDepth 2048 in
theorem output_append_shape (header : Bool) : outputAppendProgram header =
    outputAppendPrepareProgram header ++ FixedArrayAllocate.program 47 1 ++ outputAppendDataProgram header ++
      resultProgram 43 (outputAppendOwnerLocal header) ++
      resultProgram (outputAppendOwnerLocal header) (outputAppendOwnerLocal header + 1) := by
  cases header <;> rfl

theorem output_append_spec (header : Bool) (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (frame : Locals) (source upper : FreeNode) (left right : Array UInt64)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 52)
    (hValues : frame.values = []) (hScratch : I64LocalRange frame 42 57)
    (hSource : frame.get (outputAppendSourceLocal header) = some (.i64 source.root))
    (hUpper : frame.get (outputAppendUpperLocal header) = some (.i64 upper.root))
    (hHeap : heap.At store) (hLeft : heap.OwnsWords store source left) (hRight : heap.OwnsWords store upper right)
    (hSize : left.size + right.size ≤ 1280004)
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
      result.params.length = 5 → result.locals.length = 52 → result.values = [] →
      I64LocalRange result 42 57 →
      result.get (outputAppendOwnerLocal header) = some (.i64 target.root) →
      result.get (outputAppendOwnerLocal header + 1) = some (.i64 target.root) →
      (∀ index : Nat, index < 36 → index ≠ outputAppendOwnerLocal header →
        index ≠ outputAppendOwnerLocal header + 1 → result.get index = frame.get index) →
      wp module rest Q final result env) :
    wp module (outputAppendProgram header ++ rest) Q store frame env := by
  let need := normalizedCapacity (UInt64.ofNat (left.size + right.size)) 1
  let prepared := outputAppendPreparedFrame frame source.root upper.root
    (UInt64.ofNat left.size) (UInt64.ofNat right.size)
  have hPreparedParams : prepared.params.length = 5 := hParams
  have hPreparedLocals : prepared.locals.length = 52 := by
    simpa only [prepared, outputAppendPreparedFrame, outputAppendCountsFrame, outputAppendLengthsFrame,
      resultFrame_locals_length] using hLocals
  have hPreparedScratch := output_append_prepared_scratch frame source.root upper.root
    (UInt64.ofNat left.size) (UInt64.ofNat right.size) hParams hLocals hScratch
  change I64LocalRange prepared 42 57 at hPreparedScratch
  have hGets := output_append_prepared_gets frame source.root upper.root
    (UInt64.ofNat left.size) (UInt64.ofNat right.size) hParams hLocals
  rw [← UInt64.ofNat_add] at hGets
  have hSaved : (prepared.locals.take 42).length = 42 := by simp [hPreparedLocals]
  have hTail : (prepared.locals.drop 48).length = 4 := by simp [hPreparedLocals]
  have hStart : prepared.params.length + (prepared.locals.take 42).length = 47 := by omega
  obtain ⟨requested, previous, current, capacity, next, root, hEq⟩ :=
    hPreparedScratch.window 42 (by omega) (by omega) (by omega) rfl
  have hNeedGet := FixedArraySearch.frame_get prepared.params (prepared.locals.take 42)
    (prepared.locals.drop 48) requested previous current capacity next root 0 (by decide)
  simp only [hStart, Nat.add_zero, List.getElem?_cons_zero] at hNeedGet
  rw [← hEq, hGets.2.2.2.2.2] at hNeedGet
  have hRequested : requested = need := (Value.i64.inj (Option.some.inj hNeedGet)).symm
  subst requested
  have hBefore (index : Nat) (hi : index < 47) :
      ({ params := prepared.params, locals := prepared.locals.take 42, values := [] } : Locals).get index =
        prepared.get index := by
    have hGet := FixedArraySearch.frame_get_before prepared.params (prepared.locals.take 42)
      (prepared.locals.drop 48) need previous current capacity next root index (by omega)
    rw [← hEq] at hGet
    exact hGet.symm
  have hNeed : 8 * (left.size + right.size + 1) ≤ need.toNat :=
    (output_word_capacity (left.size + right.size) hSize).ge
  rw [output_append_shape]
  simp only [List.append_assoc]
  apply output_append_prepare_spec header env store frame source.root upper.root left right
    hParams hLocals hValues hSource hUpper hLeft.buffer.values hRight.buffer.values
  change wp module (FixedArrayAllocate.program 47 1 ++ (outputAppendDataProgram header ++
    (resultProgram 43 (outputAppendOwnerLocal header) ++
      (resultProgram (outputAppendOwnerLocal header) (outputAppendOwnerLocal header + 1) ++ rest))))
    Q store prepared env
  rw [hEq]
  apply output_append_allocate_spec header env store heap prepared.params (prepared.locals.take 42)
    (prepared.locals.drop 48) hPreparedParams hSaved hTail hStart need previous current capacity next root
    source upper left right hHeap hLeft hRight hNeed hBump hPages
    ((hBefore 36 (by decide)).trans hGets.1) ((hBefore 37 (by decide)).trans hGets.2.1)
    ((hBefore 40 (by decide)).trans hGets.2.2.1) ((hBefore 41 (by decide)).trans hGets.2.2.2.1)
    ((hBefore 42 (by decide)).trans hGets.2.2.2.2.1)
  intro previousAfter currentAfter capacityAfter nextAfter final hFinalHeap hLeftOwner hRightOwner hResultOwner hWrites
  let target := allocatedRoot heap.top need heap.nodes
  let allocated := FixedArraySearch.frame prepared.params (prepared.locals.take 42)
    (prepared.locals.drop 48) need previousAfter currentAfter capacityAfter nextAfter target
  let copied := outputAppendAllocationResult prepared.params (prepared.locals.take 42)
    (prepared.locals.drop 48) need previousAfter currentAfter capacityAfter nextAfter target right.size hStart
  have hAllocatedParams : allocated.params.length = 5 := hPreparedParams
  have hAllocatedLocals : allocated.locals.length = 52 := by
    simp [allocated, FixedArraySearch.frame, hSaved, hTail]
  have hAllocatedValid (index : Nat) (hi : index < 57) : allocated.validIndex index := by
    simpa only [Locals.validIndex, hAllocatedParams, hAllocatedLocals] using hi
  have hCopiedParams : copied.params.length = 5 := by
    simpa only [copied, outputAppendAllocationResult, counterFrame_params_length, resultFrame_params]
      using hAllocatedParams
  have hCopiedLocals : copied.locals.length = 52 := by
    simpa only [copied, outputAppendAllocationResult, counterFrame_locals_length, resultFrame_locals_length]
      using hAllocatedLocals
  have hAllocatedScratch : I64LocalRange allocated 42 57 := by
    have hOriginal := hPreparedScratch
    rw [hEq] at hOriginal
    exact hOriginal.search need previousAfter currentAfter capacityAfter nextAfter target
  have hCopiedScratch : I64LocalRange copied 42 57 :=
    (hAllocatedScratch.result 43 target (by omega) (hAllocatedValid 43 (by decide))).counter 44 right.size _
  have hTarget : copied.get 43 = some (.i64 target) := by
    dsimp only [copied, outputAppendAllocationResult]
    rw [counterFrame_get_ne _ _ _ _ _ (by decide)]
    exact resultFrame_get_result allocated 43 target (by omega) (hAllocatedValid 43 (by decide))
  have hBounds : 5 ≤ outputAppendOwnerLocal header ∧ outputAppendOwnerLocal header + 1 < 36 := by
    cases header <;> decide
  have hReturnValid : copied.validIndex (outputAppendOwnerLocal header) := by
    simp only [Locals.validIndex, hCopiedParams, hCopiedLocals]
    omega
  let first := resultFrame copied (outputAppendOwnerLocal header) target
  have hFirstParams : first.params.length = 5 := hCopiedParams
  have hFirstLocals : first.locals.length = 52 := by simpa only [first, resultFrame_locals_length] using hCopiedLocals
  have hFirstRoot : first.get (outputAppendOwnerLocal header) = some (.i64 target) :=
    resultFrame_get_result copied _ target (by omega) hReturnValid
  have hPointerValid : first.validIndex (outputAppendOwnerLocal header + 1) := by
    simp only [Locals.validIndex, hFirstParams, hFirstLocals]
    omega
  apply resultProgram_spec 43 (outputAppendOwnerLocal header) module env final copied target rfl hTarget
    (by omega) hReturnValid
  apply resultProgram_spec (outputAppendOwnerLocal header) (outputAppendOwnerLocal header + 1)
    module env final first target rfl hFirstRoot (by omega) hPointerValid
  apply hNext final (resultFrame first (outputAppendOwnerLocal header + 1) target)
    hFinalHeap hLeftOwner hRightOwner hResultOwner hWrites
  · exact hFirstParams
  · simpa only [resultFrame_locals_length] using hFirstLocals
  · rfl
  · exact ((hCopiedScratch.result _ target (by omega) hReturnValid).result _ target
      (by change first.params.length ≤ outputAppendOwnerLocal header + 1; omega) hPointerValid)
  · exact (resultFrame_get_ne first _ _ target (by omega) (by omega)).trans hFirstRoot
  · exact resultFrame_get_result first _ target (by omega) hPointerValid
  · intro index hi hOwnerLocal hPointerLocal
    rw [resultFrame_get_ne first _ index target (by omega) hPointerLocal]
    dsimp only [first]
    rw [resultFrame_get_ne copied _ index target (by omega) hOwnerLocal]
    dsimp only [copied, outputAppendAllocationResult]
    rw [counterFrame_get_ne _ _ _ _ _ (by omega),
      resultFrame_get_ne _ 43 index target (by change allocated.params.length ≤ 43; omega) (by omega)]
    have hAllocatedGet := FixedArraySearch.frame_get_before prepared.params (prepared.locals.take 42)
      (prepared.locals.drop 48) need previousAfter currentAfter capacityAfter nextAfter target index (by omega)
    exact hAllocatedGet.trans ((hBefore index (by omega)).trans
      (output_append_prepared_get_other frame source.root upper.root (UInt64.ofNat left.size)
        (UInt64.ofNat right.size) index hParams hi))

#print axioms output_append_shape
#print axioms output_append_spec

end Project.EulerRiemann.Execution
