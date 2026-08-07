import LeanExeGen.GeneratedRc77513211b55010d.FormalSpec
import LeanExeGen.GeneratedRc77513211b55010d.Program
import LeanExeGen.GeneratedRc77513211b55010d.AnnotationMatches
import Project.ProofKit.Array
import Project.ProofKit.Allocation
import Project.ProofKit.FixedArrayAllocatorWindow
import Project.ProofKit.FixedArrayResult

set_option maxRecDepth 1048576
set_option maxHeartbeats 8000000

namespace LeanExeGen.GeneratedRc77513211b55010d.Behavior

open Wasm Project.ProofKit

macro "wp_run16" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  simp (config := { maxSteps := 10000000 }) (discharger := omega) [wp_simp,
    Wasm.Locals.get, Wasm.Locals.set?, Wasm.Locals.validIndex,
    Wasm.Function.toLocals, Wasm.Function.numParams, Wasm.Function.numLocals,
    List.take, List.drop, List.replicate, List.length, List.map,
    List.length_set, List.getElem?_set, List.getElem?_cons_zero,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceSub,
    Wasm.ValueType.zero, List.headD, $ts,*])

def elementAddress (ptr : UInt64) (index : Nat) : UInt32 :=
  (ptr + (UInt64.ofNat index * 1 + 1) * 8).toUInt32

theorem elementOffset_eq (index : Nat) (_hIndex : index ≤ 8) :
    (UInt64.ofNat index * 1 + 1) * 8 = UInt64.ofNat (8 * (index + 1)) := by
  apply UInt64.toNat.inj
  simp (discharger := omega) [UInt64.toNat_mul, UInt64.toNat_add,
    Nat.mul_comm]

theorem elementAddress_eq (ptr : UInt64) (index : Nat) (hIndex : index ≤ 8) :
    elementAddress ptr index =
      (ptr + UInt64.ofNat (8 * (index + 1))).toUInt32 := by
  unfold elementAddress
  rw [elementOffset_eq index hIndex]

def mapFrame (base : Locals) (index : Nat) (value : UInt64) : Locals :=
  { base with
    locals := (base.locals.set 0 (.i64 value)).set 7 (.i64 (UInt64.ofNat index))
    values := [] }

def mapInv (initial : Store Unit) (inputPtr outputPtr : UInt64)
    (input : Array UInt64) (base : Locals) : AssertionF Unit :=
  fun st frame =>
    ∃ index value, index ≤ input.size ∧ frame = mapFrame base index value ∧
      st.mem.pages = initial.mem.pages ∧ UInt64Array.At st inputPtr input ∧
      st.mem.read64 outputPtr.toUInt32 = UInt64.ofNat input.size ∧
      ∀ i, (hiInput : i < input.size) → i < index →
        st.mem.read64 (elementAddress outputPtr i) =
          input[i]'hiInput + 1

def mapMeasure (size : Nat) (_ : Store Unit) (frame : Locals) : Nat :=
  match frame.locals[7]? with
  | some (Value.i64 index) => size - index.toNat
  | _ => 0

theorem artifact_behavior :
    LeanExeGen.GeneratedRc77513211b55010d.FormalSpec.ArtifactSpec LeanExeGen.GeneratedRc77513211b55010d.«module» := by
  refine ⟨0, rfl, ?_⟩
  intro env initial inputPtr input hInput
  rcases hInput with
    ⟨hArray, heapTop, allocs, retains, releases, frees, hGlobals,
      hInputBelow, hFit32, hFitMemory, hPages⟩
  change UInt64Array.At initial inputPtr input at hArray
  have hLengthRead := hArray.lengthRead
  have hLengthBound := hArray.generatedLengthBound
  have hInputAddress := hArray.pointerAddress_eq
  have hHeapTop : initial.globals.globals[0]? = some (.i64 heapTop) := by
    simp [hGlobals]
  have hFreeList : initial.globals.globals[1]? = some (.i64 0) := by
    simp [hGlobals]
  have hAllocs : initial.globals.globals[2]? = some (.i64 allocs) := by
    simp [hGlobals]
  apply TerminatesWith.of_wp_entry_for (f := func0Def)
  · rfl
  · change wp «module» func0 _ initial
      { params := [.i64 inputPtr],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0],
        values := [] } env
    unfold func0
    wp_run16 [hInputAddress, hLengthBound, hLengthRead]
    refine wp_iff_cons rfl ?_
    by_cases hSize : input.size ≤ 8
    · have hEncoded : UInt64.ofNat input.size ≤ 8 := by
        rw [UInt64.le_iff_toNat_le,
          UInt64.toNat_ofNat_of_lt' hArray.size_lt]
        change input.size ≤ 8
        exact hSize
      rw [if_pos (by simp [hEncoded])]
      wp_run16 [hInputAddress, hLengthBound, hLengthRead]
      let capacity : UInt64 :=
        (8 + UInt64.ofNat input.size * 8 + 7) / 8 * 8
      have hInputSizeNat : (UInt64.ofNat input.size).toNat = input.size :=
        UInt64.toNat_ofNat_of_lt' hArray.size_lt
      have hCapacityNat : capacity.toNat = 8 * (input.size + 1) := by
        simp (discharger := omega) [capacity, UInt64.toNat_mul,
          UInt64.toNat_div, UInt64.toNat_add, hInputSizeNat]
        omega
      have hCapacityNotLt : ¬capacity < 8 := by
        rw [UInt64.lt_iff_toNat_lt, hCapacityNat]
        change ¬8 * (input.size + 1) < 8
        omega
      refine wp_iff_cons rfl ?_
      rw [if_neg (by simpa [capacity] using hCapacityNotLt)]
      simp only [wp_nil, List.take_zero, List.drop_zero, List.nil_append]
      have hFitMemoryValid :
          heapTop.toNat + 48 + capacity.toNat ≤ initial.mem.pages * 65536 := by
        rw [hCapacityNat]
        simpa [FormalSpec.expected, hSize] using hFitMemory
      change wp «module»
        (FixedArrayAllocatorWindow.region 2 1 ++ _) _ initial _ env
      refine FixedArrayAllocatorWindow.region_spec 2 «module» env initial _
        heapTop capacity 1 allocs ?_ ?_ ?_ ?_ ?_ hFitMemoryValid hPages
          rfl hHeapTop hFreeList hAllocs _ _ ?_
      · rfl
      · rfl
      · rfl
      · simp [capacity]
      · rw [hCapacityNat]
        omega
      · let allocSt :=
          FixedArrayAllocator.allocStore initial heapTop capacity 1 allocs
        let allocFrame := FixedArrayAllocatorWindow.allocFrame 2
          { params := [.i64 inputPtr],
            locals := [.i64 0, .i64 0, .i64 0, .i64 0,
              .i64 inputPtr, .i64 (UInt64.ofNat input.size),
              .i64 0, .i64 0, .i64 0, .i64 0, .i64 capacity,
              .i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
            values := [] } heapTop capacity
        change wp «module» _ _ allocSt allocFrame env
        have hBump := Allocation.bumpFacts heapTop capacity initial.mem.pages
          hFitMemoryValid hPages
        have hRootAddressNat : (heapTop + 48).toUInt32.toNat =
            heapTop.toNat + 48 := by
          simpa using hBump.wordAddress_toNat 0 (by rw [hCapacityNat]; omega)
        have hRootBound : (heapTop + 48).toUInt32.toNat + 8 ≤
            allocSt.mem.pages * 65536 := by
          rw [hRootAddressNat]
          simp only [allocSt, FixedArrayAllocator.allocStore_pages]
          omega
        have hRootAddress : UInt32.ofNat
              ((heapTop + 48).toNat % 4294967296) =
            (heapTop + 48).toUInt32 :=
          (Memory.toUInt32_eq_ofNat (heapTop + 48)).symm
        have hRootGeneratedBound :
            (heapTop + 48).toNat % 4294967296 + 8 ≤
              allocSt.mem.pages * 65536 := by
          simpa [Memory.toUInt32_toNat] using hRootBound
        have hRootGeneratedAddress : UInt32.ofNat
              ((heapTop.toNat + 48) % 4294967296) =
            (heapTop + 48).toUInt32 := by
          rw [← hBump.rootToNat]
          exact hRootAddress
        have hRootGeneratedBound' :
            (heapTop.toNat + 48) % 4294967296 + 8 ≤
              allocSt.mem.pages * 65536 := by
          rw [← hBump.rootToNat]
          exact hRootGeneratedBound
        have hRootAddAddress : heapTop.toUInt32 + 48 =
            (heapTop + 48).toUInt32 := by
          have hHeapTop32 : heapTop.toNat < 4294967296 := by omega
          have hRoot32 : heapTop.toNat + 48 < 4294967296 := by omega
          have h48 : (48 : UInt32).toNat = 48 := rfl
          apply UInt32.toNat.inj
          rw [hRootAddressNat]
          simp only [UInt32.toNat_add, Memory.toUInt32_toNat]
          rw [Nat.mod_eq_of_lt hHeapTop32, h48, Nat.mod_eq_of_lt hRoot32]
        have hInputAlloc : UInt64Array.At allocSt inputPtr input := by
          apply hArray.frameBefore hInputBelow
          · exact FixedArrayAllocator.allocStore_pages initial heapTop capacity 1 allocs
          · intro address hAddress
            simp only [allocSt, FixedArrayAllocator.allocStore,
              FixedArrayAllocator.headerMem]
            rw [Memory.write64_bytes_before _ _ _ (by simp; omega)]
            rw [Memory.write64_bytes_before _ _ _ (by simp; omega)]
            rw [Memory.write64_bytes_before _ _ _ (by simp; omega)]
            rw [Memory.write64_bytes_before _ _ _ (by simp; omega)]
            rw [Memory.write64_bytes_before _ _ _ (by simp; omega)]
            rw [Memory.write64_bytes_before _ _ _ (by simp; omega)]
        have hInputLength : UInt64Array.At
            (FixedArrayResult.writeLength allocSt (heapTop + 48)
              (UInt64.ofNat input.size)) inputPtr input := by
          simpa [FixedArrayResult.writeLength] using
            hInputAlloc.write64After (address := (heapTop + 48).toUInt32)
              (by rw [hRootAddressNat]; omega)
        have hInputLength' : UInt64Array.At
            { allocSt with mem := (allocSt.mem.write64
                (heapTop.toUInt32 + 48) (UInt64.ofNat input.size)) }
            inputPtr input := by
          rw [hRootAddAddress]
          change UInt64Array.At
            (FixedArrayResult.writeLength allocSt (heapTop + 48)
              (UInt64.ofNat input.size)) inputPtr input
          exact hInputLength
        wp_run16 [allocFrame, FixedArrayAllocatorWindow.allocFrame,
          hRootGeneratedAddress, hRootGeneratedBound']
        apply wp_block_cons
        apply wp_loop_cons
          (Inv := mapInv initial inputPtr (heapTop + 48) input allocFrame)
          (μ := mapMeasure input.size)
        · refine ⟨0, 0, by omega, ?_, ?_, hInputLength', ?_, ?_⟩
          · simp [mapFrame, allocFrame,
              FixedArrayAllocatorWindow.allocFrame]
          · rw [Mem.write64_pages]
            simpa [allocSt] using
              FixedArrayAllocator.allocStore_pages initial heapTop capacity 1 allocs
          · rw [hRootAddAddress]
            exact Mem.read64_write64_same ..
          · intro i hiInput hi
            omega
        · rintro st s ⟨index, value, hIndex, rfl, hStatePages,
            hStateInput, hResultLength, hPrefix⟩
          have hIndexNat : (UInt64.ofNat index).toNat = index := by
            apply UInt64.toNat_ofNat_of_lt'
            have hUInt64Size : UInt64.size = 18446744073709551616 := rfl
            omega
          by_cases hDone : index = input.size
          · subst index
            have hGe : UInt64.ofNat input.size ≥ UInt64.ofNat input.size := by
              simp
            have hOutput : UInt64Array.At st (heapTop + 48)
                (input.map fun element => element + 1) := by
              refine ⟨?_, ?_, ?_, ?_⟩
              · simp only [Array.size_map]
                rw [hBump.rootToNat]
                simpa [FormalSpec.expected, hSize] using hFit32
              · simp only [Array.size_map]
                rw [hStatePages, hBump.rootToNat]
                simpa [FormalSpec.expected, hSize] using hFitMemory
              · simpa using hResultLength
              · intro i hi
                have hiInput : i < input.size := by simpa using hi
                rw [← elementAddress_eq (heapTop + 48) i (by omega)]
                simpa using hPrefix i hiInput (by omega)
            simp only [mapFrame]
            wp_run16 [allocFrame, FixedArrayAllocatorWindow.allocFrame,
              hGe, hOutput, FormalSpec.expected, hSize]
            refine ⟨heapTop + 48, rfl, ?_⟩
            change UInt64Array.At st (heapTop + 48)
              (input.map fun element => element + 1)
            exact hOutput
          · have hLt : index < input.size := by omega
            have hNotGe : ¬UInt64.ofNat index ≥ UInt64.ofNat input.size := by
              rw [ge_iff_le, UInt64.le_iff_toNat_le, hIndexNat,
                hInputSizeNat]
              omega
            rcases hStateInput.generatedElement index hLt with
              ⟨hElementBound, hElementRead⟩
            simp only [mapFrame]
            wp_run16 [allocFrame, FixedArrayAllocatorWindow.allocFrame,
              hNotGe, hElementBound, hElementRead]
            have hElementRead' : st.mem.read64
                (UInt32.ofNat ((inputPtr.toNat + (index + 1) * 8) %
                  4294967296)) = input[index] := by
              simpa [Nat.mul_comm] using hElementRead
            have hOutputLt :
                heapTop.toNat + 48 + (index + 1) * 8 < 4294967296 := by
              have hFit := hBump.fit32
              rw [hCapacityNat] at hFit
              omega
            have hOutputBound :
                (heapTop.toNat + 48 + (index + 1) * 8) % 4294967296 + 8 ≤
                  st.mem.pages * 65536 := by
              rw [Nat.mod_eq_of_lt hOutputLt, hStatePages]
              rw [hCapacityNat] at hFitMemoryValid
              omega
            have hNextIndex : UInt64.ofNat index + 1 =
                UInt64.ofNat (index + 1) := by
              apply UInt64.toNat.inj
              simp (discharger := omega) [UInt64.toNat_add, hIndexNat]
            have hNextIndexNat : (UInt64.ofNat (index + 1)).toNat =
                index + 1 := by
              apply UInt64.toNat_ofNat_of_lt'
              have hUInt64Size : UInt64.size = 18446744073709551616 := rfl
              omega
            have hWriteAddressNat :
                (UInt32.ofNat ((heapTop.toNat + 48 + (index + 1) * 8) %
                  4294967296)).toNat =
                    heapTop.toNat + 48 + (index + 1) * 8 := by
              simp [Nat.mod_eq_of_lt hOutputLt]
            have hInputNext : UInt64Array.At
                { st with mem := (st.mem.write64
                    (UInt32.ofNat ((heapTop.toNat + 48 + (index + 1) * 8) %
                      4294967296)) (input[index] + 1)) }
                inputPtr input := by
              apply hStateInput.write64After
              rw [hWriteAddressNat]
              omega
            have hResultAddressNat (i : Nat) (hi : i < input.size) :
                (elementAddress (heapTop + 48) i).toNat =
                  heapTop.toNat + 48 + (i + 1) * 8 := by
              rw [elementAddress_eq (heapTop + 48) i (by omega)]
              simpa [Nat.mul_comm] using
                hBump.wordAddress_toNat (i + 1) (by
                  rw [hCapacityNat]
                  omega)
            refine ⟨hOutputBound, ?_, ?_⟩
            · rw [hElementRead']
              refine ⟨index + 1, input[index], by omega, ?_, ?_,
                hInputNext, ?_, ?_⟩
              · rw [hNextIndex]
                rfl
              · rw [Mem.write64_pages]
                exact hStatePages
              · rw [Memory.read64_write64_disjoint _ _ _ _ (Or.inl (by
                    rw [hRootAddressNat, hWriteAddressNat]
                    omega))]
                exact hResultLength
              · intro i hiInput hiNext
                by_cases hiIndex : i = index
                · subst i
                  rw [show elementAddress (heapTop + 48) index =
                      UInt32.ofNat ((heapTop.toNat + 48 + (index + 1) * 8) %
                        4294967296) by
                    apply UInt32.toNat.inj
                    rw [hResultAddressNat index hLt, hWriteAddressNat]]
                  exact Mem.read64_write64_same ..
                · rw [Memory.read64_write64_disjoint _ _ _ _ (Or.inl (by
                    rw [hResultAddressNat i hiInput, hWriteAddressNat]
                    omega))]
                  exact hPrefix i hiInput (by omega)
            · simp only [mapMeasure, List.getElem?_cons_succ,
                List.getElem?_cons_zero, hNextIndex, hNextIndexNat, hIndexNat]
              omega
    · have hEncoded : ¬UInt64.ofNat input.size ≤ 8 := by
        rw [UInt64.le_iff_toNat_le,
          UInt64.toNat_ofNat_of_lt' hArray.size_lt]
        change ¬input.size ≤ 8
        exact hSize
      rw [if_neg (by simp [hEncoded])]
      wp_run16 []
      refine wp_iff_cons rfl ?_
      rw [if_neg (by norm_num)]
      simp only [wp_nil, List.take_zero, List.drop_zero, List.nil_append]
      have hFitMemoryInvalid :
          heapTop.toNat + 48 + (8 : UInt64).toNat ≤
            initial.mem.pages * 65536 := by
        simpa [FormalSpec.expected, hSize] using hFitMemory
      have hBump := Allocation.bumpFacts heapTop 8 initial.mem.pages
        hFitMemoryInvalid hPages
      let invalidFrame : Locals :=
        { params := [.i64 inputPtr],
          locals := [.i64 0, .i64 0, .i64 0, .i64 0,
            .i64 inputPtr, .i64 0, .i64 0, .i64 0,
            .i64 8, .i64 0, .i64 0, .i64 0,
            .i64 0, .i64 0, .i64 0, .i64 0],
          values := [] }
      change wp «module» _ _ initial invalidFrame env
      wp_run16 [invalidFrame, hFreeList]
      apply wp_block_cons
      apply wp_loop_cons
        (Inv := fun st frame => st = initial ∧
          frame = FixedArrayAllocator.searchFrame invalidFrame)
        (μ := fun _ _ => 0)
      · refine ⟨rfl, ?_⟩
        simp [FixedArrayAllocator.searchFrame, invalidFrame]
      · rintro st frame ⟨rfl, rfl⟩
        simp only [FixedArrayAllocator.searchFrame]
        wp_run16 [invalidFrame]
        refine wp_iff_cons rfl ?_
        rw [if_pos (by simp)]
        wp_run16 [invalidFrame, hHeapTop]
        refine wp_iff_cons rfl ?_
        rw [if_neg (by simpa using hBump.noOverflow)]
        simp only [wp_nil, List.take_zero, List.drop_zero, List.nil_append]
        have hMemory32 : «module».memIs64 = false := rfl
        have hPagesWord : UInt64.ofNat st.mem.pages % 4294967296 =
            (UInt32.ofNat st.mem.pages).toUInt64 := by
          apply UInt64.toNat.inj
          rw [UInt64.toNat_mod,
            Allocation.memoryPages_toNat st.mem.pages hPages]
          have hPagesNat : (UInt64.ofNat st.mem.pages).toNat =
              st.mem.pages := by
            apply UInt64.toNat_ofNat_of_lt'
            have hUInt64Size : UInt64.size = 18446744073709551616 := rfl
            omega
          rw [hPagesNat]
          have hModulusNat : (4294967296 : UInt64).toNat =
              4294967296 := rfl
          rw [hModulusNat, Nat.mod_eq_of_lt (by omega)]
        wp_run16 [invalidFrame, hMemory32]
        refine wp_iff_cons rfl ?_
        rw [if_neg (by simp [hPagesWord, hBump.noGrow])]
        simp only [wp_nil, List.take_zero, List.drop_zero, List.nil_append]
        have hHeader0ToNat : (heapTop + 48 - 48).toNat =
            heapTop.toNat := by
          rw [UInt64.toNat_sub, UInt64.toNat_add]
          have h48 : (48 : UInt64).toNat = 48 := rfl
          rw [h48]
          have hUInt64Size : UInt64.size = 18446744073709551616 := rfl
          omega
        have hBaseBound : heapTop.toNat % 4294967296 + 8 ≤
            st.mem.pages * 65536 := by
          rw [Nat.mod_eq_of_lt (by omega)]
          omega
        have hBase8Bound : (heapTop + 48 - 40).toNat % 4294967296 + 8 ≤
            st.mem.pages * 65536 := by
          rw [hBump.header40ToNat, Nat.mod_eq_of_lt (by omega)]
          omega
        have hBase16Bound : (heapTop + 48 - 32).toNat % 4294967296 + 8 ≤
            st.mem.pages * 65536 := by
          rw [hBump.header32ToNat, Nat.mod_eq_of_lt (by omega)]
          omega
        have hBase24Bound : (heapTop + 48 - 24).toNat % 4294967296 + 8 ≤
            st.mem.pages * 65536 := by
          rw [hBump.header24ToNat, Nat.mod_eq_of_lt (by omega)]
          omega
        have hBase32Bound : (heapTop + 48 - 16).toNat % 4294967296 + 8 ≤
            st.mem.pages * 65536 := by
          rw [hBump.header16ToNat, Nat.mod_eq_of_lt (by omega)]
          omega
        have hBase40Bound : (heapTop + 48 - 8).toNat % 4294967296 + 8 ≤
            st.mem.pages * 65536 := by
          rw [hBump.header8ToNat, Nat.mod_eq_of_lt (by omega)]
          omega
        wp_run16 [invalidFrame, hHeapTop, hAllocs, hHeader0ToNat,
          hBump.rootToNat, hBump.topToNat, hBump.header40ToNat,
          hBump.header32ToNat, hBump.header24ToNat,
          hBump.header16ToNat, hBump.header8ToNat, hBaseBound,
          hBase8Bound, hBase16Bound, hBase24Bound, hBase32Bound,
          hBase40Bound]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simpa [hBump.header40ToNat] using hBase8Bound
        · simpa [hBump.header32ToNat] using hBase16Bound
        · simpa [hBump.header24ToNat] using hBase24Bound
        · simpa [hBump.header16ToNat] using hBase32Bound
        · simpa [hBump.header8ToNat] using hBase40Bound
        · rw [Nat.mod_eq_of_lt (by omega)]
          omega
        · refine ⟨heapTop + 48, rfl, ?_⟩
          rw [FormalSpec.expected, if_neg hSize]
          change UInt64Array.At _ (heapTop + 48) #[]
          have hRootAddress : UInt32.ofNat
                ((heapTop.toNat + 48) % 4294967296) =
              (heapTop + 48).toUInt32 := by
            rw [← hBump.rootToNat]
            exact (Memory.toUInt32_eq_ofNat (heapTop + 48)).symm
          refine ⟨?_, ?_, ?_, ?_⟩
          · simp only [Array.size_empty]
            rw [hBump.rootToNat]
            simpa using hBump.fit32
          · simp only [Array.size_empty, Mem.write64_pages]
            rw [hBump.rootToNat]
            simpa using hFitMemoryInvalid
          · change _ = (0 : UInt64)
            rw [← hRootAddress]
            exact Mem.read64_write64_same ..
          · intro i hi
            simp at hi

end LeanExeGen.GeneratedRc77513211b55010d.Behavior
