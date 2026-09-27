import LeanExeGen.GeneratedRb9ad29e25c8033e5.FormalSpec
import LeanExeGen.GeneratedRb9ad29e25c8033e5.Program
import LeanExeGen.GeneratedRb9ad29e25c8033e5.AnnotationMatches
import Project.ProofKit.Array
import Project.ProofKit.FixedArrayAllocatorWindow
import Project.ProofKit.FixedArrayCapacity
import Project.ProofKit.FixedArrayEqNode
import Project.ProofKit.FixedArrayLengthDispatch
import Project.ProofKit.FixedArrayPairResult
import Project.ProofKit.FixedArrayResult

set_option maxRecDepth 1048576
set_option maxHeartbeats 1000000

namespace LeanExeGen.GeneratedRb9ad29e25c8033e5.Behavior

open Wasm Project.ProofKit

def entryFrame (inputPtr : UInt64) : Locals :=
  { params := [.i64 inputPtr]
    locals := (List.replicate 23 (.i64 0)).set 7 (.i64 inputPtr)
    values := [] }

def oversizedProgram : Wasm.Program :=
  FixedArrayCapacity.constantProgram 0 1 12 ++
    (FixedArrayAllocatorWindow.region 3 1 ++
      (FixedArrayResult.lengthStoreProgram 8 0 ++
        FixedArrayResult.finishProgram 8 6 7))

def zeroPred (element : UInt64) : Bool :=
  element == 0

def searchFrame (inputPtr : UInt64) (input : Array UInt64)
    (last : UInt64) (index : Nat) : Locals :=
  { entryFrame inputPtr with
    locals := (((entryFrame inputPtr).locals.set 0 (.i64 last)).set 8
      (.i64 (UInt64.ofNat input.size))).set 9
      (.i64 (UInt64.ofNat index))
    values := [] }

def searchInv (initial : Store Unit) (inputPtr : UInt64)
    (input : Array UInt64) : AssertionF Unit :=
  fun st frame => st = initial ∧ ∃ index last, index ≤ input.size ∧
    frame = searchFrame inputPtr input last index ∧
    Array.findIdx?.loop zeroPred input index = input.findIdx? zeroPred

def searchMeasure (input : Array UInt64) (_ : Store Unit)
    (frame : Locals) : Nat :=
  match frame.locals with
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: .i64 index :: _ =>
      input.size - index.toNat
  | _ => 0

def removalBaseFrame (inputPtr : UInt64) (input : Array UInt64)
    (index : Nat) (capacity : UInt64) : Locals :=
  { params := [.i64 inputPtr]
    locals := [.i64 input[index]!, .i64 (UInt64.ofNat index + 1),
      .i64 inputPtr, .i64 (UInt64.ofNat index), .i64 0, .i64 0, .i64 0,
      .i64 inputPtr, .i64 (UInt64.ofNat index),
      .i64 (UInt64.ofNat input.size), .i64 (UInt64.ofNat index),
      .i64 (UInt64.ofNat input.size - 1 - UInt64.ofNat index),
      .i64 (UInt64.ofNat input.size - 1), .i64 0, .i64 0, .i64 0,
      .i64 0, .i64 capacity, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0]
    values := [] }

def counterFrame (base : Locals) (counter : Nat) : Locals :=
  { base with
    locals := base.locals.set 14 (.i64 (UInt64.ofNat counter))
    values := [] }

def counterMeasure (stop : Nat) (_ : Store Unit) (frame : Locals) : Nat :=
  match frame.locals with
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ ::
      _ :: _ :: .i64 counter :: _ => stop - counter.toNat
  | _ => 0

def prefixInv (initial : Store Unit) (inputPtr heapTop : UInt64)
    (input : Array UInt64) (stop : Nat) (base : Locals) : AssertionF Unit :=
  fun current frame =>
    ∃ counter, counter ≤ stop ∧
      frame = counterFrame base counter ∧
      current.mem.pages = initial.mem.pages ∧
      UInt64Array.At current inputPtr input ∧
      current.mem.read64 (heapTop + 48).toUInt32 =
        UInt64.ofNat input.size - 1 ∧
      ∀ i, i < counter →
        current.mem.read64
            (heapTop + 48 + UInt64.ofNat (8 * (i + 1))).toUInt32 =
          input[i]!

def suffixInv (initial : Store Unit) (inputPtr heapTop : UInt64)
    (input : Array UInt64) (prefixSize stop : Nat)
    (base : Locals) : AssertionF Unit :=
  fun current frame =>
    ∃ counter, counter ≤ stop ∧
      frame = counterFrame base counter ∧
      current.mem.pages = initial.mem.pages ∧
      UInt64Array.At current inputPtr input ∧
      current.mem.read64 (heapTop + 48).toUInt32 =
        UInt64.ofNat input.size - 1 ∧
      (∀ i, i < prefixSize →
        current.mem.read64
            (heapTop + 48 + UInt64.ofNat (8 * (i + 1))).toUInt32 =
          input[i]!) ∧
      ∀ j, j < counter →
        current.mem.read64
            (heapTop + 48 +
              UInt64.ofNat (8 * (prefixSize + j + 1))).toUInt32 =
          input[prefixSize + j + 1]!

theorem artifact_behavior :
    LeanExeGen.GeneratedRb9ad29e25c8033e5.FormalSpec.ArtifactSpec LeanExeGen.GeneratedRb9ad29e25c8033e5.«module» := by
  refine ⟨0, rfl, ?_⟩
  intro env initial inputPtr input hInput
  rcases hInput with
    ⟨hArray, heapTop, allocs, retains, releases, frees, hGlobals,
      hInputBelow, hOutputFit32, hOutputFitMemory,
      hHeapFit32, hHeapFitMemory, hPages⟩
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
  apply Wasm.TerminatesWith.of_wp_entry_for (f := func0Def) rfl
  wp_fixed_array_length_le_dispatch_from hArray at 8, 8
  case hParams => rfl
  case hValues => rfl
  case hInputLocalPositive => decide
  case hInputLocal =>
    simp [func0Def, Wasm.Function.toLocals, Wasm.Function.numParams]
  case hMaximumSize => decide
  case hValid =>
    intro hSize
    change wp module _ _ initial (entryFrame inputPtr) env
    wp_run
    simp [entryFrame, hArray.pointerAddress_eq, hArray.lengthRead]
    rw [if_neg (Nat.not_lt.mpr hArray.generatedLengthBound)]
    apply wp_block_cons
    apply wp_loop_cons
      (Inv := searchInv initial inputPtr input)
      (μ := searchMeasure input)
    · refine ⟨rfl, 0, 0, Nat.zero_le _, ?_, rfl⟩
      simp [searchFrame, entryFrame]
    · rintro st frame ⟨rfl, index, last, hIndex, rfl, hLoop⟩
      simp only [searchFrame, entryFrame]
      wp_run
      simp
      have hIndexNat : (UInt64.ofNat index).toNat = index := by
        apply UInt64.toNat_ofNat_of_lt'
        have hUInt64Size : UInt64.size = 18446744073709551616 := rfl
        omega
      by_cases hDone : index = input.size
      · subst index
        have hGuard :
            (if UInt64.ofNat input.size ≤ UInt64.ofNat input.size
              then (1 : UInt32) else 0) = 1 := by
          simp
        rw [hGuard]
        have hFindNone : input.findIdx? zeroPred = none := by
          rw [← hLoop, Array.findIdx?.loop.eq_def]
          simp
        have hFindNone' :
            input.findIdx? (fun element => element == 0) = none := by
          simpa [zeroPred] using hFindNone
        have hExpected : FormalSpec.expected input = input := by
          simp [FormalSpec.expected, hSize, hFindNone']
        simp only [FixedArrayEqNode.branchPost]
        wp_run
        refine wp_iff_cons rfl ?_
        rw [if_neg (by simp)]
        wp_run
        simp
        refine wp_iff_cons rfl ?_
        rw [if_pos (by simp)]
        wp_run
        simp [func0Def]
        simp only [FixedArrayEqNode.branchPost]
        rw [Wasm.wp_localGet_cons]
        simp [Wasm.Locals.get]
        rw [hExpected]
        exact hArray
      · have hIndexLt : index < input.size := by omega
        have hNotGe :
            ¬UInt64.ofNat input.size ≤ UInt64.ofNat index := by
          rw [UInt64.le_iff_toNat_le,
            UInt64.toNat_ofNat_of_lt' hArray.size_lt, hIndexNat]
          omega
        rw [if_neg hNotGe]
        simp
        obtain ⟨hLoadBound, hLoadRead⟩ :=
          hArray.generatedElement index hIndexLt
        have hLoadRead' :
            st.mem.read64
                (UInt32.ofNat
                  ((inputPtr.toNat + (index + 1) * 8) % 4294967296)) =
              input[index]! := by
          simpa [Nat.mul_comm, hIndexLt] using hLoadRead
        rw [if_neg (Nat.not_lt.mpr hLoadBound)]
        rw [hLoadRead']
        have hIndexSucc :
            UInt64.ofNat index + 1 = UInt64.ofNat (index + 1) := by
          apply UInt64.toNat.inj
          rw [UInt64.toNat_add, hIndexNat]
          have hOne : (1 : UInt64).toNat = 1 := rfl
          rw [hOne,
            UInt64.toNat_ofNat_of_lt' (by
              have hUInt64Size : UInt64.size = 18446744073709551616 := rfl
              omega), Nat.mod_eq_of_lt]
          have hUInt64Size : UInt64.size = 18446744073709551616 := rfl
          omega
        have hSentinelNe : UInt64.ofNat index + 1 ≠ 0 := by
          intro h
          have hNat := congrArg UInt64.toNat h
          rw [hIndexSucc,
            UInt64.toNat_ofNat_of_lt' (by
              have hUInt64Size : UInt64.size = 18446744073709551616 := rfl
              omega)] at hNat
          norm_num at hNat
        have hIndexWordLt :
            UInt64.ofNat index < UInt64.ofNat input.size := by
          rw [UInt64.lt_iff_toNat_lt, hIndexNat,
            UInt64.toNat_ofNat_of_lt' hArray.size_lt]
          exact hIndexLt
        let capacity : UInt64 :=
          (8 + (UInt64.ofNat input.size - 1) * 8 + 7) / 8 * 8
        have hCapacityNat : capacity.toNat = 8 * input.size := by
          have hEight : (8 : UInt64).toNat = 8 := rfl
          have hSeven : (7 : UInt64).toNat = 7 := rfl
          have hOne : (1 : UInt64).toNat = 1 := rfl
          simp only [capacity, UInt64.toNat_mul, UInt64.toNat_div,
            UInt64.toNat_add, UInt64.toNat_sub,
            UInt64.toNat_ofNat_of_lt' hArray.size_lt,
            hEight, hSeven, hOne]
          norm_num
          omega
        have hCapacity : 8 ≤ capacity.toNat := by omega
        have hCapacityU : (8 : UInt64) ≤ capacity := by
          rw [UInt64.le_iff_toNat_le]
          exact hCapacity
        by_cases hZero : input[index]! = 0
        · have hZeroElem : input[index] = 0 := by
            simpa [getElem!_pos input index hIndexLt] using hZero
          have hFindSome0 : input.findIdx? zeroPred = some index := by
            rw [← hLoop, Array.findIdx?.loop.eq_def, dif_pos hIndexLt]
            simp [zeroPred, hZeroElem]
          have hFindSome :
              input.findIdx? (fun element => element == 0) = some index := by
            change input.findIdx? zeroPred = some index
            exact hFindSome0
          have hExpected : FormalSpec.expected input = input.eraseIdx! index := by
            simp [FormalSpec.expected, hSize, hFindSome]
          refine wp_iff_cons rfl ?_
          rw [if_pos hZero]
          wp_run
          simp
          refine wp_iff_cons rfl ?_
          rw [if_pos (by simp)]
          wp_run
          simp [Wasm.Locals.get, Wasm.Locals.set?]
          refine wp_iff_cons rfl ?_
          rw [if_pos (by simp [hSentinelNe])]
          wp_run
          simp
          refine wp_iff_cons rfl ?_
          rw [if_neg (by simp [hSentinelNe])]
          wp_run
          simp
          refine wp_iff_cons rfl ?_
          rw [if_pos (by simp [hSentinelNe])]
          wp_run
          simp
          refine wp_iff_cons rfl ?_
          rw [if_neg (by simp [hSentinelNe])]
          wp_run
          simp
          rw [if_neg (Nat.not_lt.mpr hArray.generatedLengthBound)]
          rw [hInputAddress, hArray.lengthRead]
          refine wp_iff_cons rfl ?_
          rw [if_pos hIndexWordLt]
          wp_run
          simp
          rw [if_neg (Nat.not_lt.mpr hArray.generatedLengthBound)]
          rw [hInputAddress, hArray.lengthRead]
          refine wp_iff_cons rfl ?_
          rw [if_pos hIndexWordLt]
          wp_run
          rw [if_pos (by decide)]
          wp_run
          simp
          refine wp_iff_cons rfl ?_
          rw [if_neg (by
            have hNot : ¬capacity < 8 := by
              rw [UInt64.lt_iff_toNat_lt, hCapacityNat]
              change ¬8 * input.size < 8
              omega
            simp [capacity, hNot])]
          rw [wp_nil]
          simp only [List.take_zero, List.drop_zero, List.nil_append]
          have hFitCapacity :
              heapTop.toNat + 48 + capacity.toNat ≤
                st.mem.pages * 65536 := by
            rw [hCapacityNat]
            have hFit := hHeapFitMemory
            simp [FormalSpec.heapReserveBytes, hSize, hFindSome] at hFit
            omega
          apply FixedArrayAllocatorWindow.region_spec_withTail
            9 0 module env st
              (removalBaseFrame inputPtr input index capacity)
              heapTop capacity 1 allocs
          · rfl
          · rfl
          · rfl
          · simp [removalBaseFrame]
          · exact hCapacity
          · exact hFitCapacity
          · exact hPages
          · rfl
          · exact hHeapTop
          · exact hFreeList
          · exact hAllocs
          · have hBump := Allocation.bumpFacts heapTop capacity
                st.mem.pages hFitCapacity hPages
            have hRootAddress :
                UInt32.ofNat ((heapTop.toNat + 48) % 4294967296) =
                  (heapTop + 48).toUInt32 := by
              simpa using hBump.wordAddress 0 hCapacity
            wp_run
            simp [FixedArrayAllocatorWindow.allocFrame, removalBaseFrame]
            rw [if_neg (by
              rw [Nat.mod_eq_of_lt]
              · rw [FixedArrayAllocator.allocStore_pages]
                omega
              · omega)]
            rw [hRootAddress]
            let base := FixedArrayAllocatorWindow.allocFrame 9
              (removalBaseFrame inputPtr input index capacity)
              heapTop capacity
            apply wp_block_cons
            apply wp_loop_cons
              (Inv := prefixInv st inputPtr heapTop input index base)
              (μ := counterMeasure index)
            · unfold prefixInv
              refine ⟨0, Nat.zero_le _, ?_, ?_, ?_, ?_, ?_⟩
              · simp [base, counterFrame,
                  FixedArrayAllocatorWindow.allocFrame, removalBaseFrame]
              · simp [FixedArrayAllocator.allocStore_pages,
                  Mem.write64_pages]
              · have hInputAlloc :=
                    FixedArrayPairResult.input_preserved_by_alloc
                      st heapTop capacity 1 allocs inputPtr input hArray
                      hInputBelow hFitCapacity hPages
                apply hInputAlloc.write64After
                have hRootToNat :
                    (heapTop + 48).toUInt32.toNat = heapTop.toNat + 48 := by
                  simpa using hBump.wordAddress_toNat 0 hCapacity
                rw [hRootToNat]
                omega
              · exact Mem.read64_write64_same ..
              · intro i hi
                omega
            · rintro current frame
                ⟨counter, hCounter, rfl, hCurrentPages, hCurrentInput,
                  hCurrentLength, hPrefix⟩
              have hCounterNat : (UInt64.ofNat counter).toNat = counter := by
                apply UInt64.toNat_ofNat_of_lt'
                have hUInt64Size : UInt64.size = 18446744073709551616 := rfl
                omega
              simp only [base, counterFrame,
                FixedArrayAllocatorWindow.allocFrame, removalBaseFrame]
              wp_run
              simp
              by_cases hDoneCopy : counter = index
              · subst counter
                have hGuard :
                    (if UInt64.ofNat index ≤ UInt64.ofNat index
                      then (1 : UInt32) else 0) = 1 := by
                  simp
                rw [hGuard]
                simp only [FixedArrayEqNode.branchPost]
                wp_run
                simp
                let stop := input.size - 1 - index
                have hStopNat :
                    (UInt64.ofNat input.size - 1 -
                      UInt64.ofNat index).toNat = stop := by
                  have hOne : (1 : UInt64).toNat = 1 := rfl
                  simp only [stop, UInt64.toNat_sub, hOne,
                    UInt64.toNat_ofNat_of_lt' hCurrentInput.size_lt,
                    hIndexNat]
                  omega
                apply wp_block_cons
                apply wp_loop_cons
                  (Inv := suffixInv st inputPtr heapTop input index stop base)
                  (μ := counterMeasure stop)
                · unfold suffixInv
                  refine ⟨0, Nat.zero_le _, ?_, hCurrentPages,
                    hCurrentInput, hCurrentLength, hPrefix, ?_⟩
                  · simp [base, counterFrame,
                      FixedArrayAllocatorWindow.allocFrame,
                      removalBaseFrame]
                  · intro j hj
                    omega
                · rintro shifted shiftFrame
                    ⟨shift, hShift, rfl, hShiftPages, hShiftInput,
                      hShiftLength, hShiftPrefix, hShiftSuffix⟩
                  have hShiftNat :
                      (UInt64.ofNat shift).toNat = shift := by
                    apply UInt64.toNat_ofNat_of_lt'
                    have hUInt64Size : UInt64.size =
                        18446744073709551616 := rfl
                    omega
                  simp only [base, counterFrame,
                    FixedArrayAllocatorWindow.allocFrame, removalBaseFrame]
                  wp_run
                  simp
                  by_cases hDoneShift : shift = stop
                  · subst shift
                    have hGuard :
                        (if UInt64.ofNat input.size - 1 -
                              UInt64.ofNat index ≤ UInt64.ofNat stop
                          then (1 : UInt32) else 0) = 1 := by
                      rw [if_pos]
                      rw [UInt64.le_iff_toNat_le, hStopNat, hShiftNat]
                    rw [hGuard]
                    simp
                    rw [hExpected]
                    refine ⟨heapTop + 48, rfl, ?_⟩
                    change UInt64Array.At shifted (heapTop + 48)
                      (input.eraseIdx! index)
                    have hEraseSize :
                        (input.eraseIdx! index).size = input.size - 1 := by
                      simp [Array.eraseIdx!, hIndexLt]
                    refine ⟨?_, ?_, ?_, ?_⟩
                    · rw [hBump.rootToNat, hEraseSize]
                      have hFit := hBump.fit32
                      rw [hCapacityNat] at hFit
                      omega
                    · rw [hBump.rootToNat, hEraseSize, hShiftPages]
                      rw [hCapacityNat] at hFitCapacity
                      omega
                    · rw [hEraseSize]
                      have hNewLength :
                          UInt64.ofNat input.size - 1 =
                            UInt64.ofNat (input.size - 1) := by
                        apply UInt64.toNat.inj
                        have hOne : (1 : UInt64).toNat = 1 := rfl
                        rw [UInt64.toNat_sub, hOne,
                          UInt64.toNat_ofNat_of_lt'
                            hShiftInput.size_lt,
                          UInt64.toNat_ofNat_of_lt' (by
                            have hUInt64Size : UInt64.size =
                                18446744073709551616 := rfl
                            omega)]
                        omega
                      rw [← hNewLength]
                      exact hShiftLength
                    · intro i hi
                      by_cases hiPrefix : i < index
                      · simp only [Array.eraseIdx!, dif_pos hIndexLt]
                        rw [Array.getElem_eraseIdx_of_lt hIndexLt
                          (by simpa [Array.eraseIdx!, hIndexLt] using hi)
                          hiPrefix]
                        simpa [getElem!_pos input i (by omega)] using
                          hShiftPrefix i hiPrefix
                      · let j := i - index
                        have hIndexJ : index + j = i := by
                          dsimp [j]
                          omega
                        have hjStop : j < stop := by
                          rw [hEraseSize] at hi
                          dsimp [stop, j]
                          omega
                        have hiSource : i + 1 < input.size := by
                          rw [hEraseSize] at hi
                          omega
                        simp only [Array.eraseIdx!, dif_pos hIndexLt]
                        rw [Array.getElem_eraseIdx_of_ge hIndexLt
                          (by simpa [Array.eraseIdx!, hIndexLt] using hi)
                          (Nat.le_of_not_gt hiPrefix)]
                        simpa [getElem!_pos input (i + 1) hiSource,
                          hIndexJ, Nat.add_assoc] using
                            hShiftSuffix j hjStop
                  · have hShiftLt : shift < stop := by omega
                    have hSourceLt : index + shift + 1 < input.size := by
                      dsimp [stop] at hShiftLt
                      omega
                    have hNotGe :
                        ¬UInt64.ofNat input.size - 1 -
                            UInt64.ofNat index ≤ UInt64.ofNat shift := by
                      rw [UInt64.le_iff_toNat_le, hStopNat, hShiftNat]
                      omega
                    rw [if_neg hNotGe]
                    obtain ⟨hShiftLoadBound, hShiftLoadRead⟩ :=
                      hShiftInput.generatedElement
                        (index + shift + 1) hSourceLt
                    have hShiftWordFit :
                        8 * (index + shift + 1 + 1) ≤ capacity.toNat := by
                      rw [hCapacityNat]
                      omega
                    have hShiftOutputAddress :
                        UInt32.ofNat
                            ((heapTop.toNat + 48 +
                              (index + shift + 1) * 8) % 4294967296) =
                          (heapTop + 48 + UInt64.ofNat
                            (8 * (index + shift + 1))).toUInt32 := by
                      have hRoot64 :
                          heapTop.toNat + 48 < 18446744073709551616 := by
                        have hFit := hBump.fit32
                        omega
                      have hAddress := hBump.wordAddress
                        (index + shift + 1) hShiftWordFit
                      rw [Nat.mod_eq_of_lt hRoot64] at hAddress
                      simpa [Nat.mul_comm, Nat.add_assoc,
                        Nat.add_left_comm, Nat.add_comm] using hAddress
                    have hShiftLoadRead' :
                        shifted.mem.read64
                            (UInt32.ofNat
                          ((inputPtr.toNat +
                                (index + 1 + shift + 1) * 8) %
                                  4294967296)) =
                          input[index + shift + 1]! := by
                      rw [getElem!_pos input (index + shift + 1) hSourceLt]
                      simpa [Nat.mul_comm, Nat.add_assoc, Nat.add_left_comm,
                        Nat.add_comm] using hShiftLoadRead
                    have hShiftSucc :
                        UInt64.ofNat shift + 1 =
                          UInt64.ofNat (shift + 1) := by
                      apply UInt64.toNat.inj
                      rw [UInt64.toNat_add, hShiftNat]
                      have hOne : (1 : UInt64).toNat = 1 := rfl
                      rw [hOne, UInt64.toNat_ofNat_of_lt' (by
                        have hUInt64Size : UInt64.size =
                            18446744073709551616 := rfl
                        omega), Nat.mod_eq_of_lt]
                      have hUInt64Size : UInt64.size =
                          18446744073709551616 := rfl
                      omega
                    simp
                    refine ⟨by
                      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
                        using hShiftLoadBound, ?_, ?_⟩
                    · rw [Nat.mod_eq_of_lt]
                      · rw [hShiftPages]
                        omega
                      · have hFit := hBump.fit32
                        rw [hCapacityNat] at hFit
                        omega
                    · rw [hShiftOutputAddress, hShiftLoadRead', hShiftSucc]
                      refine ⟨?_, ?_⟩
                      · unfold suffixInv
                        refine ⟨shift + 1, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
                        · rfl
                        · simpa [Mem.write64_pages] using hShiftPages
                        · apply hShiftInput.write64After
                          rw [hBump.wordAddress_toNat
                            (index + shift + 1) hShiftWordFit]
                          omega
                        · calc
                            (shifted.mem.write64
                                (heapTop + 48 + UInt64.ofNat
                                  (8 * (index + shift + 1))).toUInt32
                                input[index + shift + 1]!).read64
                                  (heapTop + 48).toUInt32 =
                                shifted.mem.read64
                                  (heapTop + 48).toUInt32 := by
                                  apply Memory.read64_write64_disjoint
                                  left
                                  rw [show (heapTop + 48).toUInt32.toNat =
                                      heapTop.toNat + 48 by
                                        simpa using hBump.wordAddress_toNat
                                          0 hCapacity,
                                    hBump.wordAddress_toNat
                                      (index + shift + 1) hShiftWordFit]
                                  omega
                            _ = UInt64.ofNat input.size - 1 := hShiftLength
                        · intro i hi
                          have hPrefixWordFit :
                              8 * (i + 1 + 1) ≤ capacity.toNat := by
                            rw [hCapacityNat]
                            omega
                          calc
                            (shifted.mem.write64
                                (heapTop + 48 + UInt64.ofNat
                                  (8 * (index + shift + 1))).toUInt32
                                input[index + shift + 1]!).read64
                                  (heapTop + 48 +
                                    UInt64.ofNat (8 * (i + 1))).toUInt32 =
                                shifted.mem.read64
                                  (heapTop + 48 +
                                    UInt64.ofNat (8 * (i + 1))).toUInt32 := by
                                      apply Memory.read64_write64_disjoint
                                      left
                                      rw [hBump.wordAddress_toNat
                                          (i + 1) hPrefixWordFit,
                                        hBump.wordAddress_toNat
                                          (index + shift + 1)
                                          hShiftWordFit]
                                      omega
                            _ = input[i]! := hShiftPrefix i hi
                        · intro j hj
                          by_cases hEq : j = shift
                          · subst j
                            exact Mem.read64_write64_same ..
                          · have hjShift : j < shift := by omega
                            have hSuffixWordFit :
                                8 * (index + j + 1 + 1) ≤
                                  capacity.toNat := by
                              rw [hCapacityNat]
                              omega
                            calc
                              (shifted.mem.write64
                                  (heapTop + 48 + UInt64.ofNat
                                    (8 * (index + shift + 1))).toUInt32
                                  input[index + shift + 1]!).read64
                                    (heapTop + 48 + UInt64.ofNat
                                      (8 * (index + j + 1))).toUInt32 =
                                  shifted.mem.read64
                                    (heapTop + 48 + UInt64.ofNat
                                      (8 * (index + j + 1))).toUInt32 := by
                                        apply Memory.read64_write64_disjoint
                                        left
                                        rw [hBump.wordAddress_toNat
                                            (index + j + 1) hSuffixWordFit,
                                          hBump.wordAddress_toNat
                                            (index + shift + 1)
                                            hShiftWordFit]
                                        omega
                              _ = input[index + j + 1]! :=
                                hShiftSuffix j hjShift
                      · simp [counterMeasure, hShiftNat]
                        omega
              · have hCounterLt : counter < index := by omega
                have hCounterInput : counter < input.size := by omega
                have hNotGe :
                    ¬UInt64.ofNat index ≤ UInt64.ofNat counter := by
                  rw [UInt64.le_iff_toNat_le, hCounterNat,
                    UInt64.toNat_ofNat_of_lt' (by
                      have hUInt64Size : UInt64.size =
                          18446744073709551616 := rfl
                      omega)]
                  omega
                rw [if_neg hNotGe]
                obtain ⟨hCopyLoadBound, hCopyLoadRead⟩ :=
                  hCurrentInput.generatedElement counter hCounterInput
                have hWordFit :
                    8 * (counter + 1 + 1) ≤ capacity.toNat := by
                  rw [hCapacityNat]
                  omega
                have hOutputAddress :
                    UInt32.ofNat
                        ((heapTop.toNat + 48 + (counter + 1) * 8) %
                          4294967296) =
                      (heapTop + 48 +
                        UInt64.ofNat (8 * (counter + 1))).toUInt32 := by
                  have hRoot64 :
                      heapTop.toNat + 48 < 18446744073709551616 := by
                    have hFit := hBump.fit32
                    omega
                  simpa [Nat.mod_eq_of_lt hRoot64, Nat.mul_comm,
                    Nat.add_assoc] using
                      hBump.wordAddress (counter + 1) hWordFit
                have hCopyLoadRead' :
                    current.mem.read64
                        (UInt32.ofNat
                          ((inputPtr.toNat + (counter + 1) * 8) %
                            4294967296)) = input[counter]! := by
                  simpa [Nat.mul_comm, hCounterInput] using hCopyLoadRead
                have hCounterSucc :
                    UInt64.ofNat counter + 1 =
                      UInt64.ofNat (counter + 1) := by
                  apply UInt64.toNat.inj
                  rw [UInt64.toNat_add, hCounterNat]
                  have hOne : (1 : UInt64).toNat = 1 := rfl
                  rw [hOne, UInt64.toNat_ofNat_of_lt' (by
                    have hUInt64Size : UInt64.size =
                        18446744073709551616 := rfl
                    omega), Nat.mod_eq_of_lt]
                  have hUInt64Size : UInt64.size =
                      18446744073709551616 := rfl
                  omega
                rw [if_neg (Nat.not_lt.mpr hCopyLoadBound)]
                rw [if_neg (Nat.not_lt.mpr (by
                  rw [Nat.mod_eq_of_lt]
                  · rw [hCurrentPages]
                    omega
                  · have hFit := hBump.fit32
                    rw [hCapacityNat] at hFit
                    omega))]
                rw [hOutputAddress, hCopyLoadRead', hCounterSucc]
                refine ⟨?_, ?_⟩
                · unfold prefixInv
                  refine ⟨counter + 1, by omega, ?_, ?_, ?_, ?_, ?_⟩
                  · rfl
                  · simpa [Mem.write64_pages] using hCurrentPages
                  · apply hCurrentInput.write64After
                    rw [hBump.wordAddress_toNat (counter + 1) hWordFit]
                    omega
                  · calc
                      (current.mem.write64
                          (heapTop + 48 +
                            UInt64.ofNat (8 * (counter + 1))).toUInt32
                          input[counter]!).read64
                            (heapTop + 48).toUInt32 =
                          current.mem.read64 (heapTop + 48).toUInt32 := by
                            apply Memory.read64_write64_disjoint
                            left
                            rw [show (heapTop + 48).toUInt32.toNat =
                                heapTop.toNat + 48 by
                                  simpa using
                                    hBump.wordAddress_toNat 0 hCapacity,
                              hBump.wordAddress_toNat
                                (counter + 1) hWordFit]
                            omega
                      _ = UInt64.ofNat input.size - 1 := hCurrentLength
                  · intro i hi
                    by_cases hEq : i = counter
                    · subst i
                      exact Mem.read64_write64_same ..
                    · have hiCounter : i < counter := by omega
                      have hWordFitI :
                          8 * (i + 1 + 1) ≤ capacity.toNat := by
                        rw [hCapacityNat]
                        omega
                      calc
                        (current.mem.write64
                            (heapTop + 48 + UInt64.ofNat
                              (8 * (counter + 1))).toUInt32
                            input[counter]!).read64
                              (heapTop + 48 +
                                UInt64.ofNat (8 * (i + 1))).toUInt32 =
                            current.mem.read64
                              (heapTop + 48 +
                                UInt64.ofNat (8 * (i + 1))).toUInt32 := by
                                  apply Memory.read64_write64_disjoint
                                  left
                                  rw [hBump.wordAddress_toNat
                                      (i + 1) hWordFitI,
                                    hBump.wordAddress_toNat
                                      (counter + 1) hWordFit]
                                  omega
                        _ = input[i]! := hPrefix i hiCounter
                · simp [counterMeasure, base, counterFrame,
                    FixedArrayAllocatorWindow.allocFrame,
                    removalBaseFrame, hCounterNat]
                  omega
        · have hZeroElem : input[index] ≠ 0 := by
            simpa [getElem!_pos input index hIndexLt] using hZero
          have hLoopSucc :
              Array.findIdx?.loop zeroPred input (index + 1) =
                input.findIdx? zeroPred := by
            rw [Array.findIdx?.loop.eq_def, dif_pos hIndexLt] at hLoop
            simpa [zeroPred, hZeroElem] using hLoop
          refine wp_iff_cons rfl ?_
          rw [if_neg hZero]
          wp_run
          simp
          refine wp_iff_cons rfl ?_
          rw [if_neg (by simp)]
          rw [wp_nil]
          simp only [List.take_zero, List.drop_zero, List.nil_append]
          wp_run
          refine ⟨?_, ?_⟩
          · unfold searchInv
            refine ⟨rfl, index + 1, input[index]!, by omega, ?_, hLoopSucc⟩
            rw [hIndexSucc]
            rfl
          · change input.size - (UInt64.ofNat index + 1).toNat <
              input.size - (UInt64.ofNat index).toNat
            rw [hIndexSucc, hIndexNat,
              UInt64.toNat_ofNat_of_lt' (by
                have hUInt64Size : UInt64.size = 18446744073709551616 := rfl
                omega)]
            omega
  case hInvalid =>
    intro hSize
    have hExpected : FormalSpec.expected input = #[] := by
      simp [FormalSpec.expected, hSize]
    have hFit32 : heapTop.toNat + 48 + 8 ≤ 4294967296 := by
      simpa [hExpected] using hOutputFit32
    have hFitMemory : heapTop.toNat + 48 + 8 ≤
        initial.mem.pages * 65536 := by
      simpa [hExpected] using hOutputFitMemory
    change wp module _ _ initial (entryFrame inputPtr) env
    change wp module oversizedProgram _ initial _ env
    unfold oversizedProgram
    apply FixedArrayAllocatorWindow.constantCapacityRegion_spec_withTail
      (length := 0) (stride := 1) (offset := 3) (tail := 6)
      (heapTop := heapTop) (allocs := allocs)
    · simp [entryFrame]
    · simp [entryFrame]
    · rfl
    · simpa [FixedArrayCapacity.normalizedCapacity,
        FixedArrayCapacity.unnormalizedCapacity] using hFitMemory
    · exact hPages
    · rfl
    · exact hHeapTop
    · exact hFreeList
    · exact hAllocs
    · have hBump := Allocation.bumpFacts heapTop 8 initial.mem.pages
        hFitMemory hPages
      have hRoot := FixedArrayAllocatorWindow.allocFrame_get_root
        3 6
        (FixedArrayCapacity.capacityFrame (entryFrame inputPtr) 12 8)
        heapTop 8
        (by simp [FixedArrayCapacity.capacityFrame, entryFrame])
        (by simp [FixedArrayCapacity.capacityFrame, entryFrame])
      have hRootToNat : (heapTop + 48).toUInt32.toNat =
          heapTop.toNat + 48 := by
        simpa using hBump.wordAddress_toNat 0 (by decide)
      have hRootBound : (heapTop + 48).toUInt32.toNat + 8 ≤
          (FixedArrayAllocator.allocStore initial heapTop 8 1 allocs).mem.pages *
            65536 := by
        rw [hRootToNat, FixedArrayAllocator.allocStore_pages]
        omega
      apply FixedArrayResult.lengthStore_spec
        (root := heapTop + 48) (length := 0) (rootLocal := 8)
      · exact FixedArrayAllocatorWindow.allocFrame_values ..
      · simpa [FixedArrayCapacity.normalizedCapacity,
          FixedArrayCapacity.unnormalizedCapacity] using hRoot
      · exact hRootBound
      · apply FixedArrayResult.finishProgram_spec
          (root := heapTop + 48) (rootLocal := 8)
          (destinationLocal := 6) (returnLocal := 7)
        · exact FixedArrayAllocatorWindow.allocFrame_values ..
        · simpa [FixedArrayCapacity.normalizedCapacity,
            FixedArrayCapacity.unnormalizedCapacity] using hRoot
        · simp [FixedArrayAllocatorWindow.allocFrame,
            FixedArrayCapacity.capacityFrame, entryFrame]
        · simp [FixedArrayAllocatorWindow.allocFrame,
            FixedArrayCapacity.capacityFrame, entryFrame,
            Wasm.Locals.validIndex]
        · simp [FixedArrayAllocatorWindow.allocFrame,
            FixedArrayCapacity.capacityFrame, entryFrame]
        · simp [FixedArrayAllocatorWindow.allocFrame,
            FixedArrayCapacity.capacityFrame, entryFrame,
            Wasm.Locals.validIndex]
        · rw [wp_nil]
          simp only [FixedArrayEqNode.branchPost]
          wp_run
          simp [func0Def]
          refine ⟨heapTop + 48, rfl, ?_⟩
          rw [hExpected]
          change UInt64Array.At _ _ #[]
          simpa [FixedArrayCapacity.normalizedCapacity,
            FixedArrayCapacity.unnormalizedCapacity] using
            FixedArrayResult.emptyStore_at
              (FixedArrayAllocator.allocStore initial heapTop 8 1 allocs)
              (heapTop + 48) (by
                rw [hBump.rootToNat]
                omega) (by
                rw [hBump.rootToNat,
                  FixedArrayAllocator.allocStore_pages]
                omega)

end LeanExeGen.GeneratedRb9ad29e25c8033e5.Behavior
