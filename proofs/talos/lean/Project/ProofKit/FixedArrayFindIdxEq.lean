import Project.ProofKit.FixedArrayTraversalInput
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop

namespace Project.ProofKit.FixedArrayFindIdxEq

open Wasm

def predicate (key element : UInt64) : Bool :=
  element == key

def setupProgram (scratch : Nat) : Wasm.Program :=
  [
  .localGet 0,
  .localSet scratch,
  .localGet scratch,
  .wrapI64,
  .load64 0,
  .localSet (scratch + 1),
  .constI64 0,
  .localSet (scratch + 2),
  .constI64 0,
  .localSet (scratch + 3)
  ]

def matchProgram (scratch : Nat) (key : UInt64) : Wasm.Program :=
  [
  .localGet 1,
  .constI64 key,
  .eqI64,
  .iff 0 1 [.constI64 1] [.constI64 0],
  .constI64 0,
  .neI64,
  .iff 0 0 [
    .localGet (scratch + 2),
    .constI64 1,
    .addI64,
    .localSet (scratch + 3),
    .br 2
  ] [],
  .localGet (scratch + 2),
  .constI64 1,
  .addI64,
  .localSet (scratch + 2),
  .br 0
  ]

def loopBody (scratch : Nat) (key : UInt64) : Wasm.Program :=
  FixedArrayTraversalInput.continuingProgram
      scratch (scratch + 2) (scratch + 1) 1 ++
    matchProgram scratch key

def program (scratch : Nat) (key : UInt64) : Wasm.Program :=
  setupProgram scratch ++
    [.block 0 0 [.loop 0 0 (loopBody scratch key)]] ++
    [.localGet (scratch + 3)]

def setupFrame (scratch : Nat) (frame : Locals) (inputPtr : UInt64)
    (inputSize : Nat) : Locals :=
  { frame with
    locals := (((frame.locals.set (scratch - 1) (.i64 inputPtr)).set
      scratch (.i64 (UInt64.ofNat inputSize))).set
      (scratch + 1) (.i64 0)).set (scratch + 2) (.i64 0)
    values := [] }

def loopFrame (scratch : Nat) (frame : Locals) (inputPtr : UInt64)
    (inputSize : Nat) (item : Value) (index : Nat) : Locals :=
  { setupFrame scratch frame inputPtr inputSize with
    locals := ((setupFrame scratch frame inputPtr inputSize).locals.set
      0 item).set (scratch + 1) (.i64 (UInt64.ofNat index))
    values := [] }

def noneFrame (scratch : Nat) (frame : Locals) (inputPtr : UInt64)
    (input : Array UInt64) (item : Value) : Locals :=
  { loopFrame scratch frame inputPtr input.size item input.size with
    values := [.i64 0] }

def someFrame (scratch : Nat) (frame : Locals) (inputPtr : UInt64)
    (input : Array UInt64) (index : Nat) : Locals :=
  { loopFrame scratch frame inputPtr input.size (.i64 input[index]!) index with
    locals := (loopFrame scratch frame inputPtr input.size
      (.i64 input[index]!) index).locals.set
        (scratch + 2) (.i64 (UInt64.ofNat index + 1))
    values := [.i64 (UInt64.ofNat index + 1)] }

def searchMeasure (scratch : Nat) (input : Array UInt64)
    (_ : Store Unit) (frame : Locals) : Nat :=
  match frame.get (scratch + 2) with
  | some (.i64 index) => input.size - index.toNat
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option Elab.async false in
theorem program_spec
    (scratch tail : Nat) (key : UInt64)
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit)
    (frame : Locals) (inputPtr : UInt64) (input : Array UInt64)
    (hScratch : 2 ≤ scratch)
    (hParams : frame.params = [.i64 inputPtr])
    (hLocals : frame.locals.length = scratch + 3 + tail)
    (hValues : frame.values = [])
    (hInput : UInt64Array.At st inputPtr input)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNone : input.findIdx? (predicate key) = none →
      ∀ item : Value,
        wp module_ rest Q st
          (noneFrame scratch frame inputPtr input item) env)
    (hSome : ∀ index : Nat,
      index < input.size →
      input.findIdx? (predicate key) = some index →
      wp module_ rest Q st
        (someFrame scratch frame inputPtr input index) env) :
    wp module_ (program scratch key ++ rest) Q st frame env := by
  have hArrayNotParam : ¬scratch < 1 := by omega
  have hLengthNotParam : ¬scratch + 1 < 1 := by omega
  have hIndexNotParam : ¬scratch + 2 < 1 := by omega
  have hResultNotParam : ¬scratch + 3 < 1 := by omega
  have hArrayIndex : scratch - 1 < frame.locals.length := by omega
  have hLengthIndex : scratch < frame.locals.length := by omega
  have hIndexIndex : scratch + 1 < frame.locals.length := by omega
  have hResultIndex : scratch + 2 < frame.locals.length := by omega
  have hItemIndex : 0 < frame.locals.length := by omega
  have hScratchNeZero : scratch ≠ 0 := by omega
  have hLengthRead := hInput.lengthRead
  have hLengthBound := hInput.generatedLengthBound
  have hInputAddress := hInput.pointerAddress_eq
  have hSizeToNat : (UInt64.ofNat input.size).toNat = input.size :=
    UInt64.toNat_ofNat_of_lt' hInput.size_lt
  simp only [program, setupProgram, List.cons_append, List.nil_append]
  simp (config := { maxSteps := 10000000 }) (discharger := omega) [wp_simp,
    Wasm.Locals.get, Wasm.Locals.set?, List.length,
    List.getElem?_cons_zero,
    hParams, hLocals, hValues,
    hArrayNotParam]
  rw [if_pos (by omega : scratch < 1 + (scratch + 3 + tail))]
  simp (config := { maxSteps := 10000000 }) (discharger := omega) [wp_simp,
    List.length, List.length_set, hLocals]
  rw [if_neg (by omega : scratch ≠ 0)]
  rw [if_pos (by omega : scratch < 1 + (scratch + 3 + tail))]
  simp only
  rw [if_neg (Nat.not_lt.mpr hLengthBound)]
  rw [if_pos (by omega : scratch + 1 < 1 + (scratch + 3 + tail))]
  simp only [List.length, List.length_set]
  rw [if_neg (by omega : ¬scratch + 2 < 1)]
  rw [if_pos (by rw [hLocals]; omega :
    scratch + 2 < 0 + 1 + frame.locals.length)]
  simp only [List.length, List.length_set]
  rw [if_neg (by omega : ¬scratch + 3 < 1)]
  rw [if_pos (by rw [hLocals]; omega :
    scratch + 3 < 0 + 1 + frame.locals.length)]
  simp only
  rw [hInputAddress, hLengthRead, ← hParams]
  simp only [Nat.zero_add]
  change wp module_
    (.block 0 0 [.loop 0 0 (loopBody scratch key)] ::
      .localGet (scratch + 3) :: rest)
    Q st (setupFrame scratch frame inputPtr input.size) env
  apply wp_block_cons
  apply wp_loop_cons
    (Inv := fun st' current =>
      st' = st ∧ ∃ index item, index ≤ input.size ∧
        current = loopFrame scratch frame inputPtr input.size item index ∧
        Array.findIdx?.loop (predicate key) input index =
          input.findIdx? (predicate key))
    (μ := searchMeasure scratch input)
  · have hSetupItemIndex :
        0 < (setupFrame scratch frame inputPtr input.size).locals.length := by
      simpa [setupFrame] using hItemIndex
    refine ⟨rfl, 0, ?_, Nat.zero_le _, ?_, rfl⟩
    · exact (setupFrame scratch frame inputPtr input.size).locals[0]
    · apply Project.ProofKit.Frame.ext
      · rfl
      · simp only [loopFrame]
        rw [List.set_getElem_self hSetupItemIndex]
        simp only [setupFrame]
        rw [List.set_comm _ _ (by omega : scratch + 2 ≠ scratch + 1)]
        simp only [List.set_set]
        rw [show UInt64.ofNat 0 = 0 by decide]
      · rfl
  · rintro st' current ⟨rfl, index, item, hIndex, rfl, hLoop⟩
    have hIndexToNat : (UInt64.ofNat index).toNat = index := by
      apply UInt64.toNat_ofNat_of_lt'
      exact lt_of_le_of_lt hIndex hInput.size_lt
    have hArrayLocal :
        (loopFrame scratch frame inputPtr input.size item index).get scratch =
          some (.i64 inputPtr) := by
      simp (discharger := omega) [loopFrame, setupFrame, Wasm.Locals.get,
        hParams, hLocals, hScratchNeZero];
        omega
    have hLengthLocal :
        (loopFrame scratch frame inputPtr input.size item index).get
            (scratch + 1) =
          some (.i64 (UInt64.ofNat input.size)) := by
      simp (discharger := omega) [loopFrame, setupFrame, Wasm.Locals.get,
        List.getElem?_set, hParams, hLocals, hScratchNeZero];
        omega
    have hIndexLocal :
        (loopFrame scratch frame inputPtr input.size item index).get
            (scratch + 2) =
          some (.i64 (UInt64.ofNat index)) := by
      simp (discharger := omega) [loopFrame, setupFrame, Wasm.Locals.get,
        List.getElem?_set, hParams, hLocals, hScratchNeZero];
        omega
    have hResultLocal :
        (loopFrame scratch frame inputPtr input.size item index).get
            (scratch + 3) = some (.i64 0) := by
      simp (discharger := omega) [loopFrame, setupFrame, Wasm.Locals.get,
        List.getElem?_set, hParams, hLocals, hScratchNeZero];
        omega
    have hItemValid :
        (loopFrame scratch frame inputPtr input.size item index).validIndex 1 := by
      simp [loopFrame, setupFrame, Wasm.Locals.validIndex, hParams, hLocals]
    by_cases hDone : index = input.size
    · subst index
      unfold loopBody
      apply FixedArrayTraversalInput.continuingProgram_exit_spec
        scratch (scratch + 2) (scratch + 1) 1 module_ env st'
          (loopFrame scratch frame inputPtr input.size item input.size)
          (UInt64.ofNat input.size)
      · rfl
      · exact hIndexLocal
      · exact hLengthLocal
      · have hFindNone : input.findIdx? (predicate key) = none := by
          rw [← hLoop, Array.findIdx?.loop.eq_def]
          simp
        simp only [List.take_zero, List.drop_zero, List.nil_append]
        change wp module_ (.localGet (scratch + 3) :: rest) Q st'
          (loopFrame scratch frame inputPtr input.size item input.size) env
        simp only [wp_simp, hResultLocal]
        rw [show (loopFrame scratch frame inputPtr input.size item input.size
          : Locals).values = [] by rfl]
        simpa [noneFrame] using hNone hFindNone item
    · have hIndexLt : index < input.size := by omega
      have hContinue :
          UInt64.ofNat index < UInt64.ofNat input.size := by
        rw [UInt64.lt_iff_toNat_lt, hIndexToNat, hSizeToNat]
        exact hIndexLt
      unfold loopBody
      apply FixedArrayTraversalInput.continuingProgram_spec
        scratch (scratch + 2) (scratch + 1) 1 module_ env st'
          (loopFrame scratch frame inputPtr input.size item index)
          inputPtr (UInt64.ofNat index) (UInt64.ofNat input.size)
          input index (hItem := hItemValid) (hInput := hInput)
          (hIndex := hIndexLt)
      · rfl
      · exact hArrayLocal
      · exact hIndexLocal
      · exact hLengthLocal
      · rfl
      · exact hContinue
      · have hLoadedFrame :
            FixedArrayTraversalInput.dynamicResultFrame
                (loopFrame scratch frame inputPtr input.size item index)
                1 input[index] hItemValid =
              loopFrame scratch frame inputPtr input.size
                (.i64 input[index]) index := by
          apply Project.ProofKit.Frame.ext
          · simp [FixedArrayTraversalInput.dynamicResultFrame,
              Wasm.Locals.set, loopFrame, setupFrame, hParams]
          · simp only [FixedArrayTraversalInput.dynamicResultFrame,
              Wasm.Locals.set, loopFrame, setupFrame, hParams, List.length,
              Nat.zero_add, Nat.reduceLT, Nat.reduceSub, if_false]
            rw [List.set_comm _ _ (by omega : scratch + 1 ≠ 0)]
            simp only [List.set_set]
          · simp [FixedArrayTraversalInput.dynamicResultFrame,
              Wasm.Locals.set, loopFrame, setupFrame, hParams]
        rw [hLoadedFrame]
        have hLoadedItemLocal :
            (loopFrame scratch frame inputPtr input.size
              (.i64 input[index]) index).get 1 =
              some (.i64 input[index]) := by
          simp (discharger := omega) [loopFrame, setupFrame, Wasm.Locals.get,
            List.getElem?_set, hParams, hLocals]
        have hLoadedItemLocalExpanded :
            (if 1 < (loopFrame scratch frame inputPtr input.size
                (.i64 input[index]) index).params.length then
              (loopFrame scratch frame inputPtr input.size
                (.i64 input[index]) index).params[1]?
            else if 1 < (loopFrame scratch frame inputPtr input.size
                (.i64 input[index]) index).params.length +
                (loopFrame scratch frame inputPtr input.size
                  (.i64 input[index]) index).locals.length then
              (loopFrame scratch frame inputPtr input.size
                (.i64 input[index]) index).locals[1 -
                  (loopFrame scratch frame inputPtr input.size
                    (.i64 input[index]) index).params.length]?
            else none) = some (.i64 input[index]) := by
          exact hLoadedItemLocal
        have hLoadedIndexLocal :
            (loopFrame scratch frame inputPtr input.size
              (.i64 input[index]) index).get (scratch + 2) =
              some (.i64 (UInt64.ofNat index)) := by
          simp (discharger := omega) [loopFrame, setupFrame, Wasm.Locals.get,
            List.getElem?_set, hParams, hLocals, hScratchNeZero]; omega
        have hLoadedIndexLocalExpanded :
            (if scratch + 2 < (loopFrame scratch frame inputPtr input.size
                (.i64 input[index]) index).params.length then
              (loopFrame scratch frame inputPtr input.size
                (.i64 input[index]) index).params[scratch + 2]?
            else if scratch + 2 <
                (loopFrame scratch frame inputPtr input.size
                  (.i64 input[index]) index).params.length +
                (loopFrame scratch frame inputPtr input.size
                  (.i64 input[index]) index).locals.length then
              (loopFrame scratch frame inputPtr input.size
                (.i64 input[index]) index).locals[scratch + 2 -
                  (loopFrame scratch frame inputPtr input.size
                    (.i64 input[index]) index).params.length]?
            else none) = some (.i64 (UInt64.ofNat index)) := by
          exact hLoadedIndexLocal
        have hLoadedParamsLength :
            (loopFrame scratch frame inputPtr input.size
              (.i64 input[index]) index).params.length = 1 := by
          simp [loopFrame, setupFrame, hParams]
        have hLoadedLocalsLength :
            (loopFrame scratch frame inputPtr input.size
              (.i64 input[index]) index).locals.length =
              scratch + 3 + tail := by
          simp [loopFrame, setupFrame, hLocals]
        simp only [matchProgram]
        wp_run
        rw [hLoadedItemLocalExpanded]
        wp_run
        simp
        by_cases hMatch : input[index] = key
        · refine wp_iff_cons rfl ?_
          rw [if_pos (by simp [hMatch])]
          wp_run
          refine wp_iff_cons rfl ?_
          rw [if_pos (by simp)]
          wp_run
          rw [hLoadedIndexLocalExpanded]
          wp_run
          rw [if_neg (by rw [hLoadedParamsLength]; omega)]
          rw [if_pos (by rw [hLoadedParamsLength, hLoadedLocalsLength]; omega)]
          simp only
          rw [if_neg (by rw [hLoadedParamsLength]; omega)]
          rw [if_pos (by
            simp only [List.length_set, hLoadedParamsLength,
              hLoadedLocalsLength]
            omega)]
          simp (discharger := omega)
          have hFindSome :
              input.findIdx? (predicate key) = some index := by
            rw [← hLoop, Array.findIdx?.loop.eq_def, dif_pos hIndexLt]
            simp [predicate, hMatch]
          simpa [someFrame, loopFrame, setupFrame, Wasm.Locals.get,
            Wasm.Locals.set?, hParams, hLocals, hScratch,
            getElem!_pos input index hIndexLt, List.set_set] using
              hSome index hIndexLt hFindSome
        · refine wp_iff_cons rfl ?_
          rw [if_neg (by simp [hMatch])]
          wp_run
          refine wp_iff_cons rfl ?_
          rw [if_neg (by simp)]
          wp_run
          rw [hLoadedIndexLocalExpanded]
          wp_run
          rw [if_neg (by rw [hLoadedParamsLength]; omega)]
          rw [if_pos (by rw [hLoadedParamsLength, hLoadedLocalsLength]; omega)]
          simp only [true_and]
          have hIndexSuccBound : index + 1 < UInt64.size := by
            have hInputSizeBound := hInput.size_lt
            omega
          have hIndexSucc :
              UInt64.ofNat index + 1 = UInt64.ofNat (index + 1) := by
            apply UInt64.toNat.inj
            rw [UInt64.toNat_add, hIndexToNat]
            have hOne : (1 : UInt64).toNat = 1 := rfl
            rw [hOne,
              UInt64.toNat_ofNat_of_lt' hIndexSuccBound,
              Nat.mod_eq_of_lt hIndexSuccBound]
          have hIndexSuccToNat :
              (UInt64.ofNat (index + 1)).toNat = index + 1 :=
            UInt64.toNat_ofNat_of_lt' hIndexSuccBound
          rw [hIndexSucc]
          have hNextFrame :
              ({
                params := (loopFrame scratch frame inputPtr input.size
                  (.i64 input[index]) index).params
                locals := (loopFrame scratch frame inputPtr input.size
                  (.i64 input[index]) index).locals.set
                    (scratch + 2 - (loopFrame scratch frame inputPtr
                      input.size (.i64 input[index]) index).params.length)
                    (.i64 (UInt64.ofNat (index + 1)))
                values := (loopFrame scratch frame inputPtr input.size
                  item index).values
              } : Locals) =
                loopFrame scratch frame inputPtr input.size
                  (.i64 input[index]) (index + 1) := by
            apply Project.ProofKit.Frame.ext
            · rfl
            · simp (discharger := omega) [loopFrame, setupFrame, hParams,
                List.set_set]
            · rfl
          have hNextIndexLocal :
              (loopFrame scratch frame inputPtr input.size
                (.i64 input[index]) (index + 1)).get (scratch + 2) =
                some (.i64 (UInt64.ofNat (index + 1))) := by
            simp (discharger := omega) [loopFrame, setupFrame,
              Wasm.Locals.get, List.getElem?_set, hParams, hLocals,
              hScratchNeZero]; omega
          have hLoopSucc :
              Array.findIdx?.loop (predicate key) input (index + 1) =
                input.findIdx? (predicate key) := by
            rw [Array.findIdx?.loop.eq_def, dif_pos hIndexLt] at hLoop
            simpa [predicate, hMatch] using hLoop
          refine ⟨⟨index + 1, by omega, ?_, ?_⟩, ?_⟩
          · refine ⟨.i64 input[index], ?_⟩
            exact hNextFrame
          · exact hLoopSucc
          · rw [hNextFrame]
            simp only [searchMeasure, hNextIndexLocal, hIndexLocal,
              hIndexSuccToNat, hIndexToNat]
            omega

end Project.ProofKit.FixedArrayFindIdxEq
