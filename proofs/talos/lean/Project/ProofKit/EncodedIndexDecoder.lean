import Interpreter.Wasm.Wp.Tactic

namespace Project.ProofKit.EncodedIndexDecoder

open Wasm

def program (encodedLocal scratch decodedLocal : Nat) : Wasm.Program :=
  [
  .localGet encodedLocal,
  .constI64 0,
  .eqI64,
  .eqz,
  .iff 0 1 [
    .localGet encodedLocal,
    .localSet scratch,
    .constI64 1,
    .localSet (scratch + 1),
    .localGet scratch,
    .localGet (scratch + 1),
    .ltUI64,
    .iff 0 1 [
      .constI64 0
    ] [
      .localGet scratch,
      .localGet (scratch + 1),
      .subI64
    ]
  ] [
    .constI64 0
  ],
  .localSet decodedLocal
  ]

def resultFrame (frame : Locals) (scratch decodedLocal : Nat)
    (encoded : UInt64) : Locals :=
  if encoded = 0 then
    { frame with
      locals := frame.locals.set
        (decodedLocal - frame.params.length) (.i64 0) }
  else
    { frame with
      locals :=
        ((frame.locals.set
            (scratch - frame.params.length) (.i64 encoded)).set
            (scratch + 1 - frame.params.length) (.i64 1)).set
            (decodedLocal - frame.params.length) (.i64 (encoded - 1)) }

@[simp]
theorem resultFrame_params (frame : Locals) (scratch decodedLocal : Nat)
    (encoded : UInt64) :
    (resultFrame frame scratch decodedLocal encoded).params = frame.params := by
  by_cases hZero : encoded = 0 <;> simp [resultFrame, hZero]

@[simp]
theorem resultFrame_locals_length (frame : Locals)
    (scratch decodedLocal : Nat) (encoded : UInt64) :
    (resultFrame frame scratch decodedLocal encoded).locals.length =
      frame.locals.length := by
  by_cases hZero : encoded = 0 <;> simp [resultFrame, hZero]

@[simp]
theorem resultFrame_values (frame : Locals) (scratch decodedLocal : Nat)
    (encoded : UInt64) :
    (resultFrame frame scratch decodedLocal encoded).values = frame.values := by
  by_cases hZero : encoded = 0 <;> simp [resultFrame, hZero]

@[simp]
theorem resultFrame_get_of_ne
    (frame : Locals) (scratch decodedLocal readLocal : Nat) (encoded : UInt64)
    (hScratchLower : frame.params.length ≤ scratch)
    (hDecodedLower : frame.params.length ≤ decodedLocal)
    (hReadLower : frame.params.length ≤ readLocal)
    (hReadValid : frame.validIndex readLocal)
    (hReadScratch : readLocal ≠ scratch)
    (hReadScratchNext : readLocal ≠ scratch + 1)
    (hReadDecoded : readLocal ≠ decodedLocal) :
    (resultFrame frame scratch decodedLocal encoded).get readLocal =
      frame.get readLocal := by
  have hReadNotParam : ¬readLocal < frame.params.length := by omega
  have hReadBound :
      readLocal < frame.params.length + frame.locals.length := hReadValid
  have hReadScratchIndex :
      readLocal - frame.params.length ≠ scratch - frame.params.length := by
    omega
  have hReadScratchNextIndex :
      readLocal - frame.params.length ≠
        scratch + 1 - frame.params.length := by
    omega
  have hReadDecodedIndex :
      readLocal - frame.params.length ≠
        decodedLocal - frame.params.length := by
    omega
  by_cases hZero : encoded = 0
  · simp [resultFrame, hZero, Wasm.Locals.get, hReadNotParam,
      hReadBound, hReadDecodedIndex.symm]
  · simp [resultFrame, hZero, Wasm.Locals.get, hReadNotParam,
      hReadBound, hReadScratchIndex.symm,
      hReadScratchNextIndex.symm, hReadDecodedIndex.symm]

@[simp]
theorem resultFrame_validIndex
    (frame : Locals) (scratch decodedLocal index : Nat) (encoded : UInt64) :
    (resultFrame frame scratch decodedLocal encoded).validIndex index ↔
      frame.validIndex index := by
  simp [Wasm.Locals.validIndex]

@[simp]
theorem resultFrame_decoded (frame : Locals) (scratch decodedLocal : Nat)
    (encoded : UInt64)
    (hDecodedLower : frame.params.length ≤ decodedLocal)
    (hDecodedValid : frame.validIndex decodedLocal) :
    (resultFrame frame scratch decodedLocal encoded).get decodedLocal =
      some (.i64 (if encoded = 0 then 0 else encoded - 1)) := by
  have hDecodedNotParam : ¬decodedLocal < frame.params.length := by omega
  have hDecodedBound :
      decodedLocal < frame.params.length + frame.locals.length := by
    exact hDecodedValid
  have hDecodedLocal :
      decodedLocal - frame.params.length < frame.locals.length := by
    omega
  by_cases hZero : encoded = 0
  · simp [resultFrame, hZero, Wasm.Locals.get, hDecodedNotParam,
      hDecodedBound, hDecodedLocal]
  · simp [resultFrame, hZero, Wasm.Locals.get, hDecodedNotParam,
      hDecodedBound, hDecodedLocal]

set_option maxHeartbeats 1000000 in
set_option Elab.async false in
theorem program_spec {α : Type}
    (encodedLocal scratch decodedLocal : Nat)
    (module_ : Wasm.Module) (env : HostEnv α) (st : Store α)
    (frame : Locals) (encoded : UInt64)
    (hEncoded : frame.get encodedLocal = some (.i64 encoded))
    (hScratchLower : frame.params.length ≤ scratch)
    (hScratchPairValid : frame.validIndex (scratch + 1))
    (hDecodedLower : frame.params.length ≤ decodedLocal)
    (hDecodedValid : frame.validIndex decodedLocal)
    (Q : Assertion α) (rest : Wasm.Program)
    (hNext :
      wp module_ rest Q st
        (resultFrame frame scratch decodedLocal encoded) env) :
    wp module_ (program encodedLocal scratch decodedLocal ++ rest)
      Q st frame env := by
  have hScratchValid : frame.validIndex scratch := by
    simpa [Wasm.Locals.validIndex] using
      (show scratch < frame.params.length + frame.locals.length by
        have := hScratchPairValid
        simp only [Wasm.Locals.validIndex] at this
        omega)
  have hScratchNotParam : ¬scratch < frame.params.length := by omega
  have hScratchPairNotParam : ¬scratch + 1 < frame.params.length := by omega
  have hDecodedNotParam : ¬decodedLocal < frame.params.length := by omega
  have hScratchBound :
      scratch < frame.params.length + frame.locals.length := hScratchValid
  have hScratchPairBound :
      scratch + 1 < frame.params.length + frame.locals.length :=
    hScratchPairValid
  have hDecodedBound :
      decodedLocal < frame.params.length + frame.locals.length := hDecodedValid
  have hScratchLocal : scratch - frame.params.length < frame.locals.length := by
    omega
  have hScratchPairLocal :
      scratch + 1 - frame.params.length < frame.locals.length := by
    omega
  have hDecodedLocal :
      decodedLocal - frame.params.length < frame.locals.length := by
    omega
  by_cases hZero : encoded = 0
  · subst encoded
    simp only [program, List.cons_append, List.nil_append,
      wp_localGet_cons, hEncoded, wp_constI64_cons, wp_eqI64_cons,
      wp_eqz_cons]
    refine wp_iff_cons rfl ?_
    simpa (discharger := omega)
      [resultFrame, wp_simp, Wasm.Locals.get, Wasm.Locals.set?,
        hDecodedNotParam, hDecodedBound, hDecodedLocal,
        List.length_set, List.getElem?_set] using hNext
  · have hNotLt : ¬encoded < (1 : UInt64) := by
      rw [UInt64.lt_iff_toNat_lt]
      have hOne : (1 : UInt64).toNat = 1 := rfl
      rw [hOne]
      have hPositive : 0 < encoded.toNat := by
        exact Nat.pos_of_ne_zero fun hNat =>
          hZero (UInt64.toNat.inj (by simpa using hNat))
      omega
    simp only [program, List.cons_append, List.nil_append,
      wp_localGet_cons, hEncoded, wp_constI64_cons, wp_eqI64_cons,
      wp_eqz_cons]
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp [hZero])]
    simp only [wp_localGet_cons, hEncoded, wp_localSet_cons]
    simp (config := { maxSteps := 10000000 }) (discharger := omega)
      [Wasm.Locals.get, Wasm.Locals.set?, hScratchNotParam,
        hScratchPairNotParam, hScratchBound, hScratchPairBound,
        hScratchPairLocal, List.length_set,
        List.getElem?_set, hNotLt]
    refine wp_iff_cons rfl ?_
    simpa (config := { maxSteps := 10000000 }) (discharger := omega)
      [resultFrame, wp_simp, hZero, Wasm.Locals.get, Wasm.Locals.set?,
        hScratchNotParam, hScratchPairNotParam, hDecodedNotParam,
        hScratchBound, hScratchPairBound, hDecodedBound, hScratchLocal,
        hScratchPairLocal, hDecodedLocal, List.length_set,
        List.getElem?_set] using hNext

end Project.ProofKit.EncodedIndexDecoder
