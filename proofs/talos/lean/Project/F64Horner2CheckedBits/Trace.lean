import Project.F64Horner2CheckedBits.Program
import Project.F64Horner2CheckedBits.Numerical
import Interpreter.Wasm.SmallStep

/-!
# Explicit small-step trace for the guarded binary64 Horner entry

The big-step/WP execution theorem and this file are deliberately independent.
Here every compiler-generated instruction and every administrative transition
is exposed through `Wasm.SmallStep.Steps`.  The four raw-bit checks produce five
paths: rejection at the first failing check, or a fully accepted path that
executes the two rounded Horner stages.

The small-step machine uses a top-first operand stack.  Consequently the
source result fields, pushed as `status` and then `bits`, finish as
`[bits, status]`.
-/

namespace Project.F64Horner2CheckedBits.Spec

open Wasm

private abbrev halfBits : UInt64 := 0x3FE0000000000000
private abbrev absMask : UInt64 := 0x7FFFFFFFFFFFFFFF

/-- Exact word returned by the compiler-generated magnitude helper. -/
private def guardWord (bits : UInt64) : UInt64 :=
  if Project.ProofKit.F64Bounds.f64AbsBits bits ≤ halfBits then 1 else 0

private def guardChoice : Wasm.Instruction :=
  .iff 0 1 [.constI64 1] [.constI64 0] [] [.i64]

private def c2GuardChoice : Wasm.Instruction :=
  .iff 0 1
    [.localGet 1, .localSet 5, .localGet 5, .call 0,
      .constI64 0, .eqI64, .eqz]
    [.const 0] [] [.i32]

private def c1GuardChoice : Wasm.Instruction :=
  .iff 0 1
    [.localGet 2, .localSet 6, .localGet 6, .call 0,
      .constI64 0, .eqI64, .eqz]
    [.const 0] [] [.i32]

private def c0GuardChoice : Wasm.Instruction :=
  .iff 0 1
    [.localGet 3, .localSet 7, .localGet 7, .call 0,
      .constI64 0, .eqI64, .eqz]
    [.const 0] [] [.i32]

private def acceptedBody : Wasm.Program :=
  [.constI64 0,
   .localSet 8,
   .localGet 1,
   .f64ReinterpretI64,
   .localGet 0,
   .f64ReinterpretI64,
   .f64Mul,
   .i64ReinterpretF64,
   .f64ReinterpretI64,
   .localGet 2,
   .f64ReinterpretI64,
   .f64Add,
   .i64ReinterpretF64,
   .f64ReinterpretI64,
   .localGet 0,
   .f64ReinterpretI64,
   .f64Mul,
   .i64ReinterpretF64,
   .f64ReinterpretI64,
   .localGet 3,
   .f64ReinterpretI64,
   .f64Add,
   .i64ReinterpretF64,
   .localSet 9]

private def rejectedBody : Wasm.Program :=
  [.constI64 1, .localSet 8, .constI64 0, .localSet 9]

private def resultChoice : Wasm.Instruction :=
  .iff 0 0 acceptedBody rejectedBody

/-- The twelve relational transitions made by one internal call to the
generated raw-bit magnitude helper. -/
private def guardCallTrace (bits : UInt64) : List Wasm.SmallStep.StepKind :=
  [.instruction (.call 0),
   .instruction (.localGet 0),
   .instruction (.constI64 absMask),
   .instruction .andI64,
   .instruction (.constI64 halfBits),
   .instruction .leUI64,
   .instruction guardChoice,
   .instruction (.constI64 (guardWord bits)),
   .administrative .exitControl,
   .instruction (.localSet 1),
   .instruction (.localGet 1),
   .administrative .returnFromCall]

private def firstGuardTrace (x : UInt64) : List Wasm.SmallStep.StepKind :=
  [.instruction (.localGet 0),
   .instruction (.localSet 4),
   .instruction (.localGet 4)] ++
  guardCallTrace x ++
  [.instruction (.constI64 0),
   .instruction .eqI64,
   .instruction .eqz]

/-- A short-circuit block which actually invokes the next magnitude helper. -/
private def evaluatedGuardTrace (choice : Wasm.Instruction)
    (paramIndex localIndex : Nat) (bits : UInt64) :
    List Wasm.SmallStep.StepKind :=
  [.instruction choice,
   .instruction (.localGet paramIndex),
   .instruction (.localSet localIndex),
   .instruction (.localGet localIndex)] ++
  guardCallTrace bits ++
  [.instruction (.constI64 0),
   .instruction .eqI64,
   .instruction .eqz,
   .administrative .exitControl]

/-- A short-circuit block after an earlier magnitude check has failed. -/
private def skippedGuardTrace (choice : Wasm.Instruction) :
    List Wasm.SmallStep.StepKind :=
  [.instruction choice,
   .instruction (.const 0),
   .administrative .exitControl]

/-- Compiler-generated normalization between the short-circuit result and
the final result-producing branch. -/
private def decisionTrace (accepted : Bool) : List Wasm.SmallStep.StepKind :=
  let word : UInt64 := if accepted then 1 else 0
  [.instruction guardChoice,
   .instruction (.constI64 word),
   .administrative .exitControl,
   .instruction (.constI64 1),
   .instruction .eqI64,
   .instruction guardChoice,
   .instruction (.constI64 word),
   .administrative .exitControl,
   .instruction (.constI64 0),
   .instruction .eqI64,
   .instruction .eqz]

private def acceptedTailTrace : List Wasm.SmallStep.StepKind :=
  [.instruction resultChoice,
   .instruction (.constI64 0),
   .instruction (.localSet 8),
   .instruction (.localGet 1),
   .instruction .f64ReinterpretI64,
   .instruction (.localGet 0),
   .instruction .f64ReinterpretI64,
   .instruction .f64Mul,
   .instruction .i64ReinterpretF64,
   .instruction .f64ReinterpretI64,
   .instruction (.localGet 2),
   .instruction .f64ReinterpretI64,
   .instruction .f64Add,
   .instruction .i64ReinterpretF64,
   .instruction .f64ReinterpretI64,
   .instruction (.localGet 0),
   .instruction .f64ReinterpretI64,
   .instruction .f64Mul,
   .instruction .i64ReinterpretF64,
   .instruction .f64ReinterpretI64,
   .instruction (.localGet 3),
   .instruction .f64ReinterpretI64,
   .instruction .f64Add,
   .instruction .i64ReinterpretF64,
   .instruction (.localSet 9),
   .administrative .exitControl,
   .instruction (.localGet 8),
   .instruction (.localGet 9),
   .administrative .finish]

private def rejectedTailTrace : List Wasm.SmallStep.StepKind :=
  [.instruction resultChoice,
   .instruction (.constI64 1),
   .instruction (.localSet 8),
   .instruction (.constI64 0),
   .instruction (.localSet 9),
   .administrative .exitControl,
   .instruction (.localGet 8),
   .instruction (.localGet 9),
   .administrative .finish]

private def rejectXTrace (x : UInt64) : List Wasm.SmallStep.StepKind :=
  firstGuardTrace x ++
    skippedGuardTrace c2GuardChoice ++
    skippedGuardTrace c1GuardChoice ++
    skippedGuardTrace c0GuardChoice ++
    decisionTrace false ++ rejectedTailTrace

private def rejectC2Trace (x c2 : UInt64) : List Wasm.SmallStep.StepKind :=
  firstGuardTrace x ++
    evaluatedGuardTrace c2GuardChoice 1 5 c2 ++
    skippedGuardTrace c1GuardChoice ++
    skippedGuardTrace c0GuardChoice ++
    decisionTrace false ++ rejectedTailTrace

private def rejectC1Trace (x c2 c1 : UInt64) :
    List Wasm.SmallStep.StepKind :=
  firstGuardTrace x ++
    evaluatedGuardTrace c2GuardChoice 1 5 c2 ++
    evaluatedGuardTrace c1GuardChoice 2 6 c1 ++
    skippedGuardTrace c0GuardChoice ++
    decisionTrace false ++ rejectedTailTrace

private def rejectC0Trace (x c2 c1 c0 : UInt64) :
    List Wasm.SmallStep.StepKind :=
  firstGuardTrace x ++
    evaluatedGuardTrace c2GuardChoice 1 5 c2 ++
    evaluatedGuardTrace c1GuardChoice 2 6 c1 ++
    evaluatedGuardTrace c0GuardChoice 3 7 c0 ++
    decisionTrace false ++ rejectedTailTrace

private def acceptTrace (x c2 c1 c0 : UInt64) :
    List Wasm.SmallStep.StepKind :=
  firstGuardTrace x ++
    evaluatedGuardTrace c2GuardChoice 1 5 c2 ++
    evaluatedGuardTrace c1GuardChoice 2 6 c1 ++
    evaluatedGuardTrace c0GuardChoice 3 7 c0 ++
    decisionTrace true ++ acceptedTailTrace

/-- Exact compiler trace selected by the first failing half-unit guard.  Its
five possible lengths are 47, 64, 81, 98, and 118 transitions. -/
def horner2Trace (x c2 c1 c0 : UInt64) : List Wasm.SmallStep.StepKind :=
  if Project.ProofKit.F64Bounds.f64AbsBits x ≤ halfBits then
    if Project.ProofKit.F64Bounds.f64AbsBits c2 ≤ halfBits then
      if Project.ProofKit.F64Bounds.f64AbsBits c1 ≤ halfBits then
        if Project.ProofKit.F64Bounds.f64AbsBits c0 ≤ halfBits then
          acceptTrace x c2 c1 c0
        else
          rejectC0Trace x c2 c1 c0
      else
        rejectC1Trace x c2 c1
    else
      rejectC2Trace x c2
  else
    rejectXTrace x

private def horner2MachineStore (initial : Wasm.Store Unit) :
    Wasm.SmallStep.MachineStore Unit :=
  { runtime :=
      { instances :=
          #[{ module := Project.F64Horner2CheckedBits.«module», host := {} }]
        entry := ⟨0⟩ }
    wasm := initial }

/-- Initial authoritative small-step configuration for the generated export. -/
def horner2Config (initial : Wasm.Store Unit) (x c2 c1 c0 : UInt64) :
    Wasm.SmallStep.Config Unit :=
  { expr := .running
      { locals :=
          { params := [.i64 x, .i64 c2, .i64 c1, .i64 c0]
            locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0]
            values := [] }
        code := Project.F64Horner2CheckedBits.func1
        resultArity := 2
        callerRemainder := [] }
    store := horner2MachineStore initial }

/-! The helper is stated over an arbitrary caller continuation and frame
stacks so the same twelve-transition proof composes at all four call sites,
including calls nested in compiler-generated `if` control frames. -/

private theorem guardCall_steps
    (initial : Wasm.Store Unit)
    {params localValues values : List Wasm.Value}
    {code : Wasm.Program} {resultArity : Nat}
    {callerRemainder : List Wasm.Value}
    {control : List Wasm.SmallStep.ControlFrame}
    {calls : List Wasm.SmallStep.CallFrame}
    (bits : UInt64) :
    Wasm.SmallStep.Steps
      ⟨.running
        { locals :=
            { params := params, locals := localValues,
              values := .i64 bits :: values }
          code := .call 0 :: code
          resultArity := resultArity
          callerRemainder := callerRemainder
          control := control
          calls := calls },
        horner2MachineStore initial⟩
      (guardCallTrace bits)
      ⟨.running
        { locals :=
            { params := params, locals := localValues,
              values := .i64 (guardWord bits) :: values }
          code := code
          resultArity := resultArity
          callerRemainder := callerRemainder
          control := control
          calls := calls },
        horner2MachineStore initial⟩ := by
  by_cases hguard :
      Project.ProofKit.F64Bounds.f64AbsBits bits ≤ halfBits
  · simp only [guardCallTrace, guardWord, if_pos hguard]
    apply Wasm.SmallStep.Steps.cons
      (.call
        (fn := Project.F64Horner2CheckedBits.func0Def)
        (by simp [horner2MachineStore,
          Project.F64Horner2CheckedBits.«module»])
        (by simp [horner2MachineStore,
          Project.F64Horner2CheckedBits.«module»]))
    apply Wasm.SmallStep.Steps.cons (.localGet rfl)
    apply Wasm.SmallStep.Steps.cons .constI64
    apply Wasm.SmallStep.Steps.cons .andI64
    apply Wasm.SmallStep.Steps.cons .constI64
    apply Wasm.SmallStep.Steps.cons
      (.leUI64 (result := 1) (by
        change (1 : UInt32) =
          if Project.ProofKit.F64Bounds.f64AbsBits bits ≤ halfBits then
            1
          else
            0
        rw [if_pos hguard]))
    apply Wasm.SmallStep.Steps.cons (.iff rfl)
    apply Wasm.SmallStep.Steps.cons .constI64
    apply Wasm.SmallStep.Steps.cons (.exitControl rfl)
    apply Wasm.SmallStep.Steps.cons (.localSet rfl)
    apply Wasm.SmallStep.Steps.cons (.localGet rfl)
    apply Wasm.SmallStep.Steps.cons (.returnFromCallFallthrough rfl)
    simpa [horner2MachineStore, guardChoice,
      Project.F64Horner2CheckedBits.func0,
      Project.F64Horner2CheckedBits.func0Def,
      Wasm.Function.numParams,
      Wasm.SmallStep.resumeCaller] using
      (Wasm.SmallStep.Steps.refl
        (⟨.running
          { locals :=
              { params := params, locals := localValues,
                values := .i64 1 :: values }
            code := code
            resultArity := resultArity
            callerRemainder := callerRemainder
            control := control
            calls := calls },
          horner2MachineStore initial⟩ : Wasm.SmallStep.Config Unit))
  · simp only [guardCallTrace, guardWord, if_neg hguard]
    apply Wasm.SmallStep.Steps.cons
      (.call
        (fn := Project.F64Horner2CheckedBits.func0Def)
        (by simp [horner2MachineStore,
          Project.F64Horner2CheckedBits.«module»])
        (by simp [horner2MachineStore,
          Project.F64Horner2CheckedBits.«module»]))
    apply Wasm.SmallStep.Steps.cons (.localGet rfl)
    apply Wasm.SmallStep.Steps.cons .constI64
    apply Wasm.SmallStep.Steps.cons .andI64
    apply Wasm.SmallStep.Steps.cons .constI64
    apply Wasm.SmallStep.Steps.cons
      (.leUI64 (result := 0) (by
        change (0 : UInt32) =
          if Project.ProofKit.F64Bounds.f64AbsBits bits ≤ halfBits then
            1
          else
            0
        rw [if_neg hguard]))
    apply Wasm.SmallStep.Steps.cons (.iff rfl)
    apply Wasm.SmallStep.Steps.cons .constI64
    apply Wasm.SmallStep.Steps.cons (.exitControl rfl)
    apply Wasm.SmallStep.Steps.cons (.localSet rfl)
    apply Wasm.SmallStep.Steps.cons (.localGet rfl)
    apply Wasm.SmallStep.Steps.cons (.returnFromCallFallthrough rfl)
    simpa [horner2MachineStore, guardChoice,
      Project.F64Horner2CheckedBits.func0,
      Project.F64Horner2CheckedBits.func0Def,
      Wasm.Function.numParams,
      Wasm.SmallStep.resumeCaller] using
      (Wasm.SmallStep.Steps.refl
        (⟨.running
          { locals :=
              { params := params, locals := localValues,
                values := .i64 0 :: values }
            code := code
            resultArity := resultArity
            callerRemainder := callerRemainder
            control := control
            calls := calls },
          horner2MachineStore initial⟩ : Wasm.SmallStep.Config Unit))

/-- Every input follows its exact finite relational trace through the generated
export, preserves the complete machine store, and returns the two modeled
words. -/
theorem horner2CheckedBits_steps
    (initial : Wasm.Store Unit) (x c2 c1 c0 : UInt64) :
    Wasm.SmallStep.Steps
      (horner2Config initial x c2 c1 c0)
      (horner2Trace x c2 c1 c0)
      ⟨.done
          [.i64 (horner2ResultBitsModel x c2 c1 c0),
           .i64 (horner2StatusModel x c2 c1 c0)],
        (horner2Config initial x c2 c1 c0).store⟩ := by
  by_cases hx :
      Project.ProofKit.F64Bounds.f64AbsBits x ≤ halfBits
  · by_cases hc2 :
        Project.ProofKit.F64Bounds.f64AbsBits c2 ≤ halfBits
    · by_cases hc1 :
          Project.ProofKit.F64Bounds.f64AbsBits c1 ≤ halfBits
      · by_cases hc0 :
            Project.ProofKit.F64Bounds.f64AbsBits c0 ≤ halfBits
        · simp only [horner2Trace, if_pos hx, if_pos hc2,
            if_pos hc1, if_pos hc0]
          unfold acceptTrace firstGuardTrace evaluatedGuardTrace
            decisionTrace acceptedTailTrace
          simp only [List.cons_append, List.nil_append]

          apply Wasm.SmallStep.Steps.cons (.localGet rfl)
          apply Wasm.SmallStep.Steps.cons (.localSet rfl)
          apply Wasm.SmallStep.Steps.cons (.localGet rfl)
          refine (guardCall_steps (initial := initial) (bits := x)).trans ?_
          apply Wasm.SmallStep.Steps.cons .constI64
          apply Wasm.SmallStep.Steps.cons
            (.eqI64 (result := 0) (by simp [guardWord, hx]))
          apply Wasm.SmallStep.Steps.cons (.eqz (result := 1) rfl)

          apply Wasm.SmallStep.Steps.cons (.iff rfl)
          apply Wasm.SmallStep.Steps.cons (.localGet rfl)
          apply Wasm.SmallStep.Steps.cons (.localSet rfl)
          apply Wasm.SmallStep.Steps.cons (.localGet rfl)
          refine (guardCall_steps (initial := initial) (bits := c2)).trans ?_
          apply Wasm.SmallStep.Steps.cons .constI64
          apply Wasm.SmallStep.Steps.cons
            (.eqI64 (result := 0) (by simp [guardWord, hc2]))
          apply Wasm.SmallStep.Steps.cons (.eqz (result := 1) rfl)
          apply Wasm.SmallStep.Steps.cons (.exitControl rfl)

          apply Wasm.SmallStep.Steps.cons (.iff rfl)
          apply Wasm.SmallStep.Steps.cons (.localGet rfl)
          apply Wasm.SmallStep.Steps.cons (.localSet rfl)
          apply Wasm.SmallStep.Steps.cons (.localGet rfl)
          refine (guardCall_steps (initial := initial) (bits := c1)).trans ?_
          apply Wasm.SmallStep.Steps.cons .constI64
          apply Wasm.SmallStep.Steps.cons
            (.eqI64 (result := 0) (by simp [guardWord, hc1]))
          apply Wasm.SmallStep.Steps.cons (.eqz (result := 1) rfl)
          apply Wasm.SmallStep.Steps.cons (.exitControl rfl)

          apply Wasm.SmallStep.Steps.cons (.iff rfl)
          apply Wasm.SmallStep.Steps.cons (.localGet rfl)
          apply Wasm.SmallStep.Steps.cons (.localSet rfl)
          apply Wasm.SmallStep.Steps.cons (.localGet rfl)
          refine (guardCall_steps (initial := initial) (bits := c0)).trans ?_
          apply Wasm.SmallStep.Steps.cons .constI64
          apply Wasm.SmallStep.Steps.cons
            (.eqI64 (result := 0) (by simp [guardWord, hc0]))
          apply Wasm.SmallStep.Steps.cons (.eqz (result := 1) rfl)
          apply Wasm.SmallStep.Steps.cons (.exitControl rfl)

          apply Wasm.SmallStep.Steps.cons (.iff rfl)
          apply Wasm.SmallStep.Steps.cons .constI64
          apply Wasm.SmallStep.Steps.cons (.exitControl rfl)
          apply Wasm.SmallStep.Steps.cons .constI64
          apply Wasm.SmallStep.Steps.cons
            (.eqI64 (result := 1) rfl)
          apply Wasm.SmallStep.Steps.cons (.iff rfl)
          apply Wasm.SmallStep.Steps.cons .constI64
          apply Wasm.SmallStep.Steps.cons (.exitControl rfl)
          apply Wasm.SmallStep.Steps.cons .constI64
          apply Wasm.SmallStep.Steps.cons
            (.eqI64 (result := 0) rfl)
          apply Wasm.SmallStep.Steps.cons (.eqz (result := 1) rfl)

          apply Wasm.SmallStep.Steps.cons (.iff rfl)
          apply Wasm.SmallStep.Steps.cons .constI64
          apply Wasm.SmallStep.Steps.cons (.localSet rfl)
          apply Wasm.SmallStep.Steps.cons (.localGet rfl)
          apply Wasm.SmallStep.Steps.cons (.scalarFloat1 rfl rfl)
          apply Wasm.SmallStep.Steps.cons (.localGet rfl)
          apply Wasm.SmallStep.Steps.cons (.scalarFloat1 rfl rfl)
          apply Wasm.SmallStep.Steps.cons (.scalarFloat2 rfl rfl rfl)
          apply Wasm.SmallStep.Steps.cons (.scalarFloat1 rfl rfl)
          apply Wasm.SmallStep.Steps.cons (.scalarFloat1 rfl rfl)
          apply Wasm.SmallStep.Steps.cons (.localGet rfl)
          apply Wasm.SmallStep.Steps.cons (.scalarFloat1 rfl rfl)
          apply Wasm.SmallStep.Steps.cons (.scalarFloat2 rfl rfl rfl)
          apply Wasm.SmallStep.Steps.cons (.scalarFloat1 rfl rfl)
          apply Wasm.SmallStep.Steps.cons (.scalarFloat1 rfl rfl)
          apply Wasm.SmallStep.Steps.cons (.localGet rfl)
          apply Wasm.SmallStep.Steps.cons (.scalarFloat1 rfl rfl)
          apply Wasm.SmallStep.Steps.cons (.scalarFloat2 rfl rfl rfl)
          apply Wasm.SmallStep.Steps.cons (.scalarFloat1 rfl rfl)
          apply Wasm.SmallStep.Steps.cons (.scalarFloat1 rfl rfl)
          apply Wasm.SmallStep.Steps.cons (.localGet rfl)
          apply Wasm.SmallStep.Steps.cons (.scalarFloat1 rfl rfl)
          apply Wasm.SmallStep.Steps.cons (.scalarFloat2 rfl rfl rfl)
          apply Wasm.SmallStep.Steps.cons (.scalarFloat1 rfl rfl)
          apply Wasm.SmallStep.Steps.cons (.localSet rfl)
          apply Wasm.SmallStep.Steps.cons (.exitControl rfl)
          apply Wasm.SmallStep.Steps.cons (.localGet rfl)
          apply Wasm.SmallStep.Steps.cons (.localGet rfl)
          apply Wasm.SmallStep.Steps.cons .finish
          simpa [horner2Config, horner2MachineStore, resultChoice,
            acceptedBody, c2GuardChoice, c1GuardChoice, c0GuardChoice,
            guardChoice, horner2ResultBitsModel, horner2StatusModel,
            horner2Guard, Project.ProofKit.F64Bounds.boundedByHalfBits,
            hx, hc2, hc1, hc0, horner2BitsModel,
            Project.ProofKit.F64Numerical.horner2Bits,
            Project.ProofKit.F64Numerical.hornerStepBits,
            Wasm.f64Mul, Wasm.f64Add,
            Project.F64Horner2CheckedBits.func1] using
            (Wasm.SmallStep.Steps.refl
              (⟨.done [.i64 (horner2BitsModel x c2 c1 c0), .i64 0],
                horner2MachineStore initial⟩ :
                Wasm.SmallStep.Config Unit))
        · simp only [horner2Trace, if_pos hx, if_pos hc2,
            if_pos hc1, if_neg hc0]
          unfold rejectC0Trace firstGuardTrace evaluatedGuardTrace
            decisionTrace rejectedTailTrace
          simp only [List.cons_append, List.nil_append]

          apply Wasm.SmallStep.Steps.cons (.localGet rfl)
          apply Wasm.SmallStep.Steps.cons (.localSet rfl)
          apply Wasm.SmallStep.Steps.cons (.localGet rfl)
          refine (guardCall_steps (initial := initial) (bits := x)).trans ?_
          apply Wasm.SmallStep.Steps.cons .constI64
          apply Wasm.SmallStep.Steps.cons
            (.eqI64 (result := 0) (by simp [guardWord, hx]))
          apply Wasm.SmallStep.Steps.cons (.eqz (result := 1) rfl)

          apply Wasm.SmallStep.Steps.cons (.iff rfl)
          apply Wasm.SmallStep.Steps.cons (.localGet rfl)
          apply Wasm.SmallStep.Steps.cons (.localSet rfl)
          apply Wasm.SmallStep.Steps.cons (.localGet rfl)
          refine (guardCall_steps (initial := initial) (bits := c2)).trans ?_
          apply Wasm.SmallStep.Steps.cons .constI64
          apply Wasm.SmallStep.Steps.cons
            (.eqI64 (result := 0) (by simp [guardWord, hc2]))
          apply Wasm.SmallStep.Steps.cons (.eqz (result := 1) rfl)
          apply Wasm.SmallStep.Steps.cons (.exitControl rfl)

          apply Wasm.SmallStep.Steps.cons (.iff rfl)
          apply Wasm.SmallStep.Steps.cons (.localGet rfl)
          apply Wasm.SmallStep.Steps.cons (.localSet rfl)
          apply Wasm.SmallStep.Steps.cons (.localGet rfl)
          refine (guardCall_steps (initial := initial) (bits := c1)).trans ?_
          apply Wasm.SmallStep.Steps.cons .constI64
          apply Wasm.SmallStep.Steps.cons
            (.eqI64 (result := 0) (by simp [guardWord, hc1]))
          apply Wasm.SmallStep.Steps.cons (.eqz (result := 1) rfl)
          apply Wasm.SmallStep.Steps.cons (.exitControl rfl)

          apply Wasm.SmallStep.Steps.cons (.iff rfl)
          apply Wasm.SmallStep.Steps.cons (.localGet rfl)
          apply Wasm.SmallStep.Steps.cons (.localSet rfl)
          apply Wasm.SmallStep.Steps.cons (.localGet rfl)
          refine (guardCall_steps (initial := initial) (bits := c0)).trans ?_
          apply Wasm.SmallStep.Steps.cons .constI64
          apply Wasm.SmallStep.Steps.cons
            (.eqI64 (result := 1) (by simp [guardWord, hc0]))
          apply Wasm.SmallStep.Steps.cons (.eqz (result := 0) rfl)
          apply Wasm.SmallStep.Steps.cons (.exitControl rfl)

          apply Wasm.SmallStep.Steps.cons (.iff rfl)
          apply Wasm.SmallStep.Steps.cons .constI64
          apply Wasm.SmallStep.Steps.cons (.exitControl rfl)
          apply Wasm.SmallStep.Steps.cons .constI64
          apply Wasm.SmallStep.Steps.cons
            (.eqI64 (result := 0) rfl)
          apply Wasm.SmallStep.Steps.cons (.iff rfl)
          apply Wasm.SmallStep.Steps.cons .constI64
          apply Wasm.SmallStep.Steps.cons (.exitControl rfl)
          apply Wasm.SmallStep.Steps.cons .constI64
          apply Wasm.SmallStep.Steps.cons
            (.eqI64 (result := 1) rfl)
          apply Wasm.SmallStep.Steps.cons (.eqz (result := 0) rfl)

          apply Wasm.SmallStep.Steps.cons (.iff rfl)
          apply Wasm.SmallStep.Steps.cons .constI64
          apply Wasm.SmallStep.Steps.cons (.localSet rfl)
          apply Wasm.SmallStep.Steps.cons .constI64
          apply Wasm.SmallStep.Steps.cons (.localSet rfl)
          apply Wasm.SmallStep.Steps.cons (.exitControl rfl)
          apply Wasm.SmallStep.Steps.cons (.localGet rfl)
          apply Wasm.SmallStep.Steps.cons (.localGet rfl)
          apply Wasm.SmallStep.Steps.cons .finish
          simpa [horner2Config, horner2MachineStore, resultChoice,
            rejectedBody, c2GuardChoice, c1GuardChoice, c0GuardChoice,
            guardChoice, horner2ResultBitsModel, horner2StatusModel,
            horner2Guard, Project.ProofKit.F64Bounds.boundedByHalfBits,
            hx, hc2, hc1, hc0,
            Project.F64Horner2CheckedBits.func1] using
            (Wasm.SmallStep.Steps.refl
              (⟨.done [.i64 0, .i64 1], horner2MachineStore initial⟩ :
                Wasm.SmallStep.Config Unit))
      · simp only [horner2Trace, if_pos hx, if_pos hc2, if_neg hc1]
        unfold rejectC1Trace firstGuardTrace evaluatedGuardTrace
          skippedGuardTrace decisionTrace rejectedTailTrace
        simp only [List.cons_append, List.nil_append]

        apply Wasm.SmallStep.Steps.cons (.localGet rfl)
        apply Wasm.SmallStep.Steps.cons (.localSet rfl)
        apply Wasm.SmallStep.Steps.cons (.localGet rfl)
        refine (guardCall_steps (initial := initial) (bits := x)).trans ?_
        apply Wasm.SmallStep.Steps.cons .constI64
        apply Wasm.SmallStep.Steps.cons
          (.eqI64 (result := 0) (by simp [guardWord, hx]))
        apply Wasm.SmallStep.Steps.cons (.eqz (result := 1) rfl)

        apply Wasm.SmallStep.Steps.cons (.iff rfl)
        apply Wasm.SmallStep.Steps.cons (.localGet rfl)
        apply Wasm.SmallStep.Steps.cons (.localSet rfl)
        apply Wasm.SmallStep.Steps.cons (.localGet rfl)
        refine (guardCall_steps (initial := initial) (bits := c2)).trans ?_
        apply Wasm.SmallStep.Steps.cons .constI64
        apply Wasm.SmallStep.Steps.cons
          (.eqI64 (result := 0) (by simp [guardWord, hc2]))
        apply Wasm.SmallStep.Steps.cons (.eqz (result := 1) rfl)
        apply Wasm.SmallStep.Steps.cons (.exitControl rfl)

        apply Wasm.SmallStep.Steps.cons (.iff rfl)
        apply Wasm.SmallStep.Steps.cons (.localGet rfl)
        apply Wasm.SmallStep.Steps.cons (.localSet rfl)
        apply Wasm.SmallStep.Steps.cons (.localGet rfl)
        refine (guardCall_steps (initial := initial) (bits := c1)).trans ?_
        apply Wasm.SmallStep.Steps.cons .constI64
        apply Wasm.SmallStep.Steps.cons
          (.eqI64 (result := 1) (by simp [guardWord, hc1]))
        apply Wasm.SmallStep.Steps.cons (.eqz (result := 0) rfl)
        apply Wasm.SmallStep.Steps.cons (.exitControl rfl)

        apply Wasm.SmallStep.Steps.cons (.iff rfl)
        apply Wasm.SmallStep.Steps.cons .const
        apply Wasm.SmallStep.Steps.cons (.exitControl rfl)

        apply Wasm.SmallStep.Steps.cons (.iff rfl)
        apply Wasm.SmallStep.Steps.cons .constI64
        apply Wasm.SmallStep.Steps.cons (.exitControl rfl)
        apply Wasm.SmallStep.Steps.cons .constI64
        apply Wasm.SmallStep.Steps.cons
          (.eqI64 (result := 0) rfl)
        apply Wasm.SmallStep.Steps.cons (.iff rfl)
        apply Wasm.SmallStep.Steps.cons .constI64
        apply Wasm.SmallStep.Steps.cons (.exitControl rfl)
        apply Wasm.SmallStep.Steps.cons .constI64
        apply Wasm.SmallStep.Steps.cons
          (.eqI64 (result := 1) rfl)
        apply Wasm.SmallStep.Steps.cons (.eqz (result := 0) rfl)

        apply Wasm.SmallStep.Steps.cons (.iff rfl)
        apply Wasm.SmallStep.Steps.cons .constI64
        apply Wasm.SmallStep.Steps.cons (.localSet rfl)
        apply Wasm.SmallStep.Steps.cons .constI64
        apply Wasm.SmallStep.Steps.cons (.localSet rfl)
        apply Wasm.SmallStep.Steps.cons (.exitControl rfl)
        apply Wasm.SmallStep.Steps.cons (.localGet rfl)
        apply Wasm.SmallStep.Steps.cons (.localGet rfl)
        apply Wasm.SmallStep.Steps.cons .finish
        simpa [horner2Config, horner2MachineStore, resultChoice,
          rejectedBody, c2GuardChoice, c1GuardChoice, c0GuardChoice,
          guardChoice, horner2ResultBitsModel, horner2StatusModel,
          horner2Guard, Project.ProofKit.F64Bounds.boundedByHalfBits,
          hx, hc2, hc1,
          Project.F64Horner2CheckedBits.func1] using
          (Wasm.SmallStep.Steps.refl
            (⟨.done [.i64 0, .i64 1], horner2MachineStore initial⟩ :
              Wasm.SmallStep.Config Unit))
    · simp only [horner2Trace, if_pos hx, if_neg hc2]
      unfold rejectC2Trace firstGuardTrace evaluatedGuardTrace
        skippedGuardTrace decisionTrace rejectedTailTrace
      simp only [List.cons_append, List.nil_append]

      apply Wasm.SmallStep.Steps.cons (.localGet rfl)
      apply Wasm.SmallStep.Steps.cons (.localSet rfl)
      apply Wasm.SmallStep.Steps.cons (.localGet rfl)
      refine (guardCall_steps (initial := initial) (bits := x)).trans ?_
      apply Wasm.SmallStep.Steps.cons .constI64
      apply Wasm.SmallStep.Steps.cons
        (.eqI64 (result := 0) (by simp [guardWord, hx]))
      apply Wasm.SmallStep.Steps.cons (.eqz (result := 1) rfl)

      apply Wasm.SmallStep.Steps.cons (.iff rfl)
      apply Wasm.SmallStep.Steps.cons (.localGet rfl)
      apply Wasm.SmallStep.Steps.cons (.localSet rfl)
      apply Wasm.SmallStep.Steps.cons (.localGet rfl)
      refine (guardCall_steps (initial := initial) (bits := c2)).trans ?_
      apply Wasm.SmallStep.Steps.cons .constI64
      apply Wasm.SmallStep.Steps.cons
        (.eqI64 (result := 1) (by simp [guardWord, hc2]))
      apply Wasm.SmallStep.Steps.cons (.eqz (result := 0) rfl)
      apply Wasm.SmallStep.Steps.cons (.exitControl rfl)

      apply Wasm.SmallStep.Steps.cons (.iff rfl)
      apply Wasm.SmallStep.Steps.cons .const
      apply Wasm.SmallStep.Steps.cons (.exitControl rfl)
      apply Wasm.SmallStep.Steps.cons (.iff rfl)
      apply Wasm.SmallStep.Steps.cons .const
      apply Wasm.SmallStep.Steps.cons (.exitControl rfl)

      apply Wasm.SmallStep.Steps.cons (.iff rfl)
      apply Wasm.SmallStep.Steps.cons .constI64
      apply Wasm.SmallStep.Steps.cons (.exitControl rfl)
      apply Wasm.SmallStep.Steps.cons .constI64
      apply Wasm.SmallStep.Steps.cons
        (.eqI64 (result := 0) rfl)
      apply Wasm.SmallStep.Steps.cons (.iff rfl)
      apply Wasm.SmallStep.Steps.cons .constI64
      apply Wasm.SmallStep.Steps.cons (.exitControl rfl)
      apply Wasm.SmallStep.Steps.cons .constI64
      apply Wasm.SmallStep.Steps.cons
        (.eqI64 (result := 1) rfl)
      apply Wasm.SmallStep.Steps.cons (.eqz (result := 0) rfl)

      apply Wasm.SmallStep.Steps.cons (.iff rfl)
      apply Wasm.SmallStep.Steps.cons .constI64
      apply Wasm.SmallStep.Steps.cons (.localSet rfl)
      apply Wasm.SmallStep.Steps.cons .constI64
      apply Wasm.SmallStep.Steps.cons (.localSet rfl)
      apply Wasm.SmallStep.Steps.cons (.exitControl rfl)
      apply Wasm.SmallStep.Steps.cons (.localGet rfl)
      apply Wasm.SmallStep.Steps.cons (.localGet rfl)
      apply Wasm.SmallStep.Steps.cons .finish
      simpa [horner2Config, horner2MachineStore, resultChoice,
        rejectedBody, c2GuardChoice, c1GuardChoice, c0GuardChoice,
        guardChoice, horner2ResultBitsModel, horner2StatusModel,
        horner2Guard, Project.ProofKit.F64Bounds.boundedByHalfBits,
        hx, hc2,
        Project.F64Horner2CheckedBits.func1] using
        (Wasm.SmallStep.Steps.refl
          (⟨.done [.i64 0, .i64 1], horner2MachineStore initial⟩ :
            Wasm.SmallStep.Config Unit))
  · simp only [horner2Trace, if_neg hx]
    unfold rejectXTrace firstGuardTrace skippedGuardTrace
      decisionTrace rejectedTailTrace
    simp only [List.cons_append, List.nil_append]

    apply Wasm.SmallStep.Steps.cons (.localGet rfl)
    apply Wasm.SmallStep.Steps.cons (.localSet rfl)
    apply Wasm.SmallStep.Steps.cons (.localGet rfl)
    refine (guardCall_steps (initial := initial) (bits := x)).trans ?_
    apply Wasm.SmallStep.Steps.cons .constI64
    apply Wasm.SmallStep.Steps.cons
      (.eqI64 (result := 1) (by simp [guardWord, hx]))
    apply Wasm.SmallStep.Steps.cons (.eqz (result := 0) rfl)

    apply Wasm.SmallStep.Steps.cons (.iff rfl)
    apply Wasm.SmallStep.Steps.cons .const
    apply Wasm.SmallStep.Steps.cons (.exitControl rfl)
    apply Wasm.SmallStep.Steps.cons (.iff rfl)
    apply Wasm.SmallStep.Steps.cons .const
    apply Wasm.SmallStep.Steps.cons (.exitControl rfl)
    apply Wasm.SmallStep.Steps.cons (.iff rfl)
    apply Wasm.SmallStep.Steps.cons .const
    apply Wasm.SmallStep.Steps.cons (.exitControl rfl)

    apply Wasm.SmallStep.Steps.cons (.iff rfl)
    apply Wasm.SmallStep.Steps.cons .constI64
    apply Wasm.SmallStep.Steps.cons (.exitControl rfl)
    apply Wasm.SmallStep.Steps.cons .constI64
    apply Wasm.SmallStep.Steps.cons
      (.eqI64 (result := 0) rfl)
    apply Wasm.SmallStep.Steps.cons (.iff rfl)
    apply Wasm.SmallStep.Steps.cons .constI64
    apply Wasm.SmallStep.Steps.cons (.exitControl rfl)
    apply Wasm.SmallStep.Steps.cons .constI64
    apply Wasm.SmallStep.Steps.cons
      (.eqI64 (result := 1) rfl)
    apply Wasm.SmallStep.Steps.cons (.eqz (result := 0) rfl)

    apply Wasm.SmallStep.Steps.cons (.iff rfl)
    apply Wasm.SmallStep.Steps.cons .constI64
    apply Wasm.SmallStep.Steps.cons (.localSet rfl)
    apply Wasm.SmallStep.Steps.cons .constI64
    apply Wasm.SmallStep.Steps.cons (.localSet rfl)
    apply Wasm.SmallStep.Steps.cons (.exitControl rfl)
    apply Wasm.SmallStep.Steps.cons (.localGet rfl)
    apply Wasm.SmallStep.Steps.cons (.localGet rfl)
    apply Wasm.SmallStep.Steps.cons .finish
    simpa [horner2Config, horner2MachineStore, resultChoice,
      rejectedBody, c2GuardChoice, c1GuardChoice, c0GuardChoice,
      guardChoice, horner2ResultBitsModel, horner2StatusModel,
      horner2Guard, Project.ProofKit.F64Bounds.boundedByHalfBits,
      hx, Project.F64Horner2CheckedBits.func1] using
      (Wasm.SmallStep.Steps.refl
        (⟨.done [.i64 0, .i64 1], horner2MachineStore initial⟩ :
          Wasm.SmallStep.Config Unit))

/-- Fuel-free total correctness obtained from the explicit finite trace. -/
theorem horner2CheckedBits_smallStep_exact
    (initial : Wasm.Store Unit) (x c2 c1 c0 : UInt64) :
    Wasm.SmallStep.TerminatesWith
      (horner2Config initial x c2 c1 c0)
      (fun values final =>
        values =
          [.i64 (horner2ResultBitsModel x c2 c1 c0),
           .i64 (horner2StatusModel x c2 c1 c0)] ∧
        final = (horner2Config initial x c2 c1 c0).store) :=
  Wasm.SmallStep.TerminatesWith.of_steps
    (horner2CheckedBits_steps initial x c2 c1 c0) ⟨rfl, rfl⟩

/-- The relational trace carries the same total checked numerical result as
the source-facing pure IEEE64 theorem. -/
theorem horner2CheckedBits_smallStep_real_error
    (initial : Wasm.Store Unit) (x c2 c1 c0 : UInt64) :
    Wasm.SmallStep.TerminatesWith
      (horner2Config initial x c2 c1 c0)
      (fun values final =>
        values =
          [.i64 (horner2ResultBitsModel x c2 c1 c0),
           .i64 (horner2StatusModel x c2 c1 c0)] ∧
        final = (horner2Config initial x c2 c1 c0).store ∧
        CheckedResult x c2 c1 c0
          (horner2StatusModel x c2 c1 c0)
          (horner2ResultBitsModel x c2 c1 c0)) := by
  refine (horner2CheckedBits_smallStep_exact initial x c2 c1 c0).mono ?_
  rintro values final ⟨rfl, rfl⟩
  exact ⟨rfl, rfl, horner2CheckedBits_source_real_error x c2 c1 c0⟩

#print axioms horner2CheckedBits_steps
#print axioms horner2CheckedBits_smallStep_exact
#print axioms horner2CheckedBits_smallStep_real_error

end Project.F64Horner2CheckedBits.Spec
