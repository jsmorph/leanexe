import Init.Omega
import Project.Artifact.Binary.Validate
import Project.Artifact.Binary.Validity

namespace Wasm.Binary.Validator.StackState

def toValidity (state : Validator.StackState) : Validity.Stack :=
  { values := state.values, polymorphic := state.polymorphic }

end Wasm.Binary.Validator.StackState

namespace Wasm.Binary.Validator.Context

def toValidity (context : Validator.Context) : Validity.Context :=
  { functions := context.functions
    locals := context.locals
    globals := context.globals
    labels := context.labels
    results := context.results
    hasMemory := context.hasMemory }

end Wasm.Binary.Validator.Context

namespace Wasm.Binary.Proof

@[simp] theorem toValidity_push
    (state : Validator.StackState) (type : ValType) :
    (state.push type).toValidity = state.toValidity.push type := by
  rfl

@[simp] theorem toValidity_pushMany
    (state : Validator.StackState) (types : List ValType) :
    (state.pushMany types).toValidity = state.toValidity.pushMany types := by
  rfl

@[simp] theorem toValidity_markUnreachable
    (base : Nat) (state : Validator.StackState) :
    (Validator.markUnreachable base state).toValidity =
      Validity.markUnreachable base state.toValidity := by
  rfl

theorem popExpected_sound {context : Validator.Context} {path : List Nat}
    {base : Nat} {expected : ValType} {start finish : Validator.StackState}
    (h : Validator.popExpected context path base expected start = .ok finish) :
    Validity.PopExpected base expected start.toValidity finish.toValidity := by
  unfold Validator.popExpected at h
  split at h
  · split at h
    · split at h
      · cases h
        left
        simp_all [Validator.StackState.toValidity]
      · contradiction
    · split at h
      · cases h
        right
        simp_all [Validator.StackState.toValidity]
      · contradiction
  · split at h
    · cases h
      left
      simp_all [Validator.StackState.toValidity]
    · contradiction

theorem popAny_sound {context : Validator.Context} {path : List Nat}
    {base : Nat} {start finish : Validator.StackState}
    (h : Validator.popAny context path base start = .ok finish) :
    Validity.PopAny base start.toValidity finish.toValidity := by
  unfold Validator.popAny at h
  split at h
  · split at h
    · split at h
      · cases h
        left
        simp_all [Validator.StackState.toValidity]
      · contradiction
    · cases h
      right
      simp_all [Validator.StackState.toValidity]
  · split at h
    · cases h
      left
      simp_all [Validator.StackState.toValidity]
    · contradiction

theorem popExpectedList_sound (context : Validator.Context) (path : List Nat)
    (base : Nat) (types : List ValType) (start finish : Validator.StackState)
    (h : Validator.popExpectedList context path base types start = .ok finish) :
    Validity.PopSequence base types start.toValidity finish.toValidity := by
  induction types generalizing start with
  | nil =>
      unfold Validator.popExpectedList at h
      cases h
      exact Validity.PopSequence.nil _
  | cons type rest ih =>
      unfold Validator.popExpectedList at h
      dsimp [Bind.bind, Monad.toBind, Except.bind] at h
      split at h
      · contradiction
      · rename_i parsed middle hpop
        exact Validity.PopSequence.cons type rest (start.toValidity)
          (middle.toValidity) (finish.toValidity)
          (popExpected_sound hpop) (ih middle h)

theorem popMany_sound {context : Validator.Context} {path : List Nat}
    {base : Nat} {types : List ValType} {start finish : Validator.StackState}
    (h : Validator.popMany context path base types start = .ok finish) :
    Validity.PopMany base types start.toValidity finish.toValidity := by
  exact popExpectedList_sound context path base types.reverse start finish h

theorem finishFrame_sound {context : Validator.Context} {path : List Nat}
    {base : Nat} {outer body finish : Validator.StackState}
    {results : List ValType}
    (h : Validator.finishFrame context path base outer body results = .ok finish) :
    Validity.FinishFrame base outer.toValidity body.toValidity
      finish.toValidity results := by
  unfold Validator.finishFrame at h
  dsimp [Bind.bind, Monad.toBind, Except.bind] at h
  split at h
  · contradiction
  · rename_i parsed consumed hpop
    split at h
    · rename_i hheight
      cases h
      exact ⟨consumed.toValidity, popMany_sound hpop, by exact hheight, rfl⟩
    · contradiction

theorem checkMemory_sound {context : Validator.Context} {path : List Nat}
    (h : Validator.checkMemory context path = .ok ()) :
    context.toValidity.hasMemory = true := by
  unfold Validator.checkMemory at h
  split at h
  · assumption
  · contradiction

theorem checkAlignment_sound {context : Validator.Context} {path : List Nat}
    {arg : MemArg} {maximum : UInt32}
    (h : Validator.checkAlignment context path arg maximum = .ok ()) :
    arg.align ≤ maximum := by
  unfold Validator.checkAlignment at h
  split at h
  · assumption
  · contradiction

theorem unary_sound {context : Validator.Context} {path : List Nat}
    {base : Nat} {input output : ValType} {start finish : Validator.StackState}
    (h : Validator.unary context path base input output start = .ok finish) :
    ∃ popped,
      Validity.PopExpected base input start.toValidity popped ∧
      finish.toValidity = popped.push output := by
  unfold Validator.unary at h
  dsimp [Bind.bind, Monad.toBind, Except.bind] at h
  split at h
  · contradiction
  · rename_i parsed popped hpop
    cases h
    exact ⟨popped.toValidity, popExpected_sound hpop, rfl⟩

theorem binary_sound {context : Validator.Context} {path : List Nat}
    {base : Nat} {input output : ValType} {start finish : Validator.StackState}
    (h : Validator.binary context path base input output start = .ok finish) :
    ∃ first second,
      Validity.PopExpected base input start.toValidity first ∧
      Validity.PopExpected base input first second ∧
      finish.toValidity = second.push output := by
  unfold Validator.binary at h
  dsimp [Bind.bind, Monad.toBind, Except.bind] at h
  split at h
  · contradiction
  · rename_i parsedFirst first hfirst
    split at h
    · contradiction
    · rename_i parsedSecond second hsecond
      cases h
      exact ⟨first.toValidity, second.toValidity,
        popExpected_sound hfirst, popExpected_sound hsecond, rfl⟩

theorem inSignedRange_sound {width : Nat} {value : Int}
    (h : Validator.inSignedRange width value = true) :
    -(2 : Int) ^ (width - 1) ≤ value ∧ value < (2 : Int) ^ (width - 1) := by
  simpa [Validator.inSignedRange] using h

theorem blockResults_eq (type : BlockType) :
    Validator.blockResults type = Validity.blockResults type := by
  cases type <;> rfl

mutual
  theorem validateInstr_sound (context : Validator.Context) (path : List Nat)
      (base : Nat) (start : Validator.StackState) (instr : Instr)
      (finish : Validator.StackState)
      (h : Validator.validateInstr context path base start instr = .ok finish) :
      Validity.InstrValid context.toValidity base start.toValidity instr
        finish.toValidity := by
    cases instr with
    | unreachable =>
        unfold Validator.validateInstr at h
        cases h
        exact Validity.InstrValid.unreachable start.toValidity
    | drop =>
        exact Validity.InstrValid.drop start.toValidity finish.toValidity
          (popAny_sound h)
    | block type body =>
        unfold Validator.validateInstr at h
        dsimp [Bind.bind, Monad.toBind, Except.bind] at h
        split at h
        · contradiction
        · rename_i parsed bodyFinish hbody
          apply Validity.InstrValid.block type body start.toValidity
            bodyFinish.toValidity finish.toValidity
          · have hbodyValid := validateInstrs_sound
                { context with labels := Validator.blockResults type :: context.labels }
                path start.values.length start 0 body bodyFinish hbody
            rw [blockResults_eq type] at hbodyValid
            exact hbodyValid
          · have hframeValid := finishFrame_sound h
            rw [blockResults_eq type] at hframeValid
            exact hframeValid
    | loop type body =>
        unfold Validator.validateInstr at h
        dsimp [Bind.bind, Monad.toBind, Except.bind] at h
        split at h
        · contradiction
        · rename_i parsed bodyFinish hbody
          apply Validity.InstrValid.loop type body start.toValidity
            bodyFinish.toValidity finish.toValidity
          · exact validateInstrs_sound
                { context with labels := [] :: context.labels }
                path start.values.length start 0 body bodyFinish hbody
          · have hframeValid := finishFrame_sound h
            rw [blockResults_eq type] at hframeValid
            exact hframeValid
    | iff type thenBody elseBody =>
        cases elseBody with
        | none =>
            unfold Validator.validateInstr at h
            dsimp [Bind.bind, Monad.toBind, Except.bind] at h
            split at h
            · contradiction
            · rename_i parsedOuter outer hcondition
              split at h
              · contradiction
              · rename_i parsedThen thenFinish hthen
                split at h
                · contradiction
                · rename_i parsedThenFrame thenResult hthenFrame
                  split at h
                  · contradiction
                  · rename_i parsedElseState elseState helseState
                    cases helseState
                    split at h
                    · contradiction
                    · rename_i parsedElseFrame elseResult helseFrame
                      split at h
                      · rename_i hequal
                        have hfinish : thenResult = finish := Except.ok.inj h
                        subst finish
                        rw [← hequal] at helseFrame
                        apply Validity.InstrValid.iffNone type thenBody
                          start.toValidity outer.toValidity thenFinish.toValidity
                          (Validator.StackState.toValidity thenResult)
                        · exact popExpected_sound hcondition
                        · have hthenValid := validateInstrs_sound
                              { context with labels :=
                                Validator.blockResults type :: context.labels }
                              (path ++ [0]) outer.values.length outer 0 thenBody
                              thenFinish hthen
                          rw [blockResults_eq type] at hthenValid
                          exact hthenValid
                        · have hthenFrameValid := finishFrame_sound hthenFrame
                          rw [blockResults_eq type] at hthenFrameValid
                          exact hthenFrameValid
                        · have helseFrameValid := finishFrame_sound helseFrame
                          rw [blockResults_eq type] at helseFrameValid
                          exact helseFrameValid
                      · contradiction
        | some elseBody =>
            unfold Validator.validateInstr at h
            dsimp [Bind.bind, Monad.toBind, Except.bind] at h
            split at h
            · contradiction
            · rename_i parsedOuter outer hcondition
              split at h
              · contradiction
              · rename_i parsedThen thenFinish hthen
                split at h
                · contradiction
                · rename_i parsedThenFrame thenResult hthenFrame
                  split at h
                  · contradiction
                  · rename_i parsedElse elseFinish helse
                    split at h
                    · contradiction
                    · rename_i parsedElseFrame elseResult helseFrame
                      split at h
                      · rename_i hequal
                        have hfinish : thenResult = finish := Except.ok.inj h
                        subst finish
                        rw [← hequal] at helseFrame
                        apply Validity.InstrValid.iffSome type thenBody elseBody
                          start.toValidity outer.toValidity thenFinish.toValidity
                          elseFinish.toValidity
                          (Validator.StackState.toValidity thenResult)
                        · exact popExpected_sound hcondition
                        · have hthenValid := validateInstrs_sound
                              { context with labels :=
                                Validator.blockResults type :: context.labels }
                              (path ++ [0]) outer.values.length outer 0 thenBody
                              thenFinish hthen
                          rw [blockResults_eq type] at hthenValid
                          exact hthenValid
                        · have helseValid := validateInstrs_sound
                              { context with labels :=
                                Validator.blockResults type :: context.labels }
                              (path ++ [1]) outer.values.length outer 0 elseBody
                              elseFinish helse
                          rw [blockResults_eq type] at helseValid
                          exact helseValid
                        · have hthenFrameValid := finishFrame_sound hthenFrame
                          rw [blockResults_eq type] at hthenFrameValid
                          exact hthenFrameValid
                        · have helseFrameValid := finishFrame_sound helseFrame
                          rw [blockResults_eq type] at helseFrameValid
                          exact helseFrameValid
                      · contradiction
    | br depth =>
        unfold Validator.validateInstr at h
        cases hlabel : context.labels[depth.toNat]? with
        | none =>
            rw [hlabel] at h
            contradiction
        | some types =>
            rw [hlabel] at h
            dsimp [Bind.bind, Monad.toBind, Except.bind] at h
            split at h
            · contradiction
            · rename_i parsed popped hpop
              cases h
              exact Validity.InstrValid.br depth types start.toValidity
                popped.toValidity hlabel (popMany_sound hpop)
    | brIf depth =>
        unfold Validator.validateInstr at h
        dsimp [Bind.bind, Monad.toBind, Except.bind] at h
        split at h
        · contradiction
        · rename_i parsedCondition afterCondition hcondition
          cases hlabel : context.labels[depth.toNat]? with
          | none =>
              rw [hlabel] at h
              contradiction
          | some types =>
              simp only [hlabel] at h
              split at h
              · contradiction
              · rename_i parsedOperands popped hpop
                cases h
                exact Validity.InstrValid.brIf depth types start.toValidity
                  afterCondition.toValidity popped.toValidity
                  (popExpected_sound hcondition) hlabel (popMany_sound hpop)
    | ret =>
        unfold Validator.validateInstr at h
        dsimp [Bind.bind, Monad.toBind, Except.bind] at h
        split at h
        · contradiction
        · rename_i parsed popped hpop
          cases h
          exact Validity.InstrValid.ret start.toValidity popped.toValidity
            (popMany_sound hpop)
    | call index =>
        unfold Validator.validateInstr at h
        cases htype : context.functions[index.toNat]? with
        | none =>
            rw [htype] at h
            contradiction
        | some type =>
            rw [htype] at h
            dsimp [Bind.bind, Monad.toBind, Except.bind] at h
            split at h
            · contradiction
            · rename_i parsed popped hpop
              cases h
              exact Validity.InstrValid.call index type start.toValidity
                popped.toValidity htype (popMany_sound hpop)
    | localGet index =>
        unfold Validator.validateInstr at h
        cases hlocal : context.locals index with
        | none =>
            rw [hlocal] at h
            contradiction
        | some type =>
            rw [hlocal] at h
            cases h
            exact Validity.InstrValid.localGet index type start.toValidity hlocal
    | localSet index =>
        unfold Validator.validateInstr at h
        cases hlocal : context.locals index with
        | none =>
            rw [hlocal] at h
            contradiction
        | some type =>
            rw [hlocal] at h
            exact Validity.InstrValid.localSet index type start.toValidity
              finish.toValidity hlocal (popExpected_sound h)
    | localTee index =>
        unfold Validator.validateInstr at h
        cases hlocal : context.locals index with
        | none =>
            rw [hlocal] at h
            contradiction
        | some type =>
            rw [hlocal] at h
            dsimp [Bind.bind, Monad.toBind, Except.bind] at h
            split at h
            · contradiction
            · rename_i parsed popped hpop
              cases h
              exact Validity.InstrValid.localTee index type start.toValidity
                popped.toValidity hlocal (popExpected_sound hpop)
    | globalGet index =>
        unfold Validator.validateInstr at h
        cases hglobal : context.globals[index.toNat]? with
        | none =>
            rw [hglobal] at h
            contradiction
        | some type =>
            rw [hglobal] at h
            cases h
            exact Validity.InstrValid.globalGet index type start.toValidity hglobal
    | globalSet index =>
        unfold Validator.validateInstr at h
        cases hglobal : context.globals[index.toNat]? with
        | none =>
            rw [hglobal] at h
            contradiction
        | some type =>
            simp only [hglobal] at h
            split at h
            · rename_i hmutable
              exact Validity.InstrValid.globalSet index type start.toValidity
                finish.toValidity hglobal hmutable (popExpected_sound h)
            · contradiction
    | i32Const value =>
        unfold Validator.validateInstr at h
        split at h
        · rename_i hrange
          cases h
          exact Validity.InstrValid.i32Const value start.toValidity
            (by simpa using inSignedRange_sound hrange)
        · contradiction
    | i64Const value =>
        unfold Validator.validateInstr at h
        split at h
        · rename_i hrange
          cases h
          exact Validity.InstrValid.i64Const value start.toValidity
            (by simpa using inSignedRange_sound hrange)
        · contradiction
    | i32Eqz =>
        rcases unary_sound h with ⟨popped, heffect, hfinish⟩
        rw [hfinish]
        exact Validity.InstrValid.unary .i32Eqz .i32 .i32 start.toValidity
          popped Validity.UnaryOp.i32Eqz heffect
    | i32Eq =>
        rcases binary_sound h with ⟨first, second, hfirst, hsecond, hfinish⟩
        rw [hfinish]
        exact Validity.InstrValid.binary .i32Eq .i32 .i32 start.toValidity
          first second Validity.BinaryOp.i32Eq hfirst hsecond
    | i32And =>
        rcases binary_sound h with ⟨first, second, hfirst, hsecond, hfinish⟩
        rw [hfinish]
        exact Validity.InstrValid.binary .i32And .i32 .i32 start.toValidity
          first second Validity.BinaryOp.i32And hfirst hsecond
    | i64Eqz =>
        rcases unary_sound h with ⟨popped, heffect, hfinish⟩
        rw [hfinish]
        exact Validity.InstrValid.unary .i64Eqz .i64 .i32 start.toValidity
          popped Validity.UnaryOp.i64Eqz heffect
    | i64Eq =>
        rcases binary_sound h with ⟨first, second, hfirst, hsecond, hfinish⟩
        rw [hfinish]
        exact Validity.InstrValid.binary .i64Eq .i64 .i32 start.toValidity
          first second Validity.BinaryOp.i64Eq hfirst hsecond
    | i64Ne =>
        rcases binary_sound h with ⟨first, second, hfirst, hsecond, hfinish⟩
        rw [hfinish]
        exact Validity.InstrValid.binary .i64Ne .i64 .i32 start.toValidity
          first second Validity.BinaryOp.i64Ne hfirst hsecond
    | i64LtU =>
        rcases binary_sound h with ⟨first, second, hfirst, hsecond, hfinish⟩
        rw [hfinish]
        exact Validity.InstrValid.binary .i64LtU .i64 .i32 start.toValidity
          first second Validity.BinaryOp.i64LtU hfirst hsecond
    | i64LeU =>
        rcases binary_sound h with ⟨first, second, hfirst, hsecond, hfinish⟩
        rw [hfinish]
        exact Validity.InstrValid.binary .i64LeU .i64 .i32 start.toValidity
          first second Validity.BinaryOp.i64LeU hfirst hsecond
    | i64GeU =>
        rcases binary_sound h with ⟨first, second, hfirst, hsecond, hfinish⟩
        rw [hfinish]
        exact Validity.InstrValid.binary .i64GeU .i64 .i32 start.toValidity
          first second Validity.BinaryOp.i64GeU hfirst hsecond
    | i64Add =>
        rcases binary_sound h with ⟨first, second, hfirst, hsecond, hfinish⟩
        rw [hfinish]
        exact Validity.InstrValid.binary .i64Add .i64 .i64 start.toValidity
          first second Validity.BinaryOp.i64Add hfirst hsecond
    | i64Sub =>
        rcases binary_sound h with ⟨first, second, hfirst, hsecond, hfinish⟩
        rw [hfinish]
        exact Validity.InstrValid.binary .i64Sub .i64 .i64 start.toValidity
          first second Validity.BinaryOp.i64Sub hfirst hsecond
    | i64Mul =>
        rcases binary_sound h with ⟨first, second, hfirst, hsecond, hfinish⟩
        rw [hfinish]
        exact Validity.InstrValid.binary .i64Mul .i64 .i64 start.toValidity
          first second Validity.BinaryOp.i64Mul hfirst hsecond
    | i64DivU =>
        rcases binary_sound h with ⟨first, second, hfirst, hsecond, hfinish⟩
        rw [hfinish]
        exact Validity.InstrValid.binary .i64DivU .i64 .i64 start.toValidity
          first second Validity.BinaryOp.i64DivU hfirst hsecond
    | i64RemU =>
        rcases binary_sound h with ⟨first, second, hfirst, hsecond, hfinish⟩
        rw [hfinish]
        exact Validity.InstrValid.binary .i64RemU .i64 .i64 start.toValidity
          first second Validity.BinaryOp.i64RemU hfirst hsecond
    | i64And =>
        rcases binary_sound h with ⟨first, second, hfirst, hsecond, hfinish⟩
        rw [hfinish]
        exact Validity.InstrValid.binary .i64And .i64 .i64 start.toValidity
          first second Validity.BinaryOp.i64And hfirst hsecond
    | i64Or =>
        rcases binary_sound h with ⟨first, second, hfirst, hsecond, hfinish⟩
        rw [hfinish]
        exact Validity.InstrValid.binary .i64Or .i64 .i64 start.toValidity
          first second Validity.BinaryOp.i64Or hfirst hsecond
    | i64Xor =>
        rcases binary_sound h with ⟨first, second, hfirst, hsecond, hfinish⟩
        rw [hfinish]
        exact Validity.InstrValid.binary .i64Xor .i64 .i64 start.toValidity
          first second Validity.BinaryOp.i64Xor hfirst hsecond
    | i64Shl =>
        rcases binary_sound h with ⟨first, second, hfirst, hsecond, hfinish⟩
        rw [hfinish]
        exact Validity.InstrValid.binary .i64Shl .i64 .i64 start.toValidity
          first second Validity.BinaryOp.i64Shl hfirst hsecond
    | i64ShrU =>
        rcases binary_sound h with ⟨first, second, hfirst, hsecond, hfinish⟩
        rw [hfinish]
        exact Validity.InstrValid.binary .i64ShrU .i64 .i64 start.toValidity
          first second Validity.BinaryOp.i64ShrU hfirst hsecond
    | i32WrapI64 =>
        rcases unary_sound h with ⟨popped, heffect, hfinish⟩
        rw [hfinish]
        exact Validity.InstrValid.unary .i32WrapI64 .i64 .i32 start.toValidity
          popped Validity.UnaryOp.i32WrapI64 heffect
    | i64ExtendI32U =>
        rcases unary_sound h with ⟨popped, heffect, hfinish⟩
        rw [hfinish]
        exact Validity.InstrValid.unary .i64ExtendI32U .i32 .i64 start.toValidity
          popped Validity.UnaryOp.i64ExtendI32U heffect
    | i64Load arg =>
        unfold Validator.validateInstr at h
        dsimp [Bind.bind, Monad.toBind, Except.bind] at h
        split at h
        · contradiction
        · rename_i parsedMemory _ hmemory
          split at h
          · contradiction
          · rename_i parsedAlignment _ halignment
            split at h
            · contradiction
            · rename_i parsedAddress popped haddress
              cases h
              exact Validity.InstrValid.load (.i64Load arg) arg .i32 .i64 3
                start.toValidity popped.toValidity (Or.inl rfl)
                (checkMemory_sound hmemory) (checkAlignment_sound halignment)
                (popExpected_sound haddress)
    | i32Load arg =>
        unfold Validator.validateInstr at h
        dsimp [Bind.bind, Monad.toBind, Except.bind] at h
        split at h
        · contradiction
        · rename_i parsedMemory _ hmemory
          split at h
          · contradiction
          · rename_i parsedAlignment _ halignment
            split at h
            · contradiction
            · rename_i parsedAddress popped haddress
              cases h
              exact Validity.InstrValid.load (.i32Load arg) arg .i32 .i32 2
                start.toValidity popped.toValidity (Or.inr (Or.inl rfl))
                (checkMemory_sound hmemory) (checkAlignment_sound halignment)
                (popExpected_sound haddress)
    | i32Load8U arg =>
        unfold Validator.validateInstr at h
        dsimp [Bind.bind, Monad.toBind, Except.bind] at h
        split at h
        · contradiction
        · rename_i parsedMemory _ hmemory
          split at h
          · contradiction
          · rename_i parsedAlignment _ halignment
            split at h
            · contradiction
            · rename_i parsedAddress popped haddress
              cases h
              exact Validity.InstrValid.load (.i32Load8U arg) arg .i32 .i32 0
                start.toValidity popped.toValidity (Or.inr (Or.inr rfl))
                (checkMemory_sound hmemory) (checkAlignment_sound halignment)
                (popExpected_sound haddress)
    | i64Store arg =>
        unfold Validator.validateInstr at h
        dsimp [Bind.bind, Monad.toBind, Except.bind] at h
        split at h
        · contradiction
        · rename_i parsedMemory _ hmemory
          split at h
          · contradiction
          · rename_i parsedAlignment _ halignment
            split at h
            · contradiction
            · rename_i parsedValue valuePopped hvalue
              exact Validity.InstrValid.store (.i64Store arg) arg .i64 3
                start.toValidity valuePopped.toValidity finish.toValidity
                (Or.inl rfl) (checkMemory_sound hmemory)
                (checkAlignment_sound halignment) (popExpected_sound hvalue)
                (popExpected_sound h)
    | i32Store arg =>
        unfold Validator.validateInstr at h
        dsimp [Bind.bind, Monad.toBind, Except.bind] at h
        split at h
        · contradiction
        · rename_i parsedMemory _ hmemory
          split at h
          · contradiction
          · rename_i parsedAlignment _ halignment
            split at h
            · contradiction
            · rename_i parsedValue valuePopped hvalue
              exact Validity.InstrValid.store (.i32Store arg) arg .i32 2
                start.toValidity valuePopped.toValidity finish.toValidity
                (Or.inr (Or.inl rfl)) (checkMemory_sound hmemory)
                (checkAlignment_sound halignment) (popExpected_sound hvalue)
                (popExpected_sound h)
    | i32Store8 arg =>
        unfold Validator.validateInstr at h
        dsimp [Bind.bind, Monad.toBind, Except.bind] at h
        split at h
        · contradiction
        · rename_i parsedMemory _ hmemory
          split at h
          · contradiction
          · rename_i parsedAlignment _ halignment
            split at h
            · contradiction
            · rename_i parsedValue valuePopped hvalue
              exact Validity.InstrValid.store (.i32Store8 arg) arg .i32 0
                start.toValidity valuePopped.toValidity finish.toValidity
                (Or.inr (Or.inr rfl)) (checkMemory_sound hmemory)
                (checkAlignment_sound halignment) (popExpected_sound hvalue)
                (popExpected_sound h)
    | memorySize memory =>
        unfold Validator.validateInstr at h
        dsimp [Bind.bind, Monad.toBind, Except.bind] at h
        split at h
        · contradiction
        · rename_i parsedMemory _ hmemory
          split at h
          · rename_i hzero
            cases h
            exact Validity.InstrValid.memorySize memory start.toValidity
              (checkMemory_sound hmemory) hzero
          · contradiction
    | memoryGrow memory =>
        unfold Validator.validateInstr at h
        dsimp [Bind.bind, Monad.toBind, Except.bind] at h
        split at h
        · contradiction
        · rename_i parsedMemory _ hmemory
          split at h
          · rename_i hzero
            split at h
            · contradiction
            · rename_i parsedPages popped hpages
              cases h
              exact Validity.InstrValid.memoryGrow memory start.toValidity
                popped.toValidity (checkMemory_sound hmemory) hzero
                (popExpected_sound hpages)
          · contradiction

  theorem validateInstrs_sound (context : Validator.Context) (parentPath : List Nat)
      (base : Nat) (start : Validator.StackState) (index : Nat)
      (instrs : List Instr) (finish : Validator.StackState)
      (h : Validator.validateInstrs context parentPath base start index instrs =
        .ok finish) :
      Validity.InstrsValid context.toValidity base start.toValidity instrs
        finish.toValidity := by
    cases instrs with
    | nil =>
        unfold Validator.validateInstrs at h
        cases h
        exact Validity.InstrsValid.nil _
    | cons head tail =>
        unfold Validator.validateInstrs at h
        dsimp [Bind.bind, Monad.toBind, Except.bind] at h
        split at h
        · contradiction
        · rename_i parsed middle hhead
          exact Validity.InstrsValid.cons start.toValidity middle.toValidity
            finish.toValidity head tail
            (validateInstr_sound context (parentPath ++ [index]) base start head
              middle hhead)
            (validateInstrs_sound context parentPath base middle (index + 1)
              tail finish h)
end

theorem sectionRank_eq (id : SectionId) :
    Validator.sectionRank id = id.rank := by
  cases id <;> rfl

theorem orderedSections_after (ids : List SectionId) (lastRank : Nat)
    (hall : ∀ id ∈ ids, lastRank < id.rank)
    (h : Validator.orderedSections ids = true) :
    Grammar.OrderedAfter lastRank ids := by
  induction ids generalizing lastRank with
  | nil => exact Grammar.OrderedAfter.nil lastRank
  | cons head rest ih =>
      unfold Validator.orderedSections at h
      have houter := Bool.and_eq_true_iff.mp h
      have hinner := Bool.and_eq_true_iff.mp houter.1
      have htailRanks := hinner.2
      have htailOrdered := houter.2
      apply Grammar.OrderedAfter.cons lastRank head rest
      · exact hall head (by simp)
      · apply ih head.rank
        · intro id hid
          have hrank := List.all_eq_true.mp htailRanks id hid
          simpa [sectionRank_eq] using hrank
        · exact htailOrdered

theorem orderedSections_sound {ids : List SectionId}
    (h : Validator.orderedSections ids = true) :
    Grammar.OrderedAfter 0 ids := by
  apply orderedSections_after ids 0
  · intro id _
    cases id <;> decide
  · exact h

theorem requireSection_sound {module_ : RawModule} {id : SectionId} {needed : Bool}
    (hneeded : needed = true)
    (h : Validator.requireSection module_ id needed = .ok ()) :
    id ∈ module_.sections := by
  unfold Validator.requireSection at h
  split at h
  · contradiction
  · rename_i hcondition
    simp [hneeded] at hcondition
    exact hcondition

theorem validateRequiredSections_sound (module_ : RawModule)
    (entries : List (SectionId × Bool))
    (h : Validator.validateRequiredSections module_ entries = .ok ()) :
    ∀ id needed, (id, needed) ∈ entries → needed = true →
      id ∈ module_.sections := by
  induction entries with
  | nil =>
      intro id needed hmember
      contradiction
  | cons head rest ih =>
      rcases head with ⟨headId, headNeeded⟩
      unfold Validator.validateRequiredSections at h
      dsimp [Bind.bind, Monad.toBind, Except.bind] at h
      split at h
      · contradiction
      · rename_i parsed _ hhead
        intro id needed hmember hneeded
        simp only [List.mem_cons, Prod.mk.injEq] at hmember
        rcases hmember with ⟨hid, hneed⟩ | htail
        · subst id
          have hheadNeeded : headNeeded = true := by
            rw [← hneed]
            exact hneeded
          exact requireSection_sound hheadNeeded (by simpa using hhead)
        · exact ih h id needed htail hneeded

theorem validateSections_sound {module_ : RawModule}
    (h : Validator.validateSections module_ = .ok ()) :
    Validity.SectionsValid module_ := by
  unfold Validator.validateSections at h
  split at h
  · rename_i hordered
    let entries : List (SectionId × Bool) :=
      [(.type, !module_.types.isEmpty),
       (.function, !module_.functionTypeIndices.isEmpty),
       (.memory, !module_.memories.isEmpty),
       (.global, !module_.globals.isEmpty),
       (.export, !module_.exports.isEmpty),
       (.code, !module_.codes.isEmpty)]
    have hrequired : Validator.validateRequiredSections module_ entries = .ok () := by
      simpa [entries] using h
    have hentry := validateRequiredSections_sound module_ entries hrequired
    constructor
    · exact orderedSections_sound hordered
    · constructor
      · intro hnonempty
        apply hentry .type (!module_.types.isEmpty)
        · simp [entries]
        · simpa using hnonempty
      · constructor
        · intro hnonempty
          apply hentry .function (!module_.functionTypeIndices.isEmpty)
          · simp [entries]
          · simpa using hnonempty
        · constructor
          · intro hnonempty
            apply hentry .memory (!module_.memories.isEmpty)
            · simp [entries]
            · simpa using hnonempty
          · constructor
            · intro hnonempty
              apply hentry .global (!module_.globals.isEmpty)
              · simp [entries]
              · simpa using hnonempty
            · constructor
              · intro hnonempty
                apply hentry .export (!module_.exports.isEmpty)
                · simp [entries]
                · simpa using hnonempty
              · intro hnonempty
                apply hentry .code (!module_.codes.isEmpty)
                · simp [entries]
                · simpa using hnonempty
  · contradiction

theorem validateLimits_sound {limits : Limits}
    (h : Validator.validateLimits limits = .ok ()) :
    Validity.LimitsValid limits := by
  unfold Validator.validateLimits at h
  split at h
  · rename_i hvalid
    cases h
    simp at hvalid
    constructor
    · exact hvalid.1
    · intro maximum hmember
      cases hmax : limits.max with
      | none => simp [hmax] at hmember
      | some value =>
          simp [hmax] at hmember
          subst maximum
          simpa [hmax] using hvalid.2
  · contradiction

theorem validateGlobal_sound {global : Global}
    (h : Validator.validateGlobal global = .ok ()) :
    Validity.GlobalValid global := by
  unfold Validator.validateGlobal at h
  split at h
  · rename_i htype
    cases hinit : global.init with
    | i32Const value =>
        simp only [hinit] at h htype
        unfold Validity.GlobalValid
        rw [hinit]
        split at h
        · rename_i hrange
          cases h
          exact ⟨by simpa [Validator.constType, Validity.ConstType] using htype,
            by simpa [Validity.ConstInRange] using inSignedRange_sound hrange⟩
        · contradiction
    | i64Const value =>
        simp only [hinit] at h htype
        unfold Validity.GlobalValid
        rw [hinit]
        split at h
        · rename_i hrange
          cases h
          exact ⟨by simpa [Validator.constType, Validity.ConstType] using htype,
            by simpa [Validity.ConstInRange] using inSignedRange_sound hrange⟩
        · contradiction
  · contradiction

theorem validateGlobals_sound (globals : List Global)
    (h : Validator.validateGlobals globals = .ok ()) :
    Validity.GlobalsValid globals := by
  induction globals with
  | nil =>
      intro global hmember
      contradiction
  | cons head rest ih =>
      unfold Validator.validateGlobals at h
      dsimp [Bind.bind, Monad.toBind, Except.bind] at h
      split at h
      · contradiction
      · rename_i parsed _ hhead
        intro global hmember
        simp only [List.mem_cons] at hmember
        rcases hmember with rfl | htail
        · exact validateGlobal_sound hhead
        · exact ih h global htail

theorem duplicateName_none_sound (exports : List Export)
    (h : Validator.duplicateName? exports = none) :
    Validity.ExportNamesUnique exports := by
  induction exports with
  | nil => exact List.Pairwise.nil
  | cons head rest ih =>
      unfold Validator.duplicateName? at h
      split at h
      · contradiction
      · rename_i hnone
        apply List.Pairwise.cons
        · intro other hmember hequal
          apply hnone
          apply List.any_eq_true.mpr
          exact ⟨other, hmember, by simp [hequal]⟩
        · exact ih h

theorem validateExportEntry_sound {module_ : RawModule} {entry : Export}
    (h : Validator.validateExportEntry module_ entry = .ok ()) :
    Validity.ExportValid module_ entry := by
  rcases entry with ⟨name, desc⟩
  cases desc with
  | func index =>
      unfold Validator.validateExportEntry at h
      unfold Validity.ExportValid
      dsimp at h ⊢
      split at h
      · rename_i hname
        constructor
        · exact hname
        · split at h
          · rename_i hindex
            exact of_decide_eq_true hindex
          · contradiction
      · contradiction
  | memory index =>
      unfold Validator.validateExportEntry at h
      unfold Validity.ExportValid
      dsimp at h ⊢
      split at h
      · rename_i hname
        constructor
        · exact hname
        · split at h
          · rename_i hindex
            exact of_decide_eq_true hindex
          · contradiction
      · contradiction
  | global index =>
      unfold Validator.validateExportEntry at h
      unfold Validity.ExportValid
      dsimp at h ⊢
      split at h
      · rename_i hname
        constructor
        · exact hname
        · split at h
          · rename_i hindex
            exact of_decide_eq_true hindex
          · contradiction
      · contradiction

theorem validateExportEntries_sound (module_ : RawModule) (exports : List Export)
    (h : Validator.validateExportEntries module_ exports = .ok ()) :
    ∀ entry, entry ∈ exports → Validity.ExportValid module_ entry := by
  induction exports with
  | nil =>
      intro entry hmember
      contradiction
  | cons head rest ih =>
      unfold Validator.validateExportEntries at h
      dsimp [Bind.bind, Monad.toBind, Except.bind] at h
      split at h
      · contradiction
      · rename_i parsed _ hhead
        intro entry hmember
        simp only [List.mem_cons] at hmember
        rcases hmember with rfl | htail
        · exact validateExportEntry_sound hhead
        · exact ih h entry htail

theorem validateExports_sound {module_ : RawModule}
    (h : Validator.validateExports module_ = .ok ()) :
    Validity.ExportsValid module_ := by
  unfold Validator.validateExports at h
  cases hduplicate : Validator.duplicateName? module_.exports with
  | some name =>
      rw [hduplicate] at h
      contradiction
  | none =>
      rw [hduplicate] at h
      exact ⟨duplicateName_none_sound module_.exports hduplicate,
        validateExportEntries_sound module_ module_.exports h⟩

theorem resolveTypes_sound (types : List FuncType) (indices : List UInt32)
    (resolved : List FuncType)
    (h : Validator.resolveTypes types indices = .ok resolved) :
    Validity.ResolvedTypes types indices resolved := by
  induction indices generalizing resolved with
  | nil =>
      unfold Validator.resolveTypes at h
      cases h
      exact Validity.ResolvedTypes.nil
  | cons index rest ih =>
      unfold Validator.resolveTypes at h
      cases hlookup : types[index.toNat]? with
      | none =>
          rw [hlookup] at h
          contradiction
      | some type =>
          rw [hlookup] at h
          dsimp [Bind.bind, Monad.toBind, Except.bind] at h
          split at h
          · contradiction
          · rename_i parsed tail htail
            cases h
            exact Validity.ResolvedTypes.cons index type rest tail hlookup
              (ih tail htail)

theorem resolveFunctionTypes_sound {module_ : RawModule}
    {functions : List FuncType}
    (h : Validator.resolveFunctionTypes module_ = .ok functions) :
    Validity.ResolvedTypes module_.types module_.functionTypeIndices functions := by
  exact resolveTypes_sound module_.types module_.functionTypeIndices functions h

theorem localDeclType_eq (locals : List LocalDecl) (index : Nat) :
    Validator.localDeclType locals index =
      Validity.localDeclType locals index := by
  induction locals generalizing index with
  | nil => rfl
  | cons head rest ih =>
      unfold Validator.localDeclType Validity.localDeclType
      split
      · rfl
      · exact ih (index - head.count.toNat)

theorem localType_eq (params : List ValType) (locals : List LocalDecl)
    (index : UInt32) :
    Validator.localType params locals index =
      Validity.localType params locals index := by
  unfold Validator.localType Validity.localType
  split
  · rfl
  · exact localDeclType_eq locals (index.toNat - params.length)

theorem validateFunction_sound {module_ : RawModule}
    {functions : List FuncType} {index : Nat} {type : FuncType} {code : Code}
    (h : Validator.validateFunction module_ functions index type code = .ok ()) :
    Validity.FunctionValid module_ functions type code := by
  unfold Validator.validateFunction at h
  dsimp [Bind.bind, Monad.toBind, Except.bind] at h
  split at h
  · contradiction
  · rename_i parsedBody state hbody
    split at h
    · contradiction
    · rename_i parsedFrame finish hframe
      unfold Validity.FunctionValid
      refine ⟨state.toValidity, finish.toValidity, ?_, ?_⟩
      · have hbodyValid := validateInstrs_sound
            { functionIndex := index
              functions
              locals := Validator.localType type.params code.locals
              globals := module_.globals.map (·.type)
              labels := [type.results]
              results := type.results
              hasMemory := module_.memories.length = 1 }
            [] 0 { values := [], polymorphic := false } 0 code.body state hbody
        have hlocalTypes :
            Validator.localType type.params code.locals =
              Validity.localType type.params code.locals := by
          funext localIndex
          exact localType_eq type.params code.locals localIndex
        rw [hlocalTypes] at hbodyValid
        exact hbodyValid
      · simpa [Validator.StackState.toValidity] using finishFrame_sound hframe

theorem validateFunctionPairs_sound (module_ : RawModule)
    (functions : List FuncType) (index : Nat) (types : List FuncType)
    (codes : List Code)
    (h : Validator.validateFunctionPairs module_ functions index types codes =
      .ok ()) :
    Validity.FunctionPairsValid module_ functions types codes := by
  induction types generalizing index codes with
  | nil =>
      cases codes with
      | nil =>
          exact Validity.FunctionPairsValid.nil
      | cons code codes =>
          unfold Validator.validateFunctionPairs at h
          contradiction
  | cons type types ih =>
      cases codes with
      | nil =>
          unfold Validator.validateFunctionPairs at h
          contradiction
      | cons code codes =>
          unfold Validator.validateFunctionPairs at h
          dsimp [Bind.bind, Monad.toBind, Except.bind] at h
          split at h
          · contradiction
          · rename_i parsed _ hhead
            exact Validity.FunctionPairsValid.cons type code types codes
              (validateFunction_sound hhead) (ih (index + 1) codes h)

theorem validateFunctions_sound {module_ : RawModule}
    {functions : List FuncType}
    (h : Validator.validateFunctions module_ functions = .ok ()) :
    Validity.FunctionPairsValid module_ functions functions module_.codes := by
  exact validateFunctionPairs_sound module_ functions 0 functions module_.codes h

theorem exists_eq_singleton_of_length_eq_one {α : Type} (values : List α)
    (h : values.length = 1) :
    ∃ value, values = [value] := by
  cases values with
  | nil => contradiction
  | cons head tail =>
      cases tail with
      | nil => exact ⟨head, rfl⟩
      | cons next rest => simp at h

theorem validateRaw_sound {module_ : RawModule}
    (h : Validator.validateRaw module_ = .ok ()) :
    CoreValid module_ := by
  unfold Validator.validateRaw at h
  dsimp [Bind.bind, Monad.toBind, Except.bind] at h
  split at h
  · contradiction
  · rename_i parsedSections _ hsections
    split at h
    · rename_i hmemoryCount
      split at h
      · contradiction
      · rename_i parsedLimits _ hlimits
        split at h
        · contradiction
        · rename_i parsedGlobals _ hglobals
          split at h
          · contradiction
          · rename_i parsedExports _ hexports
            split at h
            · contradiction
            · rename_i parsedTypes functions htypes
              unfold CoreValid Validity.ModuleValid
              refine ⟨validateSections_sound (by simpa using hsections), ?_,
                validateGlobals_sound module_.globals (by simpa using hglobals),
                validateExports_sound (by simpa using hexports), ?_⟩
              · rcases exists_eq_singleton_of_length_eq_one
                    module_.memories hmemoryCount with ⟨memory, hmemory⟩
                refine ⟨memory, hmemory, ?_⟩
                apply validateLimits_sound
                rw [hmemory] at hlimits
                change Validator.validateLimits memory.limits = .ok _ at hlimits
                simpa using hlimits
              · exact ⟨functions, resolveFunctionTypes_sound htypes,
                  validateFunctions_sound h⟩
    · contradiction

theorem validate_sound {module_ : RawModule} {validated : ValidatedModule}
    (h : validate module_ = .ok validated) :
    CoreValid module_ := by
  unfold validate at h
  dsimp [Bind.bind, Monad.toBind, Except.bind] at h
  split at h
  · contradiction
  · rename_i parsed _ hraw
    exact validateRaw_sound hraw

theorem validate_raw_eq {module_ : RawModule} {validated : ValidatedModule}
    (h : validate module_ = .ok validated) :
    validated.raw = module_ := by
  unfold validate at h
  dsimp [Bind.bind, Monad.toBind, Except.bind] at h
  split at h
  · contradiction
  · cases h
    rfl

end Wasm.Binary.Proof
