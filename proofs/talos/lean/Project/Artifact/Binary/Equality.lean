import Project.Artifact.Binary.Syntax

namespace Wasm.Binary.Equality

inductive InstrAtom where
  | unreachable
  | drop
  | br (depth : UInt32)
  | brIf (depth : UInt32)
  | ret
  | call (index : UInt32)
  | localGet (index : UInt32)
  | localSet (index : UInt32)
  | localTee (index : UInt32)
  | globalGet (index : UInt32)
  | globalSet (index : UInt32)
  | i32Const (value : Int)
  | i64Const (value : Int)
  | i32Eqz
  | i32Eq
  | i32And
  | i64Eqz
  | i64Eq
  | i64Ne
  | i64LtU
  | i64LeU
  | i64GeU
  | i64Add
  | i64Sub
  | i64Mul
  | i64DivU
  | i64RemU
  | i64And
  | i64Or
  | i64Xor
  | i64Shl
  | i64ShrU
  | f64Add
  | f64Mul
  | i32WrapI64
  | i64ExtendI32U
  | i64ReinterpretF64
  | f64ReinterpretI64
  | i64Load (arg : MemArg)
  | i32Load (arg : MemArg)
  | i32Load8U (arg : MemArg)
  | i64Store (arg : MemArg)
  | i32Store (arg : MemArg)
  | i32Store8 (arg : MemArg)
  | memorySize (memory : UInt32)
  | memoryGrow (memory : UInt32)
  deriving DecidableEq

inductive InstrView where
  | atom (value : InstrAtom)
  | block (type : BlockType) (body : List Instr)
  | loop (type : BlockType) (body : List Instr)
  | iff (type : BlockType) (thenBody : List Instr) (elseBody : Option (List Instr))

def instrView : Instr → InstrView
  | .unreachable => .atom .unreachable
  | .drop => .atom .drop
  | .block type body => .block type body
  | .loop type body => .loop type body
  | .iff type thenBody elseBody => .iff type thenBody elseBody
  | .br depth => .atom (.br depth)
  | .brIf depth => .atom (.brIf depth)
  | .ret => .atom .ret
  | .call index => .atom (.call index)
  | .localGet index => .atom (.localGet index)
  | .localSet index => .atom (.localSet index)
  | .localTee index => .atom (.localTee index)
  | .globalGet index => .atom (.globalGet index)
  | .globalSet index => .atom (.globalSet index)
  | .i32Const value => .atom (.i32Const value)
  | .i64Const value => .atom (.i64Const value)
  | .i32Eqz => .atom .i32Eqz
  | .i32Eq => .atom .i32Eq
  | .i32And => .atom .i32And
  | .i64Eqz => .atom .i64Eqz
  | .i64Eq => .atom .i64Eq
  | .i64Ne => .atom .i64Ne
  | .i64LtU => .atom .i64LtU
  | .i64LeU => .atom .i64LeU
  | .i64GeU => .atom .i64GeU
  | .i64Add => .atom .i64Add
  | .i64Sub => .atom .i64Sub
  | .i64Mul => .atom .i64Mul
  | .i64DivU => .atom .i64DivU
  | .i64RemU => .atom .i64RemU
  | .i64And => .atom .i64And
  | .i64Or => .atom .i64Or
  | .i64Xor => .atom .i64Xor
  | .i64Shl => .atom .i64Shl
  | .i64ShrU => .atom .i64ShrU
  | .f64Add => .atom .f64Add
  | .f64Mul => .atom .f64Mul
  | .i32WrapI64 => .atom .i32WrapI64
  | .i64ExtendI32U => .atom .i64ExtendI32U
  | .i64ReinterpretF64 => .atom .i64ReinterpretF64
  | .f64ReinterpretI64 => .atom .f64ReinterpretI64
  | .i64Load arg => .atom (.i64Load arg)
  | .i32Load arg => .atom (.i32Load arg)
  | .i32Load8U arg => .atom (.i32Load8U arg)
  | .i64Store arg => .atom (.i64Store arg)
  | .i32Store arg => .atom (.i32Store arg)
  | .i32Store8 arg => .atom (.i32Store8 arg)
  | .memorySize memory => .atom (.memorySize memory)
  | .memoryGrow memory => .atom (.memoryGrow memory)

def InstrAtom.toInstr : InstrAtom → Instr
  | .unreachable => .unreachable
  | .drop => .drop
  | .br depth => .br depth
  | .brIf depth => .brIf depth
  | .ret => .ret
  | .call index => .call index
  | .localGet index => .localGet index
  | .localSet index => .localSet index
  | .localTee index => .localTee index
  | .globalGet index => .globalGet index
  | .globalSet index => .globalSet index
  | .i32Const value => .i32Const value
  | .i64Const value => .i64Const value
  | .i32Eqz => .i32Eqz
  | .i32Eq => .i32Eq
  | .i32And => .i32And
  | .i64Eqz => .i64Eqz
  | .i64Eq => .i64Eq
  | .i64Ne => .i64Ne
  | .i64LtU => .i64LtU
  | .i64LeU => .i64LeU
  | .i64GeU => .i64GeU
  | .i64Add => .i64Add
  | .i64Sub => .i64Sub
  | .i64Mul => .i64Mul
  | .i64DivU => .i64DivU
  | .i64RemU => .i64RemU
  | .i64And => .i64And
  | .i64Or => .i64Or
  | .i64Xor => .i64Xor
  | .i64Shl => .i64Shl
  | .i64ShrU => .i64ShrU
  | .f64Add => .f64Add
  | .f64Mul => .f64Mul
  | .i32WrapI64 => .i32WrapI64
  | .i64ExtendI32U => .i64ExtendI32U
  | .i64ReinterpretF64 => .i64ReinterpretF64
  | .f64ReinterpretI64 => .f64ReinterpretI64
  | .i64Load arg => .i64Load arg
  | .i32Load arg => .i32Load arg
  | .i32Load8U arg => .i32Load8U arg
  | .i64Store arg => .i64Store arg
  | .i32Store arg => .i32Store arg
  | .i32Store8 arg => .i32Store8 arg
  | .memorySize memory => .memorySize memory
  | .memoryGrow memory => .memoryGrow memory

def InstrView.toInstr : InstrView → Instr
  | .atom value => value.toInstr
  | .block type body => .block type body
  | .loop type body => .loop type body
  | .iff type thenBody elseBody => .iff type thenBody elseBody

theorem instrView_toInstr (instr : Instr) : (instrView instr).toInstr = instr := by
  cases instr <;> rfl

mutual
  def instrEqualFuel : Nat → Instr → Instr → Bool
    | 0, _, _ => false
    | fuel + 1, first, second =>
        match instrView first, instrView second with
        | .atom left, .atom right => decide (left = right)
        | .block leftType leftBody, .block rightType rightBody =>
            decide (leftType = rightType) &&
              instrListEqualFuel fuel leftBody rightBody
        | .loop leftType leftBody, .loop rightType rightBody =>
            decide (leftType = rightType) &&
              instrListEqualFuel fuel leftBody rightBody
        | .iff leftType leftThen leftElse, .iff rightType rightThen rightElse =>
            decide (leftType = rightType) &&
              instrListEqualFuel fuel leftThen rightThen &&
              instrListOptionEqualFuel fuel leftElse rightElse
        | _, _ => false

  def instrListEqualFuel : Nat → List Instr → List Instr → Bool
    | 0, _, _ => false
    | _ + 1, [], [] => true
    | fuel + 1, head :: tail, otherHead :: otherTail =>
        instrEqualFuel fuel head otherHead &&
          instrListEqualFuel fuel tail otherTail
    | _ + 1, _, _ => false

  def instrListOptionEqualFuel : Nat → Option (List Instr) →
      Option (List Instr) → Bool
    | 0, _, _ => false
    | _ + 1, none, none => true
    | fuel + 1, some values, some other =>
        instrListEqualFuel fuel values other
    | _ + 1, _, _ => false
end

theorem instr_eq_of_view_eq {first second : Instr}
    (h : instrView first = instrView second) : first = second := by
  rw [← instrView_toInstr first, ← instrView_toInstr second, h]

mutual
  theorem instrEqualFuel_sound (fuel : Nat) (first second : Instr)
      (h : instrEqualFuel fuel first second = true) :
      first = second := by
    cases fuel with
    | zero => simp [instrEqualFuel] at h
    | succ fuel =>
        cases hfirst : instrView first with
        | atom firstAtom =>
            cases hsecond : instrView second with
            | atom secondAtom =>
                simp [instrEqualFuel, hfirst, hsecond] at h
                apply instr_eq_of_view_eq
                simp [hfirst, hsecond, h]
            | block type body => simp [instrEqualFuel, hfirst, hsecond] at h
            | loop type body => simp [instrEqualFuel, hfirst, hsecond] at h
            | iff type thenBody elseBody =>
                simp [instrEqualFuel, hfirst, hsecond] at h
        | block firstType firstBody =>
            cases hsecond : instrView second with
            | atom secondAtom => simp [instrEqualFuel, hfirst, hsecond] at h
            | block secondType secondBody =>
                simp [instrEqualFuel, hfirst, hsecond] at h
                rcases h with ⟨htype, hbody⟩
                have hbodyEq := instrListEqualFuel_sound fuel firstBody secondBody hbody
                apply instr_eq_of_view_eq
                simp [hfirst, hsecond, htype, hbodyEq]
            | loop type body => simp [instrEqualFuel, hfirst, hsecond] at h
            | iff type thenBody elseBody =>
                simp [instrEqualFuel, hfirst, hsecond] at h
        | loop firstType firstBody =>
            cases hsecond : instrView second with
            | atom secondAtom => simp [instrEqualFuel, hfirst, hsecond] at h
            | block type body => simp [instrEqualFuel, hfirst, hsecond] at h
            | loop secondType secondBody =>
                simp [instrEqualFuel, hfirst, hsecond] at h
                rcases h with ⟨htype, hbody⟩
                have hbodyEq := instrListEqualFuel_sound fuel firstBody secondBody hbody
                apply instr_eq_of_view_eq
                simp [hfirst, hsecond, htype, hbodyEq]
            | iff type thenBody elseBody =>
                simp [instrEqualFuel, hfirst, hsecond] at h
        | iff firstType firstThen firstElse =>
            cases hsecond : instrView second with
            | atom secondAtom => simp [instrEqualFuel, hfirst, hsecond] at h
            | block type body => simp [instrEqualFuel, hfirst, hsecond] at h
            | loop type body => simp [instrEqualFuel, hfirst, hsecond] at h
            | iff secondType secondThen secondElse =>
                simp [instrEqualFuel, hfirst, hsecond] at h
                have htype := h.1.1
                have hthen := h.1.2
                have helse := h.2
                have hthenEq := instrListEqualFuel_sound fuel firstThen secondThen hthen
                have helseEq := instrListOptionEqualFuel_sound fuel firstElse secondElse helse
                apply instr_eq_of_view_eq
                simp [hfirst, hsecond, htype, hthenEq, helseEq]

  theorem instrListEqualFuel_sound (fuel : Nat) (first second : List Instr)
      (h : instrListEqualFuel fuel first second = true) :
      first = second := by
    cases fuel with
    | zero => simp [instrListEqualFuel] at h
    | succ fuel =>
        cases first with
        | nil =>
            cases second with
            | nil => rfl
            | cons head tail => simp [instrListEqualFuel] at h
        | cons head tail =>
            cases second with
            | nil => simp [instrListEqualFuel] at h
            | cons otherHead otherTail =>
                simp [instrListEqualFuel] at h
                rcases h with ⟨hhead, htail⟩
                rw [instrEqualFuel_sound fuel head otherHead hhead,
                  instrListEqualFuel_sound fuel tail otherTail htail]

  theorem instrListOptionEqualFuel_sound (fuel : Nat)
      (first second : Option (List Instr))
      (h : instrListOptionEqualFuel fuel first second = true) :
      first = second := by
    cases fuel with
    | zero => simp [instrListOptionEqualFuel] at h
    | succ fuel =>
        cases first with
        | none =>
            cases second with
            | none => rfl
            | some values => simp [instrListOptionEqualFuel] at h
        | some values =>
            cases second with
            | none => simp [instrListOptionEqualFuel] at h
            | some other =>
                simp [instrListOptionEqualFuel] at h
                rw [instrListEqualFuel_sound fuel values other h]
end

def codeEqual (fuel : Nat) (first second : Code) : Bool :=
  decide (first.locals = second.locals) &&
    instrListEqualFuel fuel first.body second.body

def codeListEqual (fuel : Nat) : List Code → List Code → Bool
  | [], [] => true
  | head :: tail, otherHead :: otherTail =>
      codeEqual fuel head otherHead && codeListEqual fuel tail otherTail
  | _, _ => false

theorem code_ext {first second : Code}
    (hlocals : first.locals = second.locals)
    (hbody : first.body = second.body) : first = second := by
  cases first
  cases second
  simp_all

theorem codeEqual_sound {fuel : Nat} {first second : Code}
    (h : codeEqual fuel first second = true) : first = second := by
  simp [codeEqual] at h
  rcases h with ⟨hlocals, hbody⟩
  have hbodyEq := instrListEqualFuel_sound fuel first.body second.body hbody
  exact code_ext hlocals hbodyEq

theorem codeListEqual_sound (fuel : Nat) (first second : List Code)
    (h : codeListEqual fuel first second = true) : first = second := by
  induction first generalizing second with
  | nil =>
      cases second with
      | nil => rfl
      | cons head tail => simp [codeListEqual] at h
  | cons head tail ih =>
      cases second with
      | nil => simp [codeListEqual] at h
      | cons otherHead otherTail =>
          simp [codeListEqual] at h
          rcases h with ⟨hhead, htail⟩
          rw [codeEqual_sound hhead, ih otherTail htail]

def rawModuleEqual (fuel : Nat) (first second : RawModule) : Bool :=
  decide (first.sections = second.sections) &&
  decide (first.types = second.types) &&
  decide (first.functionTypeIndices = second.functionTypeIndices) &&
  decide (first.memories = second.memories) &&
  decide (first.globals = second.globals) &&
  decide (first.exports = second.exports) &&
  codeListEqual fuel first.codes second.codes

theorem rawModule_ext {first second : RawModule}
    (hsections : first.sections = second.sections)
    (htypes : first.types = second.types)
    (hindices : first.functionTypeIndices = second.functionTypeIndices)
    (hmemories : first.memories = second.memories)
    (hglobals : first.globals = second.globals)
    (hexports : first.exports = second.exports)
    (hcodes : first.codes = second.codes) : first = second := by
  cases first
  cases second
  simp_all

theorem rawModuleEqual_sound {fuel : Nat} {first second : RawModule}
    (h : rawModuleEqual fuel first second = true) : first = second := by
  simp [rawModuleEqual] at h
  have hsections := h.1.1.1.1.1.1
  have htypes := h.1.1.1.1.1.2
  have hindices := h.1.1.1.1.2
  have hmemories := h.1.1.1.2
  have hglobals := h.1.1.2
  have hexports := h.1.2
  have hcodes := h.2
  have hcodesEq := codeListEqual_sound fuel first.codes second.codes hcodes
  exact rawModule_ext hsections htypes hindices hmemories hglobals hexports
    hcodesEq

end Wasm.Binary.Equality
