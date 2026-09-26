import Interpreter.Wasm.Semantics.Lemmas
import Lean.Elab.Tactic.Cbv

namespace Project.ProofKit.InterpreterEvaluation
open Wasm

@[cbv_eval] theorem execOne_localGet {α : Type} (f : Nat) (m : Module)
    (st : Store α) (s : Locals) (env : HostEnv α) (i : Nat) :
    execOne (Nat.succ f) m st s (.localGet i) env =
    (match s.get i with
      | some v => .Fallthrough st { s with values := v :: s.values }
      | none   => .Invalid "localGet index out of bounds") := by
  rw [execOne.eq_def] <;> rfl

@[cbv_eval] theorem execOne_localSet {α : Type} (f : Nat) (m : Module)
    (st : Store α) (s : Locals) (env : HostEnv α) (i : Nat) :
    execOne (Nat.succ f) m st s (.localSet i) env =
    (match s.values with
      | v :: vs => match s.set? i v with
        | some s => .Fallthrough st { s with values := vs }
        | none   => .Invalid "localSet index out of bounds"
      | _ => .Invalid "localSet with empty stack") := by
  rw [execOne.eq_def] <;> rfl

@[cbv_eval] theorem execOne_localTee {α : Type} (f : Nat) (m : Module)
    (st : Store α) (s : Locals) (env : HostEnv α) (i : Nat) :
    execOne (Nat.succ f) m st s (.localTee i) env =
    (match s.values with
      | v :: _ => match s.set? i v with
        | some s => .Fallthrough st s
        | none   => .Invalid "localTee index out of bounds"
      | _ => .Invalid "localTee with empty stack") := by
  rw [execOne.eq_def] <;> rfl

@[cbv_eval] theorem execOne_globalGet {α : Type} (f : Nat) (m : Module)
    (st : Store α) (s : Locals) (env : HostEnv α) (i : Nat) :
    execOne (Nat.succ f) m st s (.globalGet i) env =
    (match st.globals.globals[i]? with
      | some v => .Fallthrough st { s with values := v :: s.values }
      | none   => .Invalid "globalGet index out of bounds") := by
  rw [execOne.eq_def] <;> rfl

@[cbv_eval] theorem execOne_globalSet {α : Type} (f : Nat) (m : Module)
    (st : Store α) (s : Locals) (env : HostEnv α) (i : Nat) :
    execOne (Nat.succ f) m st s (.globalSet i) env =
    (match s.values with
      | v :: vs => match st.globals.globals[i]? with
        | some _ =>
          .Fallthrough { st with globals := { globals := st.globals.globals.set i v } }
                       { s with values := vs }
        | none => .Invalid "globalSet index out of bounds"
      | _ => .Invalid "globalSet with empty stack") := by
  rw [execOne.eq_def] <;> rfl

@[cbv_eval] theorem execOne_const {α : Type} (f : Nat) (m : Module)
    (st : Store α) (s : Locals) (env : HostEnv α) (v : UInt32) :
    execOne (Nat.succ f) m st s (.const v) env =
    (.Fallthrough st { s with values := .i32 v :: s.values }) := by
  rw [execOne.eq_def] <;> rfl

@[cbv_eval] theorem execOne_constI64 {α : Type} (f : Nat) (m : Module)
    (st : Store α) (s : Locals) (env : HostEnv α) (v : UInt64) :
    execOne (Nat.succ f) m st s (.constI64 v) env =
    (.Fallthrough st { s with values := .i64 v :: s.values }) := by
  rw [execOne.eq_def] <;> rfl

@[cbv_eval] theorem execOne_eqz {α : Type} (f : Nat) (m : Module)
    (st : Store α) (s : Locals) (env : HostEnv α) :
    execOne (Nat.succ f) m st s (.eqz) env =
    (match s.values with
      | .i32 a :: vs => .Fallthrough st { s with values := .i32 (if a = 0 then 1 else 0) :: vs }
      | _ => .Invalid "eqz: ill-shaped operand stack") := by
  rw [execOne.eq_def] <;> rfl

@[cbv_eval] theorem execOne_eq {α : Type} (f : Nat) (m : Module)
    (st : Store α) (s : Locals) (env : HostEnv α) :
    execOne (Nat.succ f) m st s (.eq) env =
    (match s.values with
      | .i32 b :: .i32 a :: vs => .Fallthrough st { s with values := .i32 (if a = b then 1 else 0) :: vs }
      | _ => .Invalid "eq: ill-shaped operand stack") := by
  rw [execOne.eq_def] <;> rfl

@[cbv_eval] theorem execOne_addI64 {α : Type} (f : Nat) (m : Module)
    (st : Store α) (s : Locals) (env : HostEnv α) :
    execOne (Nat.succ f) m st s (.addI64) env =
    (match s.values with
      | .i64 b :: .i64 a :: vs => .Fallthrough st { s with values := .i64 (a + b) :: vs }
      | _ => .Invalid "addI64: ill-shaped operand stack") := by
  rw [execOne.eq_def] <;> rfl

@[cbv_eval] theorem execOne_subI64 {α : Type} (f : Nat) (m : Module)
    (st : Store α) (s : Locals) (env : HostEnv α) :
    execOne (Nat.succ f) m st s (.subI64) env =
    (match s.values with
      | .i64 b :: .i64 a :: vs => .Fallthrough st { s with values := .i64 (a - b) :: vs }
      | _ => .Invalid "subI64: ill-shaped operand stack") := by
  rw [execOne.eq_def] <;> rfl

@[cbv_eval] theorem execOne_mulI64 {α : Type} (f : Nat) (m : Module)
    (st : Store α) (s : Locals) (env : HostEnv α) :
    execOne (Nat.succ f) m st s (.mulI64) env =
    (match s.values with
      | .i64 b :: .i64 a :: vs => .Fallthrough st { s with values := .i64 (a * b) :: vs }
      | _ => .Invalid "mulI64: ill-shaped operand stack") := by
  rw [execOne.eq_def] <;> rfl

@[cbv_eval] theorem execOne_divUI64 {α : Type} (f : Nat) (m : Module)
    (st : Store α) (s : Locals) (env : HostEnv α) :
    execOne (Nat.succ f) m st s (.divUI64) env =
    (match s.values with
      | .i64 b :: .i64 a :: vs =>
        if b = 0 then .Trap st "integer divide by zero"
        else .Fallthrough st { s with values := .i64 (a / b) :: vs }
      | _ => .Invalid "divUI64: ill-shaped operand stack") := by
  rw [execOne.eq_def] <;> rfl

@[cbv_eval] theorem execOne_eqzI64 {α : Type} (f : Nat) (m : Module)
    (st : Store α) (s : Locals) (env : HostEnv α) :
    execOne (Nat.succ f) m st s (.eqzI64) env =
    (match s.values with
      | .i64 a :: vs => .Fallthrough st { s with values := .i32 (if a = 0 then 1 else 0) :: vs }
      | _ => .Invalid "eqzI64: ill-shaped operand stack") := by
  rw [execOne.eq_def] <;> rfl

@[cbv_eval] theorem execOne_eqI64 {α : Type} (f : Nat) (m : Module)
    (st : Store α) (s : Locals) (env : HostEnv α) :
    execOne (Nat.succ f) m st s (.eqI64) env =
    (match s.values with
      | .i64 b :: .i64 a :: vs => .Fallthrough st { s with values := .i32 (if a = b then 1 else 0) :: vs }
      | _ => .Invalid "eqI64: ill-shaped operand stack") := by
  rw [execOne.eq_def] <;> rfl

@[cbv_eval] theorem execOne_neI64 {α : Type} (f : Nat) (m : Module)
    (st : Store α) (s : Locals) (env : HostEnv α) :
    execOne (Nat.succ f) m st s (.neI64) env =
    (match s.values with
      | .i64 b :: .i64 a :: vs => .Fallthrough st { s with values := .i32 (if a ≠ b then 1 else 0) :: vs }
      | _ => .Invalid "neI64: ill-shaped operand stack") := by
  rw [execOne.eq_def] <;> rfl

@[cbv_eval] theorem execOne_ltUI64 {α : Type} (f : Nat) (m : Module)
    (st : Store α) (s : Locals) (env : HostEnv α) :
    execOne (Nat.succ f) m st s (.ltUI64) env =
    (match s.values with
      | .i64 b :: .i64 a :: vs => .Fallthrough st { s with values := .i32 (if a < b then 1 else 0) :: vs }
      | _ => .Invalid "ltUI64: ill-shaped operand stack") := by
  rw [execOne.eq_def] <;> rfl

@[cbv_eval] theorem execOne_geUI64 {α : Type} (f : Nat) (m : Module)
    (st : Store α) (s : Locals) (env : HostEnv α) :
    execOne (Nat.succ f) m st s (.geUI64) env =
    (match s.values with
      | .i64 b :: .i64 a :: vs => .Fallthrough st { s with values := .i32 (if a ≥ b then 1 else 0) :: vs }
      | _ => .Invalid "geUI64: ill-shaped operand stack") := by
  rw [execOne.eq_def] <;> rfl

@[cbv_eval] theorem execOne_andI64 {α : Type} (f : Nat) (m : Module)
    (st : Store α) (s : Locals) (env : HostEnv α) :
    execOne (Nat.succ f) m st s (.andI64) env =
    (match s.values with
      | .i64 b :: .i64 a :: vs => .Fallthrough st { s with values := .i64 (a &&& b) :: vs }
      | _ => .Invalid "andI64: ill-shaped operand stack") := by
  rw [execOne.eq_def] <;> rfl

@[cbv_eval] theorem execOne_shrUI64 {α : Type} (f : Nat) (m : Module)
    (st : Store α) (s : Locals) (env : HostEnv α) :
    execOne (Nat.succ f) m st s (.shrUI64) env =
    (match s.values with
      | .i64 b :: .i64 a :: vs =>
        let k := b % 64
        .Fallthrough st { s with values := .i64 (a >>> k) :: vs }
      | _ => .Invalid "shrUI64: ill-shaped operand stack") := by
  rw [execOne.eq_def] <;> rfl

@[cbv_eval] theorem execOne_wrapI64 {α : Type} (f : Nat) (m : Module)
    (st : Store α) (s : Locals) (env : HostEnv α) :
    execOne (Nat.succ f) m st s (.wrapI64) env =
    (match s.values with
      | .i64 a :: vs => .Fallthrough st { s with values := .i32 (UInt32.ofNat (a.toNat % 2 ^ 32)) :: vs }
      | _ => .Invalid "wrapI64: ill-shaped operand stack") := by
  rw [execOne.eq_def] <;> rfl

@[cbv_eval] theorem execOne_extendUI32 {α : Type} (f : Nat) (m : Module)
    (st : Store α) (s : Locals) (env : HostEnv α) :
    execOne (Nat.succ f) m st s (.extendUI32) env =
    (match s.values with
      | .i32 a :: vs => .Fallthrough st { s with values := .i64 (UInt64.ofNat a.toNat) :: vs }
      | _ => .Invalid "extendUI32: ill-shaped operand stack") := by
  rw [execOne.eq_def] <;> rfl

@[cbv_eval] theorem execOne_block {α : Type} (f : Nat) (m : Module)
    (st : Store α) (s : Locals) (env : HostEnv α) (paramArity resultArity : Nat) (body : Program) (paramTypes resultTypes : List ValueType) :
    execOne (Nat.succ f) m st s (.block paramArity resultArity body paramTypes resultTypes) env =
    (let belowStack := s.values.drop paramArity
      match exec f m st s body env with
      | .Fallthrough r' s' =>
        .Fallthrough r' { s' with values := s'.values.take resultArity ++ belowStack }
      | .Break 0 r' s' =>
        .Fallthrough r' { s' with values := s'.values.take resultArity ++ belowStack }
      | .Break (k + 1) r' s' => .Break k r' s'
      | other => other) := by
  rw [execOne.eq_def] <;> rfl

@[cbv_eval] theorem execOne_loop {α : Type} (f : Nat) (m : Module)
    (st : Store α) (s : Locals) (env : HostEnv α) (paramArity resultArity : Nat) (body : Program) (paramTypes resultTypes : List ValueType) :
    execOne (Nat.succ f) m st s (.loop paramArity resultArity body paramTypes resultTypes) env =
    (let belowStack := s.values.drop paramArity
      match exec f m st s body env with
      | .Fallthrough r' s' =>
        .Fallthrough r' { s' with values := s'.values.take resultArity ++ belowStack }
      | .Break 0 r' s' =>
        execOne f m r' { s' with values := s'.values.take paramArity ++ belowStack } (.loop paramArity resultArity body paramTypes resultTypes) env
      | .Break (k + 1) r' s' => .Break k r' s'
      | other => other) := by
  rw [execOne.eq_def] <;> rfl

@[cbv_eval] theorem execOne_iff {α : Type} (f : Nat) (m : Module)
    (st : Store α) (s : Locals) (env : HostEnv α) (paramArity resultArity : Nat) (thn els : Program) (paramTypes resultTypes : List ValueType) :
    execOne (Nat.succ f) m st s (.iff paramArity resultArity thn els paramTypes resultTypes) env =
    (match s.values with
      | .i32 c :: vs =>
        let belowStack := vs.drop paramArity
        let s' : Locals := { s with values := vs }
        let body := if c ≠ 0 then thn else els
        match exec f m st s' body env with
        | .Fallthrough r' s'' =>
          .Fallthrough r' { s'' with values := s''.values.take resultArity ++ belowStack }
        | .Break 0 r' s'' =>
          .Fallthrough r' { s'' with values := s''.values.take resultArity ++ belowStack }
        | .Break (k + 1) r' s'' => .Break k r' s''
        | other => other
      | _ => .Invalid "iff: ill-shaped operand stack") := by
  rw [execOne.eq_def] <;> rfl

@[cbv_eval] theorem execOne_br {α : Type} (f : Nat) (m : Module)
    (st : Store α) (s : Locals) (env : HostEnv α) (n : Nat) :
    execOne (Nat.succ f) m st s (.br n) env =
    (.Break n st s) := by
  rw [execOne.eq_def] <;> rfl

@[cbv_eval] theorem execOne_br_if {α : Type} (f : Nat) (m : Module)
    (st : Store α) (s : Locals) (env : HostEnv α) (n : Nat) :
    execOne (Nat.succ f) m st s (.br_if n) env =
    (match s.values with
      | .i32 0 :: vs => .Fallthrough st { s with values := vs }
      | .i32 _ :: vs => .Break n st { s with values := vs }
      | _ => .Invalid "br_if: ill-shaped operand stack") := by
  rw [execOne.eq_def] <;> rfl

@[cbv_eval] theorem execOne_call {α : Type} (f : Nat) (m : Module)
    (st : Store α) (s : Locals) (env : HostEnv α) (id : Nat) :
    execOne (Nat.succ f) m st s (.call id) env =
    (match run f m id st s.values env with
      | .Success vs st' => .Fallthrough st' { s with values := vs }
      | .Trap st' msg   => .Trap st' msg
      | .Invalid msg    => .Invalid msg
      | .OutOfFuel      => .OutOfFuel
      | .Thrown tag args st' => .Throwing tag args st' s) := by
  rw [execOne.eq_def] <;> rfl

@[cbv_eval] theorem execOne_load32 {α : Type} (f : Nat) (m : Module)
    (st : Store α) (s : Locals) (env : HostEnv α) (off : UInt32) :
    execOne (Nat.succ f) m st s (.load32 off) env =
    (match s.values with
      | .i32 a :: vs =>
        if a.toNat + off.toNat + 4 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v := st.mem.read32 (a + off)
          .Fallthrough st { s with values := .i32 v :: vs }
      | .i64 a :: vs =>
        if a.toNat + off.toNat + 4 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v := st.mem.read32 (a.toUInt32 + off)
          .Fallthrough st { s with values := .i32 v :: vs }
      | _ => .Invalid "load32: ill-shaped operand stack") := by
  rw [execOne.eq_def] <;> rfl

@[cbv_eval] theorem execOne_store32 {α : Type} (f : Nat) (m : Module)
    (st : Store α) (s : Locals) (env : HostEnv α) (off : UInt32) :
    execOne (Nat.succ f) m st s (.store32 off) env =
    (match s.values with
      | .i32 v :: .i32 a :: vs =>
        if a.toNat + off.toNat + 4 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let mem' := st.mem.write32 (a + off) v
          .Fallthrough { st with mem := mem' } { s with values := vs }
      | .i32 v :: .i64 a :: vs =>
        if a.toNat + off.toNat + 4 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let mem' := st.mem.write32 (a.toUInt32 + off) v
          .Fallthrough { st with mem := mem' } { s with values := vs }
      | _ => .Invalid "store32: ill-shaped operand stack") := by
  rw [execOne.eq_def] <;> rfl

@[cbv_eval] theorem execOne_load64 {α : Type} (f : Nat) (m : Module)
    (st : Store α) (s : Locals) (env : HostEnv α) (off : UInt32) :
    execOne (Nat.succ f) m st s (.load64 off) env =
    (match s.values with
      | .i32 a :: vs =>
        if a.toNat + off.toNat + 8 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v := st.mem.read64 (a + off)
          .Fallthrough st { s with values := .i64 v :: vs }
      | .i64 a :: vs =>
        if a.toNat + off.toNat + 8 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v := st.mem.read64 (a.toUInt32 + off)
          .Fallthrough st { s with values := .i64 v :: vs }
      | _ => .Invalid "load64: ill-shaped operand stack") := by
  rw [execOne.eq_def] <;> rfl

@[cbv_eval] theorem execOne_store64 {α : Type} (f : Nat) (m : Module)
    (st : Store α) (s : Locals) (env : HostEnv α) (off : UInt32) :
    execOne (Nat.succ f) m st s (.store64 off) env =
    (match s.values with
      | .i64 v :: .i32 a :: vs =>
        if a.toNat + off.toNat + 8 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let mem' := st.mem.write64 (a + off) v
          .Fallthrough { st with mem := mem' } { s with values := vs }
      | .i64 v :: .i64 a :: vs =>
        if a.toNat + off.toNat + 8 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let mem' := st.mem.write64 (a.toUInt32 + off) v
          .Fallthrough { st with mem := mem' } { s with values := vs }
      | _ => .Invalid "store64: ill-shaped operand stack") := by
  rw [execOne.eq_def] <;> rfl

@[cbv_eval] theorem execOne_memorySize {α : Type} (f : Nat) (m : Module)
    (st : Store α) (s : Locals) (env : HostEnv α) :
    execOne (Nat.succ f) m st s (.memorySize) env =
    (.Fallthrough st { s with values := sizeValue m.memIs64 st.mem.pages :: s.values }) := by
  rw [execOne.eq_def] <;> rfl

@[cbv_eval] theorem execOne_memoryGrow {α : Type} (f : Nat) (m : Module)
    (st : Store α) (s : Locals) (env : HostEnv α) :
    execOne (Nat.succ f) m st s (.memoryGrow) env =
    (match s.values with
      | .i32 delta :: vs =>
        match st.mem.grow delta (st.memoryCap m 0) with
        | some (mem', cur) =>
          .Fallthrough { st with mem := mem' }
            { s with values := .i32 cur.toUInt32 :: vs }
        | none =>
          .Fallthrough st { s with values := .i32 (0xFFFFFFFF : UInt32) :: vs }
      | .i64 delta :: vs =>
        if delta.toNat ≥ 2 ^ 32 then
          .Fallthrough st { s with values := .i64 (0xFFFFFFFFFFFFFFFF : UInt64) :: vs }
        else
          match st.mem.grow delta.toUInt32 (st.memoryCap m 0) with
          | some (mem', cur) =>
            .Fallthrough { st with mem := mem' }
              { s with values := .i64 cur.toUInt64 :: vs }
          | none =>
            .Fallthrough st { s with values := .i64 (0xFFFFFFFFFFFFFFFF : UInt64) :: vs }
      | _ => .Invalid "memoryGrow: ill-shaped operand stack") := by
  rw [execOne.eq_def] <;> rfl

@[cbv_eval] theorem execOne_ret {α : Type} (f : Nat) (m : Module)
    (st : Store α) (s : Locals) (env : HostEnv α) :
    execOne (Nat.succ f) m st s (.ret) env =
    (.Return st s.values) := by
  rw [execOne.eq_def] <;> rfl

@[cbv_eval] theorem execOne_unreachable {α : Type} (f : Nat) (m : Module)
    (st : Store α) (s : Locals) (env : HostEnv α) :
    execOne (Nat.succ f) m st s (.unreachable) env =
    (.Trap st "unreachable") := by
  rw [execOne.eq_def] <;> rfl

end Project.ProofKit.InterpreterEvaluation
