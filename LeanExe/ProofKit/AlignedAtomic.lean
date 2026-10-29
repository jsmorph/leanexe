import LeanExe.ProofKit.AlignedFlagRules

/-!
The flagged forms of Talos's atomic rules for the instructions of the native subset, generated from
`Interpreter/Wasm/Wp/Atomic.lean`: each states the rule with `wpX strict` for `wp` and proves it
from Talos's rule at `strict = false` and from the `wpA` step rules at `strict = true`.  They carry
`@[simp]`, as Talos's rules do, so that `simp` runs straight-line code under either value of the
flag.  `load64` and `store64` have their own rules, with the alignment conjunct.
-/

namespace LeanExe.ProofKit

open Wasm

/-- The `wpA` form of an atomic rule: split the rule's cases, and close each by the step rules
with the instruction's step computed by `simp`. -/
syntax "wpA_atomic" : tactic

macro_rules
  | `(tactic| wpA_atomic) => `(tactic| first
      | (split <;> wpA_atomic)
      | (refine wpA_cons_stop (fun _ => ?e) (by simp) (fun _ => ?a)
         case e => (simp only [execOne.eq_def]; done)
         case a => simp [AlignedOne])
      | (refine wpA_cons_fall (fun _ => ?e) (fun _ => ?a)
         case e => (simp [execOne.eq_def, *]; done)
         case a => simp [AlignedOne])
      | (refine wpA_cons_stop (fun _ => ?e) (by simp) (fun _ => ?a)
         case e => (simp [execOne.eq_def, *]; done)
         case a => simp [AlignedOne]))

variable {α : Type} {strict : Bool} {m : Module} {Q : Assertion α} {st : Store α} {s : Locals}
  {env : HostEnv α} {rest : Program}

@[simp] theorem wpX_const_cons :
    wpX strict m (.const v :: rest) Q st s env ↔
    wpX strict m rest Q st { s with values := .i32 v :: s.values } env := by
  cases strict
  · exact wp_const_cons
  · wpA_atomic

@[simp] theorem wpX_eq_cons :
    wpX strict m (.eq :: rest) Q st s env ↔
    (match s.values with
     | .i32 b :: .i32 a :: vs => wpX strict m rest Q st { s with values := .i32 (if a = b then 1 else 0) :: vs } env
     | _ => Q (.Invalid "eq: ill-shaped operand stack")) := by
  cases strict
  · exact wp_eq_cons
  · wpA_atomic

@[simp] theorem wpX_eqz_cons :
    wpX strict m (.eqz :: rest) Q st s env ↔
    (match s.values with
     | .i32 a :: vs => wpX strict m rest Q st { s with values := .i32 (if a = 0 then 1 else 0) :: vs } env
     | _ => Q (.Invalid "eqz: ill-shaped operand stack")) := by
  cases strict
  · exact wp_eqz_cons
  · wpA_atomic

@[simp] theorem wpX_and_cons :
    wpX strict m (.and :: rest) Q st s env ↔
    (match s.values with
     | .i32 a :: .i32 b :: vs => wpX strict m rest Q st { s with values := .i32 (a &&& b) :: vs } env
     | _ => Q (.Invalid "and: ill-shaped operand stack")) := by
  cases strict
  · exact wp_and_cons
  · wpA_atomic

@[simp] theorem wpX_extendUI32_cons :
    wpX strict m (.extendUI32 :: rest) Q st s env ↔
    (match s.values with
     | .i32 a :: vs => wpX strict m rest Q st { s with values := .i64 (UInt64.ofNat a.toNat) :: vs } env
     | _ => Q (.Invalid "extendUI32: ill-shaped operand stack")) := by
  cases strict
  · exact wp_extendUI32_cons
  · wpA_atomic

@[simp] theorem wpX_subI64_cons :
    wpX strict m (.subI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 b :: .i64 a :: vs => wpX strict m rest Q st { s with values := .i64 (a - b) :: vs } env
     | _ => Q (.Invalid "subI64: ill-shaped operand stack")) := by
  cases strict
  · exact wp_subI64_cons
  · wpA_atomic

@[simp] theorem wpX_divUI64_cons :
    wpX strict m (.divUI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 b :: .i64 a :: vs =>
       if b = 0 then Q (.Trap st "integer divide by zero")
       else wpX strict m rest Q st { s with values := .i64 (a / b) :: vs } env
     | _ => Q (.Invalid "divUI64: ill-shaped operand stack")) := by
  cases strict
  · exact wp_divUI64_cons
  · wpA_atomic

@[simp] theorem wpX_remUI64_cons :
    wpX strict m (.remUI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 b :: .i64 a :: vs =>
       if b = 0 then Q (.Trap st "integer divide by zero")
       else wpX strict m rest Q st { s with values := .i64 (a % b) :: vs } env
     | _ => Q (.Invalid "remUI64: ill-shaped operand stack")) := by
  cases strict
  · exact wp_remUI64_cons
  · wpA_atomic

@[simp] theorem wpX_andI64_cons :
    wpX strict m (.andI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 b :: .i64 a :: vs => wpX strict m rest Q st { s with values := .i64 (a &&& b) :: vs } env
     | _ => Q (.Invalid "andI64: ill-shaped operand stack")) := by
  cases strict
  · exact wp_andI64_cons
  · wpA_atomic

@[simp] theorem wpX_orI64_cons :
    wpX strict m (.orI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 b :: .i64 a :: vs => wpX strict m rest Q st { s with values := .i64 (a ||| b) :: vs } env
     | _ => Q (.Invalid "orI64: ill-shaped operand stack")) := by
  cases strict
  · exact wp_orI64_cons
  · wpA_atomic

@[simp] theorem wpX_xorI64_cons :
    wpX strict m (.xorI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 b :: .i64 a :: vs => wpX strict m rest Q st { s with values := .i64 (a ^^^ b) :: vs } env
     | _ => Q (.Invalid "xorI64: ill-shaped operand stack")) := by
  cases strict
  · exact wp_xorI64_cons
  · wpA_atomic

@[simp] theorem wpX_shlI64_cons :
    wpX strict m (.shlI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 b :: .i64 a :: vs => wpX strict m rest Q st { s with values := .i64 (a <<< (b % 64)) :: vs } env
     | _ => Q (.Invalid "shlI64: ill-shaped operand stack")) := by
  cases strict
  · exact wp_shlI64_cons
  · wpA_atomic

@[simp] theorem wpX_shrUI64_cons :
    wpX strict m (.shrUI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 b :: .i64 a :: vs => wpX strict m rest Q st { s with values := .i64 (a >>> (b % 64)) :: vs } env
     | _ => Q (.Invalid "shrUI64: ill-shaped operand stack")) := by
  cases strict
  · exact wp_shrUI64_cons
  · wpA_atomic

@[simp] theorem wpX_eqI64_cons :
    wpX strict m (.eqI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 b :: .i64 a :: vs => wpX strict m rest Q st { s with values := .i32 (if a = b then 1 else 0) :: vs } env
     | _ => Q (.Invalid "eqI64: ill-shaped operand stack")) := by
  cases strict
  · exact wp_eqI64_cons
  · wpA_atomic

@[simp] theorem wpX_neI64_cons :
    wpX strict m (.neI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 b :: .i64 a :: vs => wpX strict m rest Q st { s with values := .i32 (if a ≠ b then 1 else 0) :: vs } env
     | _ => Q (.Invalid "neI64: ill-shaped operand stack")) := by
  cases strict
  · exact wp_neI64_cons
  · wpA_atomic

@[simp] theorem wpX_ltUI64_cons :
    wpX strict m (.ltUI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 b :: .i64 a :: vs => wpX strict m rest Q st { s with values := .i32 (if a < b then 1 else 0) :: vs } env
     | _ => Q (.Invalid "ltUI64: ill-shaped operand stack")) := by
  cases strict
  · exact wp_ltUI64_cons
  · wpA_atomic

@[simp] theorem wpX_leUI64_cons :
    wpX strict m (.leUI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 b :: .i64 a :: vs => wpX strict m rest Q st { s with values := .i32 (if a ≤ b then 1 else 0) :: vs } env
     | _ => Q (.Invalid "leUI64: ill-shaped operand stack")) := by
  cases strict
  · exact wp_leUI64_cons
  · wpA_atomic

@[simp] theorem wpX_eqzI64_cons :
    wpX strict m (.eqzI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 a :: vs => wpX strict m rest Q st { s with values := .i32 (if a = 0 then 1 else 0) :: vs } env
     | _ => Q (.Invalid "eqzI64: ill-shaped operand stack")) := by
  cases strict
  · exact wp_eqzI64_cons
  · wpA_atomic

@[simp] theorem wpX_globalGet_cons :
    wpX strict m (.globalGet i :: rest) Q st s env ↔
    (match st.globals.globals[i]? with
     | some v => wpX strict m rest Q st { s with values := v :: s.values } env
     | none   => Q (.Invalid "globalGet index out of bounds")) := by
  cases strict
  · exact wp_globalGet_cons
  · wpA_atomic

@[simp] theorem wpX_globalSet_cons :
    wpX strict m (.globalSet i :: rest) Q st s env ↔
    (match s.values with
     | v :: vs =>
       (match st.globals.globals[i]? with
        | some _ =>
          wpX strict m rest Q { st with globals := { globals := st.globals.globals.set i v } }
                      { s with values := vs } env
        | none => Q (.Invalid "globalSet index out of bounds"))
     | _ => Q (.Invalid "globalSet with empty stack")) := by
  cases strict
  · exact wp_globalSet_cons
  · wpA_atomic

@[simp] theorem wpX_load8U_cons :
    wpX strict m (.load8U off :: rest) Q st s env ↔
    (match s.values with
     | .i32 a :: vs =>
       if a.toNat + off.toNat + 1 > st.mem.pages * 65536 then
         Q (.Trap st "out of bounds memory access")
       else wpX strict m rest Q st { s with values := .i32 (st.mem.read8 (a + off)).toUInt32 :: vs } env
     | .i64 a :: vs =>
       if a.toNat + off.toNat + 1 > st.mem.pages * 65536 then
         Q (.Trap st "out of bounds memory access")
       else wpX strict m rest Q st { s with values := .i32 (st.mem.read8 (a.toUInt32 + off)).toUInt32 :: vs } env
     | _ => Q (.Invalid "load8U: ill-shaped operand stack")) := by
  cases strict
  · exact wp_load8U_cons
  · wpA_atomic

@[simp] theorem wpX_store8_cons :
    wpX strict m (.store8 off :: rest) Q st s env ↔
    (match s.values with
     | .i32 v :: .i32 a :: vs =>
       if a.toNat + off.toNat + 1 > st.mem.pages * 65536 then
         Q (.Trap st "out of bounds memory access")
       else wpX strict m rest Q { st with mem := st.mem.write8 (a + off) v.toUInt8 } { s with values := vs } env
     | .i32 v :: .i64 a :: vs =>
       if a.toNat + off.toNat + 1 > st.mem.pages * 65536 then
         Q (.Trap st "out of bounds memory access")
       else wpX strict m rest Q { st with mem := st.mem.write8 (a.toUInt32 + off) v.toUInt8 } { s with values := vs } env
     | _ => Q (.Invalid "store8: ill-shaped operand stack")) := by
  cases strict
  · exact wp_store8_cons
  · wpA_atomic

@[simp] theorem wpX_memorySize_cons :
    wpX strict m (.memorySize :: rest) Q st s env ↔
    wpX strict m rest Q st { s with values := sizeValue m.memIs64 st.mem.pages :: s.values } env := by
  cases strict
  · exact wp_memorySize_cons
  · wpA_atomic

@[simp] theorem wpX_ret_cons : wpX strict m (.ret :: rest) Q st s env ↔ Q (.Return st s.values) := by
  cases strict
  · exact wp_ret_cons
  · wpA_atomic

@[simp] theorem wpX_drop_cons :
    wpX strict m (.drop :: rest) Q st s env ↔
    (match s.values with
     | _ :: vs => wpX strict m rest Q st { s with values := vs } env
     | _ => Q (.Invalid "drop: empty operand stack")) := by
  cases strict
  · exact wp_drop_cons
  · wpA_atomic

@[simp] theorem wpX_select_cons :
    wpX strict m (.select :: rest) Q st s env ↔
    (match s.values with
     | .i32 c :: v2 :: v1 :: vs =>
       wpX strict m rest Q st { s with values := (if c ≠ 0 then v1 else v2) :: vs } env
     | _ => Q (.Invalid "select: ill-shaped operand stack")) := by
  cases strict
  · exact wp_select_cons
  · wpA_atomic

@[simp] theorem wpX_nop_cons : wpX strict m (.nop :: rest) Q st s env ↔ wpX strict m rest Q st s env := by
  cases strict
  · exact wp_nop_cons
  · wpA_atomic

@[simp] theorem wpX_f64Const_cons :
    wpX strict m (.f64Const v :: rest) Q st s env ↔
    wpX strict m rest Q st { s with values := .f64 v :: s.values } env := by
  cases strict
  · exact wp_f64Const_cons
  · wpA_atomic

@[simp] theorem wpX_f64Add_cons :
    wpX strict m (.f64Add :: rest) Q st s env ↔
    (match s.values with
     | .f64 b :: .f64 a :: vs => wpX strict m rest Q st { s with values := .f64 (f64Add a b) :: vs } env
     | _ => Q (.Invalid "f64Add: ill-shaped operand stack")) := by
  cases strict
  · exact wp_f64Add_cons
  · wpA_atomic

@[simp] theorem wpX_f64Sub_cons :
    wpX strict m (.f64Sub :: rest) Q st s env ↔
    (match s.values with
     | .f64 b :: .f64 a :: vs => wpX strict m rest Q st { s with values := .f64 (f64Sub a b) :: vs } env
     | _ => Q (.Invalid "f64Sub: ill-shaped operand stack")) := by
  cases strict
  · exact wp_f64Sub_cons
  · wpA_atomic

@[simp] theorem wpX_f64Mul_cons :
    wpX strict m (.f64Mul :: rest) Q st s env ↔
    (match s.values with
     | .f64 b :: .f64 a :: vs => wpX strict m rest Q st { s with values := .f64 (f64Mul a b) :: vs } env
     | _ => Q (.Invalid "f64Mul: ill-shaped operand stack")) := by
  cases strict
  · exact wp_f64Mul_cons
  · wpA_atomic

@[simp] theorem wpX_f64Div_cons :
    wpX strict m (.f64Div :: rest) Q st s env ↔
    (match s.values with
     | .f64 b :: .f64 a :: vs => wpX strict m rest Q st { s with values := .f64 (f64Div a b) :: vs } env
     | _ => Q (.Invalid "f64Div: ill-shaped operand stack")) := by
  cases strict
  · exact wp_f64Div_cons
  · wpA_atomic

@[simp] theorem wpX_f64Eq_cons :
    wpX strict m (.f64Eq :: rest) Q st s env ↔
    (match s.values with
     | .f64 b :: .f64 a :: vs => wpX strict m rest Q st { s with values := .i32 (if f64Eq a b then 1 else 0) :: vs } env
     | _ => Q (.Invalid "f64Eq: ill-shaped operand stack")) := by
  cases strict
  · exact wp_f64Eq_cons
  · wpA_atomic

@[simp] theorem wpX_f64Lt_cons :
    wpX strict m (.f64Lt :: rest) Q st s env ↔
    (match s.values with
     | .f64 b :: .f64 a :: vs => wpX strict m rest Q st { s with values := .i32 (if f64Lt a b then 1 else 0) :: vs } env
     | _ => Q (.Invalid "f64Lt: ill-shaped operand stack")) := by
  cases strict
  · exact wp_f64Lt_cons
  · wpA_atomic

@[simp] theorem wpX_f64Le_cons :
    wpX strict m (.f64Le :: rest) Q st s env ↔
    (match s.values with
     | .f64 b :: .f64 a :: vs => wpX strict m rest Q st { s with values := .i32 (if f64Le a b then 1 else 0) :: vs } env
     | _ => Q (.Invalid "f64Le: ill-shaped operand stack")) := by
  cases strict
  · exact wp_f64Le_cons
  · wpA_atomic

@[simp] theorem wpX_f64Sqrt_cons :
    wpX strict m (.f64Sqrt :: rest) Q st s env ↔
    (match s.values with
     | .f64 a :: vs => wpX strict m rest Q st { s with values := .f64 (f64Sqrt a) :: vs } env
     | _ => Q (.Invalid "f64Sqrt: ill-shaped operand stack")) := by
  cases strict
  · exact wp_f64Sqrt_cons
  · wpA_atomic

@[simp] theorem wpX_f64Abs_cons :
    wpX strict m (.f64Abs :: rest) Q st s env ↔
    (match s.values with
     | .f64 a :: vs => wpX strict m rest Q st { s with values := .f64 (f64Abs a) :: vs } env
     | _ => Q (.Invalid "f64Abs: ill-shaped operand stack")) := by
  cases strict
  · exact wp_f64Abs_cons
  · wpA_atomic

@[simp] theorem wpX_f64Neg_cons :
    wpX strict m (.f64Neg :: rest) Q st s env ↔
    (match s.values with
     | .f64 a :: vs => wpX strict m rest Q st { s with values := .f64 (f64Neg a) :: vs } env
     | _ => Q (.Invalid "f64Neg: ill-shaped operand stack")) := by
  cases strict
  · exact wp_f64Neg_cons
  · wpA_atomic

@[simp] theorem wpX_f64ConvertI64U_cons :
    wpX strict m (.f64ConvertI64U :: rest) Q st s env ↔
    (match s.values with
     | .i64 a :: vs => wpX strict m rest Q st { s with values := .f64 (f64ConvertI64U a) :: vs } env
     | _ => Q (.Invalid "f64ConvertI64U: ill-shaped operand stack")) := by
  cases strict
  · exact wp_f64ConvertI64U_cons
  · wpA_atomic

@[simp] theorem wpX_f64ReinterpretI64_cons :
    wpX strict m (.f64ReinterpretI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 b :: vs => wpX strict m rest Q st { s with values := .f64 b :: vs } env
     | _ => Q (.Invalid "f64ReinterpretI64: ill-shaped operand stack")) := by
  cases strict
  · exact wp_f64ReinterpretI64_cons
  · wpA_atomic

@[simp] theorem wpX_i64ReinterpretF64_cons :
    wpX strict m (.i64ReinterpretF64 :: rest) Q st s env ↔
    (match s.values with
     | .f64 b :: vs => wpX strict m rest Q st { s with values := .i64 b :: vs } env
     | _ => Q (.Invalid "i64ReinterpretF64: ill-shaped operand stack")) := by
  cases strict
  · exact wp_i64ReinterpretF64_cons
  · wpA_atomic

@[simp] theorem wpX_i64TruncSatF64U_cons :
    wpX strict m (.i64TruncSatF64U :: rest) Q st s env ↔
    (match s.values with
     | .f64 a :: vs => wpX strict m rest Q st { s with values := .i64 (i64TruncSatF64U a) :: vs } env
     | _ => Q (.Invalid "i64TruncSatF64U: ill-shaped operand stack")) := by
  cases strict
  · exact wp_i64TruncSatF64U_cons
  · wpA_atomic

@[simp] theorem wpX_f32Const_cons :
    wpX strict m (.f32Const v :: rest) Q st s env ↔
    wpX strict m rest Q st { s with values := .f32 v :: s.values } env := by
  cases strict
  · exact wp_f32Const_cons
  · wpA_atomic

@[simp] theorem wpX_f32Add_cons :
    wpX strict m (.f32Add :: rest) Q st s env ↔
    (match s.values with
     | .f32 b :: .f32 a :: vs => wpX strict m rest Q st { s with values := .f32 (f32Add a b) :: vs } env
     | _ => Q (.Invalid "f32Add: ill-shaped operand stack")) := by
  cases strict
  · exact wp_f32Add_cons
  · wpA_atomic

@[simp] theorem wpX_f32Sub_cons :
    wpX strict m (.f32Sub :: rest) Q st s env ↔
    (match s.values with
     | .f32 b :: .f32 a :: vs => wpX strict m rest Q st { s with values := .f32 (f32Sub a b) :: vs } env
     | _ => Q (.Invalid "f32Sub: ill-shaped operand stack")) := by
  cases strict
  · exact wp_f32Sub_cons
  · wpA_atomic

@[simp] theorem wpX_f32Mul_cons :
    wpX strict m (.f32Mul :: rest) Q st s env ↔
    (match s.values with
     | .f32 b :: .f32 a :: vs => wpX strict m rest Q st { s with values := .f32 (f32Mul a b) :: vs } env
     | _ => Q (.Invalid "f32Mul: ill-shaped operand stack")) := by
  cases strict
  · exact wp_f32Mul_cons
  · wpA_atomic

@[simp] theorem wpX_f32Div_cons :
    wpX strict m (.f32Div :: rest) Q st s env ↔
    (match s.values with
     | .f32 b :: .f32 a :: vs => wpX strict m rest Q st { s with values := .f32 (f32Div a b) :: vs } env
     | _ => Q (.Invalid "f32Div: ill-shaped operand stack")) := by
  cases strict
  · exact wp_f32Div_cons
  · wpA_atomic

@[simp] theorem wpX_f32Eq_cons :
    wpX strict m (.f32Eq :: rest) Q st s env ↔
    (match s.values with
     | .f32 b :: .f32 a :: vs => wpX strict m rest Q st { s with values := .i32 (if f32Eq a b then 1 else 0) :: vs } env
     | _ => Q (.Invalid "f32Eq: ill-shaped operand stack")) := by
  cases strict
  · exact wp_f32Eq_cons
  · wpA_atomic

@[simp] theorem wpX_f32Lt_cons :
    wpX strict m (.f32Lt :: rest) Q st s env ↔
    (match s.values with
     | .f32 b :: .f32 a :: vs => wpX strict m rest Q st { s with values := .i32 (if f32Lt a b then 1 else 0) :: vs } env
     | _ => Q (.Invalid "f32Lt: ill-shaped operand stack")) := by
  cases strict
  · exact wp_f32Lt_cons
  · wpA_atomic

@[simp] theorem wpX_f32Le_cons :
    wpX strict m (.f32Le :: rest) Q st s env ↔
    (match s.values with
     | .f32 b :: .f32 a :: vs => wpX strict m rest Q st { s with values := .i32 (if f32Le a b then 1 else 0) :: vs } env
     | _ => Q (.Invalid "f32Le: ill-shaped operand stack")) := by
  cases strict
  · exact wp_f32Le_cons
  · wpA_atomic

@[simp] theorem wpX_f32Sqrt_cons :
    wpX strict m (.f32Sqrt :: rest) Q st s env ↔
    (match s.values with
     | .f32 a :: vs => wpX strict m rest Q st { s with values := .f32 (f32Sqrt a) :: vs } env
     | _ => Q (.Invalid "f32Sqrt: ill-shaped operand stack")) := by
  cases strict
  · exact wp_f32Sqrt_cons
  · wpA_atomic

@[simp] theorem wpX_f32Abs_cons :
    wpX strict m (.f32Abs :: rest) Q st s env ↔
    (match s.values with
     | .f32 a :: vs => wpX strict m rest Q st { s with values := .f32 (f32Abs a) :: vs } env
     | _ => Q (.Invalid "f32Abs: ill-shaped operand stack")) := by
  cases strict
  · exact wp_f32Abs_cons
  · wpA_atomic

@[simp] theorem wpX_f32Nearest_cons :
    wpX strict m (.f32Nearest :: rest) Q st s env ↔
    (match s.values with
     | .f32 a :: vs => wpX strict m rest Q st { s with values := .f32 (f32Nearest a) :: vs } env
     | _ => Q (.Invalid "f32Nearest: ill-shaped operand stack")) := by
  cases strict
  · exact wp_f32Nearest_cons
  · wpA_atomic

@[simp] theorem wpX_f32ConvertI64U_cons :
    wpX strict m (.f32ConvertI64U :: rest) Q st s env ↔
    (match s.values with
     | .i64 a :: vs => wpX strict m rest Q st { s with values := .f32 (f32ConvertI64U a) :: vs } env
     | _ => Q (.Invalid "f32ConvertI64U: ill-shaped operand stack")) := by
  cases strict
  · exact wp_f32ConvertI64U_cons
  · wpA_atomic

@[simp] theorem wpX_f32ConvertI32S_cons :
    wpX strict m (.f32ConvertI32S :: rest) Q st s env ↔
    (match s.values with
     | .i32 a :: vs => wpX strict m rest Q st { s with values := .f32 (f32ConvertI32S a) :: vs } env
     | _ => Q (.Invalid "f32ConvertI32S: ill-shaped operand stack")) := by
  cases strict
  · exact wp_f32ConvertI32S_cons
  · wpA_atomic

@[simp] theorem wpX_f32ReinterpretI32_cons :
    wpX strict m (.f32ReinterpretI32 :: rest) Q st s env ↔
    (match s.values with
     | .i32 b :: vs => wpX strict m rest Q st { s with values := .f32 b :: vs } env
     | _ => Q (.Invalid "f32ReinterpretI32: ill-shaped operand stack")) := by
  cases strict
  · exact wp_f32ReinterpretI32_cons
  · wpA_atomic

@[simp] theorem wpX_i32ReinterpretF32_cons :
    wpX strict m (.i32ReinterpretF32 :: rest) Q st s env ↔
    (match s.values with
     | .f32 b :: vs => wpX strict m rest Q st { s with values := .i32 b :: vs } env
     | _ => Q (.Invalid "i32ReinterpretF32: ill-shaped operand stack")) := by
  cases strict
  · exact wp_i32ReinterpretF32_cons
  · wpA_atomic

@[simp] theorem wpX_i64TruncSatF32U_cons :
    wpX strict m (.i64TruncSatF32U :: rest) Q st s env ↔
    (match s.values with
     | .f32 a :: vs => wpX strict m rest Q st { s with values := .i64 (i64TruncSatF32U a) :: vs } env
     | _ => Q (.Invalid "i64TruncSatF32U: ill-shaped operand stack")) := by
  cases strict
  · exact wp_i64TruncSatF32U_cons
  · wpA_atomic

@[simp] theorem wpX_i32TruncSatF32S_cons :
    wpX strict m (.i32TruncSatF32S :: rest) Q st s env ↔
    (match s.values with
     | .f32 a :: vs => wpX strict m rest Q st { s with values := .i32 (i32TruncSatF32S a) :: vs } env
     | _ => Q (.Invalid "i32TruncSatF32S: ill-shaped operand stack")) := by
  cases strict
  · exact wp_i32TruncSatF32S_cons
  · wpA_atomic

end LeanExe.ProofKit
