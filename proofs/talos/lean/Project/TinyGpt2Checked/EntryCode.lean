import Project.TinyGpt2Checked.Inference
import Project.TinyGpt2Checked.ClipPrepare

namespace Project.TinyGpt2Checked.Spec
open Wasm Project.ProofKit

def checkedParams (pointer bound t0 t1 t2 t3 : UInt64) : List Wasm.Value :=
  [.i64 pointer, .i64 bound, .i64 t0, .i64 t1, .i64 t2, .i64 t3]

def checkedFrame (pointer bound t0 t1 t2 t3 : UInt64) : Locals :=
  func85Def.toLocals (checkedParams pointer bound t0 t1 t2 t3)

def tokenAccept : Wasm.Program :=
  [
   .call 7,
   .localSet 6,
   .localGet 6,
   .localSet 7,
   .localGet 1,
   .localSet 8,
   .constI64 0,
   .localSet 9,
   .localGet 0,
   .localSet 10,
   .localGet 7,
   .localGet 8,
   .localGet 9,
   .localGet 10,
   .call 6,
   .localSet 12,
   .localSet 11,
   .localGet 11,
   .localSet 13,
   .localGet 12,
   .localSet 14,
   .call 7,
   .localSet 15,
   .localGet 14,
   .localSet 27,
   .localGet 27,
   .wrapI64,
   .load64 0,
   .localGet 15,
   .eqI64,
   .iff 0 1 [
    .constI64 1
   ] [
    .constI64 0
   ] [] [.i64],
   .constI64 1,
   .eqI64,
   .iff 0 1 [
    .constI64 1
   ] [
    .constI64 0
   ] [] [.i64],
   .constI64 0,
   .eqI64,
   .eqz,
   .iff 0 0 [
    .localGet 13,
    .localSet 16,
    .localGet 14,
    .localSet 17,
    .localGet 2,
    .localSet 18,
    .localGet 3,
    .localSet 19,
    .localGet 4,
    .localSet 20,
    .localGet 5,
    .localSet 21,
    .localGet 16,
    .localGet 17,
    .localGet 18,
    .localGet 19,
    .localGet 20,
    .localGet 21,
    .call 84,
    .localSet 23,
    .localSet 22,
    .localGet 22,
    .localSet 25,
    .localGet 23,
    .localSet 26
   ] [
    .localGet 13,
    .localSet 25,
    .localGet 14,
    .localSet 26
   ]
  ]

def tokenReject : Wasm.Program :=
  (Annotation.resolve func85 [{ instructionIndex := 13, field := .elseBranch }]).getD []

def tokenGuard : Wasm.Program :=
  [.localGet 2, .constI64 256, .ltUI64,
   .iff 0 1 [.localGet 3, .constI64 256, .ltUI64] [.const 0] [] [.i32],
   .iff 0 1 [.localGet 4, .constI64 256, .ltUI64] [.const 0] [] [.i32],
   .iff 0 1 [.localGet 5, .constI64 256, .ltUI64] [.const 0] [] [.i32],
   .iff 0 1 [.constI64 1] [.constI64 0] [] [.i64], .constI64 1, .eqI64,
   .iff 0 1 [.constI64 1] [.constI64 0] [] [.i64], .constI64 0, .eqI64, .eqz]

theorem checked_shape : func85 = tokenGuard ++
    [.iff 0 0 tokenAccept tokenReject, .localGet 26] := rfl

theorem token_reject_shape : tokenReject =
    FixedArrayCapacity.constantProgram 0 1 31 ++
    FixedArrayAllocateNone.program 31 (FixedArrayReuse.program 31 1) 1 ++
    [.localGet 36, .localSet 27] ++ FixedArrayResult.lengthStoreProgram 27 0 ++
    [.localGet 27, .localSet 24, .localGet 24, .localSet 25, .localGet 24, .localSet 26] := rfl

theorem token_guard_spec (env : HostEnv Unit) (initial : Store Unit)
    (pointer bound t0 t1 t2 t3 : UInt64) (Q : Assertion Unit)
    (hNext : wp module [.iff 0 0 tokenAccept tokenReject, .localGet 26] Q initial
      { checkedFrame pointer bound t0 t1 t2 t3 with values :=
          [.i32 (if t0 < 256 ∧ t1 < 256 ∧ t2 < 256 ∧ t3 < 256 then 1 else 0)] } env) :
    wp module func85 Q initial (checkedFrame pointer bound t0 t1 t2 t3) env := by
  rw [checked_shape]
  simp only [tokenGuard, List.cons_append, List.nil_append]
  by_cases h0 : t0 < 256 <;> by_cases h1 : t1 < 256 <;>
    by_cases h2 : t2 < 256 <;> by_cases h3 : t3 < 256
  all_goals
    simp only [h0, h1, h2, h3, and_self, false_and, and_false, ite_true, ite_false] at hNext
    repeat first
      | exact hNext
      | wp_fixed_frame [checkedFrame, checkedParams, func85Def, h0, h1, h2, h3]
      | (try simp only [wp_iff_control_types]
         refine wp_iff_cons rfl ?_
         simp)

#print axioms token_guard_spec
end Project.TinyGpt2Checked.Spec
