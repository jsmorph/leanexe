import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Loop
import LeanExe.ProofKit.AlignedLoop

/-!
The flag `strict`.  `wpX false` is Talos's `wp` and `wpX true` is `wpA`, both by definition, so a
proof written once against the `wpX` rules proves today's statement at `strict = false` and the
aligned statement at `strict = true`.  Each rule below is the two rules it joins: Talos's rule
for `false` and the `wpA` rule for `true`.  In the rules for `load64` and `store64` the alignment
of an access inside memory is a conjunct under `strict = true`, which is vacuous at `false`.
-/

namespace LeanExe.ProofKit

open Wasm

variable {α : Type}

/-- `wp` when `strict` is false and `wpA` when it is true. -/
def wpX (strict : Bool) (m : Module) (c : Program) (Q : Assertion α) (st : Store α) (s : Locals)
    (env : HostEnv α := {}) : Prop :=
  match strict with
  | false => wp m c Q st s env
  | true => wpA m c Q st s env

section

variable {strict : Bool} {m : Module} {Q Q' : Assertion α} {st : Store α} {s : Locals}
  {env : HostEnv α} {c rest : Program}

@[simp] theorem wpX_false : wpX false m c Q st s env = wp m c Q st s env := rfl
@[simp] theorem wpX_true : wpX true m c Q st s env = wpA m c Q st s env := rfl

theorem wpX.wp (h : wpX strict m c Q st s env) : wp m c Q st s env := by
  cases strict
  · exact h
  · exact wpA.wp h

theorem wpX.conseq (hq : Q ⇛ Q') (h : wpX strict m c Q st s env) : wpX strict m c Q' st s env := by
  cases strict
  · exact Wasm.wp.conseq hq h
  · exact wpA.conseq hq h

@[simp] theorem wpX_nil : wpX strict m [] Q st s env ↔ Q (.Fallthrough st s) := by
  cases strict
  · exact wp_nil
  · exact wpA_nil

@[simp] theorem wpX_localGet_cons {i : Nat} :
    wpX strict m (.localGet i :: rest) Q st s env ↔
    (match s.get i with
     | some v => wpX strict m rest Q st { s with values := v :: s.values } env
     | none => Q (.Invalid "localGet index out of bounds")) := by
  cases strict
  · exact wp_localGet_cons
  · exact wpA_localGet_cons

@[simp] theorem wpX_constI64_cons {v : UInt64} :
    wpX strict m (.constI64 v :: rest) Q st s env ↔
    wpX strict m rest Q st { s with values := .i64 v :: s.values } env := by
  cases strict
  · exact wp_constI64_cons
  · exact wpA_constI64_cons

@[simp] theorem wpX_addI64_cons :
    wpX strict m (.addI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 b :: .i64 a :: vs => wpX strict m rest Q st { s with values := .i64 (a + b) :: vs } env
     | _ => Q (.Invalid "addI64: ill-shaped operand stack")) := by
  cases strict
  · exact wp_addI64_cons
  · exact wpA_addI64_cons

@[simp] theorem wpX_mulI64_cons :
    wpX strict m (.mulI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 b :: .i64 a :: vs => wpX strict m rest Q st { s with values := .i64 (a * b) :: vs } env
     | _ => Q (.Invalid "mulI64: ill-shaped operand stack")) := by
  cases strict
  · exact wp_mulI64_cons
  · exact wpA_mulI64_cons

@[simp] theorem wpX_wrapI64_cons :
    wpX strict m (.wrapI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 a :: vs =>
       wpX strict m rest Q st { s with values := .i32 (UInt32.ofNat (a.toNat % 2 ^ 32)) :: vs } env
     | _ => Q (.Invalid "wrapI64: ill-shaped operand stack")) := by
  cases strict
  · exact wp_wrapI64_cons
  · exact wpA_wrapI64_cons

theorem wpA_geUI64_cons :
    wpA m (.geUI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 b :: .i64 a :: vs =>
       wpA m rest Q st { s with values := .i32 (if a ≥ b then 1 else 0) :: vs } env
     | _ => Q (.Invalid "geUI64: ill-shaped operand stack")) := by
  have hal : ∀ f, AlignedOne (f + 1) m st s .geUI64 env := fun f => by simp [AlignedOne]
  split
  · rename_i b a vs hv
    exact wpA_cons_fall (fun f => by simp [execOne.eq_def, hv]) hal
  · rename_i hv
    refine wpA_cons_stop (fun f => ?_) (by simp) hal
    simp only [execOne.eq_def]

@[simp] theorem wpX_geUI64_cons :
    wpX strict m (.geUI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 b :: .i64 a :: vs =>
       wpX strict m rest Q st { s with values := .i32 (if a ≥ b then 1 else 0) :: vs } env
     | _ => Q (.Invalid "geUI64: ill-shaped operand stack")) := by
  cases strict
  · exact wp_geUI64_cons
  · exact wpA_geUI64_cons

theorem wpA_br_cons {n : Nat} : wpA m (.br n :: rest) Q st s env ↔ Q (.Break n st s) :=
  wpA_cons_stop (fun f => by simp [execOne.eq_def]) (by simp) (fun f => by simp [AlignedOne])

@[simp] theorem wpX_br_cons {n : Nat} : wpX strict m (.br n :: rest) Q st s env ↔ Q (.Break n st s) := by
  cases strict
  · exact wp_br_cons
  · exact wpA_br_cons

theorem wpA_br_if_cons {n : Nat} :
    wpA m (.br_if n :: rest) Q st s env ↔
    (match s.values with
     | .i32 0 :: vs => wpA m rest Q st { s with values := vs } env
     | .i32 _ :: vs => Q (.Break n st { s with values := vs })
     | _ => Q (.Invalid "br_if: ill-shaped operand stack")) := by
  have hal : ∀ f, AlignedOne (f + 1) m st s (.br_if n) env := fun f => by simp [AlignedOne]
  split
  · rename_i vs hv
    exact wpA_cons_fall (fun f => by simp [execOne.eq_def, hv]) hal
  · rename_i c vs hc hv
    exact wpA_cons_stop (fun f => by simp [execOne.eq_def, hv]) (by simp) hal
  · rename_i h1 h2
    refine wpA_cons_stop (fun f => ?_) (by simp) hal
    simp only [execOne.eq_def]

@[simp] theorem wpX_br_if_cons {n : Nat} :
    wpX strict m (.br_if n :: rest) Q st s env ↔
    (match s.values with
     | .i32 0 :: vs => wpX strict m rest Q st { s with values := vs } env
     | .i32 _ :: vs => Q (.Break n st { s with values := vs })
     | _ => Q (.Invalid "br_if: ill-shaped operand stack")) := by
  cases strict
  · exact wp_br_if_cons
  · exact wpA_br_if_cons

/-- `load64` in match form, with the alignment of an access inside memory as a conjunct. -/
theorem wpA_load64_cons {off : UInt32} :
    wpA m (.load64 off :: rest) Q st s env ↔
    (match s.values with
     | .i32 a :: vs =>
       if a.toNat + off.toNat + 8 > st.mem.pages * 65536 then
         Q (.Trap st "out of bounds memory access")
       else (a.toNat + off.toNat) % 8 = 0 ∧
         wpA m rest Q st { s with values := .i64 (st.mem.read64 (a + off)) :: vs } env
     | .i64 a :: vs =>
       if a.toNat + off.toNat + 8 > st.mem.pages * 65536 then
         Q (.Trap st "out of bounds memory access")
       else (a.toUInt32.toNat + off.toNat) % 8 = 0 ∧
         wpA m rest Q st { s with values := .i64 (st.mem.read64 (a.toUInt32 + off)) :: vs } env
     | _ => Q (.Invalid "load64: ill-shaped operand stack")) := by
  split
  · rename_i a vs hv
    exact wpA_load64_i32 hv
  · rename_i a vs hv
    split
    · rename_i hout
      refine wpA_cons_stop (fun f => by simp [execOne.eq_def, hv, hout]) (by simp)
        (fun f => ?_)
      simp only [AlignedOne, hv]
      omega
    · rename_i hin
      refine wpA_cons_fall_iff (fun f => by simp [execOne.eq_def, hv, hin]) (fun f => ?_)
      simp only [AlignedOne, hv]
      exact ⟨fun h => h (by omega), fun h _ => h⟩
  · rename_i hv
    refine wpA_cons_stop (fun f => ?_) (by simp) (fun f => ?_)
    · simp only [execOne.eq_def]
    · simp only [AlignedOne]

theorem wpX_load64_cons {off : UInt32} :
    wpX strict m (.load64 off :: rest) Q st s env ↔
    (match s.values with
     | .i32 a :: vs =>
       if a.toNat + off.toNat + 8 > st.mem.pages * 65536 then
         Q (.Trap st "out of bounds memory access")
       else (strict = true → (a.toNat + off.toNat) % 8 = 0) ∧
         wpX strict m rest Q st { s with values := .i64 (st.mem.read64 (a + off)) :: vs } env
     | .i64 a :: vs =>
       if a.toNat + off.toNat + 8 > st.mem.pages * 65536 then
         Q (.Trap st "out of bounds memory access")
       else (strict = true → (a.toUInt32.toNat + off.toNat) % 8 = 0) ∧
         wpX strict m rest Q st { s with values := .i64 (st.mem.read64 (a.toUInt32 + off)) :: vs }
           env
     | _ => Q (.Invalid "load64: ill-shaped operand stack")) := by
  split
  · rename_i a vs hv
    cases strict
    · simp only [wpX_false, wp_load64_cons, hv, Bool.false_eq_true, false_implies, true_and]
    · simp only [wpX_true, wpA_load64_cons, hv, forall_const]
  · rename_i a vs hv
    cases strict
    · simp only [wpX_false, wp_load64_cons, hv, Bool.false_eq_true, false_implies, true_and]
    · simp only [wpX_true, wpA_load64_cons, hv, forall_const]
  · cases strict
    · rw [wpX_false, wp_load64_cons]
      split <;> simp_all
    · rw [wpX_true, wpA_load64_cons]
      split <;> simp_all

theorem wpX_store64_cons {off : UInt32} :
    wpX strict m (.store64 off :: rest) Q st s env ↔
    (match s.values with
     | .i64 v :: .i32 a :: vs =>
       if a.toNat + off.toNat + 8 > st.mem.pages * 65536 then
         Q (.Trap st "out of bounds memory access")
       else (strict = true → (a.toNat + off.toNat) % 8 = 0) ∧
         wpX strict m rest Q { st with mem := st.mem.write64 (a + off) v } { s with values := vs }
           env
     | .i64 v :: .i64 a :: vs =>
       if a.toNat + off.toNat + 8 > st.mem.pages * 65536 then
         Q (.Trap st "out of bounds memory access")
       else (strict = true → (a.toUInt32.toNat + off.toNat) % 8 = 0) ∧
         wpX strict m rest Q { st with mem := st.mem.write64 (a.toUInt32 + off) v }
           { s with values := vs } env
     | _ => Q (.Invalid "store64: ill-shaped operand stack")) := by
  split
  · rename_i v a vs hv
    cases strict
    · simp only [wpX_false, wp_store64_cons, hv, Bool.false_eq_true, false_implies, true_and]
    · simp only [wpX_true, wpA_store64_cons, hv, forall_const]
  · rename_i v a vs hv
    cases strict
    · simp only [wpX_false, wp_store64_cons, hv, Bool.false_eq_true, false_implies, true_and]
    · simp only [wpX_true, wpA_store64_cons, hv, forall_const]
  · cases strict
    · rw [wpX_false, wp_store64_cons]
      split <;> simp_all
    · rw [wpX_true, wpA_store64_cons]
      split <;> simp_all

theorem wpX_block_cons {ps rs : Nat} {body : Program}
    (h : wpX strict m body
          (fun c => match c with
            | .Fallthrough st' s' =>
              wpX strict m rest Q st' { s' with values := s'.values.take rs ++ s.values.drop ps } env
            | .Break 0 st' s' =>
              wpX strict m rest Q st' { s' with values := s'.values.take rs ++ s.values.drop ps } env
            | .Break (k + 1) st' s' => Q (.Break k st' s')
            | other => Q other)
          st s env) :
    wpX strict m (.block ps rs body :: rest) Q st s env := by
  cases strict
  · exact wp_block_cons h
  · exact wpA_block_cons h

theorem wpX_loop_cons {ps rs : Nat} {body : Program}
    (Inv : AssertionF α) (μ : Store α → Locals → Nat) (hInit : Inv st s)
    (hStep : ∀ st s, Inv st s →
        wpX strict m body
          (fun c => match c with
            | .Fallthrough st' s' =>
              wpX strict m rest Q st' { s' with values := s'.values.take rs ++ s.values.drop ps } env
            | .Break 0 st' s' =>
              Inv st' { s' with values := s'.values.take ps ++ s.values.drop ps } ∧
                μ st' { s' with values := s'.values.take ps ++ s.values.drop ps } < μ st s
            | .Break (k + 1) st' s' => Q (.Break k st' s')
            | other => Q other)
          st s env) :
    wpX strict m (.loop ps rs body :: rest) Q st s env := by
  cases strict
  · exact wp_loop_cons Inv μ hInit hStep
  · exact wpA_loop_cons Inv μ hInit hStep

end

end LeanExe.ProofKit
