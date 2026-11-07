import Interpreter.Wasm.Syntax

/-!
The types of Talos values, which the simulation proofs of the AArch64 and Cortex-M7 back ends
share: `HasType t v` states that the value `v` has the type `t`, and `Typed ts vs` that the values
`vs` have the types `ts`, one for one.
-/

namespace LeanExe.ProofKit

open Wasm

/-- The value `v` has the type `t`. -/
def HasType : ValueType → Value → Prop
  | .i32, .i32 _ => True
  | .i64, .i64 _ => True
  | .f32, .f32 _ => True
  | .f64, .f64 _ => True
  | _, _ => False

/-- The values `vs` have the types `ts`, one for one. -/
def Typed : List ValueType → List Value → Prop
  | [], [] => True
  | t :: ts, v :: vs => HasType t v ∧ Typed ts vs
  | _, _ => False

theorem Typed.length : ∀ {ts : List ValueType} {vs : List Value}, Typed ts vs →
    ts.length = vs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by rw [List.length_cons, List.length_cons, Typed.length h.2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem Typed.cons {t : ValueType} {v : Value} {ts : List ValueType} {vs : List Value}
    (ht : HasType t v) (h : Typed ts vs) : Typed (t :: ts) (v :: vs) := ⟨ht, h⟩

theorem Typed.tail : ∀ {ts : List ValueType} {vs : List Value}, Typed ts vs →
    Typed ts.tail vs.tail
  | [], [], _ => trivial
  | _ :: _, _ :: _, h => h.2
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem Typed.drop : ∀ (n : Nat) {ts : List ValueType} {vs : List Value}, Typed ts vs →
    Typed (ts.drop n) (vs.drop n)
  | 0, _, _, h => h
  | _ + 1, [], [], _ => trivial
  | n + 1, _ :: _, _ :: _, h => Typed.drop n h.2
  | _ + 1, [], _ :: _, h => h.elim
  | _ + 1, _ :: _, [], h => h.elim

theorem Typed.take : ∀ (n : Nat) {ts : List ValueType} {vs : List Value}, Typed ts vs →
    Typed (ts.take n) (vs.take n)
  | 0, _, _, _ => trivial
  | _ + 1, [], [], _ => trivial
  | n + 1, _ :: _, _ :: _, h => ⟨h.1, Typed.take n h.2⟩
  | _ + 1, [], _ :: _, h => h.elim
  | _ + 1, _ :: _, [], h => h.elim

theorem Typed.append : ∀ {ts ts' : List ValueType} {vs vs' : List Value}, Typed ts vs →
    Typed ts' vs' → Typed (ts ++ ts') (vs ++ vs')
  | [], _, [], _, _, h' => h'
  | _ :: _, _, _ :: _, _, h, h' => ⟨h.1, Typed.append h.2 h'⟩
  | [], _, _ :: _, _, h, _ => h.elim
  | _ :: _, _, [], _, h, _ => h.elim

theorem Typed.getElem : ∀ {ts : List ValueType} {vs : List Value} (h : Typed ts vs) {i : Nat}
    (hi : i < ts.length), HasType ts[i] (vs[i]'(by rw [← h.length]; exact hi))
  | _ :: _, _ :: _, h, 0, _ => h.1
  | _ :: _, _ :: _, h, i + 1, hi => Typed.getElem h.2 (by simp at hi; omega)
  | [], _, _, _, hi => absurd hi (by simp)
  | _ :: _, [], h, _, _ => h.elim

theorem Typed.set : ∀ {ts : List ValueType} {vs : List Value}, Typed ts vs → ∀ {i : Nat}
    (hi : i < ts.length) {v : Value}, HasType ts[i] v → Typed ts (vs.set i v)
  | _ :: _, _ :: _, h, 0, _, _, hv => ⟨hv, h.2⟩
  | _ :: _, _ :: _, h, i + 1, hi, _, hv =>
      ⟨h.1, Typed.set h.2 (by simp at hi; omega) (by simpa using hv)⟩
  | [], _, _, _, hi, _, _ => absurd hi (by simp)
  | _ :: _, [], h, _, _, _, _ => h.elim

theorem Typed.reverse : ∀ {ts : List ValueType} {vs : List Value}, Typed ts vs →
    Typed ts.reverse vs.reverse
  | [], [], _ => trivial
  | _ :: _, _ :: _, h => by
      simp only [List.reverse_cons]
      exact Typed.append (Typed.reverse h.2) ⟨h.1, trivial⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

end LeanExe.ProofKit
