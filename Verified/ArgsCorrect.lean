import Verified.ExprSpec
import Verified.VarCorrect

namespace Verified

variable {pool : Bytes.LiteralPool}

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

section

variable {S : List Sig} {m : Module} {funs : Funs S} {flags : Flags S} {bounds : Bounds S}
  {fits : Fits S} {host : HostEnv Unit} {pv : List Value}

/-- The allowance of an allocation of a part, from that of the whole, which may allocate. -/
theorem _root_.Wasm.TrapOK.alloc {Q : Assertion Unit} {d a : Bool} {P P' : Prop} [Decidable P]
    [Decidable P'] (h : TrapOK (d || (a && !decide P)) Q) (ha : a = true)
    (hP : d = false → P → P') : TrapOK (!decide P') Q :=
  h.part (d' := false) (a' := true) nofun (fun _ => ha) hP

/-- A potential counted under `P` is at most one counted under `Q` when `P` implies `Q` and the two
agree under `P`. -/
theorem pot_keep {P Q : Bool} {a b : Nat} (hPQ : P = true → Q = true) (hab : P = true → a = b) :
    (if P = true then a else 0) ≤ (if Q = true then b else 0) := by
  cases P <;> cases Q <;> simp_all

/-- An allowance for a trap when `top` cannot rise by a charge gives the allowance of a part
that takes no call depth and whose room follows from the charge's. -/
theorem _root_.Wasm.TrapOK.narrow {Q : Assertion Unit} {a : Bool} {P P' : Prop} [Decidable P]
    [Decidable P'] (h : TrapOK (!decide P) Q) (hP : P → P') :
    TrapOK (false || (a && !decide P')) Q :=
  h.of_imp fun h' => by
    simp only [Bool.false_or, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h' ⊢
    exact fun hp => h'.2 (hP hp)

end

/-- The mode of a parameter's slot is the parameter's mode. -/
theorem paramSlots_getD_mode (ps : List Ty) (ms : List Mode) (p0 i : Nat) :
    ((paramSlots ps ms p0).getD i default).mode = paramMode ps ms i := by
  rw [← Slot.modes_getD, paramSlots_modes]
  rfl

/-- The potential of a function's parameters, read from their slots, is that of its arguments'
words when each slot holds its parameter's words. -/
theorem Env.pot_paramSlots {store : Store Unit} {s : Locals} :
    {ps : List Ty} → (ms : List Mode) → (p0 : Nat) → (sel : Nat → Bool) → (ws : List Value) →
    (args : Env ps) → ws.length = widthSum ps →
    (∀ {t : Ty} (x : Var ps t),
      LocalsHold s (p0 + x.offset) t.types ((ws.drop x.offset).take t.width)) →
    args.pot store s (paramSlots ps ms p0) sel = Env.argPot store sel ws args
  | [], _, _, _, _, .nil, _, _ => rfl
  | t :: ts, ms, p0, sel, ws, .cons v rest, hl, hHold => by
    have hw := hHold (Var.here : Var (t :: ts) t)
    simp only [Var.offset, List.drop_zero, Nat.add_zero] at hw
    have hlt : (ws.take t.width).length = t.types.length := by
      simp only [List.length_take, Ty.types_length, widthSum, List.map_cons, List.sum_cons] at hl ⊢
      omega
    have hrest := Env.pot_paramSlots (store := store) (s := s) ms.tail (p0 + t.width)
      (fun i => sel (i + 1)) (ws.drop t.width) rest (by
        simp only [List.length_drop, widthSum, List.map_cons, List.sum_cons] at hl ⊢
        omega) fun x => by
      have := hHold (Var.there x)
      simp only [Var.offset] at this
      rw [show p0 + t.width + x.offset = p0 + (t.width + x.offset) by omega, List.drop_drop]
      exact this
    simp only [paramSlots, Env.pot, Env.argPot, List.getD_cons_zero, List.tail_cons]
    rw [hw.read_eq hlt, hrest]

end Verified
