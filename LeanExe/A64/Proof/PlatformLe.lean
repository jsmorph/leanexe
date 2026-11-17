import LeanExe.A64.Linux
import LeanExe.A64.Proof.Lift

/-!
A platform that maps more.  `Platform.Le P P'` states that `P'` maps as Normal memory every byte
that `P` maps, with the same UART and receiver.  A step of the program's model on `P` is then a
step on `P'`: a load or store that `P` allows, `P'` allows, and every other form reads no
platform but the UART, which the two share (`exec_le`).  `Reach.le` and `IReach.le` carry runs of
the program's model and of `istep` from `P` to `P'`.  With `Reach.frame`, by which a run on `P`
keeps every byte that `P` does not map, a machine can run its code on a platform that leaves out
some memory and its process on one that maps it, and a relation on the memory left out survives
every run of the code.
-/

namespace LeanExe.A64

/-- `P'` maps as Normal memory every byte that `P` maps, with the same UART and receiver. -/
structure Platform.Le (P P' : Platform) : Prop where
  normal : ∀ a, P.normal a = true → P'.normal a = true
  uart : P'.uart = P.uart
  rx : P'.rx = P.rx

theorem Platform.Le.refl (P : Platform) : P.Le P := ⟨fun _ h => h, rfl, rfl⟩

theorem Platform.Le.trans {P P' P'' : Platform} (h : P.Le P') (h' : P'.Le P'') : P.Le P'' :=
  ⟨fun a ha => h'.normal a (h.normal a ha), by rw [h'.uart, h.uart], by rw [h'.rx, h.rx]⟩

theorem Platform.Le.mapped {P P' : Platform} (h : P.Le P') {a : UInt64} {k : Nat}
    (hm : P.mapped a k = true) : P'.mapped a k = true := by
  unfold Platform.mapped at *
  rw [List.all_eq_true] at *
  exact fun i hi => h.normal _ (hm i hi)

theorem Platform.Le.devLoad {P P' : Platform} (h : P.Le P') (io : Io) (a : UInt64) :
    P'.devLoad io a = P.devLoad io a := by
  simp only [Platform.devLoad, h.uart, h.rx]

/-- An instruction that executes on `P` executes the same way on a platform that maps more. -/
theorem exec_le {P P' : Platform} (h : P.Le P') {i : Instr} {s t : State}
    (he : exec P i s = some t) : exec P' i s = some t := by
  cases i
  case ldr r n imm =>
    simp only [exec] at he ⊢
    split at he
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      rw [if_pos (by simp only [Bool.and_eq_true]; exact ⟨hc.1, h.mapped hc.2⟩)]
      exact he
    · cases he
  case str r n imm =>
    simp only [exec] at he ⊢
    split at he
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      rw [if_pos (by simp only [Bool.and_eq_true]; exact ⟨hc.1, h.mapped hc.2⟩)]
      exact he
    · cases he
  case strb r n imm =>
    simp only [exec, h.uart] at he ⊢
    split at he
    · cases he
    rename_i hal
    rw [if_neg hal]
    split at he
    · rename_i hu
      rw [if_pos hu]
      exact he
    rename_i hu
    rw [if_neg hu]
    split at he
    · rename_i hn
      rw [if_pos (h.normal _ hn)]
      exact he
    · cases he
  case ldrW r n imm =>
    simp only [exec, h.devLoad] at he ⊢
    exact he
  case ldrb r n imm =>
    simp only [exec] at he ⊢
    split at he
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      rw [if_pos (by simp only [Bool.and_eq_true]; exact ⟨hc.1, h.normal _ hc.2⟩)]
      exact he
    · cases he
  all_goals exact he

theorem step_le {P P' : Platform} (h : P.Le P') {code : UInt64 → Option UInt32}
    {s t : State} (hs : step P code s = some t) : step P' code s = some t := by
  obtain ⟨w, i, hc, hd, he⟩ := step_some hs
  simp only [step, hc, hd, Option.bind_eq_bind, Option.bind_some]
  exact exec_le h he

/-- A run of the program's model on `P` is a run on a platform that maps more. -/
theorem Reach.le {P P' : Platform} (h : P.Le P') {code : UInt64 → Option UInt32}
    {s t : State} (hr : Reach P code s t) : Reach P' code s t := by
  induction hr with
  | refl => exact .refl _
  | next hs _ ih => exact .next (step_le h hs) ih

theorem istep_le {P P' : Platform} (h : P.Le P') {code : UInt64 → Option UInt32}
    {p q : Proc} (hs : istep P code p = some q) : istep P' code p = some q := by
  unfold istep at hs ⊢
  cases hc : code p.core.pc with
  | none => simp only [hc] at hs; cases hs
  | some w =>
    simp only [hc] at hs ⊢
    by_cases hsv : w = svcWord
    · simp only [hsv, ↓reduceIte] at hs
      cases hs
    simp only [hsv, ↓reduceIte] at hs ⊢
    cases hd : decode w with
    | none => simp only [hd] at hs; cases hs
    | some i =>
      simp only [hd] at hs ⊢
      cases hf : i.fpcrSource with
      | some t => simp only [hf] at hs ⊢; exact hs
      | none =>
        simp only [hf] at hs ⊢
        by_cases hfp : i.isFP = true ∧ p.fpcr ≠ fpcrValue
        · rw [if_pos hfp] at hs
          cases hs
        rw [if_neg hfp] at hs ⊢
        cases he : exec P i p.core with
        | none => simp only [he] at hs; cases hs
        | some c =>
          simp only [he] at hs
          rw [exec_le h he]
          exact hs

/-- A run of `istep` on `P` is a run on a platform that maps more. -/
theorem IReach.le {P P' : Platform} (h : P.Le P') {code : UInt64 → Option UInt32}
    {p q : Proc} (hr : IReach P code p q) : IReach P' code p q := by
  induction hr with
  | refl => exact .refl _
  | next hs _ ih => exact .next (istep_le h hs) ih

end LeanExe.A64
