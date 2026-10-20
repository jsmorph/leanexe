import Verified.ArgPot
import Verified.TailBound
import Verified.EnvStep

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime

theorem paramModes_any_owned {params : List Ty} {modes : List Mode} {i : Nat}
    (h : paramMode params modes i = .owned) :
    (paramModes params modes).any (· == .owned) = true := by
  simp only [paramMode, List.getD_eq_getElem?_getD] at h
  cases hi : (paramModes params modes)[i]? with
  | none => rw [hi] at h; exact nomatch h
  | some mode =>
    rw [hi] at h
    exact List.any_eq_true.mpr
      ⟨mode, List.mem_of_getElem? hi, by simp [Option.getD] at h; simp [h]⟩

theorem TailBody.next_placeArgs {S : List Sig} {Γ params : List Ty} {result : Ty}
    (args : (i : Fin params.length) → Expr S Γ (params.get i))
    (targetModes sourceModes : List Mode)
    (place : (TailBody.next (result := result) args).placeArgs targetModes sourceModes = true) :
    (∀ i, (args i).placeArgs = true) ∧
      (∀ i : Fin params.length, paramMode params targetModes i = .owned →
        ∃ x, args i = .var x) ∧
      (∀ i, (params.get i).scalar = false → paramMode params targetModes i = .borrowed →
        (args i).isPlace = true ∧ (args i).mode sourceModes = .borrowed) := by
  simp only [TailBody.placeArgs, Bool.and_eq_true, Bool.not_eq_true'] at place
  refine ⟨fun i => ?_, (fun i hm => ?_), fun i hs hm => ?_⟩
  · have hi := argsAny_eq_false place.1 i
    simpa using hi
  · have hi := argsAny_eq_false place.2 i
    have hs := paramMode_owned hm
    rw [hs] at hi
    apply Expr.exists_var (args i)
    simpa [hm] using hi
  · have hi := argsAny_eq_false place.2 i
    rw [hs] at hi
    simpa [hm, Bool.or_eq_false_iff] using hi

theorem TailBody.next_borrowed_vars {S : List Sig} {Γ params : List Ty} {result : Ty}
    (args : (i : Fin params.length) → Expr S Γ (params.get i))
    (targetModes sourceModes : List Mode)
    (place : (TailBody.next (result := result) args).placeArgs targetModes sourceModes = true)
    (k : Nat) (used : (argsAny fun i => paramMode params targetModes i == .borrowed &&
      !(params.get i).scalar && (args i).uses k) = true) : modeAt sourceModes k = .borrowed := by
  obtain ⟨i, hi⟩ := argsAny_true.mp used
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hi
  obtain ⟨placeArg, borrowed⟩ := (TailBody.next_placeArgs args targetModes sourceModes place).2.2
    i hi.1.2 hi.1.1
  exact (args i).place_modes placeArg borrowed k hi.2

theorem args_reads_apart_owned {S : List Sig} {Γ ps : List Ty} {funs : Funs S}
    (modes : Nat → Mode) (args : (i : Fin ps.length) → Expr S Γ (ps.get i))
    {env : Env Γ} {slots : List Slot} {all : Nat → Bool} {base : Nat}
    {heap heap1 : Heap} {store store1 : Store Unit} {s s1 : Locals}
    {words : List Value} {fresh : List (Nat × Nat)}
    (uses : ∀ i k, (args i).uses k = true → all k = true)
    (borrowed : ∀ k, (argsAny fun i => modes i == .borrowed &&
      !(ps.get i).scalar && (args i).uses k) = true → modeAt (slots.map Slot.mode) k = .borrowed)
    (vars : Holds env slots all base heap store s)
    (step : Step heap store (fun _ => True) heap1 store1 fresh) (frame : Frame base s s1)
    (reads : ∀ r, Holds.ApartFrom env slots
      (fun k => argsAny fun i => modes i == .borrowed && !(ps.get i).scalar && (args i).uses k)
      store s r → ∀ c ∈ Env.reads store1 modes words (Env.ofFn fun i => (args i).denote funs env),
        regionsDisjoint r c) :
    ∀ (t : Ty) (x : Var Γ t), all x.index = true →
      (slots.getD x.index default).mode = .owned →
      ∀ wx, LocalsHold s1 (slots.getD x.index default).loc t.types wx → wx.length = t.width →
      ∀ r ∈ t.blocks store1 wx (env.get x),
        ∀ c ∈ Env.reads store1 modes words (Env.ofFn fun i => (args i).denote funs env),
          regionsDisjoint r c := by
  intro t x hx hm wx hold length r hr c hc
  have hold' := (vars.hold_agree frame hx length).mp hold
  have same := (vars.regions_after step hx hold' length fun _ _ => trivial).1
  simp only [hm, Ty.regions] at same
  rw [same] at hr
  refine reads r (Holds.ApartFrom.owned vars hx hm hold' length ?_ r hr) c hc
  intro k hk
  obtain ⟨i, hi⟩ := argsAny_true.mp hk
  simp only [Bool.and_eq_true] at hi
  refine ⟨uses i k hi.2, fun he => ?_⟩
  have hb := borrowed k hk
  simp only [modeAt, Slot.modes_getD, he, hm] at hb
  exact nomatch hb

#print axioms TailBody.next_placeArgs
#print axioms TailBody.next_borrowed_vars
#print axioms args_reads_apart_owned

end Verified
