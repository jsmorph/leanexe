import Verified.TailCompile
import Verified.After

namespace Verified

open Wasm LeanExe.Pipeline

theorem storeCode_append (h base : Nat) (first second : List ValueType) :
    storeCode h base (first ++ second) =
      storeCode h (base + first.length) second ++ storeCode h base first := by
  induction first generalizing base with
  | nil => simp [storeCode]
  | cons ty first ih =>
    simp [storeCode, ih, List.append_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem storeParamsCode_eq (h base : Nat) (params : List Ty) :
    storeParamsCode h base params = storeCode h base (params.flatMap Ty.types) := by
  induction params generalizing base with
  | nil => rfl
  | cons t params ih =>
    simp [storeParamsCode, List.flatMap_cons, storeCode_append, ih, Ty.types_length]

theorem LocalsHold.var {Γ : List Ty} {s : Locals} {base : Nat} {ws : List Value}
    (hold : LocalsHold s base (Γ.flatMap Ty.types) ws)
    {t : Ty} (x : Var Γ t) :
    LocalsHold s (base + x.offset) t.types ((ws.drop x.offset).take t.width) := by
  intro k hk
  have hk' := hk
  simp only [List.length_take, List.length_drop] at hk'
  have hlt : x.offset + k < ws.length := by omega
  have hkw : k < t.width := by omega
  have h := hold (x.offset + k) hlt
  rw [x.types_getD hkw] at h
  simpa [List.getElem_take, List.getElem_drop, Nat.add_assoc] using h

theorem Holds.ofEnvRep {Γ : List Ty} {modes : List Mode} {heap : Heap} {store : Store Unit}
    {ws : List Value} {env : Env Γ} {s : Locals} {base : Nat}
    (hRep : Env.Rep (paramMode Γ modes) heap store ws env)
    (hSep : Separate store (Env.moves store (paramMode Γ modes) ws env)
      (Env.reads store (paramMode Γ modes) ws env))
    (hold : LocalsHold s base (Γ.flatMap Ty.types) ws) :
    Holds env (paramSlots Γ modes base) (fun _ => true) (base + widthSum Γ) heap store s := by
  have hWords : ∀ {t : Ty} (x : Var Γ t),
      ((ws.drop x.offset).take t.width).length = t.width :=
    fun x => (hRep.var x).length
  refine ⟨fun t x _ => ?_, fun t u x y _ _ hxy hmo wx wy hwx hlx hwy hly => ?_⟩
  · rw [paramSlots_getD x]
    exact ⟨by
      change base + x.offset + t.width ≤ base + widthSum Γ
      have := x.offset_width
      omega, _, hold.var x, hRep.var x⟩
  · rw [paramSlots_getD x] at hwx hmo
    rw [paramSlots_getD y] at hwy ⊢
    obtain rfl := LocalsHold.unique hwx (hold.var x) (by rw [hlx, hWords])
    obtain rfl := LocalsHold.unique hwy (hold.var y) (by rw [hly, hWords])
    exact hRep.apart x hSep y hxy hmo

#print axioms Holds.ofEnvRep

end Verified
