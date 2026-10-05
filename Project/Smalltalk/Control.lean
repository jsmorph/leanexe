import LeanExe.Smalltalk.Control
namespace Project.Smalltalk.Control
open LeanExe.Smalltalk.Control

theorem own_sound {ms c s m} (h : own ms c s = some m) : First ms c s m := by
  induction ms with
  | nil => simp [own] at h
  | cons a rest ih =>
    by_cases hit : a.owner = c ∧ a.selector = s
    · simp [own, hit] at h
      subst m
      exact .here hit
    · simp [own, hit] at h
      exact .there hit (ih h)
theorem own_complete {ms c s m} (h : First ms c s m) : own ms c s = some m := by
  induction h with
  | here h => simp [own, h]
  | there h _ ih => simp [own, h, ih]
theorem own_correct {ms c s m} : own ms c s = some m ↔ First ms c s m := ⟨own_sound, own_complete⟩
theorem first_deterministic {ms c s a b} (ha : First ms c s a) (hb : First ms c s b) : a = b := by
  have h := (own_complete ha).symm.trans (own_complete hb)
  exact Option.some.inj h

theorem resolve_sound {classes methods fuel c s m}
    (h : resolve classes methods fuel c s = some m) : Resolves classes methods fuel c s m := by
  induction fuel generalizing c with
  | zero => simp [resolve] at h
  | succ fuel ih =>
    by_cases live : c = 0
    · simp [resolve, live] at h
    · cases found : own methods c s with
      | none =>
        simp [resolve, live, found] at h
        exact .up live found (ih h)
      | some result =>
        simp [resolve, live, found] at h
        subst m
        exact .here live (own_sound found)
theorem resolve_complete {classes methods fuel c s m}
    (h : Resolves classes methods fuel c s m) : resolve classes methods fuel c s = some m := by
  induction h with
  | here live first => simp [resolve, live, own_complete first]
  | up live absent _ ih => simp [resolve, live, absent, ih]
theorem resolve_correct {classes methods fuel c s m} :
    resolve classes methods fuel c s = some m ↔ Resolves classes methods fuel c s m :=
  ⟨resolve_sound, resolve_complete⟩

@[simp] theorem retire_slots (a : Activation) : (retire a).slots = a.slots := rfl
@[simp] theorem retire_home (a : Activation) : (retire a).lexicalHome = a.lexicalHome := rfl
@[simp] theorem retire_id (a : Activation) : (retire a).id = a.id := rfl
theorem finished_cannot_return (target : Nat) (a : Activation) (rest : List Activation) :
    unwind target (retire a :: rest) = none := rfl

theorem unwind_sound {target chain retired tail}
    (h : unwind target chain = some (retired, tail)) : Unwinds target chain retired tail := by
  induction chain generalizing retired tail with
  | nil => simp [unwind] at h
  | cons a rest ih =>
    by_cases live : a.live = true
    · by_cases same : a.id = target
      · simp [unwind, live, same] at h
        rcases h with ⟨rfl, rfl⟩
        exact .here live same
      · cases result : unwind target rest with
        | none => simp [unwind, live, same, result] at h
        | some pair =>
          rcases pair with ⟨rs, ts⟩
          simp [unwind, live, same, result] at h
          rcases h with ⟨rfl, rfl⟩
          exact .next live same (ih result)
    · simp [unwind, live] at h
theorem unwind_complete {target chain retired tail}
    (h : Unwinds target chain retired tail) : unwind target chain = some (retired, tail) := by
  induction h with
  | here live same => simp [unwind, live, same]
  | next live different _ ih => simp [unwind, live, different, ih]
theorem unwind_correct {target chain retired tail} :
    unwind target chain = some (retired, tail) ↔ Unwinds target chain retired tail :=
  ⟨unwind_sound, unwind_complete⟩
theorem unwind_deterministic {target chain ra ta rb tb}
    (ha : Unwinds target chain ra ta) (hb : Unwinds target chain rb tb) : (ra, ta) = (rb, tb) :=
  Option.some.inj ((unwind_complete ha).symm.trans (unwind_complete hb))

end Project.Smalltalk.Control
