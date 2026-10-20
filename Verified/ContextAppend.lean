import Verified.FieldsCompose

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime

def Var.prefix {ps qs : List Ty} {t : Ty} : Var ps t → Var (ps ++ qs) t
  | .here => .here
  | .there x => .there x.prefix

def Var.suffix (ps : List Ty) {qs : List Ty} {t : Ty} (x : Var qs t) : Var (ps ++ qs) t :=
  match ps with
  | [] => x
  | _ :: rest => .there (x.suffix rest)

@[simp] theorem Var.prefix_index {ps qs : List Ty} {t : Ty} (x : Var ps t) :
    (x.prefix (qs := qs)).index = x.index := by
  induction x <;> simp_all [Var.prefix, Var.index]

@[simp] theorem Var.suffix_index (ps : List Ty) {qs : List Ty} {t : Ty} (x : Var qs t) :
    (x.suffix ps).index = ps.length + x.index := by
  induction ps <;> simp_all [Var.suffix, Var.index, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem Var.append_cases {ps qs : List Ty} {t : Ty} (x : Var (ps ++ qs) t) :
    (∃ y : Var ps t, x = y.prefix) ∨ (∃ y : Var qs t, x = y.suffix ps) := by
  induction ps with
  | nil => exact .inr ⟨x, rfl⟩
  | cons p ps ih =>
    cases x with
    | here => exact .inl ⟨.here, rfl⟩
    | there x =>
      rcases ih x with ⟨y, rfl⟩ | ⟨y, rfl⟩
      · exact .inl ⟨.there y, rfl⟩
      · exact .inr ⟨y, rfl⟩

@[simp] theorem Env.get_append_prefix {ps qs : List Ty} {t : Ty}
    (values : Env ps) (tail : Env qs) (x : Var ps t) :
    (values.append tail).get x.prefix = values.get x := by
  induction x with
  | here => cases values; rfl
  | there x ih => cases values; exact ih _

@[simp] theorem Env.get_append_suffix {ps qs : List Ty} {t : Ty}
    (values : Env ps) (tail : Env qs) (x : Var qs t) :
    (values.append tail).get (x.suffix ps) = tail.get x := by
  induction values with
  | nil => rfl
  | cons value values ih => exact ih

theorem slots_append_prefix {ps : List Ty} {t : Ty} (x : Var ps t)
    (first rest : List Slot) (hLength : first.length = ps.length) :
    (first ++ rest).getD x.index default = first.getD x.index default := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by rw [hLength]; exact x.index_lt)]

theorem slots_append_suffix {ps qs : List Ty} {t : Ty} (x : Var qs t)
    (first rest : List Slot) (hLength : first.length = ps.length) :
    (first ++ rest).getD (x.suffix ps).index default = rest.getD x.index default := by
  rw [Var.suffix_index, ← hLength]
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]

theorem Holds.popPrefix {ps qs : List Ty} {values : Env ps} {tail : Env qs}
    {first rest : List Slot} {live : Nat → Bool} {base : Nat} {heap : Heap}
    {store : Store Unit} {s : Locals} (hLength : first.length = ps.length)
    (h : Holds (values.append tail) (first ++ rest) live base heap store s) :
    Holds tail rest (fun i => live (ps.length + i)) base heap store s := by
  refine ⟨fun t x hx => ?_, fun t u x y hx hy hne hm wx wy hwx hlx hwy hly => ?_⟩
  · have hx' : live (x.suffix ps).index = true := by simpa using hx
    simpa only [slots_append_suffix x first rest hLength, Env.get_append_suffix] using
      h.1 t (x.suffix ps) hx'
  · have hx' : live (x.suffix ps).index = true := by simpa using hx
    have hy' : live (y.suffix ps).index = true := by simpa using hy
    have hApart := h.2 t u (x.suffix ps) (y.suffix ps) hx' hy'
      (by simpa using hne)
    simp only [slots_append_suffix x first rest hLength,
      slots_append_suffix y first rest hLength, Env.get_append_suffix] at hApart
    exact hApart hm wx wy hwx hlx hwy hly

theorem Holds.append {ps qs : List Ty} {values : Env ps} {tail : Env qs}
    {first rest : List Slot} {live : Nat → Bool} {base : Nat} {heap : Heap}
    {store : Store Unit} {s : Locals} (hLength : first.length = ps.length)
    (hFirst : Holds values first live base heap store s)
    (hTail : Holds tail rest (fun i => live (ps.length + i)) base heap store s)
    (hApart : ∀ (t : Ty) (x : Var ps t), live x.index = true → ∀ ws,
      LocalsHold s (first.getD x.index default).loc t.types ws → ws.length = t.width →
      Holds.Apart tail rest (fun i => live (ps.length + i)) store s t
        (first.getD x.index default).mode ws (values.get x)) :
    Holds (values.append tail) (first ++ rest) live base heap store s := by
  refine ⟨fun t x hx => ?_, fun t u x y hx hy hne hm wx wy hwx hlx hwy hly => ?_⟩
  · rcases x.append_cases with ⟨x, rfl⟩ | ⟨x, rfl⟩
    · have hx' : live x.index = true := by simpa using hx
      simpa only [Var.prefix_index, slots_append_prefix x first rest hLength,
        Env.get_append_prefix] using hFirst.1 t x hx'
    · have hx' : live (ps.length + x.index) = true := by simpa using hx
      simpa only [slots_append_suffix x first rest hLength, Env.get_append_suffix] using
        hTail.1 t x hx'
  · rcases x.append_cases with ⟨x, rfl⟩ | ⟨x, rfl⟩
    · simp only [Var.prefix_index, slots_append_prefix x first rest hLength,
        Env.get_append_prefix] at hx hm hwx ⊢
      rcases y.append_cases with ⟨y, rfl⟩ | ⟨y, rfl⟩
      · simp only [Var.prefix_index, slots_append_prefix y first rest hLength,
          Env.get_append_prefix] at hy hne hwy ⊢
        exact hFirst.2 t u x y hx hy hne hm wx wy hwx hlx hwy hly
      · simp only [slots_append_suffix y first rest hLength, Env.get_append_suffix] at hwy ⊢
        have hy' : live (ps.length + y.index) = true := by simpa using hy
        have h := hApart t x hx wx hwx hlx u y hy' (.inl hm) wy hwy hly
        rw [hm] at h
        exact h
    · simp only [slots_append_suffix x first rest hLength, Env.get_append_suffix] at hm hwx ⊢
      have hx' : live (ps.length + x.index) = true := by simpa using hx
      rcases y.append_cases with ⟨y, rfl⟩ | ⟨y, rfl⟩
      · simp only [Var.prefix_index, slots_append_prefix y first rest hLength,
          Env.get_append_prefix] at hy hwy ⊢
        intro b hb c hc
        have h := hApart u y hy wy hwy hly t x hx' (.inr hm) wx hwx hlx c hc
        rw [hm] at h
        exact regionsDisjoint_symm (h b hb)
      · simp only [slots_append_suffix y first rest hLength, Env.get_append_suffix] at hwy ⊢
        have hy' : live (ps.length + y.index) = true := by simpa using hy
        exact hTail.2 t u x y hx' hy' (by simpa using hne) hm wx wy hwx hlx hwy hly

theorem Holds.Apart.popPrefix {ps qs : List Ty} {values : Env ps} {tail : Env qs}
    {first rest : List Slot} {live : Nat → Bool} {store : Store Unit} {s : Locals}
    {t : Ty} {mode : Mode} {ws : List Value} {v : t.denote}
    (hLength : first.length = ps.length)
    (h : Holds.Apart (values.append tail) (first ++ rest) live store s t mode ws v) :
    Holds.Apart tail rest (fun i => live (ps.length + i)) store s t mode ws v := by
  intro u x hx
  have hx' : live (x.suffix ps).index = true := by simpa using hx
  have h' := h u (x.suffix ps) hx'
  simpa only [slots_append_suffix x first rest hLength, Env.get_append_suffix] using h'

end Verified
