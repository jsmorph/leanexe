import LeanExe.PTX.Det

/-!
Runs of statement lists that neither stop, store, nor return: `Runs s o l code P` states that from
`l`, after any events, `code` adds only loads and ends in a local that satisfies `P`.  The lemmas
compose such runs over appended lists, unguarded instructions, and conditionals.
-/

namespace LeanExe.PTX

theorem Res.andThen_assoc (r : Res α) (f : List Event → α → Res β)
    (g : List Event → β → Res γ) :
    (r.andThen f).andThen g = r.andThen fun evs x => (f evs x).andThen g := by
  rcases r with ⟨evs, _ | x⟩ <;> rfl

theorem Stmt.execList_returned (s : Shape) (o : Oracle) {l : Local} (h : l.returned = true)
    (evs : List Event) (code : List Stmt) : Stmt.execList s o l evs code = (evs, some l) := by
  cases code <;> simp [Stmt.execList, h]

theorem Stmt.execList_append (s : Shape) (o : Oracle) (a b : List Stmt) :
    ∀ (l : Local) (evs : List Event), Stmt.execList s o l evs (a ++ b) =
      (Stmt.execList s o l evs a).andThen fun evs l => Stmt.execList s o l evs b := by
  induction a with
  | nil => intro l evs; rfl
  | cons st rest ih =>
      intro l evs
      by_cases h : l.returned = true
      · simp [Stmt.execList, h, Res.andThen, Stmt.execList_returned s o h]
      · simp only [List.cons_append, Stmt.execList, h, Bool.false_eq_true, ↓reduceIte,
          Res.andThen_assoc]
        congr 1
        funext evs l
        exact ih l evs

/-- From `l`, after any events, `code` adds only loads, does not return, and ends in a local that
satisfies `P`. -/
def Runs (s : Shape) (o : Oracle) (l : Local) (code : List Stmt) (P : Local → Prop) : Prop :=
  ∀ evs, ∃ added l', Stmt.execList s o l evs code = (evs ++ added, some l') ∧
    writesOf added = [] ∧ l'.returned = false ∧ P l'

theorem Runs.nil {s : Shape} {o : Oracle} {l : Local} {P : Local → Prop}
    (hr : l.returned = false) (hP : P l) : Runs s o l [] P :=
  fun evs => ⟨[], l, by simp [Stmt.execList], rfl, hr, hP⟩

theorem Runs.mono {s : Shape} {o : Oracle} {l : Local} {code : List Stmt} {P Q : Local → Prop}
    (h : Runs s o l code P) (hPQ : ∀ l', P l' → Q l') : Runs s o l code Q := by
  intro evs
  obtain ⟨added, l', he, hw, hr, hP⟩ := h evs
  exact ⟨added, l', he, hw, hr, hPQ l' hP⟩

theorem Runs.append {s : Shape} {o : Oracle} {l : Local} {a b : List Stmt}
    {P Q : Local → Prop} (ha : Runs s o l a P) (hb : ∀ l', P l' → l'.returned = false →
      Runs s o l' b Q) : Runs s o l (a ++ b) Q := by
  intro evs
  obtain ⟨added, l1, he1, hw1, hr1, hP⟩ := ha evs
  obtain ⟨added2, l2, he2, hw2, hr2, hQ⟩ := hb l1 hP hr1 (evs ++ added)
  refine ⟨added ++ added2, l2, ?_, by rw [writesOf_append, hw1, hw2]; rfl, hr2, hQ⟩
  rw [Stmt.execList_append, he1]
  simpa [Res.andThen] using he2

theorem Runs.cons {s : Shape} {o : Oracle} {l : Local} {st : Stmt} {rest : List Stmt}
    {P Q : Local → Prop} (h : Runs s o l [st] P)
    (k : ∀ l', P l' → l'.returned = false → Runs s o l' rest Q) : Runs s o l (st :: rest) Q :=
  Runs.append (a := [st]) h k

/-- An unguarded instruction that changes the local to `l'` and adds no event. -/
theorem Runs.step {s : Shape} {o : Oracle} {l l' : Local} {i : Instr} {P : Local → Prop}
    (hr : l.returned = false) (hi : ∀ evs, i.exec s o l evs = (evs, some l'))
    (hr' : l'.returned = false) (hP : P l') : Runs s o l [.instr none i] P := by
  intro evs
  refine ⟨[], l', ?_, rfl, hr', hP⟩
  simp [Stmt.execList, Stmt.exec, hr, hi, Res.andThen]

theorem Runs.ite_true {s : Shape} {o : Oracle} {l : Local} {p : Nat} {ts es : List Stmt}
    {P : Local → Prop} (hr : l.returned = false) (hp : l.rp p = some true)
    (h : Runs s o l ts P) : Runs s o l [.ite p ts es] P := by
  intro evs
  obtain ⟨added, l', he, hw, hr', hP⟩ := h evs
  refine ⟨added, l', ?_, hw, hr', hP⟩
  simp [Stmt.execList, Stmt.exec, hr, hp, he, Res.andThen]

theorem Runs.ite_false {s : Shape} {o : Oracle} {l : Local} {p : Nat} {ts es : List Stmt}
    {P : Local → Prop} (hr : l.returned = false) (hp : l.rp p = some false)
    (h : Runs s o l es P) : Runs s o l [.ite p ts es] P := by
  intro evs
  obtain ⟨added, l', he, hw, hr', hP⟩ := h evs
  refine ⟨added, l', ?_, hw, hr', hP⟩
  simp [Stmt.execList, Stmt.exec, hr, hp, he, Res.andThen]

end LeanExe.PTX
