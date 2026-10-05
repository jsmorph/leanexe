import Project.IR.Stmt

/-!
Straight-line statements as a function on states.  `Stmt.run` computes the effect
of assignments, sequences, and conditionals, and `Stmt.run_spec` turns a computed
effect into a `Triple`.  `State.update` is `State.set?` without the `Option`, so
`simp` can compute the effect of a statement on a symbolic state.
-/

namespace Project.IR

open Wasm

variable {m : Module} {a : Bool}

/-- Local `index` receives `value`; an index beyond the locals changes nothing. -/
def State.update (state : State) (index : Nat) (value : Value) : State :=
  if index < state.params.length then { state with params := state.params.set index value }
  else { state with locals := state.locals.set (index - state.params.length) value }

@[simp]
theorem State.update_params_length (state : State) (index : Nat) (value : Value) :
    (state.update index value).params.length = state.params.length := by
  unfold State.update; split <;> simp

@[simp]
theorem State.update_locals_length (state : State) (index : Nat) (value : Value) :
    (state.update index value).locals.length = state.locals.length := by
  unfold State.update; split <;> simp

theorem State.set?_eq_update {state : State} {index : Nat} (value : Value)
    (h : index < state.params.length + state.locals.length) :
    state.set? index value = some (state.update index value) := by
  unfold State.set? State.update
  by_cases hParam : index < state.params.length
  · simp [hParam]
  · simp [hParam, h]

@[simp]
theorem State.get_update_same {state : State} {index : Nat} {value : Value}
    (h : index < state.params.length + state.locals.length) :
    (state.update index value).get index = some value :=
  State.get_set?_same (State.set?_eq_update value h)

@[simp]
theorem State.get_update_ne {state : State} {index j : Nat} {value : Value}
    (hNe : j ≠ index) : (state.update index value).get j = state.get j := by
  by_cases h : index < state.params.length + state.locals.length
  · exact State.get_set?_ne hNe (State.set?_eq_update value h)
  · have hNot : ¬index < state.params.length := by omega
    unfold State.update
    rw [if_neg hNot]
    rw [List.set_eq_of_length_le (by omega)]

@[simp]
theorem State.update_update_same (state : State) (index : Nat) (first second : Value) :
    (state.update index first).update index second = state.update index second := by
  unfold State.update
  by_cases h : index < state.params.length <;> simp [h]

/-- A conditional whose branches leave the same state gives a conditional value. -/
@[simp]
theorem ite_some_pair {c : Prop} [Decidable c] (a b : α) (state : β) :
    (if c then some (a, state) else some (b, state)) = some (if c then a else b, state) := by
  split <;> rfl

theorem State.Frame.update {scratch index : Nat} {writes : List Nat} {before state : State}
    {value : Value} (hFrame : State.Frame scratch writes before state)
    (hIndex : index ∈ writes ∨ scratch ≤ index) :
    State.Frame scratch writes before (state.update index value) :=
  ⟨by simp [hFrame.params], by simp [hFrame.locals], fun j hj hOut => by
    rw [State.get_update_ne (fun h => by subst h; rcases hIndex with h | h <;> [exact hOut h; omega])]
    exact hFrame.get j hj hOut⟩

/-- The effect of a statement built from assignments, sequences, and
conditionals; `none` for other statements and failed evaluations. -/
def Stmt.run (mem : Mem) (scratch : Nat) : Stmt → State → Option State
  | .skip, state => some state
  | .assign (type := type) index value, state => do
      let (result, after) ← value.eval mem scratch state
      after.set? index (type.value result)
  | .seq first second, state => do
      Stmt.run mem scratch second (← Stmt.run mem scratch first state)
  | .load type index address, state => do
      let (word, after) ← address.eval mem scratch state
      if word.toUInt32.toNat + 8 ≤ mem.pages * 65536 then
        after.set? index (type.ofBits (mem.read64 word.toUInt32))
      else none
  | .ite condition thenStmt elseStmt, state => do
      let (result, after) ← condition.eval mem scratch state
      if result then Stmt.run mem scratch thenStmt after
      else Stmt.run mem scratch elseStmt after
  | _, _ => none

/-- A statement whose effect `Stmt.run` computes ends in the computed state and
keeps the store. -/
theorem Stmt.run_spec {s : Stmt} {scratch : Nat} {initial : Store Unit} :
    ∀ {state final : State}, s.run initial.mem scratch state = some final →
      TripleA a m s scratch (fun store st => store = initial ∧ st = state)
        (fun store st => store = initial ∧ st = final) := by
  induction s with
  | skip =>
      intro state final hRun
      obtain rfl := Option.some.inj hRun
      exact Stmt.skip_spec.mono (fun _ _ h => h) fun _ _ h => h
  | assign index value =>
      intro state final hRun
      simp only [Stmt.run, Option.bind_eq_bind, Option.bind_eq_some_iff] at hRun
      obtain ⟨⟨result, after⟩, hEval, hSet⟩ := hRun
      refine Stmt.assign_spec.mono ?_ fun _ _ h => h
      rintro store st ⟨rfl, rfl⟩
      exact ⟨result, after, final, hEval, hSet, rfl, rfl⟩
  | seq first second ihFirst ihSecond =>
      intro state final hRun
      simp only [Stmt.run, Option.bind_eq_bind, Option.bind_eq_some_iff] at hRun
      obtain ⟨middle, hFirst, hSecond⟩ := hRun
      exact Stmt.seq_spec (ihFirst hFirst) (ihSecond hSecond)
  | ite condition thenStmt elseStmt ihThen ihElse =>
      intro state final hRun
      simp only [Stmt.run, Option.bind_eq_bind, Option.bind_eq_some_iff] at hRun
      obtain ⟨⟨result, after⟩, hEval, hBranch⟩ := hRun
      refine (Stmt.ite_spec
        (PThen := fun store st => result = true ∧ store = initial ∧ st = after)
        (PElse := fun store st => result = false ∧ store = initial ∧ st = after) ?_ ?_).mono
          ?_ fun _ _ h => h
      · cases result
        · exact fun _ _ _ _ _ _ _ h => absurd h.1 (by simp)
        · exact (ihThen (by simpa using hBranch)).mono (fun _ _ h => h.2) fun _ _ h => h
      · cases result
        · exact (ihElse (by simpa using hBranch)).mono (fun _ _ h => h.2) fun _ _ h => h
        · exact fun _ _ _ _ _ _ _ h => absurd h.1 (by simp)
      · rintro store st ⟨rfl, rfl⟩
        exact ⟨result, after, hEval, by cases result <;> simp⟩
  | load type index address =>
      intro state final hRun
      simp only [Stmt.run, Option.bind_eq_bind, Option.bind_eq_some_iff] at hRun
      obtain ⟨⟨word, after⟩, hEval, hLoad⟩ := hRun
      split at hLoad
      · refine Stmt.load_spec.mono ?_ fun _ _ h => h
        rintro store st ⟨rfl, rfl⟩
        exact ⟨word, after, final, hEval, by assumption, hLoad, rfl, rfl⟩
      · cases hLoad
  | «while» | store | call | abort =>
      intro state final hRun
      simp [Stmt.run] at hRun

/-- A statement that `Stmt.run` completes meets every postcondition that holds of its final
state. -/
theorem Stmt.run_triple {s : Stmt} {scratch : Nat} {initial : Store Unit} {state : State}
    {post : Store Unit → State → Prop}
    (h : ∃ final, s.run initial.mem scratch state = some final ∧ post initial final) :
    TripleA a m s scratch (fun store st => store = initial ∧ st = state) post :=
  let ⟨_, hRun, hPost⟩ := h
  (Stmt.run_spec hRun).mono (fun _ _ h => h) fun _ _ ⟨hStore, hState⟩ => hStore ▸ hState ▸ hPost

/-- A statement that `Stmt.run` completes, followed by `rest` from the state it leaves. -/
theorem Stmt.seq_run {s rest : Stmt} {scratch : Nat} {initial : Store Unit} {state : State}
    {Q : Store Unit → State → Prop}
    (h : ∃ mid, s.run initial.mem scratch state = some mid ∧
      TripleA a m rest scratch (fun store st => store = initial ∧ st = mid) Q) :
    TripleA a m (.seq s rest) scratch (fun store st => store = initial ∧ st = state) Q :=
  let ⟨_, hRun, hRest⟩ := h
  Stmt.seq_spec (Stmt.run_spec hRun) hRest

end Project.IR
