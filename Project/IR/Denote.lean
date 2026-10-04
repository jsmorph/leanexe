import Project.IR.Read

/-!
The value of an expression of the kernel subset from the values of the locals it reads and the
arrays at its pointer locals, without memory or scratch locals.  `Expr.eval_denote` shows that
`Expr.eval` computes the same value when the state holds those locals below the scratch base, each
array is laid out at its pointer local, and the scratch locals exist.  A per-element fact stated
with `Expr.denote` therefore serves both a Wasm proof and a WGSL kernel proof.
-/

namespace Project.IR

open Wasm Project.ProofKit

def Expr.denote (locals : Nat → Option Value) (arrays : Nat → Option (Array UInt64)) :
    {type : ScalarType} → Expr type → Option type.denote
  | .u64, .get j => match locals j with
    | some (.i64 v) => some v
    | _ => none
  | .u64, .const v => some v
  | .u64, .bin op left right =>
      if op = .divU ∨ op = .remU then none
      else do pure (op.apply (← left.denote locals arrays) (← right.denote locals arrays))
  | .bool, .ltU left right => do
      pure (decide ((← left.denote locals arrays) < (← right.denote locals arrays)))
  | .f32, .getF32 j => match locals j with
    | some (.f32 v) => some v
    | _ => none
  | .f32, .constF32 bits => some bits
  | .f32, .binF32 op left right => do
      pure (op.apply (← left.denote locals arrays) (← right.denote locals arrays))
  | .f32, .unF32 op operand => (operand.denote locals arrays).map op.apply
  | .f32, .ofBits32 operand => (operand.denote locals arrays).map (·.toUInt32)
  | .u64, .toBits32 operand => (operand.denote locals arrays).map (·.toUInt64)
  | .u64, .read array position => do
      let xs ← arrays array
      let k ← position.denote locals arrays
      pure xs[k.toNat]!
  | _, _ => none

/-- The state holds the locals and arrays of a denotation below the scratch base. -/
structure Agrees (locals : Nat → Option Value) (arrays : Nat → Option (Array UInt64))
    (store : Store Unit) (scratch : Nat) (state : State) : Prop where
  locals : ∀ j v, locals j = some v → j < scratch ∧ state.get j = some v
  arrays : ∀ a xs, arrays a = some xs →
    a < scratch ∧ ∃ ptr, state.get a = some (.i64 ptr) ∧ UInt64Array.At store ptr xs

/-- Agreement below the scratch base passes to a state that matches below it. -/
theorem Agrees.frame {locals : Nat → Option Value} {arrays : Nat → Option (Array UInt64)}
    {store : Store Unit} {scratch : Nat} {state next : State}
    (h : Agrees locals arrays store scratch state)
    (hSame : ∀ j, j < scratch → next.get j = state.get j) :
    Agrees locals arrays store scratch next := by
  refine ⟨fun j v hj => ?_, fun a xs ha => ?_⟩
  · obtain ⟨hlt, hget⟩ := h.locals j v hj
    exact ⟨hlt, (hSame j hlt).trans hget⟩
  · obtain ⟨hlt, ptr, hget, hAt⟩ := h.arrays a xs ha
    exact ⟨hlt, ptr, (hSame a hlt).trans hget, hAt⟩

theorem Agrees.mono {locals : Nat → Option Value} {arrays : Nat → Option (Array UInt64)}
    {store : Store Unit} {scratch scratch' : Nat} {state : State}
    (h : Agrees locals arrays store scratch state) (hle : scratch ≤ scratch') :
    Agrees locals arrays store scratch' state :=
  ⟨fun j v hj => ⟨by have := (h.locals j v hj).1; omega, (h.locals j v hj).2⟩,
    fun a xs ha => ⟨by have := (h.arrays a xs ha).1; omega, (h.arrays a xs ha).2⟩⟩

/-- `Expr.eval` computes the denotation. -/
theorem Expr.eval_denote {locals : Nat → Option Value} {arrays : Nat → Option (Array UInt64)}
    {store : Store Unit} : ∀ {type : ScalarType} (e : Expr type) (scratch : Nat) (state : State)
    (v : type.denote), Agrees locals arrays store scratch state →
    scratch + e.scratchWidth ≤ state.params.length + state.locals.length →
    e.denote locals arrays = some v →
    ∃ next, e.eval store.mem scratch state = some (v, next) := by
  intro type e
  induction e with
  | get j =>
      intro scratch state v hAgree _ hDenote
      simp only [Expr.denote] at hDenote
      split at hDenote
      · rename_i w hw
        obtain ⟨-, hget⟩ := hAgree.locals j _ hw
        cases hDenote
        exact ⟨state, by simp [Expr.eval, hget]⟩
      · cases hDenote
  | const c =>
      intro scratch state v _ _ hDenote
      cases hDenote
      exact ⟨state, rfl⟩
  | bin op left right ihl ihr =>
      intro scratch state v hAgree hRoom hDenote
      simp only [Expr.denote] at hDenote
      split at hDenote
      · cases hDenote
      rename_i hOp
      simp only [Option.bind_eq_bind, Option.pure_def] at hDenote
      cases hl : left.denote locals arrays with
      | none => simp [hl] at hDenote
      | some lv =>
        cases hr : right.denote locals arrays with
        | none => simp [hl, hr] at hDenote
        | some rv =>
          simp only [hl, hr, Option.bind_some, Option.some.injEq] at hDenote
          subst hDenote
          simp only [Expr.scratchWidth, hOp, ↓reduceIte] at hRoom
          obtain ⟨s1, h1⟩ := ihl scratch state lv hAgree (by omega) hl
          have hFrame := Expr.eval_frame [] left store.mem scratch state s1 lv h1
          have hAgree1 := hAgree.frame fun j hj =>
            Expr.eval_preserves_below left store.mem scratch state s1 lv j h1 hj
          obtain ⟨s2, h2⟩ := ihr scratch s1 rv hAgree1
            (by rw [hFrame.params, hFrame.locals]; omega) hr
          exact ⟨s2, by simp [Expr.eval, hOp, h1, h2]⟩
  | ltU left right ihl ihr =>
      intro scratch state v hAgree hRoom hDenote
      simp only [Expr.denote, Option.bind_eq_bind, Option.pure_def] at hDenote
      cases hl : left.denote locals arrays with
      | none => simp [hl] at hDenote
      | some lv =>
        cases hr : right.denote locals arrays with
        | none => simp [hl, hr] at hDenote
        | some rv =>
          simp only [hl, hr, Option.bind_some, Option.some.injEq] at hDenote
          subst hDenote
          simp only [Expr.scratchWidth] at hRoom
          obtain ⟨s1, h1⟩ := ihl scratch state lv hAgree (by omega) hl
          have hFrame := Expr.eval_frame [] left store.mem scratch state s1 lv h1
          have hAgree1 := hAgree.frame fun j hj =>
            Expr.eval_preserves_below left store.mem scratch state s1 lv j h1 hj
          obtain ⟨s2, h2⟩ := ihr scratch s1 rv hAgree1
            (by rw [hFrame.params, hFrame.locals]; omega) hr
          exact ⟨s2, by simp [Expr.eval, h1, h2]⟩
  | getF32 j =>
      intro scratch state v hAgree _ hDenote
      simp only [Expr.denote] at hDenote
      split at hDenote
      · rename_i w hw
        obtain ⟨-, hget⟩ := hAgree.locals j _ hw
        cases hDenote
        exact ⟨state, by simp [Expr.eval, hget]⟩
      · cases hDenote
  | constF32 bits =>
      intro scratch state v _ _ hDenote
      cases hDenote
      exact ⟨state, rfl⟩
  | binF32 op left right ihl ihr =>
      intro scratch state v hAgree hRoom hDenote
      simp only [Expr.denote, Option.bind_eq_bind, Option.pure_def] at hDenote
      cases hl : left.denote locals arrays with
      | none => simp [hl] at hDenote
      | some lv =>
        cases hr : right.denote locals arrays with
        | none => simp [hl, hr] at hDenote
        | some rv =>
          simp only [hl, hr, Option.bind_some, Option.some.injEq] at hDenote
          subst hDenote
          simp only [Expr.scratchWidth] at hRoom
          obtain ⟨s1, h1⟩ := ihl scratch state lv hAgree (by omega) hl
          have hFrame := Expr.eval_frame [] left store.mem scratch state s1 lv h1
          have hAgree1 := hAgree.frame fun j hj =>
            Expr.eval_preserves_below left store.mem scratch state s1 lv j h1 hj
          obtain ⟨s2, h2⟩ := ihr scratch s1 rv hAgree1
            (by rw [hFrame.params, hFrame.locals]; omega) hr
          exact ⟨s2, by simp [Expr.eval, h1, h2]⟩
  | unF32 op operand ih =>
      intro scratch state v hAgree hRoom hDenote
      simp only [Expr.denote] at hDenote
      cases ho : operand.denote locals arrays with
      | none => simp [ho] at hDenote
      | some w =>
        simp only [ho, Option.map_some, Option.some.injEq] at hDenote
        subst hDenote
        obtain ⟨s1, h1⟩ := ih scratch state w hAgree (by simpa [Expr.scratchWidth] using hRoom) ho
        exact ⟨s1, by simp [Expr.eval, h1]⟩
  | ofBits32 operand ih =>
      intro scratch state v hAgree hRoom hDenote
      simp only [Expr.denote] at hDenote
      cases ho : operand.denote locals arrays with
      | none => simp [ho] at hDenote
      | some w =>
        simp only [ho, Option.map_some, Option.some.injEq] at hDenote
        subst hDenote
        obtain ⟨s1, h1⟩ := ih scratch state w hAgree (by simpa [Expr.scratchWidth] using hRoom) ho
        exact ⟨s1, by simp [Expr.eval, h1]⟩
  | toBits32 operand ih =>
      intro scratch state v hAgree hRoom hDenote
      simp only [Expr.denote] at hDenote
      cases ho : operand.denote locals arrays with
      | none => simp [ho] at hDenote
      | some w =>
        simp only [ho, Option.map_some, Option.some.injEq] at hDenote
        subst hDenote
        obtain ⟨s1, h1⟩ := ih scratch state w hAgree (by simpa [Expr.scratchWidth] using hRoom) ho
        exact ⟨s1, by simp [Expr.eval, h1]⟩
  | read array position ih =>
      intro scratch state v hAgree hRoom hDenote
      simp only [Expr.denote, Option.bind_eq_bind, Option.pure_def] at hDenote
      cases ha : arrays array with
      | none => simp [ha] at hDenote
      | some xs =>
        cases hp : position.denote locals arrays with
        | none => simp [ha, hp] at hDenote
        | some k =>
          simp only [ha, hp, Option.bind_some, Option.some.injEq] at hDenote
          subst hDenote
          simp only [Expr.scratchWidth] at hRoom
          obtain ⟨hlt, ptr, hget, hAt⟩ := hAgree.arrays array xs ha
          obtain ⟨s1, h1⟩ := ih (scratch + 1) state k (hAgree.mono (by omega)) (by omega) hp
          have hFrame := Expr.eval_frame [] position store.mem (scratch + 1) state s1 k h1
          obtain ⟨s2, hset⟩ := State.exists_set? (state := s1) (index := scratch) (.i64 k)
            (by rw [hFrame.params, hFrame.locals]; omega)
          have hget2 : s2.get array = some (.i64 ptr) := by
            rw [State.get_set?_ne (by omega) hset,
              Expr.eval_preserves_below position store.mem (scratch + 1) state s1 k array h1
                (by omega)]
            exact hget
          exact ⟨s2, by simp [Expr.eval, h1, hset, Expr.readValue_at hAt hget2]⟩
  | _ =>
      intro scratch state v _ _ hDenote
      simp [Expr.denote] at hDenote

end Project.IR
