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
  | .bool, .bconst b => some b
  | .u64, .bin op left right => do
      pure (op.apply (← left.denote locals arrays) (← right.denote locals arrays))
  | .bool, .eq left right => do
      pure ((← left.denote locals arrays) == (← right.denote locals arrays))
  | .bool, .ne left right => do
      pure ((← left.denote locals arrays) != (← right.denote locals arrays))
  | .bool, .ltU left right => do
      pure (decide ((← left.denote locals arrays) < (← right.denote locals arrays)))
  | .bool, .leU left right => do
      pure (decide ((← left.denote locals arrays) ≤ (← right.denote locals arrays)))
  | .bool, .not operand => (operand.denote locals arrays).map (!·)
  | .bool, .and left right => do
      if (← left.denote locals arrays) then right.denote locals arrays else pure false
  | .bool, .or left right => do
      if (← left.denote locals arrays) then pure true else right.denote locals arrays
  | .u64, .ite c t e => do
      if (← c.denote locals arrays) then t.denote locals arrays else e.denote locals arrays
  | .f32, .getF32 j => match locals j with
    | some (.f32 v) => some v
    | _ => none
  | .f32, .constF32 bits => some bits
  | .f32, .binF32 op left right => do
      pure (op.apply (← left.denote locals arrays) (← right.denote locals arrays))
  | .f32, .unF32 op operand => (operand.denote locals arrays).map op.apply
  | .f32, .ofBits32 operand => (operand.denote locals arrays).map (·.toUInt32)
  | .u64, .toBits32 operand => (operand.denote locals arrays).map (·.toUInt64)
  | .f32, .iteF32 c t e => do
      if (← c.denote locals arrays) then t.denote locals arrays else e.denote locals arrays
  | .bool, .eqF32 left right => do
      pure (IEEE32.eq (← left.denote locals arrays) (← right.denote locals arrays))
  | .bool, .ltF32 left right => do
      pure (IEEE32.lt (← left.denote locals arrays) (← right.denote locals arrays))
  | .bool, .leF32 left right => do
      pure (IEEE32.le (← left.denote locals arrays) (← right.denote locals arrays))
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

/-- What `Expr.eval_denote` states for one expression. -/
def EvalsDenote (locals : Nat → Option Value) (arrays : Nat → Option (Array UInt64))
    (store : Store Unit) {type : ScalarType} (e : Expr type) : Prop :=
  ∀ (scratch : Nat) (state : State) (v : type.denote), Agrees locals arrays store scratch state →
    scratch + e.scratchWidth ≤ state.params.length + state.locals.length →
    e.denote locals arrays = some v → ∃ next, e.eval store.mem scratch state = some (v, next)

/-- Two operands evaluated in order at one scratch base. -/
theorem eval_two {locals : Nat → Option Value} {arrays : Nat → Option (Array UInt64)}
    {store : Store Unit} {t1 t2 : ScalarType} {left : Expr t1} {right : Expr t2} {scratch : Nat}
    {state : State} {lv : t1.denote} {rv : t2.denote}
    (ihl : EvalsDenote locals arrays store left) (ihr : EvalsDenote locals arrays store right)
    (hAgree : Agrees locals arrays store scratch state)
    (hRoom : scratch + max left.scratchWidth right.scratchWidth ≤
      state.params.length + state.locals.length)
    (hl : left.denote locals arrays = some lv) (hr : right.denote locals arrays = some rv) :
    ∃ s1 s2, left.eval store.mem scratch state = some (lv, s1) ∧
      right.eval store.mem scratch s1 = some (rv, s2) := by
  obtain ⟨s1, h1⟩ := ihl scratch state lv hAgree (by omega) hl
  have hFrame := Expr.eval_frame [] left store.mem scratch state s1 lv h1
  have hAgree1 := hAgree.frame fun j hj =>
    Expr.eval_preserves_below left store.mem scratch state s1 lv j h1 hj
  obtain ⟨s2, h2⟩ := ihr scratch s1 rv hAgree1 (by rw [hFrame.params, hFrame.locals]; omega) hr
  exact ⟨s1, s2, h1, h2⟩

/-- An operand evaluated after another, from the state the first leaves. -/
theorem eval_after {locals : Nat → Option Value} {arrays : Nat → Option (Array UInt64)}
    {store : Store Unit} {t1 t2 : ScalarType} {first : Expr t1} {second : Expr t2} {scratch : Nat}
    {state s1 : State} {fv : t1.denote} {v : t2.denote}
    (ih : EvalsDenote locals arrays store second) (hAgree : Agrees locals arrays store scratch state)
    (hRoom : scratch + second.scratchWidth ≤ state.params.length + state.locals.length)
    (h1 : first.eval store.mem scratch state = some (fv, s1))
    (hd : second.denote locals arrays = some v) :
    ∃ s2, second.eval store.mem scratch s1 = some (v, s2) := by
  have hFrame := Expr.eval_frame [] first store.mem scratch state s1 fv h1
  have hAgree1 := hAgree.frame fun j hj =>
    Expr.eval_preserves_below first store.mem scratch state s1 fv j h1 hj
  exact ih scratch s1 v hAgree1 (by rw [hFrame.params, hFrame.locals]; omega) hd

theorem denote_two {locals : Nat → Option Value} {arrays : Nat → Option (Array UInt64)}
    {t1 t2 t : ScalarType} {left : Expr t1} {right : Expr t2} {f : t1.denote → t2.denote → t.denote}
    {v : t.denote}
    (h : (do pure (f (← left.denote locals arrays) (← right.denote locals arrays))) = some v) :
    ∃ lv rv, left.denote locals arrays = some lv ∧ right.denote locals arrays = some rv ∧
      f lv rv = v := by
  cases hl : left.denote locals arrays <;> cases hr : right.denote locals arrays <;>
    simp_all

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
  | bconst b =>
      intro scratch state v _ _ hDenote
      cases hDenote
      exact ⟨state, rfl⟩
  | bin op left right ihl ihr =>
      intro scratch state v hAgree hRoom hDenote
      simp only [Expr.denote] at hDenote
      obtain ⟨lv, rv, hl, hr, rfl⟩ := denote_two hDenote
      by_cases hop : op = .divU ∨ op = .remU
      · simp only [Expr.scratchWidth, hop, ↓reduceIte] at hRoom
        obtain ⟨s1, h1⟩ := ihl (scratch + 2) state lv (hAgree.mono (by omega)) (by omega) hl
        have hF1 := Expr.eval_frame [] left store.mem (scratch + 2) state s1 lv h1
        obtain ⟨t1, hset1⟩ := State.exists_set? (state := s1) (index := scratch) (.i64 lv)
          (by rw [hF1.params, hF1.locals]; omega)
        have hT1 := (State.Frame.refl scratch [] s1).set? hset1 (Or.inr (le_refl _))
        have hA1 : Agrees locals arrays store (scratch + 2) t1 :=
          (hAgree.frame fun j hj => by
            rw [State.get_set?_ne (by omega) hset1]
            exact Expr.eval_preserves_below left store.mem (scratch + 2) state s1 lv j h1
              (by omega)).mono (by omega)
        obtain ⟨s2, h2⟩ := ihr (scratch + 2) t1 rv hA1
          (by rw [hT1.params, hT1.locals, hF1.params, hF1.locals]; omega) hr
        have hF2 := Expr.eval_frame [] right store.mem (scratch + 2) t1 s2 rv h2
        obtain ⟨t2, hset2⟩ := State.exists_set? (state := s2) (index := scratch + 1) (.i64 rv)
          (by rw [hF2.params, hF2.locals, hT1.params, hT1.locals, hF1.params, hF1.locals]
              omega)
        rcases hop with rfl | rfl <;>
          exact ⟨t2, by simp [Expr.eval, h1, hset1, h2, hset2]⟩
      · obtain ⟨s1, s2, h1, h2⟩ := eval_two ihl ihr hAgree
          (by simpa [Expr.scratchWidth, hop] using hRoom) hl hr
        exact ⟨s2, by simp [Expr.eval, hop, h1, h2]⟩
  | eq left right ihl ihr | ne left right ihl ihr | ltU left right ihl ihr
  | leU left right ihl ihr =>
      intro scratch state v hAgree hRoom hDenote
      simp only [Expr.denote] at hDenote
      obtain ⟨lv, rv, hl, hr, rfl⟩ := denote_two hDenote
      obtain ⟨s1, s2, h1, h2⟩ := eval_two ihl ihr hAgree (by simpa [Expr.scratchWidth] using hRoom)
        hl hr
      exact ⟨s2, by simp [Expr.eval, h1, h2]⟩
  | eqF32 left right ihl ihr | ltF32 left right ihl ihr | leF32 left right ihl ihr
  | binF32 op left right ihl ihr =>
      intro scratch state v hAgree hRoom hDenote
      simp only [Expr.denote] at hDenote
      obtain ⟨lv, rv, hl, hr, rfl⟩ := denote_two hDenote
      obtain ⟨s1, s2, h1, h2⟩ := eval_two ihl ihr hAgree (by simpa [Expr.scratchWidth] using hRoom)
        hl hr
      exact ⟨s2, by simp [Expr.eval, h1, h2]⟩
  | not operand ih | unF32 op operand ih | ofBits32 operand ih | toBits32 operand ih =>
      intro scratch state v hAgree hRoom hDenote
      simp only [Expr.denote] at hDenote
      obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp hDenote
      obtain ⟨s1, h1⟩ := ih scratch state w hAgree (by simpa [Expr.scratchWidth] using hRoom) hw
      exact ⟨s1, by simp [Expr.eval, h1]⟩
  | and left right ihl ihr | or left right ihl ihr =>
      intro scratch state v hAgree hRoom hDenote
      simp only [Expr.denote, Option.bind_eq_bind] at hDenote
      simp only [Expr.scratchWidth] at hRoom
      cases hl : left.denote locals arrays with
      | none => simp [hl] at hDenote
      | some lv =>
        simp only [hl, Option.bind_some] at hDenote
        obtain ⟨s1, h1⟩ := ihl scratch state lv hAgree (by omega) hl
        cases lv <;> simp only [Bool.false_eq_true, ↓reduceIte, Option.pure_def,
          Option.some.injEq] at hDenote
        all_goals first
          | (subst hDenote; exact ⟨s1, by simp [Expr.eval, h1]⟩)
          | (obtain ⟨s2, h2⟩ := eval_after ihr hAgree (by omega) h1 hDenote
             exact ⟨s2, by simp [Expr.eval, h1, h2]⟩)
  | ite c t e ihc iht ihe | iteF32 c t e ihc iht ihe =>
      intro scratch state v hAgree hRoom hDenote
      simp only [Expr.denote, Option.bind_eq_bind] at hDenote
      simp only [Expr.scratchWidth] at hRoom
      cases hc : c.denote locals arrays with
      | none => simp [hc] at hDenote
      | some b =>
        simp only [hc, Option.bind_some] at hDenote
        obtain ⟨s1, h1⟩ := ihc scratch state b hAgree (by omega) hc
        cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at hDenote
        · obtain ⟨s2, h2⟩ := eval_after ihe hAgree (by omega) h1 hDenote
          exact ⟨s2, by simp [Expr.eval, h1, h2]⟩
        · obtain ⟨s2, h2⟩ := eval_after iht hAgree (by omega) h1 hDenote
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
