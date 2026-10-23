import LeanExe.Wasi.Prefix

namespace LeanExe.Wasi

inductive Outcome.Rel (relation : α → β → Prop) : Outcome α → Outcome β → Prop where
  | returned {left right} (value : relation left right) :
      Rel relation (.returned left) (.returned right)
  | exited (code : UInt64) : Rel relation (.exited code) (.exited code)
  | trapped (message : String) : Rel relation (.trapped message) (.trapped message)

inductive Action.Rel : {α β : Type} → (α → β → Prop) → Action α → Action β → Prop where
  | pure {relation : α → β → Prop} {left right} (value : relation left right) :
      Rel relation (.pure left) (.pure right)
  | read {relation : α → β → Prop} (capacity : UInt64)
      {left : ReadResult → Action α} {right : ReadResult → Action β}
      (next : ∀ reply, Rel relation (left reply) (right reply)) :
      Rel relation (.read capacity left) (.read capacity right)
  | write {relation : α → β → Prop} (output : Output) (bytes : Bytes)
      {left : WriteResult → Action α} {right : WriteResult → Action β}
      (next : ∀ reply, Rel relation (left reply) (right reply)) :
      Rel relation (.write output bytes left) (.write output bytes right)
  | exit {relation : α → β → Prop} (code : UInt64) :
      Rel relation (.exit code) (.exit code)
  | loop {relation : α → β → Prop} {states : σ → τ → Prop}
      (count : UInt64) {leftState : σ} {rightState : τ}
      {leftTest : UInt64 → σ → Bool} {rightTest : UInt64 → τ → Bool}
      {leftStep : UInt64 → σ → Action σ} {rightStep : UInt64 → τ → Action τ}
      {leftNext : σ → Action α} {rightNext : τ → Action β}
      (initial : states leftState rightState)
      (test : ∀ index left right, states left right → leftTest index left = rightTest index right)
      (step : ∀ index left right, states left right →
        Rel states (leftStep index left) (rightStep index right))
      (next : ∀ left right, states left right → Rel relation (leftNext left) (rightNext right)) :
      Rel relation (.loop count leftState leftTest leftStep leftNext)
        (.loop count rightState rightTest rightStep rightNext)

namespace Action.Rel

theorem refl (action : Action α) : Rel Eq action action := by
  induction action with
  | pure value => exact .pure rfl
  | read capacity next ih => exact .read capacity ih
  | write output bytes next ih => exact .write output bytes ih
  | exit code => exact .exit code
  | loop count state test step next hStep hNext =>
      refine .loop (states := Eq) count rfl ?_ ?_ ?_
      · intro index left right h; cases h; rfl
      · intro index left right h; cases h; exact hStep index left
      · intro left right h; cases h; exact hNext left

theorem mono {relation other : α → β → Prop} {left : Action α} {right : Action β}
    (h : Rel relation left right) (weaken : ∀ a b, relation a b → other a b) :
    Rel other left right := by
  induction h with
  | pure value => exact .pure (weaken _ _ value)
  | read capacity next ih => exact .read capacity (fun reply => ih reply weaken)
  | write output bytes next ih => exact .write output bytes (fun reply => ih reply weaken)
  | exit code => exact .exit code
  | loop count initial test step next _ ih =>
      exact .loop count initial test step (fun a b h => ih a b h weaken)

theorem symm {relation : α → β → Prop} {left : Action α} {right : Action β}
    (h : Rel relation left right) : Rel (fun b a => relation a b) right left := by
  induction h with
  | pure value => exact .pure value
  | read capacity next ih => exact .read capacity ih
  | write output bytes next ih => exact .write output bytes ih
  | exit code => exact .exit code
  | loop count initial test step next hStep hNext =>
      exact .loop count initial (fun i a b h => (test i b a h).symm)
        (fun i a b h => hStep i b a h) (fun a b h => hNext b a h)

theorem bind {relation : α → β → Prop} {results : γ → δ → Prop}
    {left : Action α} {right : Action β} {leftNext : α → Action γ} {rightNext : β → Action δ}
    (h : Rel relation left right)
    (next : ∀ a b, relation a b → Rel results (leftNext a) (rightNext b)) :
    Rel results (Action.bind left leftNext) (Action.bind right rightNext) := by
  induction h with
  | pure value => exact next _ _ value
  | read capacity continuation ih => exact .read capacity (fun reply => ih reply next)
  | write output bytes continuation ih => exact .write output bytes (fun reply => ih reply next)
  | exit code => exact .exit code
  | loop count initial test step continuation _ ih =>
      exact .loop count initial test step (fun a b h => ih a b h next)

theorem map (flatten : α → β) (action : Action α) :
    Rel (fun native flat => flat = flatten native) action
      (Action.bind action fun value => .pure (flatten value)) := by
  have mapped := (refl action).bind (results := fun native flat => flat = flatten native)
    (leftNext := Action.pure) (rightNext := fun value => .pure (flatten value))
    (fun a b same => by cases same; exact .pure rfl)
  simpa only [Action.bind_pure] using mapped

theorem of_map_eq (flatten : α → β) {action : Action α} {target : Action β}
    (equation : Action.bind action (fun value => .pure (flatten value)) = target) :
    Rel (fun native flat => flat = flatten native) action target :=
  equation ▸ map flatten action

end Action.Rel

end LeanExe.Wasi
