import LeanExe.Core.Program
import Init.Data.List.Monadic
import Init.Data.List.Range
import Init.Data.Range.Lemmas

namespace LeanExe.Core.NativeLoop

open LeanExe.Wasm.ScalarDescriptor (Cond)

variable {α σ : Type}

/-- The ordinary Lean `for` iterator, with a stateful body that continues after
each iteration. This definition is only an abbreviation used in the proofs. -/
def runRange (body : Nat → α → StateM σ α) (start count : Nat) (accumulator : α) :
    StateM σ α :=
  forIn (List.range' start count) accumulator fun index current => do
    return .yield (← body index current)

theorem runRange_zero (body : Nat → α → StateM σ α) (start : Nat)
    (accumulator : α) (initial : σ) :
    runRange body start 0 accumulator initial = (accumulator, initial) := rfl

theorem runRange_succ (body : Nat → α → StateM σ α) (start count : Nat)
    (accumulator : α) (initial : σ) :
    runRange body start (count + 1) accumulator initial =
      runRange body (start + 1) count
        (body start accumulator initial).1 (body start accumulator initial).2 := by
  simp only [runRange, List.range'_succ, List.forIn_cons]
  rfl

/-- A native bounded loop evaluates to the same state and accumulator as the
core loop. The relation permits arbitrary scratch locals. The compiler proves
the guard and one iteration; induction supplies every finite iteration. -/
theorem range_eval
    {functions : Module} {effects : Effects σ} {condition : Cond} {statement : Stmt}
    (body : Nat → α → StateM σ α) (represented : Nat → α → Locals → Prop)
    (limit : Nat)
    (guard : ∀ index accumulator locals, index ≤ limit →
      represented index accumulator locals →
      condition.eval locals = some (decide (index < limit)))
    (iteration : ∀ index accumulator initial locals, index < limit →
      represented index accumulator locals →
      ∃ next, Eval functions effects statement initial locals
          (body index accumulator initial).2 next ∧
        represented (index + 1) (body index accumulator initial).1 next)
    {start count : Nat} (counted : start + count = limit)
    (accumulator : α) (initial : σ) (locals : Locals)
    (related : represented start accumulator locals) :
    ∃ result, Eval functions effects (.loop condition statement) initial locals
        (runRange body start count accumulator initial).2 result ∧
      represented limit (runRange body start count accumulator initial).1 result := by
  induction count generalizing start accumulator initial locals with
  | zero =>
    have same : start = limit := by omega
    subst start
    refine ⟨locals, ?_, ?_⟩
    · exact .done (by simpa using guard limit accumulator locals (by omega) related)
    · exact related
  | succ count induction =>
    have before : start < limit := by omega
    obtain ⟨next, executed, nextRelated⟩ :=
      iteration start accumulator initial locals before related
    obtain ⟨result, rest, finalRelated⟩ :=
      induction (start := start + 1) (by omega)
        (body start accumulator initial).1 (body start accumulator initial).2 next nextRelated
    refine ⟨result, ?_, ?_⟩
    · rw [runRange_succ]
      exact .step (by simpa [before] using guard start accumulator locals (by omega) related)
        executed rest
    · rw [runRange_succ]
      exact finalRelated

/-- Direct form for ordinary `for index in List.range limit` in `StateM`. -/
theorem listRange_eval
    {functions : Module} {effects : Effects σ} {condition : Cond} {statement : Stmt}
    (body : Nat → α → StateM σ α) (represented : Nat → α → Locals → Prop)
    (limit : Nat)
    (guard : ∀ index accumulator locals, index ≤ limit →
      represented index accumulator locals →
      condition.eval locals = some (decide (index < limit)))
    (iteration : ∀ index accumulator initial locals, index < limit →
      represented index accumulator locals →
      ∃ next, Eval functions effects statement initial locals
          (body index accumulator initial).2 next ∧
        represented (index + 1) (body index accumulator initial).1 next)
    (accumulator : α) (initial : σ) (locals : Locals)
    (related : represented 0 accumulator locals) :
    let native := (forIn (List.range limit) accumulator fun index current => do
      return .yield (← body index current)) initial
    ∃ result, Eval functions effects (.loop condition statement) initial locals native.2 result ∧
      represented limit native.1 result := by
  simpa only [runRange, List.range_eq_range'] using
    range_eval body represented limit guard iteration (start := 0) (count := limit)
      (by omega) accumulator initial locals related

/-- Lean's range notation has the same native semantics as the list iterator. -/
theorem legacyRange_forIn_eq {m : Type → Type} [Monad m]
    (body : Nat → α → m (ForInStep α)) (limit : Nat) (accumulator : α) :
    forIn ({ stop := limit, step_pos := Nat.zero_lt_one } : Std.Legacy.Range)
        accumulator body =
      forIn (List.range limit) accumulator body := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
    List.range_eq_range']

theorem legacyRange_eq
    (body : Nat → α → StateM σ α) (limit : Nat) (accumulator : α) :
    (forIn ({ stop := limit, step_pos := Nat.zero_lt_one } : Std.Legacy.Range)
      accumulator fun index current => do return .yield (← body index current)) =
      runRange body 0 limit accumulator := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rfl

theorem runRange_pure (body : Nat → α → α) (start count : Nat)
    (accumulator : α) (initial : σ) :
    runRange (fun index current => pure (body index current)) start count accumulator initial =
      (forIn (m := Id) (List.range' start count) accumulator
        (fun index current => pure (.yield (body index current))), initial) := by
  induction count generalizing start accumulator with
  | zero => rfl
  | succ count induction =>
    rw [runRange_succ]
    simp only [List.range'_succ, List.forIn_cons]
    exact induction (start + 1) (body start accumulator)

/-- The same bridge for an ordinary pure `for` loop. Native arithmetic in the
body is unchanged; the generated body proof establishes its core evaluation. -/
theorem listRange_pure_eval
    {functions : Module} {effects : Effects σ} {condition : Cond} {statement : Stmt}
    (body : Nat → α → α) (represented : Nat → α → Locals → Prop)
    (limit : Nat)
    (guard : ∀ index accumulator locals, index ≤ limit →
      represented index accumulator locals →
      condition.eval locals = some (decide (index < limit)))
    (iteration : ∀ index accumulator initial locals, index < limit →
      represented index accumulator locals →
      ∃ next, Eval functions effects statement initial locals initial next ∧
        represented (index + 1) (body index accumulator) next)
    (accumulator : α) (initial : σ) (locals : Locals)
    (related : represented 0 accumulator locals) :
    ∃ result, Eval functions effects (.loop condition statement) initial locals initial result ∧
      represented limit
        (forIn (m := Id) (List.range limit) accumulator
          (fun index current => pure (.yield (body index current)))) result := by
  have evaluated := range_eval (fun index current => (pure (body index current) : StateM σ α))
    represented limit guard iteration (start := 0) (count := limit)
    (by omega) accumulator initial locals related
  rw [runRange_pure] at evaluated
  simpa only [List.range_eq_range'] using evaluated

/-- A counter bounded by a source word is represented exactly, including the
final counter after the last iteration. -/
theorem counter_toNat (limit : UInt64) (index : Nat) (bound : index ≤ limit.toNat) :
    (UInt64.ofNat index).toNat = index :=
  UInt64.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt bound limit.toBitVec.isLt)

theorem counter_lt (limit : UInt64) (index : Nat) (bound : index ≤ limit.toNat) :
    decide (UInt64.ofNat index < limit) = decide (index < limit.toNat) := by
  simp only [UInt64.lt_iff_toNat_lt, counter_toNat limit index bound]

theorem counter_succ (index : Nat) :
    UInt64.ofNat index + 1 = UInt64.ofNat (index + 1) := by
  simp only [UInt64.ofNat_add]
  rfl

end LeanExe.Core.NativeLoop
