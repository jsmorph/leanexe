import Demos.StreamFold.Interface

namespace Demos.StreamFold.Model

variable {Acc : Type} {kernel : Kernel Acc}

@[simp] theorem consume_nil (state : State Acc) : consume kernel state [] = .ok state := rfl

theorem consume_cons (state : State Acc) (byte : UInt64) (bytes : List UInt64) :
    consume kernel state (byte :: bytes) =
      consumeByte kernel state byte >>= fun next => consume kernel next bytes := rfl

theorem consume_append (state : State Acc) (a b : List UInt64) :
    consume kernel state (a ++ b) =
      consume kernel state a >>= fun next => consume kernel next b := by
  induction a generalizing state with
  | nil => rfl
  | cons byte rest ih =>
      simp only [List.cons_append, consume_cons, ih]
      cases consumeByte kernel state byte <;> rfl

theorem safe_append_iff (spec : KernelSpec kernel) (state : State Acc) (a b : List UInt64) :
    Safe spec state (a ++ b) ↔ Safe spec state a ∧
      ∀ next, consume kernel state a = .ok next → Safe spec next b := by
  induction a generalizing state with
  | nil => simp [Safe]
  | cons byte rest ih =>
      constructor
      · intro safe
        refine ⟨⟨safe.1, ?_⟩, ?_⟩
        · intro next executed
          exact ((ih next).mp (safe.2 next executed)).1
        · intro next executed
          cases step : consumeByte kernel state byte with
          | error stopped => simp [consume_cons, step, bind, Except.bind] at executed
          | ok middle =>
              apply ((ih middle).mp (safe.2 middle step)).2 next
              simpa [consume_cons, step, bind, Except.bind] using executed
      · rintro ⟨safe, tailSafe⟩
        refine ⟨safe.1, ?_⟩
        intro middle executed
        apply (ih middle).mpr
        refine ⟨safe.2 middle executed, ?_⟩
        intro next restExecuted
        apply tailSafe next
        simpa [consume_cons, executed, bind, Except.bind] using restExecuted

theorem outcome_cons_ok {state next : State Acc} {byte : UInt64} (bytes : List UInt64)
    (step : consumeByte kernel state byte = .ok next) :
    outcome kernel state (byte :: bytes) = outcome kernel next bytes := by
  unfold outcome
  rw [consume_cons, step]
  rfl

theorem outcome_cons_error {state stopped : State Acc} {byte : UInt64} (bytes : List UInt64)
    (step : consumeByte kernel state byte = .error stopped) :
    outcome kernel state (byte :: bytes) = (stopped.output, 28) := by
  unfold outcome
  rw [consume_cons, step]
  rfl

theorem outcome_append_ok {state next : State Acc} {a : List UInt64} (b : List UInt64)
    (executed : consume kernel state a = .ok next) :
    outcome kernel state (a ++ b) = outcome kernel next b := by
  unfold outcome
  rw [consume_append, executed]
  rfl

theorem outcome_append_error {state stopped : State Acc} {a : List UInt64} (b : List UInt64)
    (executed : consume kernel state a = .error stopped) :
    outcome kernel state (a ++ b) = (stopped.output, 28) := by
  unfold outcome
  rw [consume_append, executed]
  rfl

/-- The lines of `bytes` after the partial line `pending`: each segment that LF ends, then the
final segment when it is nonempty. -/
def linesFrom (pending : Array UInt64) : List UInt64 → List (Array UInt64)
  | [] => if pending.size = 0 then [] else [pending]
  | byte :: bytes =>
      if byte == 10 then pending :: linesFrom #[] bytes else linesFrom (pending.push byte) bytes

def lines (bytes : List UInt64) : List (Array UInt64) := linesFrom #[] bytes

/-- The outputs of the kernel for `lines` from `total` before the first rejected line, and the
status: 0 when the kernel accepts every line and 28 when it rejects one. -/
def foldOutcome (kernel : Kernel Acc) (total : Acc) : List (Array UInt64) → List LeanExe.Bytes × UInt64
  | [] => ([], 0)
  | line :: rest =>
      let result := kernel total line
      if result.valid then
        let after := foldOutcome kernel result.total rest
        (result.output :: after.1, after.2)
      else ([], 28)

theorem outcome_lines (total : Acc) (pending : Array UInt64) (history : List LeanExe.Bytes)
    (bytes : List UInt64) :
    outcome kernel ⟨total, pending, history⟩ bytes =
      (history ++ (foldOutcome kernel total (linesFrom pending bytes)).1,
        (foldOutcome kernel total (linesFrom pending bytes)).2) := by
  induction bytes generalizing total pending history with
  | nil =>
      by_cases empty : pending.size = 0
      · simp [outcome, finish, empty, linesFrom, foldOutcome, bind, Except.bind]
      · cases accepted : (kernel total pending).valid <;>
          simp [outcome, finish, emitLine, empty, accepted, linesFrom, foldOutcome, bind,
            Except.bind]
  | cons byte bytes ih =>
      by_cases newline : byte = 10
      · subst newline
        cases accepted : (kernel total pending).valid with
        | false =>
            rw [outcome_cons_error (stopped := ⟨total, pending, history⟩) bytes
              (by simp [consumeByte, emitLine, accepted])]
            simp [linesFrom, foldOutcome, accepted]
        | true =>
            rw [outcome_cons_ok (next := ⟨(kernel total pending).total, #[],
              history ++ [(kernel total pending).output]⟩) bytes
              (by simp [consumeByte, emitLine, accepted]), ih]
            simp [linesFrom, foldOutcome, accepted]
      · rw [outcome_cons_ok (next := ⟨total, pending.push byte, history⟩) bytes
          (by simp [consumeByte, newline]), ih]
        simp [linesFrom, newline]

theorem outcome_initial (seed : Acc) (bytes : List UInt64) :
    outcome kernel (initial seed) bytes = foldOutcome kernel seed (lines bytes) := by
  rw [initial, outcome_lines]
  rfl

/-- `values` holds the values of the lines before the first line without a value, and `status`
is 0 when every line has a value and 28 when one does not. -/
inductive LineValues {α : Type} (Denotes : Array UInt64 → α → Prop) :
    List (Array UInt64) → List α → UInt64 → Prop
  | nil : LineValues Denotes [] [] 0
  | accept {line lines value values status} (denotes : Denotes line value)
      (rest : LineValues Denotes lines values status) :
      LineValues Denotes (line :: lines) (value :: values) status
  | reject {line lines} (invalid : ∀ value, ¬ Denotes line value) :
      LineValues Denotes (line :: lines) [] 28

theorem LineValues.unique {α : Type} {Denotes : Array UInt64 → α → Prop}
    (functional : ∀ {line a b}, Denotes line a → Denotes line b → a = b)
    {lines : List (Array UInt64)} {values others : List α} {status other : UInt64}
    (first : LineValues Denotes lines values status)
    (second : LineValues Denotes lines others other) : values = others ∧ status = other := by
  induction first generalizing others other with
  | nil =>
      cases second
      exact ⟨rfl, rfl⟩
  | accept denotes rest ih =>
      cases second with
      | accept otherDenotes otherRest =>
          obtain ⟨same, statusEq⟩ := ih otherRest
          exact ⟨by rw [functional denotes otherDenotes, same], statusEq⟩
      | reject invalid => exact (invalid _ denotes).elim
  | reject invalid =>
      cases second with
      | accept otherDenotes _ => exact (invalid _ otherDenotes).elim
      | reject _ => exact ⟨rfl, rfl⟩

theorem LineValues.status {α : Type} {Denotes : Array UInt64 → α → Prop}
    {lines : List (Array UInt64)} {values : List α} {status : UInt64}
    (run : LineValues Denotes lines values status) : status = 0 ∨ status = 28 := by
  induction run with
  | nil => exact Or.inl rfl
  | accept _ _ ih => exact ih
  | reject _ => exact Or.inr rfl

theorem LineValues.exitStatus {α : Type} {Denotes : Array UInt64 → α → Prop}
    {lines : List (Array UInt64)} {values : List α} {status : UInt64}
    (run : LineValues Denotes lines values status) : LeanExe.Wasi.exitStatus status = status := by
  induction run with
  | nil => rfl
  | accept _ _ ih => exact ih
  | reject _ => rfl

def LineRooms {kernel : Kernel Acc} (spec : KernelSpec kernel) (total : Acc) :
    List (Array UInt64) → Prop
  | [] => True
  | line :: rest => spec.Room total line ∧
      ((kernel total line).valid = true → LineRooms spec (kernel total line).total rest)

theorem linesFrom_newline (pending : Array UInt64) (bytes : List UInt64) :
    linesFrom pending (10 :: bytes) = pending :: linesFrom #[] bytes := by
  simp [linesFrom]

theorem linesFrom_byte (pending : Array UInt64) {byte : UInt64} (bytes : List UInt64)
    (notLf : byte ≠ 10) : linesFrom pending (byte :: bytes) = linesFrom (pending.push byte) bytes := by
  simp [linesFrom, notLf]

theorem safe_of_rooms (spec : KernelSpec kernel) (total : Acc) (pending : Array UInt64)
    (history : List LeanExe.Bytes) (bytes : List UInt64)
    (rooms : LineRooms spec total (linesFrom pending bytes)) :
    Safe spec ⟨total, pending, history⟩ bytes := by
  induction bytes generalizing total pending history with
  | nil => trivial
  | cons byte bytes ih =>
      by_cases newline : byte = 10
      · subst newline
        rw [linesFrom_newline] at rooms
        refine ⟨fun _ => rooms.1, ?_⟩
        intro next executed
        cases accepted : (kernel total pending).valid with
        | false => simp [consumeByte, emitLine, accepted] at executed
        | true =>
            have same : next =
                ⟨(kernel total pending).total, #[], history ++ [(kernel total pending).output]⟩ := by
              simpa [consumeByte, emitLine, accepted] using executed.symm
            subst next
            exact ih _ _ _ (rooms.2 accepted)
      · rw [linesFrom_byte pending bytes newline] at rooms
        refine ⟨fun lf => (newline lf).elim, ?_⟩
        intro next executed
        have same : next = ⟨total, pending.push byte, history⟩ := by
          simpa [consumeByte, newline] using executed.symm
        subst next
        exact ih _ _ _ rooms

theorem room_of_rooms (spec : KernelSpec kernel) (total : Acc) (pending : Array UInt64)
    (history : List LeanExe.Bytes) (bytes : List UInt64)
    (rooms : LineRooms spec total (linesFrom pending bytes)) {final : State Acc}
    (executed : consume kernel ⟨total, pending, history⟩ bytes = .ok final)
    (nonempty : final.pending.size ≠ 0) : spec.Room final.total final.pending := by
  induction bytes generalizing total pending history with
  | nil =>
      have same : final = ⟨total, pending, history⟩ := by simpa using executed.symm
      subst final
      have nonempty : pending.size ≠ 0 := nonempty
      have single : linesFrom pending [] = [pending] := by simp [linesFrom, nonempty]
      rw [single] at rooms
      exact rooms.1
  | cons byte bytes ih =>
      by_cases newline : byte = 10
      · subst newline
        rw [linesFrom_newline] at rooms
        cases accepted : (kernel total pending).valid with
        | false =>
            simp [consume_cons, consumeByte, emitLine, accepted, bind, Except.bind] at executed
        | true =>
            apply ih _ _ _ (rooms.2 accepted)
            simpa [consume_cons, consumeByte, emitLine, accepted, bind, Except.bind] using executed
      · rw [linesFrom_byte pending bytes newline] at rooms
        apply ih _ _ _ rooms
        simpa [consume_cons, consumeByte, newline, bind, Except.bind] using executed

end Demos.StreamFold.Model
