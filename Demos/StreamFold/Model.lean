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
          | error code => simp [consume_cons, step, bind, Except.bind] at executed
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

inductive Lines (validLine : Array UInt64 → Prop) :
    Array UInt64 → List UInt64 → List (Array UInt64) → Array UInt64 → Prop
  | nil (pending) : Lines validLine pending [] [] pending
  | byte {pending bytes lines tail} (byte : UInt64) (notLf : byte ≠ 10)
      (rest : Lines validLine (pending.push byte) bytes lines tail) :
      Lines validLine pending (byte :: bytes) lines tail
  | newline {pending bytes lines tail} (valid : validLine pending)
      (rest : Lines validLine #[] bytes lines tail) :
      Lines validLine pending (10 :: bytes) (pending :: lines) tail

def ValidInput (validLine : Array UInt64 → Prop) (bytes : List UInt64)
    (inputs : List (Array UInt64)) : Prop :=
  ∃ complete pending, Lines validLine #[] bytes complete pending ∧
    if pending.size = 0 then inputs = complete
    else validLine pending ∧ inputs = complete ++ [pending]

def foldLines (kernel : Kernel Acc) (total : Acc) :
    List (Array UInt64) → Except UInt64 (Acc × List LeanExe.Bytes)
  | [] => .ok (total, [])
  | line :: rest =>
      let result := kernel total line
      if result.valid then
        match foldLines kernel result.total rest with
        | .error code => .error code
        | .ok (final, output) => .ok (final, result.output :: output)
      else .error 28

theorem consume_lines {validLine pending bytes inputs tail}
    (trace : Lines validLine pending bytes inputs tail) (total : Acc) (history : List LeanExe.Bytes) :
    consume kernel ⟨total, pending, history⟩ bytes =
      match foldLines kernel total inputs with
      | .error code => .error code
      | .ok (final, output) => .ok ⟨final, tail, history ++ output⟩ := by
  induction trace generalizing total history with
  | nil pending => simp [foldLines]
  | @byte pending bytes lines tail byte notLf rest ih =>
      simpa [consume_cons, consumeByte, notLf, bind, Except.bind] using ih total history
  | @newline pending bytes lines tail valid rest ih =>
      cases accepted : (kernel total pending).valid with
      | false => simp [consume_cons, consumeByte, emitLine, foldLines, accepted, bind, Except.bind]
      | true =>
          simp only [consume_cons, consumeByte, beq_self_eq_true, ↓reduceIte, emitLine,
            accepted, foldLines]
          simp only [bind, Except.bind]
          rw [ih]
          cases foldLines kernel (kernel total pending).total lines with
          | error code => rfl
          | ok result =>
              rcases result with ⟨final, output⟩
              simp [List.append_assoc]

def LineRooms {kernel : Kernel Acc} (spec : KernelSpec kernel) (total : Acc) :
    List (Array UInt64) → Prop
  | [] => True
  | line :: rest => spec.Room total line ∧
      ((kernel total line).valid = true → LineRooms spec (kernel total line).total rest)

theorem safe_of_lines {validLine pending bytes inputs tail}
    (spec : KernelSpec kernel) (trace : Lines validLine pending bytes inputs tail)
    (total : Acc) (history : List LeanExe.Bytes) (rooms : LineRooms spec total inputs) :
    Safe spec ⟨total, pending, history⟩ bytes := by
  induction trace generalizing total history with
  | nil pending => trivial
  | @byte pending bytes lines tail byte notLf rest ih =>
      refine ⟨fun newline => (notLf newline).elim, ?_⟩
      intro next executed
      have same : next = ⟨total, pending.push byte, history⟩ := by
        simpa [consumeByte, notLf] using executed.symm
      subst next
      exact ih total history rooms
  | @newline pending bytes lines tail valid rest ih =>
      refine ⟨fun _ => rooms.1, ?_⟩
      intro next executed
      cases accepted : (kernel total pending).valid with
      | false => simp [consumeByte, emitLine, accepted] at executed
      | true =>
          have same : next =
              ⟨(kernel total pending).total, #[], history ++ [(kernel total pending).output]⟩ := by
            simpa [consumeByte, emitLine, accepted] using executed.symm
          subst next
          exact ih _ _ (rooms.2 accepted)

theorem foldLines_append (total : Acc) (first rest : List (Array UInt64)) :
    foldLines kernel total (first ++ rest) =
      match foldLines kernel total first with
      | .error code => .error code
      | .ok (middle, output) =>
          match foldLines kernel middle rest with
          | .error code => .error code
          | .ok (final, after) => .ok (final, output ++ after) := by
  induction first generalizing total with
  | nil =>
      simp only [List.nil_append, foldLines]
      cases foldLines kernel total rest <;> rfl
  | cons line first ih =>
      cases accepted : (kernel total line).valid with
      | false => simp [foldLines, accepted]
      | true =>
          simp only [List.cons_append, foldLines, accepted, ↓reduceIte]
          rw [ih]
          cases foldLines kernel (kernel total line).total first with
          | error code => rfl
          | ok result =>
              rcases result with ⟨middle, output⟩
              simp only
              cases foldLines kernel middle rest <;> rfl

theorem finish_consume_input {validLine bytes inputs}
    (valid : ValidInput validLine bytes inputs) (seed : Acc) :
    (consume kernel (initial seed) bytes >>= finish kernel) =
      match foldLines kernel seed inputs with
      | .error code => .error code
      | .ok (total, output) => .ok ⟨total, #[], output⟩ := by
  obtain ⟨complete, pending, trace, last⟩ := valid
  have consumed := consume_lines (kernel := kernel) trace seed []
  change consume kernel ⟨seed, #[], []⟩ bytes >>= finish kernel = _
  rw [consumed]
  by_cases empty : pending.size = 0
  · simp only [empty, ↓reduceIte] at last
    subst inputs
    cases foldLines kernel seed complete with
    | error code => rfl
    | ok result =>
        rcases result with ⟨total, output⟩
        have pendingEmpty : pending = #[] := Array.eq_empty_of_size_eq_zero empty
        simp [finish, pendingEmpty, bind, Except.bind]
  · simp only [empty, ↓reduceIte] at last
    obtain ⟨_, rfl⟩ := last
    rw [foldLines_append]
    cases foldLines kernel seed complete with
    | error code => rfl
    | ok result =>
        rcases result with ⟨total, output⟩
        cases accepted : (kernel total pending).valid <;>
          simp [finish, emitLine, empty, foldLines, accepted, bind, Except.bind]

theorem LineRooms.prefix (spec : KernelSpec kernel) (total : Acc)
    (first rest : List (Array UInt64)) (rooms : LineRooms spec total (first ++ rest)) :
    LineRooms spec total first := by
  induction first generalizing total with
  | nil => trivial
  | cons line first ih =>
      exact ⟨rooms.1, fun accepted => ih _ (rooms.2 accepted)⟩

theorem LineRooms.after_fold (spec : KernelSpec kernel) (total : Acc)
    (first rest : List (Array UInt64)) (rooms : LineRooms spec total (first ++ rest))
    {final output} (executed : foldLines kernel total first = .ok (final, output)) :
    LineRooms spec final rest := by
  induction first generalizing total final output with
  | nil =>
      cases executed
      exact rooms
  | cons line first ih =>
      cases accepted : (kernel total line).valid with
      | false => simp [foldLines, accepted] at executed
      | true =>
          cases next : foldLines kernel (kernel total line).total first with
          | error code => simp [foldLines, accepted, next] at executed
          | ok result =>
              rcases result with ⟨middle, outputs⟩
              have same : (middle, (kernel total line).output :: outputs) = (final, output) := by
                simpa [foldLines, accepted, next, bind, Except.bind] using executed
              have totalEq : middle = final := congrArg Prod.fst same
              rw [← totalEq]
              exact ih _ (rooms.2 accepted) next

theorem consume_lines_properties {validLine pending bytes inputs tail}
    (spec : KernelSpec kernel) (trace : Lines validLine pending bytes inputs tail)
    (total : Acc) (history : List LeanExe.Bytes) (rest : List (Array UInt64))
    (rooms : LineRooms spec total (inputs ++ rest)) {final}
    (executed : consume kernel ⟨total, pending, history⟩ bytes = .ok final) :
    final.pending = tail ∧ LineRooms spec final.total rest := by
  rw [consume_lines trace total history] at executed
  cases folded : foldLines kernel total inputs with
  | error code => simp [folded] at executed
  | ok result =>
      rcases result with ⟨next, output⟩
      have same : final = ⟨next, tail, history ++ output⟩ := by
        simpa [folded] using executed.symm
      subst final
      exact ⟨rfl, LineRooms.after_fold spec total inputs rest rooms folded⟩

theorem validInput_safe_and_finalRoom {validLine bytes inputs}
    (spec : KernelSpec kernel) (valid : ValidInput validLine bytes inputs) (seed : Acc)
    (rooms : LineRooms spec seed inputs) :
    Safe spec (initial seed) bytes ∧
      ∀ final, consume kernel (initial seed) bytes = .ok final →
        final.pending.size ≠ 0 → spec.Room final.total final.pending := by
  obtain ⟨complete, pending, trace, last⟩ := valid
  by_cases empty : pending.size = 0
  · simp only [empty, ↓reduceIte] at last
    subst inputs
    refine ⟨safe_of_lines spec trace seed [] rooms, ?_⟩
    intro final executed nonempty
    have facts := consume_lines_properties spec trace seed [] []
      (by simpa only [List.append_nil] using rooms) executed
    exact False.elim (nonempty (by rw [facts.1]; exact empty))
  · simp only [empty, ↓reduceIte] at last
    obtain ⟨_, rfl⟩ := last
    refine ⟨safe_of_lines spec trace seed [] (LineRooms.prefix spec seed complete [pending] rooms), ?_⟩
    intro final executed _
    obtain ⟨same, remaining⟩ := consume_lines_properties spec trace seed [] [pending] rooms executed
    simpa only [same] using remaining.1

end Demos.StreamFold.Model
