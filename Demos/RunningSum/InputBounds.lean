import Demos.RunningSum.StreamModel

namespace Demos.RunningSum.StreamModel

theorem safe_append_iff (state : State) (a b : List UInt64) :
    Safe state (a ++ b) ↔ Safe state a ∧
      ∀ next, consume state a = .ok next → Safe next b := by
  induction a generalizing state with
  | nil => simp [Safe]
  | cons byte rest ih =>
      constructor
      · intro safe
        refine ⟨⟨safe.1, ?_⟩, ?_⟩
        · intro next executed
          exact ((ih next).mp (safe.2 next executed)).1
        · intro next executed
          cases step : consumeByte state byte with
          | error code =>
              simp [consume_cons, step, bind, Except.bind] at executed
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

def integerDigitCount (value : Int) : Nat := (Nat.digits 10 value.natAbs).length

structure BoundsFrom (total : Int) (inputs : List (Array UInt64)) : Prop where
  lines : ∀ input ∈ inputs, input.size + 3 < UInt64.size
  totals : ∀ prior, prior <+: inputs →
    integerDigitCount (total + (prior.map lineInteger).sum) + 3 < UInt64.size

def InputBounds (inputs : List (Array UInt64)) : Prop := BoundsFrom 0 inputs

theorem BoundsFrom.current {total : Int} {inputs : List (Array UInt64)}
    (bounds : BoundsFrom total inputs) : integerDigitCount total + 3 < UInt64.size := by
  simpa using bounds.totals [] List.nil_prefix

theorem BoundsFrom.tail {total : Int} {input : Array UInt64} {inputs : List (Array UInt64)}
    (bounds : BoundsFrom total (input :: inputs)) :
    BoundsFrom (total + lineInteger input) inputs := by
  refine ⟨fun next member => bounds.lines next (List.mem_cons_of_mem _ member), ?_⟩
  intro prior isPrefix
  have bound := bounds.totals (input :: prior)
    (List.cons_prefix_cons.mpr ⟨rfl, isPrefix⟩)
  simpa only [List.map_cons, List.sum_cons, add_assoc] using bound

theorem decimal_digitCount (number : Decimal) (normal : number.Valid) :
    integerDigitCount number.value = number.digits.size := by
  unfold integerDigitCount Decimal.value
  cases number.negative <;> simp only [Bool.false_eq_true, ↓reduceIte,
    Int.natAbs_neg, Int.natAbs_natCast, normal_natDigits number.digits normal,
    List.length_map, List.length_reverse, Array.length_toList]

def withTail (inputs : List (Array UInt64)) (pending : Array UInt64) :
    List (Array UInt64) := inputs ++ if pending.size = 0 then [] else [pending]

theorem Lines.pending_size_bound {pending bytes inputs tail}
    (trace : Lines pending bytes inputs tail)
    (lineBounds : ∀ input ∈ inputs, input.size + 3 < UInt64.size)
    (tailBound : tail.size + 3 < UInt64.size) : pending.size + 3 < UInt64.size := by
  induction trace with
  | nil pending => exact tailBound
  | byte byte notLf rest ih =>
      have next := ih lineBounds
      simp only [Array.size_push] at next
      omega
  | newline valid rest ih => exact lineBounds _ List.mem_cons_self

theorem room_of_lines {pending bytes inputs tail}
    (trace : Lines pending bytes inputs tail) (state : State)
    (pendingEq : state.pending = pending) (normal : state.total.Valid)
    (bounds : BoundsFrom state.total.value (withTail inputs tail)) : Room state := by
  have totalBound := bounds.current
  rw [decimal_digitCount state.total normal] at totalBound
  have lineBounds : ∀ input ∈ inputs, input.size + 3 < UInt64.size := by
    intro input member
    exact bounds.lines input (List.mem_append_left _ member)
  have tailBound : tail.size + 3 < UInt64.size := by
    by_cases empty : tail.size = 0
    · simp only [empty]
      decide
    · apply bounds.lines tail
      simp [withTail, empty]
  have pendingBound := trace.pending_size_bound lineBounds tailBound
  unfold Room
  rw [pendingEq]
  omega

theorem Lines.safe_and_finalRoom {pending bytes inputs tail}
    (trace : Lines pending bytes inputs tail) (state : State)
    (pendingEq : state.pending = pending) (normal : state.total.Valid)
    (bounds : BoundsFrom state.total.value (withTail inputs tail)) :
    Safe state bytes ∧
      ∀ next, consume state bytes = .ok next → next.total.Valid ∧ Room next := by
  induction trace generalizing state with
  | nil pending =>
      refine ⟨trivial, ?_⟩
      intro next executed
      have same : next = state := by simpa using executed.symm
      subst next
      exact ⟨normal, room_of_lines (.nil pending) state pendingEq normal bounds⟩
  | byte byte notLf rest ih =>
      let middle : State := { state with pending := state.pending.push byte }
      have byteStep : consumeByte state byte = .ok middle := by
        simp [consumeByte, notLf, middle]
      obtain ⟨nextSafe, finalRoom⟩ := ih middle (by simp [middle, pendingEq]) normal bounds
      constructor
      · refine ⟨fun newline => False.elim (notLf newline), ?_⟩
        intro next executed
        rw [byteStep] at executed
        cases executed
        exact nextSafe
      · intro next executed
        apply finalRoom next
        simpa [consume_cons, byteStep, bind, Except.bind] using executed
  | newline valid rest ih =>
      have room := room_of_lines (.newline valid rest) state pendingEq normal bounds
      obtain ⟨middle, _, emitted, middleNormal, _, middleValue, middlePending, _, _⟩ :=
        emitLine_correct state normal room (pendingEq ▸ valid)
      have byteStep : consumeByte state 10 = .ok middle := by
        simpa [consumeByte] using emitted
      have nextBounds := BoundsFrom.tail bounds
      rw [← pendingEq, ← middleValue] at nextBounds
      obtain ⟨nextSafe, finalRoom⟩ := ih middle middlePending middleNormal nextBounds
      constructor
      · refine ⟨fun _ => room, ?_⟩
        intro next executed
        rw [byteStep] at executed
        cases executed
        exact nextSafe
      · intro next executed
        apply finalRoom next
        simpa [consume_cons, byteStep, bind, Except.bind] using executed

theorem validInput_safe_and_finalRoom (bytes : List UInt64) (inputs : List (Array UInt64))
    (valid : ValidInput bytes inputs) (bounds : InputBounds inputs) :
    Safe initial bytes ∧ ∀ state, consume initial bytes = .ok state → Room state := by
  obtain ⟨complete, pending, trace, last⟩ := valid
  have inputsEq : inputs = withTail complete pending := by
    unfold withTail
    split_ifs with empty
    · simpa only [empty, ↓reduceIte, List.append_nil] using last
    · simp only [empty, ↓reduceIte] at last
      exact last.2
  have proof := trace.safe_and_finalRoom initial rfl zero_valid
    (by simpa only [InputBounds, initial, zero_value, ← inputsEq] using bounds)
  exact ⟨proof.1, fun state executed => (proof.2 state executed).2⟩

theorem stream_correct_of_inputBounds (bytes : List UInt64) (inputs : List (Array UInt64))
    (valid : ValidInput bytes inputs) (bounds : InputBounds inputs) :
    ∃ state final, consume initial bytes = .ok state ∧ finish state = .ok final ∧
      List.Forall₂ DecimalOutput (prefixSums 0 inputs) final.output ∧
      final.total.value = (inputs.map lineInteger).sum := by
  obtain ⟨safe, finalRoom⟩ := validInput_safe_and_finalRoom bytes inputs valid bounds
  exact stream_correct bytes inputs valid safe finalRoom

end Demos.RunningSum.StreamModel
