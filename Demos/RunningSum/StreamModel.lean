import Demos.RunningSum.Addition
import Demos.RunningSum.Parsing
import Demos.RunningSum.Rendering
import Mathlib.Data.List.Forall2

namespace Demos.RunningSum.StreamModel

structure State where
  total : Decimal
  pending : Array UInt64
  output : List LeanExe.Bytes

def emitLine (state : State) : Except UInt64 State :=
  let parsed := parse state.pending
  if parsed.valid then
    let total := add state.total parsed.value
    .ok ⟨total, #[], state.output ++ [render total]⟩
  else .error 28

def consumeByte (state : State) (byte : UInt64) : Except UInt64 State :=
  if byte == 10 then emitLine state
  else .ok { state with pending := state.pending.push byte }

def consume (state : State) (bytes : List UInt64) : Except UInt64 State :=
  bytes.foldlM consumeByte state

def finish (state : State) : Except UInt64 State :=
  if state.pending.size = 0 then .ok state else emitLine state

def Room (state : State) : Prop :=
  max state.total.digits.size state.pending.size + 3 < UInt64.size

def Safe : State → List UInt64 → Prop
  | _, [] => True
  | state, byte :: bytes =>
      (byte = 10 → Room state) ∧
        ∀ next, consumeByte state byte = .ok next → Safe next bytes

def prefixSums (total : Int) : List (Array UInt64) → List Int
  | [] => []
  | input :: rest =>
      let next := total + lineInteger input
      next :: prefixSums next rest

inductive Lines : Array UInt64 → List UInt64 → List (Array UInt64) → Array UInt64 → Prop
  | nil (pending) : Lines pending [] [] pending
  | byte {pending bytes lines tail} (byte : UInt64) (notLf : byte ≠ 10)
      (rest : Lines (pending.push byte) bytes lines tail) :
      Lines pending (byte :: bytes) lines tail
  | newline {pending bytes lines tail} (valid : ValidLine pending)
      (rest : Lines #[] bytes lines tail) :
      Lines pending (10 :: bytes) (pending :: lines) tail

@[simp] theorem consume_nil (state : State) : consume state [] = .ok state := rfl

theorem consume_cons (state : State) (byte : UInt64) (bytes : List UInt64) :
    consume state (byte :: bytes) = consumeByte state byte >>= fun next => consume next bytes := rfl

theorem consume_append (state : State) (a b : List UInt64) :
    consume state (a ++ b) = consume state a >>= fun next => consume next b := by
  induction a generalizing state with
  | nil => rfl
  | cons byte rest ih =>
      simp only [List.cons_append, consume_cons, ih]
      cases consumeByte state byte <;> rfl

theorem emitLine_correct (state : State) (normal : state.total.Valid) (room : Room state)
    (valid : ValidLine state.pending) :
    ∃ next out, emitLine state = .ok next ∧ next.total.Valid ∧ next.total.Fits ∧
      next.total.value = state.total.value + lineInteger state.pending ∧
      next.pending = #[] ∧ next.output = state.output ++ [out] ∧
      DecimalOutput next.total.value out := by
  have inputBound : state.pending.size < UInt64.size := by
    unfold Room at room
    omega
  have accepted := (parse_valid_iff state.pending inputBound).mpr valid
  have parsedNormal := parse_valid state.pending inputBound accepted
  have parsedSize := parse_digits_size_le state.pending inputBound
  have addBound : max state.total.digits.size (parse state.pending).value.digits.size + 3 <
      UInt64.size := by
    unfold Room at room
    omega
  obtain ⟨sumNormal, sumFits, sumValue, sumSize⟩ :=
    add_correct state.total (parse state.pending).value normal parsedNormal addBound
  rw [parse_value state.pending inputBound] at sumValue
  let total := add state.total (parse state.pending).value
  refine ⟨⟨total, #[], state.output ++ [render total]⟩, render total,
    ?_, sumNormal, sumFits, sumValue, rfl, rfl, ?_⟩
  · simp [emitLine, accepted, total]
  · exact render_correct total sumNormal sumFits

theorem consume_correct {pending bytes inputs tail}
    (trace : Lines pending bytes inputs tail) (state : State)
    (pendingEq : state.pending = pending) (normal : state.total.Valid)
    (safe : Safe state bytes) :
    ∃ next output, consume state bytes = .ok next ∧ next.total.Valid ∧ next.pending = tail ∧
      next.output = state.output ++ output ∧
      List.Forall₂ DecimalOutput (prefixSums state.total.value inputs) output ∧
      next.total.value = state.total.value + (inputs.map lineInteger).sum := by
  induction trace generalizing state with
  | nil pending =>
      refine ⟨state, [], rfl, normal, pendingEq, ?_, .nil, ?_⟩ <;> simp
  | byte byte notLf rest ih =>
      have byteStep : consumeByte state byte =
          .ok { state with pending := state.pending.push byte } := by
        simp [consumeByte, notLf]
      have nextSafe := safe.2 _ byteStep
      obtain ⟨next, output, executed, nextNormal, nextPending, nextOutput, outputs, sum⟩ :=
        ih { state with pending := state.pending.push byte } (by simp [pendingEq]) normal nextSafe
      refine ⟨next, output, ?_, nextNormal, nextPending, nextOutput, outputs, sum⟩
      simpa [consume_cons, byteStep, bind, Except.bind] using executed
  | newline valid rest ih =>
      obtain ⟨middle, out, emitted, middleNormal, _, middleValue, middlePending,
        middleOutput, encoded⟩ := emitLine_correct state normal (safe.1 rfl) (pendingEq ▸ valid)
      have byteStep : consumeByte state 10 = .ok middle := by
        simpa [consumeByte] using emitted
      obtain ⟨next, output, executed, nextNormal, nextPending, nextOutput, outputs, sum⟩ :=
        ih middle middlePending middleNormal (safe.2 _ byteStep)
      refine ⟨next, out :: output, ?_, nextNormal, nextPending, ?_, ?_, ?_⟩
      · simpa [consume_cons, byteStep, bind, Except.bind] using executed
      · simp [nextOutput, middleOutput, List.append_assoc]
      · simp only [prefixSums, ← pendingEq, ← middleValue]
        exact .cons encoded outputs
      · simp only [List.map_cons, List.sum_cons, ← pendingEq]
        omega

def consumeChunks (state : State) (chunks : List LeanExe.Bytes) : Except UInt64 State :=
  chunks.foldlM (fun state chunk =>
    consume state (chunk.data.data.toList.map UInt8.toUInt64)) state

theorem consumeChunks_eq (state : State) (chunks : List LeanExe.Bytes) :
    consumeChunks state chunks =
      consume state (chunks.flatMap fun chunk => chunk.data.data.toList.map UInt8.toUInt64) := by
  induction chunks generalizing state with
  | nil => rfl
  | cons chunk chunks ih =>
      simp only [consumeChunks, List.foldlM_cons, List.flatMap_cons, consume_append]
      cases consume state (chunk.data.data.toList.map UInt8.toUInt64) with
      | error code => rfl
      | ok next => exact ih next

def initial : State := ⟨zero, #[], []⟩

def ValidInput (bytes : List UInt64) (inputs : List (Array UInt64)) : Prop :=
  ∃ complete pending, Lines #[] bytes complete pending ∧
    if pending.size = 0 then inputs = complete
    else ValidLine pending ∧ inputs = complete ++ [pending]

theorem prefixSums_append (total : Int) (a b : List (Array UInt64)) :
    prefixSums total (a ++ b) = prefixSums total a ++
      prefixSums (total + (a.map lineInteger).sum) b := by
  induction a generalizing total with
  | nil => simp [prefixSums]
  | cons input rest ih => simp [prefixSums, ih, add_assoc]

theorem stream_correct (bytes : List UInt64) (inputs : List (Array UInt64))
    (valid : ValidInput bytes inputs) (safe : Safe initial bytes)
    (finalRoom : ∀ state, consume initial bytes = .ok state → Room state) :
    ∃ state final, consume initial bytes = .ok state ∧ finish state = .ok final ∧
      List.Forall₂ DecimalOutput (prefixSums 0 inputs) final.output ∧
      final.total.value = (inputs.map lineInteger).sum := by
  obtain ⟨complete, pending, lines, last⟩ := valid
  obtain ⟨state, output, executed, normal, pendingEq, outputEq, outputs, sum⟩ :=
    consume_correct lines initial rfl zero_valid safe
  have initialValue : initial.total.value = 0 := zero_value
  rw [initialValue] at outputs sum
  by_cases empty : pending.size = 0
  · simp only [empty, ↓reduceIte] at last
    subst inputs
    refine ⟨state, state, executed, ?_, ?_, ?_⟩
    · simp [finish, pendingEq, empty]
    · simpa only [outputEq, initial, List.nil_append] using outputs
    · simpa using sum
  · simp only [empty, ↓reduceIte] at last
    obtain ⟨lastValid, rfl⟩ := last
    obtain ⟨final, out, emitted, _, _, finalValue, _, finalOutput, encoded⟩ :=
      emitLine_correct state normal (finalRoom state executed) (pendingEq ▸ lastValid)
    refine ⟨state, final, executed, ?_, ?_, ?_⟩
    · simp [finish, pendingEq, empty, emitted]
    · rw [finalOutput, outputEq]
      simp only [initial, List.nil_append]
      rw [prefixSums_append]
      apply List.rel_append
      · exact outputs
      · have value : final.total.value = (complete.map lineInteger).sum + lineInteger pending := by
          rw [finalValue, sum, pendingEq, zero_add]
        simpa [prefixSums, value] using List.Forall₂.cons encoded List.Forall₂.nil
    · simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero]
      rw [finalValue, sum, pendingEq, zero_add]

end Demos.RunningSum.StreamModel
