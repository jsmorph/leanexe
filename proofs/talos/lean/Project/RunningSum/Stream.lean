import Project.RunningSum.Render
import Mathlib.Data.List.Forall2

namespace Project.RunningSum

open LeanExe.Examples.RunningSum (Decimal parse add render)

structure StreamState where
  total : Decimal
  pending : ByteArray
  output : List ByteArray

def emitLine (state : StreamState) : Except UInt32 StreamState :=
  match parse state.pending with
  | none => .error 28
  | some value =>
      let next := add state.total value
      .ok ⟨next, ByteArray.empty, state.output ++ [render next]⟩

def consumeByte (state : StreamState) (byte : UInt8) : Except UInt32 StreamState :=
  if byte == 10 then emitLine state
  else .ok { state with pending := state.pending.push byte }

def consume (state : StreamState) (bytes : List UInt8) : Except UInt32 StreamState :=
  bytes.foldlM consumeByte state

def finish (state : StreamState) : Except UInt32 StreamState :=
  if state.pending.size == 0 then .ok state else emitLine state

def prefixSums (total : Int) : List ByteArray → List Int
  | [] => []
  | input :: rest =>
      let next := total + lineInteger input
      next :: prefixSums next rest

inductive Lines : ByteArray → List UInt8 → List ByteArray → ByteArray → Prop
  | nil (pending) : Lines pending [] [] pending
  | byte {pending bytes lines tail} (byte : UInt8) (hne : byte ≠ 10)
      (rest : Lines (pending.push byte) bytes lines tail) :
      Lines pending (byte :: bytes) lines tail
  | newline {pending bytes lines tail} (valid : ValidLine pending)
      (rest : Lines ByteArray.empty bytes lines tail) :
      Lines pending (10 :: bytes) (pending :: lines) tail

theorem consume_nil (state : StreamState) : consume state [] = .ok state := rfl

theorem consume_cons (state : StreamState) (byte : UInt8) (bytes : List UInt8) :
    consume state (byte :: bytes) = consumeByte state byte >>= fun next => consume next bytes := rfl

theorem consume_append (state : StreamState) (a b : List UInt8) :
    consume state (a ++ b) = consume state a >>= fun next => consume next b := by
  induction a generalizing state with
  | nil => rfl
  | cons byte rest ih =>
    simp only [List.cons_append, consume_cons, ih]
    cases consumeByte state byte <;> rfl

theorem emitLine_correct (state : StreamState) (hc : Canonical state.total.digits)
    (hv : ValidLine state.pending) :
    ∃ next out, emitLine state = .ok next ∧
      Canonical next.total.digits ∧
      integer next.total = integer state.total + lineInteger state.pending ∧
      next.pending = ByteArray.empty ∧ next.output = state.output ++ [out] ∧
      DecimalOutput (integer next.total) out := by
  obtain ⟨value, hp, hn, hs, ho⟩ := line_add_correct state.total hc state.pending hv
  refine ⟨⟨add state.total value, ByteArray.empty,
    state.output ++ [render (add state.total value)]⟩, render (add state.total value), ?_⟩
  exact ⟨by simp [emitLine, hp], hn, hs, rfl, rfl, hs ▸ ho⟩

theorem consume_correct {pending bytes inputs tail}
    (trace : Lines pending bytes inputs tail) (state : StreamState)
    (hp : state.pending = pending) (hc : Canonical state.total.digits) :
    ∃ next output, consume state bytes = .ok next ∧
      Canonical next.total.digits ∧ next.pending = tail ∧
      next.output = state.output ++ output ∧
      List.Forall₂ DecimalOutput (prefixSums (integer state.total) inputs) output ∧
      integer next.total = integer state.total + (inputs.map lineInteger).sum := by
  induction trace generalizing state with
  | nil pending =>
    refine ⟨state, [], rfl, hc, hp, ?_, .nil, ?_⟩ <;> simp
  | byte byte hne rest ih =>
    have hb : (byte == 10) = false := by simp [hne]
    obtain ⟨next, output, he, hn, ht, ho, houts, hsum⟩ :=
      ih { state with pending := state.pending.push byte } (by simp [hp]) hc
    refine ⟨next, output, ?_, hn, ht, ho, houts, hsum⟩
    simpa [consume_cons, consumeByte, hb, bind, Except.bind] using he
  | newline valid rest ih =>
    obtain ⟨mid, out, he, hm, hv, hpending, hout, hd⟩ := emitLine_correct state hc (hp ▸ valid)
    obtain ⟨next, output, he', hn, ht, ho, houts, hsum⟩ := ih mid hpending hm
    refine ⟨next, out :: output, ?_, hn, ht, ?_, ?_, ?_⟩
    · simp [consume_cons, consumeByte, he, he', bind, Except.bind]
    · simp [ho, hout, List.append_assoc]
    · simp only [prefixSums, ← hp, ← hv]
      exact .cons hd houts
    · simp only [List.map_cons, List.sum_cons, ← hp]
      omega

#print axioms consume_correct

def consumeChunks (state : StreamState) (chunks : List ByteArray) : Except UInt32 StreamState :=
  chunks.foldlM (fun state chunk => consume state chunk.data.toList) state

theorem consumeChunks_eq (state : StreamState) (chunks : List ByteArray) :
    consumeChunks state chunks = consume state (chunks.flatMap (fun chunk => chunk.data.toList)) := by
  induction chunks generalizing state with
  | nil => rfl
  | cons chunk chunks ih =>
    simp only [consumeChunks, List.foldlM_cons, List.flatMap_cons, consume_append]
    cases consume state chunk.data.toList with
    | error code => rfl
    | ok next => exact ih next

def initial : StreamState := ⟨⟨false, ByteArray.empty⟩, ByteArray.empty, []⟩

def ValidInput (bytes : List UInt8) (inputs : List ByteArray) : Prop :=
  ∃ complete pending, Lines ByteArray.empty bytes complete pending ∧
    if pending.size = 0 then inputs = complete
    else ValidLine pending ∧ inputs = complete ++ [pending]

theorem prefixSums_append (total : Int) (a b : List ByteArray) :
    prefixSums total (a ++ b) = prefixSums total a ++
      prefixSums (total + (a.map lineInteger).sum) b := by
  induction a generalizing total with
  | nil => simp [prefixSums]
  | cons input rest ih => simp [prefixSums, ih, add_assoc]

theorem stream_correct (bytes : List UInt8) (inputs : List ByteArray)
    (h : ValidInput bytes inputs) :
    ∃ state final, consume initial bytes = .ok state ∧ finish state = .ok final ∧
      List.Forall₂ DecimalOutput (prefixSums 0 inputs) final.output ∧
      integer final.total = (inputs.map lineInteger).sum := by
  obtain ⟨complete, pending, hlines, hend⟩ := h
  have hc : Canonical initial.total.digits := by
    constructor
    · intro i hi
      simp [initial] at hi
    · left; rfl
  obtain ⟨state, output, hs, hc, hp, ho, hout, hsum⟩ := consume_correct hlines initial rfl hc
  have hz : integer initial.total = 0 := rfl
  rw [hz] at hout hsum
  by_cases hempty : pending.size = 0
  · simp only [hempty, ↓reduceIte] at hend
    subst inputs
    refine ⟨state, state, hs, ?_, ?_, ?_⟩
    · simp [finish, hp, hempty]
    · simpa only [ho, initial, List.nil_append] using hout
    · simpa using hsum
  · simp only [hempty, ↓reduceIte] at hend
    obtain ⟨hv, rfl⟩ := hend
    obtain ⟨final, out, hf, _, hval, _, hfout, hd⟩ := emitLine_correct state hc (hp ▸ hv)
    refine ⟨state, final, hs, ?_, ?_, ?_⟩
    · simp [finish, hp, hempty, hf]
    · rw [hfout, ho]
      simp only [initial, List.nil_append]
      rw [prefixSums_append]
      apply List.rel_append
      · exact hout
      · have he : integer final.total = (complete.map lineInteger).sum + lineInteger pending := by
          rw [hval, hsum, hp, zero_add]
        simpa [prefixSums, he] using List.Forall₂.cons hd List.Forall₂.nil
    · simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero]
      rw [hval, hsum, hp, zero_add]

#print axioms consumeChunks_eq
#print axioms stream_correct

end Project.RunningSum
