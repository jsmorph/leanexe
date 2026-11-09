import LeanExe.Requests.Records

/-!
Records delimited by zero bytes over a UART, through the program with requests.  Each record
travels encoded by Consistent Overhead Byte Stuffing (COBS; Cheshire and Baker, 1999), which
leaves no zero byte in the encoding, and is followed by a single `0x00`.  A segment is the list
of bytes before a `0x00`, since the last one.  `cobsEncode` transcribes the paper's `StuffData`,
and `cobsDecode` its `UnStuffData` with checks of each block and the removal of the zero that the
encoder appends to the data in its logical view.  `segments` splits a stream of bytes into its
complete segments, and `segResult` gives the result for a segment: an overflow when the segment
is longer than a maximum length, a decoding error when it is no encoding, and the record
otherwise.  `delimAnswers` runs a machine over the results of the nonempty segments and joins
its answers, each encoded and followed by a `0x00`.  `split` and `answerRun` append to the end of
a list at each segment, and compiled code computes them as `splitLinear` and `answerRunLinear`,
in time linear in the bytes and the segments, which the `csimp` theorems `split_eq_splitLinear`
and `answerRun_eq_answerRunLinear` prove equal to them.

F1 is `cobsDecode_encode` with `zero_not_mem_cobsEncode` and `length_cobsEncode`: decoding
inverts encoding for every record, the encoding holds no zero byte, and a record shorter than 254
bytes gains one byte.  `cobsDecode_eq_some_iff` states the converse, that a segment decodes to
`r` exactly when it is `cobsEncode r`, so the theorems' statements rest on `cobsEncode` alone.
F2 is `segments_append_zero`, by which the segments after a `0x00` do not depend on the bytes
before it, and `delimAnswers_encode`, by which a segment that equals the encoding of a record `r`
gives the machine `r` whatever bytes came before.

`delimTick` is a step that reads the bytes of a segment, stores up to `maxLen` of them and counts
the rest, and in the window of the `0x00` calls the machine once for a nonempty segment and then
writes the encoded answer and a `0x00`.  An empty segment gets no call and no answer.  F3 is
`delim_prefix`, the analog of `frame_prefix`: for every sequence `σ` of the values that the
reads return and every trace type with its `Bus`, the bytes that the first `n` windows write to
the transmit register begin `delimAnswers` of the bytes that those windows read from the receive
register.  `delim_answered` adds that when window `n` reads the receive register, those bytes are
all the answers, so no complete segment waits for its answer.  A compiled step relates to
`delimTick` through an abstraction that commutes with the step on the states of an invariant,
and `reqTrace_mapOn` carries the window traces, and with them F3, to its program.
-/

namespace LeanExe.Requests

open LeanExe.Native (readReq writeReq)

/-! ## Abstractions on an invariant -/

section

variable {G α : Type}

/-- A map `abs` of states that commutes with the steps on the states of an invariant `I`, which
the steps keep and the initial state satisfies, carries the run. -/
theorem reqRun_mapOn {G' : Type} {tick : G → UInt64 → G × UInt64}
    {tick' : G' → UInt64 → G' × UInt64} (abs : G → G') (I : G → Prop)
    (h : ∀ s v, I s → I (tick s v).1 ∧ tick' (abs s) v = (abs (tick s v).1, (tick s v).2))
    (s0 : G) (h0 : I s0) (σ : Nat → UInt32) :
    ∀ n, I (reqRun tick s0 σ n).state ∧
      (reqRun tick' (abs s0) σ n).state = abs (reqRun tick s0 σ n).state ∧
      (reqRun tick' (abs s0) σ n).last = (reqRun tick s0 σ n).last ∧
      (reqRun tick' (abs s0) σ n).reads = (reqRun tick s0 σ n).reads
  | 0 => ⟨h0, rfl, rfl, rfl⟩
  | n + 1 => by
      obtain ⟨hI, h1, h2, h3⟩ := reqRun_mapOn abs I h s0 h0 σ n
      obtain ⟨hI', he⟩ := h _ (reqRun tick s0 σ n).last hI
      simp only [reqRun, reqNext, h1, h2, h3, he]
      split <;> exact ⟨hI', rfl, rfl, rfl⟩

/-- A map `abs` of states that commutes with the steps on the states of an invariant that the
steps keep and the initial state satisfies leaves the window traces unchanged, as
`reqTrace_map` states for a map that commutes on every state. -/
theorem reqTrace_mapOn {B : Bus α} {G' : Type} {tick : G → UInt64 → G × UInt64}
    {tick' : G' → UInt64 → G' × UInt64} (abs : G → G') (I : G → Prop)
    (h : ∀ s v, I s → I (tick s v).1 ∧ tick' (abs s) v = (abs (tick s v).1, (tick s v).2))
    (s0 : G) (h0 : I s0) (σ : Nat → UInt32) :
    reqTrace B tick' (abs s0) σ = reqTrace B tick s0 σ := by
  funext n
  obtain ⟨hI, h1, h2, h3⟩ := reqRun_mapOn abs I h s0 h0 σ n
  simp only [reqTrace, reqEvent, h1, h2, h3, (h _ _ hI).2]

end

/-! ## COBS -/

/-- The bytes that `StuffData` writes for the data bytes `bs` when the current block holds the
nonzero bytes `blk`.  A block ends with the code `blk.length + 1` at a zero byte and at the end of
the data, and with the code `0xFF` after 254 nonzero bytes. -/
def cobsStuff : List UInt8 → List UInt8 → List UInt8
  | [], blk => UInt8.ofNat (blk.length + 1) :: blk
  | b :: bs, blk =>
      if b = 0 then (UInt8.ofNat (blk.length + 1) :: blk) ++ cobsStuff bs []
      else if blk.length = 253 then ((255 : UInt8) :: (blk ++ [b])) ++ cobsStuff bs []
      else cobsStuff bs (blk ++ [b])

/-- The COBS encoding of the record `r`. -/
def cobsEncode (r : List UInt8) : List UInt8 := cobsStuff r []

/-- `UnStuffData` with checks: each block is a code byte `c` from 1 to 255 followed by `c - 1`
bytes, none of them zero, and gives those bytes followed by a zero when `c` is below `0xFF`. -/
def cobsUnstuff : List UInt8 → Option (List UInt8)
  | [] => some []
  | c :: rest =>
      if c = 0 ∨ rest.length < c.toNat - 1 ∨ 0 ∈ rest.take (c.toNat - 1) then none
      else (cobsUnstuff (rest.drop (c.toNat - 1))).map fun d =>
        rest.take (c.toNat - 1) ++ (if c = 255 then [] else [0]) ++ d
termination_by s => s.length
decreasing_by simp only [List.length_drop, List.length_cons]; omega

/-- The record that the COBS encoding `s` encodes: the bytes of the blocks without the zero that
the last block, whose code must lie below `0xFF`, gives at the end. -/
def cobsDecode (s : List UInt8) : Option (List UInt8) :=
  match cobsUnstuff s with
  | some d => if d.getLast? = some 0 then some d.dropLast else none
  | none => none

theorem cobsUnstuff_block {c : UInt8} {data : List UInt8} (more : List UInt8) (hc : c ≠ 0)
    (hd : data.length = c.toNat - 1) (hz : 0 ∉ data) :
    cobsUnstuff (c :: (data ++ more)) =
      (cobsUnstuff more).map fun d => data ++ (if c = 255 then [] else [0]) ++ d := by
  rw [cobsUnstuff]
  have ht : (data ++ more).take (c.toNat - 1) = data := List.take_left' hd
  have hdr : (data ++ more).drop (c.toNat - 1) = more := List.drop_left' hd
  have hl : ¬(data ++ more).length < c.toNat - 1 := by
    rw [List.length_append]
    omega
  rw [ite_eq_right (by rw [ht]; exact fun h => h.elim hc fun h => h.elim hl hz), ht, hdr]

theorem toNat_ofNat_succ {k : Nat} (hk : k ≤ 253) : (UInt8.ofNat (k + 1)).toNat = k + 1 := by
  rw [UInt8.toNat_ofNat']
  omega

theorem ofNat_succ_ne_zero {k : Nat} (hk : k ≤ 253) : UInt8.ofNat (k + 1) ≠ 0 := by
  intro h
  have := toNat_ofNat_succ hk
  rw [h] at this
  simp at this

theorem ofNat_succ_ne_255 {k : Nat} (hk : k ≤ 252) : UInt8.ofNat (k + 1) ≠ 255 := by
  intro h
  have := toNat_ofNat_succ (k := k) (by omega)
  rw [h] at this
  simp at this
  omega

theorem cobsUnstuff_stuff :
    ∀ (bs blk : List UInt8), 0 ∉ blk → blk.length ≤ 253 →
      cobsUnstuff (cobsStuff bs blk) = some (blk ++ bs ++ [0])
  | [], blk, hz, hl => by
      have h1 := cobsUnstuff_block (c := UInt8.ofNat (blk.length + 1)) (data := blk) []
        (ofNat_succ_ne_zero hl) (by rw [toNat_ofNat_succ hl]; simp) hz
      rw [List.append_nil] at h1
      rw [cobsStuff, h1]
      by_cases h : blk.length = 253
      · rw [ite_eq_right (by rw [h]; decide)]
        simp [cobsUnstuff]
      · rw [ite_eq_right (ofNat_succ_ne_255 (by omega))]
        simp [cobsUnstuff]
  | b :: bs, blk, hz, hl => by
      rw [cobsStuff]
      by_cases hb : b = 0
      · rw [ite_eq_left hb, List.cons_append, cobsUnstuff_block _ (ofNat_succ_ne_zero hl)
          (by rw [toNat_ofNat_succ hl]; simp) hz,
          cobsUnstuff_stuff bs [] (by simp) (by simp)]
        by_cases h : blk.length = 253
        · rw [ite_eq_right (by rw [h]; decide)]
          simp [hb]
        · rw [ite_eq_right (ofNat_succ_ne_255 (by omega))]
          simp [hb]
      · rw [ite_eq_right hb]
        by_cases h : blk.length = 253
        · rw [ite_eq_left h, List.cons_append, cobsUnstuff_block _ (by decide)
            (by rw [List.length_append, h]; rfl) (by simp [hz, Ne.symm hb]),
            cobsUnstuff_stuff bs [] (by simp) (by simp)]
          simp
        · rw [ite_eq_right h, cobsUnstuff_stuff bs (blk ++ [b]) (by simp [hz, Ne.symm hb])
            (by rw [List.length_append, List.length_singleton]; omega)]
          simp

/-- F1: decoding inverts encoding. -/
theorem cobsDecode_encode (r : List UInt8) : cobsDecode (cobsEncode r) = some r := by
  rw [cobsDecode, cobsEncode, cobsUnstuff_stuff r [] (by simp) (by simp)]
  simp

theorem zero_not_mem_cobsStuff :
    ∀ (bs blk : List UInt8), 0 ∉ blk → blk.length ≤ 253 → 0 ∉ cobsStuff bs blk
  | [], blk, hz, hl => by
      rw [cobsStuff, List.mem_cons, not_or]
      exact ⟨Ne.symm (ofNat_succ_ne_zero hl), hz⟩
  | b :: bs, blk, hz, hl => by
      rw [cobsStuff]
      by_cases hb : b = 0
      · rw [ite_eq_left hb, List.mem_append, List.mem_cons, not_or, not_or]
        exact ⟨⟨Ne.symm (ofNat_succ_ne_zero hl), hz⟩,
          zero_not_mem_cobsStuff bs [] (by simp) (by simp)⟩
      · rw [ite_eq_right hb]
        by_cases h : blk.length = 253
        · rw [ite_eq_left h, List.mem_append, List.mem_cons, not_or, not_or]
          exact ⟨⟨by decide, by simp [hz, Ne.symm hb]⟩,
            zero_not_mem_cobsStuff bs [] (by simp) (by simp)⟩
        · rw [ite_eq_right h]
          exact zero_not_mem_cobsStuff bs _ (by simp [hz, Ne.symm hb])
            (by rw [List.length_append, List.length_singleton]; omega)

/-- F1: the encoding holds no zero byte. -/
theorem zero_not_mem_cobsEncode (r : List UInt8) : 0 ∉ cobsEncode r :=
  zero_not_mem_cobsStuff r [] (by simp) (by simp)

theorem length_cobsStuff :
    ∀ (bs blk : List UInt8), blk.length + bs.length ≤ 253 →
      (cobsStuff bs blk).length = blk.length + bs.length + 1
  | [], blk, _ => by simp [cobsStuff]
  | b :: bs, blk, hl => by
      rw [cobsStuff]
      simp only [List.length_cons] at hl
      by_cases hb : b = 0
      · rw [ite_eq_left hb, List.length_append, length_cobsStuff bs [] (by simp; omega)]
        simp
        omega
      · rw [ite_eq_right hb, ite_eq_right (by omega), length_cobsStuff bs _ (by simp; omega)]
        simp
        omega

/-- F1: a record shorter than 254 bytes gains one byte. -/
theorem length_cobsEncode {r : List UInt8} (h : r.length < 254) :
    (cobsEncode r).length = r.length + 1 := by
  rw [cobsEncode, length_cobsStuff r [] (by simp; omega)]
  simp

theorem cobsStuff_append_nonzero : ∀ (data blk rest : List UInt8), 0 ∉ data →
    blk.length + data.length ≤ 253 → cobsStuff (data ++ rest) blk = cobsStuff rest (blk ++ data)
  | [], blk, rest, _, _ => by simp
  | b :: data, blk, rest, hz, hl => by
      rw [List.mem_cons, not_or] at hz
      simp only [List.length_cons] at hl
      rw [List.cons_append, cobsStuff, ite_eq_right (Ne.symm hz.1), ite_eq_right (by omega),
        cobsStuff_append_nonzero data (blk ++ [b]) rest hz.2 (by simp; omega)]
      simp

theorem cobsUnstuff_eq_nil : ∀ s : List UInt8, cobsUnstuff s = some [] → s = []
  | [], _ => rfl
  | c :: rest, h => by
      exfalso
      rw [cobsUnstuff] at h
      split at h
      · simp at h
      · next hc =>
        cases hu : cobsUnstuff (rest.drop (c.toNat - 1)) with
        | none =>
            rw [hu] at h
            simp at h
        | some u =>
            rw [hu] at h
            simp only [Option.map_some, Option.some.injEq, List.append_eq_nil_iff] at h
            obtain ⟨⟨h1, h2⟩, -⟩ := h
            by_cases h255 : c = 255
            · rw [h255] at hc h1
              have h255n : (255 : UInt8).toNat = 255 := rfl
              have hl1 := congrArg List.length h1
              simp only [List.length_take, List.length_nil, h255n] at hl1
              have hl2 : ¬rest.length < (255 : UInt8).toNat - 1 :=
                fun h => hc (Or.inr (Or.inl h))
              rw [h255n] at hl2
              omega
            · rw [ite_eq_right h255] at h2
              simp at h2

theorem eq_concat_zero {a r u : List UInt8} (hu : u ≠ [])
    (h : a ++ u = r ++ [0]) : ∃ r', u = r' ++ [0] ∧ r = a ++ r' := by
  obtain ⟨L, b, hL⟩ : ∃ L b, u = L ++ [b] := by
    rcases List.eq_nil_or_concat u with h' | ⟨L, b, h'⟩
    · exact absurd h' hu
    · exact ⟨L, b, by rw [h', List.concat_eq_append]⟩
  rw [hL, ← List.append_assoc] at h
  obtain ⟨h1, h2⟩ := List.append_inj' h rfl
  simp only [List.cons.injEq, and_true] at h2
  exact ⟨L, by rw [hL, h2], h1.symm⟩

/-- `cobsEncode` inverts `cobsUnstuff` on the encodings whose blocks give the record and the
logical zero. -/
theorem cobsStuff_of_unstuff (s r : List UInt8) (h : cobsUnstuff s = some (r ++ [0])) :
    cobsStuff r [] = s := by
  match s, h with
  | [], h => simp [cobsUnstuff] at h
  | c :: rest, h =>
    rw [cobsUnstuff] at h
    split at h
    · simp at h
    · next hc =>
      rw [not_or, not_or] at hc
      obtain ⟨hc0, hlen, hz⟩ := hc
      obtain ⟨u, hu, hE⟩ : ∃ u, cobsUnstuff (rest.drop (c.toNat - 1)) = some u ∧
          rest.take (c.toNat - 1) ++ (if c = 255 then [] else [0]) ++ u = r ++ [0] := by
        cases hu : cobsUnstuff (rest.drop (c.toNat - 1)) with
        | none =>
            rw [hu] at h
            simp at h
        | some u =>
            rw [hu] at h
            exact ⟨u, rfl, by simpa using h⟩
      have hdl : (rest.take (c.toNat - 1)).length = c.toNat - 1 := by
        rw [List.length_take]
        omega
      have hc1 : 1 ≤ c.toNat := by
        have : c.toNat ≠ 0 := fun e => hc0 (UInt8.toNat_inj.mp (by rw [e]; rfl))
        omega
      have hcl : c.toNat < 256 := c.toNat_lt
      have hrest := List.take_append_drop (c.toNat - 1) rest
      by_cases h255 : c = 255
      · rw [ite_eq_left h255, List.append_nil] at hE
        have hu0 : u ≠ [] := by
          intro e
          rw [e, List.append_nil] at hE
          exact hz (by rw [hE]; simp)
        obtain ⟨r', hr', hrr⟩ := eq_concat_zero hu0 hE
        rw [hr'] at hu
        have ih := cobsStuff_of_unstuff _ r' hu
        have h254 : c.toNat - 1 = 254 := by rw [h255]; rfl
        rw [h254] at hdl hz hrest ih hrr
        obtain ⟨L, b, hLb⟩ : ∃ L b, rest.take 254 = L ++ [b] := by
          rcases List.eq_nil_or_concat (rest.take 254) with e | ⟨L, b, e⟩
          · rw [e] at hdl
            simp at hdl
          · exact ⟨L, b, by rw [e, List.concat_eq_append]⟩
        have hLl : L.length = 253 := by
          have := congrArg List.length hLb
          rw [hdl, List.length_append, List.length_singleton] at this
          omega
        have hb : b ≠ 0 := fun e => hz (by rw [hLb, e]; simp)
        have hL0 : 0 ∉ L := fun e => hz (by rw [hLb]; exact List.mem_append_left _ e)
        rw [hrr, hLb, List.append_assoc, List.singleton_append,
          cobsStuff_append_nonzero L [] _ hL0 (by simp [hLl]), List.nil_append, cobsStuff,
          ite_eq_right hb, ite_eq_left hLl, ih, h255, ← hLb, List.cons_append, hrest]
      · rw [ite_eq_right h255] at hE
        have hcl' : c.toNat - 1 ≤ 253 := by
          have : c.toNat ≠ 255 := fun e => h255 (UInt8.toNat_inj.mp (by rw [e]; rfl))
          omega
        have hcode : UInt8.ofNat ((rest.take (c.toNat - 1)).length + 1) = c := by
          rw [hdl, show c.toNat - 1 + 1 = c.toNat by omega, UInt8.ofNat_toNat]
        by_cases hu0 : u = []
        · rw [hu0, List.append_nil] at hE
          obtain ⟨h1, -⟩ := List.append_inj' hE rfl
          rw [hu0] at hu
          have hmore := cobsUnstuff_eq_nil _ hu
          rw [hmore, List.append_nil] at hrest
          rw [← h1, ← List.append_nil (rest.take (c.toNat - 1)),
            cobsStuff_append_nonzero _ [] [] hz (by simp; omega), List.nil_append, cobsStuff,
            hcode, hrest]
        · obtain ⟨r', hr', hrr⟩ := eq_concat_zero hu0 hE
          rw [hr'] at hu
          have ih := cobsStuff_of_unstuff _ r' hu
          rw [hrr, List.append_assoc, List.singleton_append,
            cobsStuff_append_nonzero _ [] _ hz (by simp; omega),
            List.nil_append, cobsStuff, ite_eq_left rfl, hcode, ih, List.cons_append, hrest]
termination_by s.length
decreasing_by
  all_goals
    simp only [List.length_drop, List.length_cons]
    omega

/-- F1's converse: a segment decodes to `r` only when it is the encoding of `r`, so a reader of
`cobsDecode` need trust only `cobsEncode`. -/
theorem cobsDecode_eq_some_iff (s r : List UInt8) : cobsDecode s = some r ↔ cobsEncode r = s := by
  constructor
  · intro h
    unfold cobsDecode at h
    split at h
    · next d hd =>
      split at h
      · next hl =>
        rw [Option.some.injEq] at h
        have hd' : d = r ++ [0] := by
          rw [← h]
          rcases List.eq_nil_or_concat d with e | ⟨L, b, e⟩
          · rw [e] at hl
            simp at hl
          · rw [e, List.concat_eq_append] at hl ⊢
            simp only [List.getLast?_concat, Option.some.injEq] at hl
            rw [hl, List.dropLast_concat]
        rw [hd'] at hd
        exact cobsStuff_of_unstuff s r hd
      · simp at h
    · simp at h
  · intro h
    rw [← h]
    exact cobsDecode_encode r

/-! ## Segments -/

/-- The complete segments `done` and the bytes `cur` since the last `0x00`. -/
structure Split where
  done : List (List UInt8)
  cur : List UInt8

/-- The split after the byte `b`: a `0x00` closes the current segment. -/
def splitByte (s : Split) (b : UInt8) : Split :=
  if b = 0 then ⟨s.done ++ [s.cur], []⟩ else ⟨s.done, s.cur ++ [b]⟩

/-- The split of the bytes `bs`. -/
def split (bs : List UInt8) : Split := bs.foldl splitByte ⟨[], []⟩

/-- `splitByte` on the segments and the current segment's bytes in reverse order. -/
def splitByteRev (p : List (List UInt8) × List UInt8) (b : UInt8) :
    List (List UInt8) × List UInt8 :=
  if b = 0 then (p.2.reverse :: p.1, []) else (p.1, b :: p.2)

/-- `split` in time linear in the number of bytes. -/
def splitLinear (bs : List UInt8) : Split :=
  let p := bs.foldl splitByteRev ([], [])
  ⟨p.1.reverse, p.2.reverse⟩

theorem foldl_splitByteRev : ∀ (bs : List UInt8) (D : List (List UInt8)) (c : List UInt8),
    bs.foldl splitByte ⟨D, c⟩ =
      ⟨(bs.foldl splitByteRev (D.reverse, c.reverse)).1.reverse,
        (bs.foldl splitByteRev (D.reverse, c.reverse)).2.reverse⟩
  | [], D, c => by simp
  | b :: bs, D, c => by
      by_cases hb : b = 0
      · simpa [splitByte, splitByteRev, hb] using foldl_splitByteRev bs (D ++ [c]) []
      · simpa [splitByte, splitByteRev, hb] using foldl_splitByteRev bs D (c ++ [b])

/-- Compiled code computes `split` as `splitLinear`. -/
@[csimp] theorem split_eq_splitLinear : @split = @splitLinear := by
  funext bs
  exact foldl_splitByteRev bs [] []

/-- The complete segments of the bytes `bs`: the bytes between consecutive `0x00` bytes, in
order, the first segment beginning at the start of `bs`.  The bytes after the last `0x00` form
no segment yet. -/
def segments (bs : List UInt8) : List (List UInt8) := (split bs).done

/-- The errors of a segment: a segment that is no COBS encoding, and one longer than the maximum
length. -/
inductive SegErr where
  | decode
  | overflow
  deriving DecidableEq, Repr

/-- The result for the segment `s`: an overflow when `s` is longer than `maxLen` bytes, a
decoding error when `cobsDecode` rejects it, and the record that it encodes otherwise. -/
def segResult (maxLen : Nat) (s : List UInt8) : Except SegErr (List UInt8) :=
  if maxLen < s.length then .error .overflow
  else match cobsDecode s with
    | some r => .ok r
    | none => .error .decode

variable {M α : Type}

/-- The machine's state and the bytes of its answers after the segments `segs`, from `m0`: for
each nonempty segment, in order, the machine's answer to its result, encoded and followed by a
`0x00`.  An empty segment changes nothing. -/
def answerRun (mach : M → Except SegErr (List UInt8) → M × List UInt8) (maxLen : Nat) (m0 : M)
    (segs : List (List UInt8)) : M × List UInt8 :=
  segs.foldl (fun p s => if s = [] then p else
    ((mach p.1 (segResult maxLen s)).1,
      p.2 ++ cobsEncode (mach p.1 (segResult maxLen s)).2 ++ [0])) (m0, [])

/-- The step of `answerRun` with the answers' bytes in an array. -/
def answerStepArray (mach : M → Except SegErr (List UInt8) → M × List UInt8) (maxLen : Nat)
    (p : M × Array UInt8) (s : List UInt8) : M × Array UInt8 :=
  if s = [] then p else
    let r := mach p.1 (segResult maxLen s)
    (r.1, (p.2 ++ cobsEncode r.2).push 0)

/-- `answerRun` in time linear in the number of segments and the length of the answers. -/
def answerRunLinear (mach : M → Except SegErr (List UInt8) → M × List UInt8) (maxLen : Nat)
    (m0 : M) (segs : List (List UInt8)) : M × List UInt8 :=
  let p := segs.foldl (answerStepArray mach maxLen) (m0, #[])
  (p.1, p.2.toList)

theorem foldl_answerStepArray (mach : M → Except SegErr (List UInt8) → M × List UInt8)
    (maxLen : Nat) : ∀ (segs : List (List UInt8)) (m : M) (a : Array UInt8),
    segs.foldl (fun p s => if s = [] then p else
        ((mach p.1 (segResult maxLen s)).1,
          p.2 ++ cobsEncode (mach p.1 (segResult maxLen s)).2 ++ [0])) (m, a.toList) =
      ((segs.foldl (answerStepArray mach maxLen) (m, a)).1,
        (segs.foldl (answerStepArray mach maxLen) (m, a)).2.toList)
  | [], m, a => rfl
  | s :: segs, m, a => by
      by_cases hs : s = []
      · simpa [answerStepArray, hs] using foldl_answerStepArray mach maxLen segs m a
      · simpa [answerStepArray, hs] using foldl_answerStepArray mach maxLen segs
          (mach m (segResult maxLen s)).1 ((a ++ cobsEncode (mach m (segResult maxLen s)).2).push 0)

/-- Compiled code computes `answerRun` as `answerRunLinear`. -/
@[csimp] theorem answerRun_eq_answerRunLinear : @answerRun = @answerRunLinear := by
  funext M mach maxLen m0 segs
  exact foldl_answerStepArray mach maxLen segs m0 #[]

/-- The bytes of the machine's answers to the complete segments of the bytes `bs`. -/
def delimAnswers (mach : M → Except SegErr (List UInt8) → M × List UInt8) (maxLen : Nat) (m0 : M)
    (bs : List UInt8) : List UInt8 :=
  (answerRun mach maxLen m0 (segments bs)).2

theorem split_append (bs : List UInt8) (b : UInt8) :
    split (bs ++ [b]) = splitByte (split bs) b := by
  simp [split, List.foldl_append]

theorem foldl_splitByte : ∀ (b : List UInt8) (D : List (List UInt8)) (c : List UInt8),
    b.foldl splitByte ⟨D, c⟩ =
      ⟨D ++ (b.foldl splitByte ⟨[], c⟩).done, (b.foldl splitByte ⟨[], c⟩).cur⟩
  | [], D, c => by simp
  | x :: b, D, c => by
      simp only [List.foldl_cons, splitByte]
      by_cases hx : x = 0
      · rw [ite_eq_left hx, ite_eq_left hx, foldl_splitByte b (D ++ [c]) [],
          foldl_splitByte b ([] ++ [c]) []]
        simp
      · rw [ite_eq_right hx, ite_eq_right hx, foldl_splitByte b D (c ++ [x])]

/-- F2: the segments after a `0x00` do not depend on the bytes before it. -/
theorem segments_append_zero (a b : List UInt8) :
    segments (a ++ 0 :: b) = segments (a ++ [0]) ++ segments b := by
  have h : split (a ++ [0]) = ⟨(split a).done ++ [(split a).cur], []⟩ := by
    rw [split_append, splitByte, ite_eq_left rfl]
  have e : split (a ++ 0 :: b) = b.foldl splitByte (split (a ++ [0])) := by
    show List.foldl splitByte ⟨[], []⟩ (a ++ 0 :: b) = _
    rw [show a ++ 0 :: b = (a ++ [0]) ++ b by simp, List.foldl_append]
    rfl
  unfold segments
  rw [e, h, foldl_splitByte]
  rfl

theorem split_nonzero : ∀ (s : List UInt8) (c : List UInt8), 0 ∉ s →
    s.foldl splitByte ⟨[], c⟩ = ⟨[], c ++ s⟩
  | [], c, _ => by simp
  | x :: s, c, h => by
      rw [List.mem_cons, not_or] at h
      rw [List.foldl_cons, splitByte, ite_eq_right (Ne.symm h.1), split_nonzero s (c ++ [x]) h.2]
      simp

/-- A segment of nonzero bytes followed by a `0x00` is one segment. -/
theorem segments_segment {s : List UInt8} (h : 0 ∉ s) : segments (s ++ [0]) = [s] := by
  rw [segments, split_append, split, split_nonzero s [] h, splitByte, ite_eq_left rfl]
  rfl

theorem answerRun_append (mach : M → Except SegErr (List UInt8) → M × List UInt8)
    (maxLen : Nat) (m0 : M) (segs : List (List UInt8)) (s : List UInt8) :
    answerRun mach maxLen m0 (segs ++ [s]) =
      if s = [] then answerRun mach maxLen m0 segs else
        ((mach (answerRun mach maxLen m0 segs).1 (segResult maxLen s)).1,
          (answerRun mach maxLen m0 segs).2 ++
            cobsEncode (mach (answerRun mach maxLen m0 segs).1 (segResult maxLen s)).2 ++ [0]) := by
  simp [answerRun, List.foldl_append]

theorem segResult_encode {maxLen : Nat} {r : List UInt8} (h : (cobsEncode r).length ≤ maxLen) :
    segResult maxLen (cobsEncode r) = .ok r := by
  rw [segResult, ite_eq_right (by omega), cobsDecode_encode]

/-- F2: a segment that equals the encoding of the record `r`, after a `0x00`, gives the machine
`r` from its state after the bytes before it, whatever those bytes are. -/
theorem delimAnswers_encode (mach : M → Except SegErr (List UInt8) → M × List UInt8)
    {maxLen : Nat} (m0 : M) (pre : List UInt8) {r : List UInt8}
    (h : (cobsEncode r).length ≤ maxLen) :
    delimAnswers mach maxLen m0 (pre ++ [0] ++ cobsEncode r ++ [0]) =
      delimAnswers mach maxLen m0 (pre ++ [0]) ++
        cobsEncode (mach (answerRun mach maxLen m0 (segments (pre ++ [0]))).1 (.ok r)).2 ++
          [0] := by
  have hne : cobsEncode r ≠ [] := by
    intro he
    have := cobsDecode_encode r
    rw [he] at this
    simp [cobsDecode, cobsUnstuff] at this
  have e : pre ++ [0] ++ cobsEncode r ++ [0] = pre ++ 0 :: (cobsEncode r ++ [0]) := by simp
  rw [e, delimAnswers, segments_append_zero, segments_segment (zero_not_mem_cobsEncode r), answerRun_append,
    ite_eq_right hne, segResult_encode h]
  rfl

/-! ## The step -/

/-- The state of the delimited framing.  The phase names the last request, as in `Framing`: 0 a
read of the status before a byte is read, 1 a read of the receive register, 2 a read of the
status before a byte is written, and 3 a write of the transmit register.  `len` counts the bytes
of the current segment up to `maxLen + 1`, `seg` holds its first `maxLen` bytes, `out` holds the
bytes still to write, and `m` is the machine's state. -/
structure Delim (M : Type) where
  phase : UInt64
  len : UInt64
  seg : List UInt8
  out : List UInt8
  m : M

/-- One window of the delimited framing over the UART `u`, from the state `f` and the value `v`
that the last request read, for segments of at most `maxLen` bytes and the machine `mach`. -/
def delimTick (u : Uart) (maxLen : Nat) (mach : M → Except SegErr (List UInt8) → M × List UInt8)
    (f : Delim M) (v : UInt64) : Delim M × UInt64 :=
  if f.phase == 0 then
    if v &&& u.rxFull != 0 then ({ f with phase := 1 }, readReq u.rx)
    else (f, readReq u.status)
  else if f.phase == 1 then
    if v &&& 255 != 0 then
      ({ f with
          phase := 0,
          len := if f.len ≤ UInt64.ofNat maxLen then f.len + 1 else f.len,
          seg := if f.len < UInt64.ofNat maxLen then f.seg ++ [(v &&& 255).toUInt8] else f.seg },
        readReq u.status)
    else if f.len == 0 then ({ f with phase := 0 }, readReq u.status)
    else
      ({ phase := 2, len := 0, seg := [],
          out := cobsEncode (mach f.m (if UInt64.ofNat maxLen < f.len then .error .overflow
            else segResult maxLen f.seg)).2 ++ [0],
          m := (mach f.m (if UInt64.ofNat maxLen < f.len then .error .overflow
            else segResult maxLen f.seg)).1 }, readReq u.status)
  else if f.phase == 2 then
    if v &&& u.txMask == u.txRoom then ({ f with phase := 3 }, writeReq u.tx (f.out.headD 0).toUInt64)
    else (f, readReq u.status)
  else ({ f with phase := if f.out.length ≤ 1 then 0 else 2, out := f.out.tail }, readReq u.status)

/-- The initial state of the delimited framing, with the machine's state `m0`. -/
def delim0 (m0 : M) : Delim M := ⟨0, 0, [], [], m0⟩

/-! ## The invariant -/

/-- While a segment is received, the framing's state `f` holds the split `s` of the bytes read,
and the bytes written, `out`, are the answers to its complete segments. -/
structure DRecv (mach : M → Except SegErr (List UInt8) → M × List UInt8) (maxLen : Nat) (m0 : M)
    (f : Delim M) (s : Split) (out : List UInt64) : Prop where
  m : f.m = (answerRun mach maxLen m0 s.done).1
  out : out = (answerRun mach maxLen m0 s.done).2.map UInt8.toUInt64
  len : f.len.toNat = min s.cur.length (maxLen + 1)
  seg : f.seg = s.cur.take maxLen

/-- While an answer is written, the split `s` of the bytes read has no current bytes, and the
bytes written, `out`, followed by the bytes `rest`, are the answers to its segments. -/
structure DSend (mach : M → Except SegErr (List UInt8) → M × List UInt8) (maxLen : Nat) (m0 : M)
    (f : Delim M) (s : Split) (out : List UInt64) (rest : List UInt8) : Prop where
  m : f.m = (answerRun mach maxLen m0 s.done).1
  out : out ++ rest.map UInt8.toUInt64 = (answerRun mach maxLen m0 s.done).2.map UInt8.toUInt64
  cur : s.cur = []
  len : f.len = 0
  seg : f.seg = []
  ne : f.out ≠ []

/-- The invariant of the delimited framing's state `f`, the last value `v`, and the bytes read and
written so far. -/
def DelimInv (mach : M → Except SegErr (List UInt8) → M × List UInt8) (maxLen : Nat) (m0 : M)
    (f : Delim M) (v : UInt64) (inp out : List UInt64) : Prop :=
  (f.phase = 0 ∧ DRecv mach maxLen m0 f (split (inp.map UInt64.toUInt8)) out) ∨
  (f.phase = 1 ∧ ∃ inp0, inp = inp0 ++ [v &&& 255] ∧
    DRecv mach maxLen m0 f (split (inp0.map UInt64.toUInt8)) out) ∨
  (f.phase = 2 ∧ DSend mach maxLen m0 f (split (inp.map UInt64.toUInt8)) out f.out) ∨
  (f.phase = 3 ∧ DSend mach maxLen m0 f (split (inp.map UInt64.toUInt8)) out f.out.tail)

/-! ## The prefix theorem -/

theorem toUInt8_eq_zero {x : UInt64} (h : x.toNat < 256) : x.toUInt8 = 0 ↔ x = 0 := by
  constructor
  · intro hx
    apply UInt64.toNat_inj.mp
    have := congrArg UInt8.toNat hx
    rw [UInt64.toNat_toUInt8] at this
    simp at this ⊢
    omega
  · intro hx
    rw [hx]
    rfl

theorem and255_lt (v : UInt64) : (v &&& 255).toNat < 256 := by
  rw [UInt64.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem toUInt64_lt (b : UInt8) : b.toUInt64.toNat < 256 := by
  rw [UInt8.toNat_toUInt64]
  exact b.toNat_lt

theorem toNat_ofNat_max {maxLen : Nat} (hmax : maxLen < 2 ^ 63) :
    (UInt64.ofNat maxLen).toNat = maxLen := by
  rw [UInt64.toNat_ofNat']
  omega

theorem split_snoc (inp0 : List UInt64) (v : UInt64) :
    split ((inp0 ++ [v &&& 255]).map UInt64.toUInt8) =
      splitByte (split (inp0.map UInt64.toUInt8)) (v &&& 255).toUInt8 := by
  rw [List.map_append, List.map_singleton, split_append]

theorem answerRun_prefix (mach : M → Except SegErr (List UInt8) → M × List UInt8)
    (maxLen : Nat) (m0 : M) :
    ∀ (more segs : List (List UInt8)),
      (answerRun mach maxLen m0 segs).2 <+: (answerRun mach maxLen m0 (segs ++ more)).2
  | [], segs => by simp
  | s :: more, segs => by
      have := answerRun_prefix mach maxLen m0 more (segs ++ [s])
      rw [List.append_assoc, List.singleton_append] at this
      refine List.IsPrefix.trans ?_ this
      rw [answerRun_append]
      split
      · exact List.prefix_refl _
      · exact ⟨_, (List.append_assoc _ _ _).symm⟩

section

variable {B : Bus α} {u : Uart} {maxLen : Nat}
  {mach : M → Except SegErr (List UInt8) → M × List UInt8} {m0 : M}

/-- The invariant after the window from the state `f`, the last value `v`, and `k` reads. -/
def DelimNext (B : Bus α) (u : Uart) (maxLen : Nat)
    (mach : M → Except SegErr (List UInt8) → M × List UInt8) (m0 : M) (σ : Nat → UInt32)
    (f : Delim M) (v : UInt64) (k : Nat) (inp out : List UInt64) : Prop :=
  DelimInv mach maxLen m0 (reqNext (delimTick u maxLen mach) σ ⟨f, v, k⟩).state
    (reqNext (delimTick u maxLen mach) σ ⟨f, v, k⟩).last
    (inp ++ dataIn B u [reqEvent B (delimTick u maxLen mach) σ ⟨f, v, k⟩])
    (out ++ dataOut B u [reqEvent B (delimTick u maxLen mach) σ ⟨f, v, k⟩])

variable (hrx : u.rx.toNat < 65536) (htx : u.tx.toNat < 65536) (hs : u.status.toNat < 65536)
  (hrs : u.rx ≠ u.status) (hmax : maxLen < 2 ^ 63) (σ : Nat → UInt32) (f : Delim M) (v : UInt64)
  (k : Nat) {inp out : List UInt64}

include hrx hs hrs in
theorem delimNext_status {g : Delim M}
    (htick : delimTick u maxLen mach f v = (g, readReq u.status))
    (h : ∀ x, DelimInv mach maxLen m0 g x inp out) :
    DelimNext B u maxLen mach m0 σ f v k inp out := by
  obtain ⟨h1, h2, h3⟩ := next_read (B := B) (σ := σ) (r := ⟨f, v, k⟩) htick (reqWrite_readReq hs)
  unfold DelimNext
  rw [h1, h2, h3, reqReg_readReq hs, dataIn_status B u hrx hs hrs, dataOut_read B u,
    List.append_nil, List.append_nil]
  exact h _

include hrx hs hrs in
theorem delimNext_phase0 (hp : f.phase = 0)
    (hr : DRecv mach maxLen m0 f (split (inp.map UInt64.toUInt8)) out) :
    DelimNext B u maxLen mach m0 σ f v k inp out := by
  by_cases hx : (v &&& u.rxFull != 0) = true
  · have htick : delimTick u maxLen mach f v = ({ f with phase := 1 }, readReq u.rx) := by
      rw [delimTick, ite_eq_left (by rw [hp]; rfl), ite_eq_left hx]
    obtain ⟨h1, h2, h3⟩ :=
      next_read (B := B) (σ := σ) (r := ⟨f, v, k⟩) htick (reqWrite_readReq hrx)
    unfold DelimNext
    rw [h1, h2, h3, reqReg_readReq hrx, dataIn_data B u, dataOut_read B u, List.append_nil]
    exact Or.inr (Or.inl ⟨rfl, inp, rfl, hr.m, hr.out, hr.len, hr.seg⟩)
  · exact delimNext_status hrx hs hrs σ f v k
      (by rw [delimTick, ite_eq_left (by rw [hp]; rfl), ite_eq_right hx])
      (fun _ => Or.inl ⟨hp, hr⟩)

include hrx hs hrs hmax in
theorem delimNext_byte {inp0 : List UInt64} (hp : f.phase = 1)
    (hin : inp = inp0 ++ [v &&& 255])
    (hr : DRecv mach maxLen m0 f (split (inp0.map UInt64.toUInt8)) out)
    (hb : (v &&& 255 != 0) = true) :
    DelimNext B u maxLen mach m0 σ f v k inp out := by
  have hb' : (v &&& 255).toUInt8 ≠ 0 := fun h =>
    absurd ((toUInt8_eq_zero (and255_lt v)).mp h) (by simpa using hb)
  have hM := toNat_ofNat_max hmax
  have hlen := hr.len
  refine delimNext_status hrx hs hrs σ f v k (g := { f with
    phase := 0,
    len := if f.len ≤ UInt64.ofNat maxLen then f.len + 1 else f.len,
    seg := if f.len < UInt64.ofNat maxLen then f.seg ++ [(v &&& 255).toUInt8] else f.seg })
    (by rw [delimTick, ite_eq_right (by rw [hp]; decide), ite_eq_left (by rw [hp]; rfl),
      ite_eq_left hb])
    (fun _ => Or.inl ⟨rfl, ?_⟩)
  rw [hin, split_snoc, splitByte, ite_eq_right hb']
  refine ⟨hr.m, hr.out, ?_, ?_⟩
  · show (if f.len ≤ UInt64.ofNat maxLen then f.len + 1 else f.len).toNat = _
    rw [List.length_append, List.length_singleton]
    split
    next h =>
      have h' := UInt64.le_iff_toNat_le.mp h
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      omega
    next h =>
      have h' : ¬f.len.toNat ≤ maxLen := fun h' => h (UInt64.le_iff_toNat_le.mpr (by omega))
      omega
  · show (if f.len < UInt64.ofNat maxLen then f.seg ++ [(v &&& 255).toUInt8] else f.seg) = _
    rw [hr.seg]
    split
    next h =>
      have h' := UInt64.lt_iff_toNat_lt.mp h
      have hc : (split (inp0.map UInt64.toUInt8)).cur.length < maxLen := by omega
      show (split (inp0.map UInt64.toUInt8)).cur.take maxLen ++ [(v &&& 255).toUInt8] =
        ((split (inp0.map UInt64.toUInt8)).cur ++ [(v &&& 255).toUInt8]).take maxLen
      rw [List.take_of_length_le (by omega),
        List.take_of_length_le (by rw [List.length_append, List.length_singleton]; omega)]
    next h =>
      have h' : ¬f.len.toNat < maxLen := fun h' => h (UInt64.lt_iff_toNat_lt.mpr (by omega))
      have hc : maxLen ≤ (split (inp0.map UInt64.toUInt8)).cur.length := by omega
      show (split (inp0.map UInt64.toUInt8)).cur.take maxLen =
        ((split (inp0.map UInt64.toUInt8)).cur ++ [(v &&& 255).toUInt8]).take maxLen
      rw [List.take_append_of_le_length hc]

include hrx hs hrs in
theorem delimNext_empty {inp0 : List UInt64} (hp : f.phase = 1)
    (hin : inp = inp0 ++ [v &&& 255])
    (hr : DRecv mach maxLen m0 f (split (inp0.map UInt64.toUInt8)) out)
    (hb : ¬(v &&& 255 != 0) = true) (hl : (f.len == 0) = true) :
    DelimNext B u maxLen mach m0 σ f v k inp out := by
  have hb0 : (v &&& 255).toUInt8 = 0 := (toUInt8_eq_zero (and255_lt v)).mpr (by simpa using hb)
  have hl0 : f.len = 0 := by simpa using hl
  have hcur : (split (inp0.map UInt64.toUInt8)).cur = [] := by
    have := hr.len
    rw [hl0] at this
    exact List.eq_nil_of_length_eq_zero (by simp at this; omega)
  refine delimNext_status hrx hs hrs σ f v k (g := { f with phase := 0 })
    (by rw [delimTick, ite_eq_right (by rw [hp]; decide), ite_eq_left (by rw [hp]; rfl),
      ite_eq_right hb, ite_eq_left hl])
    (fun _ => Or.inl ⟨rfl, ?_⟩)
  rw [hin, split_snoc, splitByte, ite_eq_left hb0]
  refine ⟨?_, ?_, ?_, ?_⟩
  · show f.m = _
    rw [answerRun_append, ite_eq_left hcur]
    exact hr.m
  · rw [answerRun_append, ite_eq_left hcur]
    exact hr.out
  · show f.len.toNat = _
    rw [hl0]
    rfl
  · show f.seg = _
    rw [hr.seg, hcur]

include hrx hs hrs hmax in
theorem delimNext_answer {inp0 : List UInt64} (hp : f.phase = 1)
    (hin : inp = inp0 ++ [v &&& 255])
    (hr : DRecv mach maxLen m0 f (split (inp0.map UInt64.toUInt8)) out)
    (hb : ¬(v &&& 255 != 0) = true) (hl : ¬(f.len == 0) = true) :
    DelimNext B u maxLen mach m0 σ f v k inp out := by
  have hb0 : (v &&& 255).toUInt8 = 0 := (toUInt8_eq_zero (and255_lt v)).mpr (by simpa using hb)
  have hM := toNat_ofNat_max hmax
  have hlen := hr.len
  have hl0 : f.len.toNat ≠ 0 := fun h => hl (by
    rw [beq_iff_eq]
    exact UInt64.toNat_inj.mp h)
  have hcur : (split (inp0.map UInt64.toUInt8)).cur ≠ [] := by
    intro h
    rw [h] at hlen
    simp at hlen
    exact hl0 hlen
  have hres : (if UInt64.ofNat maxLen < f.len then .error .overflow else segResult maxLen f.seg) =
      segResult maxLen (split (inp0.map UInt64.toUInt8)).cur := by
    by_cases ho : UInt64.ofNat maxLen < f.len
    · have ho' := UInt64.lt_iff_toNat_lt.mp ho
      rw [ite_eq_left ho, segResult, ite_eq_left (by omega)]
    · have ho' : ¬maxLen < f.len.toNat := fun h => ho (UInt64.lt_iff_toNat_lt.mpr (by omega))
      rw [ite_eq_right ho, hr.seg, List.take_of_length_le (by omega)]
  refine delimNext_status hrx hs hrs σ f v k (g := {
      phase := 2, len := 0, seg := [],
      out := cobsEncode (mach f.m (if UInt64.ofNat maxLen < f.len then .error .overflow
        else segResult maxLen f.seg)).2 ++ [0],
      m := (mach f.m (if UInt64.ofNat maxLen < f.len then .error .overflow
        else segResult maxLen f.seg)).1 })
    (by rw [delimTick, ite_eq_right (by rw [hp]; decide), ite_eq_left (by rw [hp]; rfl),
      ite_eq_right hb, ite_eq_right hl])
    (fun _ => Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩)))
  rw [hin, split_snoc, splitByte, ite_eq_left hb0]
  refine ⟨?_, ?_, rfl, rfl, rfl, by simp⟩
  · show (mach f.m _).1 = _
    rw [answerRun_append, ite_eq_right hcur, ← hr.m, hres]
  · show out ++ (cobsEncode (mach f.m _).2 ++ [0]).map UInt8.toUInt64 = _
    rw [answerRun_append, ite_eq_right hcur, ← hr.m, hres, hr.out, ← List.map_append,
      List.append_assoc]

include hrx htx hs hrs in
theorem delimNext_phase2 (hp : f.phase = 2)
    (hsd : DSend mach maxLen m0 f (split (inp.map UInt64.toUInt8)) out f.out) :
    DelimNext B u maxLen mach m0 σ f v k inp out := by
  by_cases hx : (v &&& u.txMask == u.txRoom) = true
  · have htick : delimTick u maxLen mach f v =
        ({ f with phase := 3 }, writeReq u.tx (f.out.headD 0).toUInt64) := by
      rw [delimTick, ite_eq_right (by rw [hp]; decide), ite_eq_right (by rw [hp]; decide),
        ite_eq_left (by rw [hp]; rfl), ite_eq_left hx]
    obtain ⟨h1, h2, h3⟩ :=
      next_write (B := B) (σ := σ) (r := ⟨f, v, k⟩) htick (reqWrite_writeReq _ htx)
    unfold DelimNext
    rw [h1, h2, h3, reqReg_writeReq _ htx, dataIn_write B u,
      dataOut_write B u htx (toUInt64_lt _), List.append_nil]
    refine Or.inr (Or.inr (Or.inr ⟨rfl, ?_⟩))
    obtain ⟨b, t, hbt⟩ := List.exists_cons_of_ne_nil hsd.ne
    refine ⟨hsd.m, ?_, hsd.cur, hsd.len, hsd.seg, hsd.ne⟩
    have ho := hsd.out
    show (out ++ [(f.out.headD 0).toUInt64]) ++ f.out.tail.map UInt8.toUInt64 = _
    rw [hbt] at ho ⊢
    simpa using ho
  · exact delimNext_status hrx hs hrs σ f v k
      (by rw [delimTick, ite_eq_right (by rw [hp]; decide), ite_eq_right (by rw [hp]; decide),
        ite_eq_left (by rw [hp]; rfl), ite_eq_right hx])
      (fun _ => Or.inr (Or.inr (Or.inl ⟨hp, hsd⟩)))

include hrx hs hrs in
theorem delimNext_phase3 (hp : f.phase = 3)
    (hsd : DSend mach maxLen m0 f (split (inp.map UInt64.toUInt8)) out f.out.tail) :
    DelimNext B u maxLen mach m0 σ f v k inp out := by
  refine delimNext_status hrx hs hrs σ f v k
    (g := { f with phase := if f.out.length ≤ 1 then 0 else 2, out := f.out.tail })
    (by rw [delimTick, ite_eq_right (by rw [hp]; decide), ite_eq_right (by rw [hp]; decide),
      ite_eq_right (by rw [hp]; decide)])
    (fun _ => ?_)
  by_cases h1 : f.out.length ≤ 1
  · have ht : f.out.tail = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [List.length_tail]
      omega
    refine Or.inl ⟨by simp only [ite_eq_left h1], hsd.m, ?_, ?_, ?_⟩
    · have ho := hsd.out
      rw [ht, List.map_nil, List.append_nil] at ho
      exact ho
    · show f.len.toNat = _
      rw [hsd.len, hsd.cur]
      rfl
    · show f.seg = _
      rw [hsd.seg, hsd.cur, List.take_nil]
  · refine Or.inr (Or.inr (Or.inl ⟨by simp only [ite_eq_right h1],
      hsd.m, hsd.out, hsd.cur, hsd.len, hsd.seg, ?_⟩))
    show f.out.tail ≠ []
    intro h
    have := congrArg List.length h
    rw [List.length_tail] at this
    simp at this
    omega

include hrx htx hs hrs hmax in
/-- One window keeps the invariant of the delimited framing. -/
theorem delimInv_next (r : ReqState (Delim M))
    (h : DelimInv mach maxLen m0 r.state r.last inp out) :
    DelimInv mach maxLen m0 (reqNext (delimTick u maxLen mach) σ r).state
      (reqNext (delimTick u maxLen mach) σ r).last
      (inp ++ dataIn B u [reqEvent B (delimTick u maxLen mach) σ r])
      (out ++ dataOut B u [reqEvent B (delimTick u maxLen mach) σ r]) := by
  obtain ⟨f, v, k⟩ := r
  change DelimInv mach maxLen m0 f v inp out at h
  change DelimNext B u maxLen mach m0 σ f v k inp out
  rcases h with ⟨hp, hr⟩ | ⟨hp, inp0, hin, hr⟩ | ⟨hp, hsd⟩ | ⟨hp, hsd⟩
  · exact delimNext_phase0 hrx hs hrs σ f v k hp hr
  · by_cases hb : (v &&& 255 != 0) = true
    · exact delimNext_byte hrx hs hrs hmax σ f v k hp hin hr hb
    · by_cases hl : (f.len == 0) = true
      · exact delimNext_empty hrx hs hrs σ f v k hp hin hr hb hl
      · exact delimNext_answer hrx hs hrs hmax σ f v k hp hin hr hb hl
  · exact delimNext_phase2 hrx htx hs hrs σ f v k hp hsd
  · exact delimNext_phase3 hrx hs hrs σ f v k hp hsd

end

section

variable {B : Bus α} {u : Uart} {maxLen : Nat}
  {mach : M → Except SegErr (List UInt8) → M × List UInt8} {m0 : M}

/-- The invariant of the delimited framing holds before every window. -/
theorem delimInv_run (hrx : u.rx.toNat < 65536) (htx : u.tx.toNat < 65536)
    (hs : u.status.toNat < 65536) (hrs : u.rx ≠ u.status) (hmax : maxLen < 2 ^ 63)
    (σ : Nat → UInt32) : ∀ n,
    DelimInv mach maxLen m0 (reqRun (delimTick u maxLen mach) (delim0 m0) σ n).state
      (reqRun (delimTick u maxLen mach) (delim0 m0) σ n).last
      (dataIn B u (windows (reqTrace B (delimTick u maxLen mach) (delim0 m0) σ) n))
      (dataOut B u (windows (reqTrace B (delimTick u maxLen mach) (delim0 m0) σ) n))
  | 0 => Or.inl ⟨rfl, rfl, rfl, rfl, List.take_nil.symm⟩
  | n + 1 => by
      rw [windows, dataIn_append, dataOut_append]
      exact delimInv_next hrx htx hs hrs hmax σ _
        (delimInv_run hrx htx hs hrs hmax σ n)

/-- F3: the bytes that the first `n` windows of the delimited framing write to the transmit
register begin the machine's answers to the complete nonempty segments of the bytes that those
windows read from the receive register, each answer encoded and followed by a `0x00`, for every
sequence `σ` of the values read. -/
theorem delim_prefix (hrx : u.rx.toNat < 65536) (htx : u.tx.toNat < 65536)
    (hs : u.status.toNat < 65536) (hrs : u.rx ≠ u.status) (hmax : maxLen < 2 ^ 63)
    (σ : Nat → UInt32) (n : Nat) :
    dataOut B u (windows (reqTrace B (delimTick u maxLen mach) (delim0 m0) σ) n) <+:
      (delimAnswers mach maxLen m0 ((dataIn B u (windows (reqTrace B (delimTick u maxLen mach)
        (delim0 m0) σ) n)).map UInt64.toUInt8)).map UInt8.toUInt64 := by
  rcases delimInv_run (B := B) (m0 := m0) (mach := mach) hrx htx hs hrs hmax σ n with
    ⟨-, hr⟩ | ⟨-, inp0, hin, hr⟩ | ⟨-, hsd⟩ | ⟨-, hsd⟩
  · rw [hr.out]
    exact List.prefix_refl _
  · rw [hr.out, delimAnswers, segments, hin, split_snoc]
    apply List.IsPrefix.map
    unfold splitByte
    split
    · exact answerRun_prefix mach maxLen m0 _ _
    · exact List.prefix_refl _
  · exact ⟨_, hsd.out⟩
  · exact ⟨_, hsd.out⟩

theorem delimTick_req (f : Delim M) (v : UInt64) (hp : f.phase ≠ 0) :
    (delimTick u maxLen mach f v).2 = readReq u.status ∨
      ∃ x, (delimTick u maxLen mach f v).2 = writeReq u.tx x := by
  unfold delimTick
  rw [ite_eq_right (by simpa using hp)]
  split
  · split
    · exact Or.inl rfl
    · split
      · exact Or.inl rfl
      · exact Or.inl rfl
  · split
    · split
      · exact Or.inr ⟨_, rfl⟩
      · exact Or.inl rfl
    · exact Or.inl rfl

theorem dataIn_event {G : Type} (hrx : u.rx.toNat < 65536) (htx : u.tx.toNat < 65536)
    (hs : u.status.toNat < 65536) (hrs : u.rx ≠ u.status) {tick : G → UInt64 → G × UInt64}
    {σ : Nat → UInt32} {r : ReqState G}
    (h : (tick r.state r.last).2 = readReq u.status ∨
      ∃ x, (tick r.state r.last).2 = writeReq u.tx x) :
    dataIn B u [reqEvent B tick σ r] = [] := by
  unfold reqEvent
  rcases h with h | ⟨x, h⟩
  · rw [h, reqWrite_readReq hs, reqReg_readReq hs]
    exact dataIn_status B u hrx hs hrs _
  · rw [h, reqWrite_writeReq _ htx, reqReg_writeReq _ htx]
    exact dataIn_write B u _ _

/-- F3 for a window that reads a byte: when window `n` reads the receive register, the bytes that
the first `n` windows wrote are all the answers to the complete nonempty segments of the bytes
that they read, so no segment that ended before window `n` waits for its answer. -/
theorem delim_answered (hrx : u.rx.toNat < 65536) (htx : u.tx.toNat < 65536)
    (hs : u.status.toNat < 65536) (hrs : u.rx ≠ u.status) (hmax : maxLen < 2 ^ 63)
    (σ : Nat → UInt32) (n : Nat)
    (hread : dataIn B u (reqTrace B (delimTick u maxLen mach) (delim0 m0) σ n) ≠ []) :
    dataOut B u (windows (reqTrace B (delimTick u maxLen mach) (delim0 m0) σ) n) =
      (delimAnswers mach maxLen m0 ((dataIn B u (windows (reqTrace B (delimTick u maxLen mach)
        (delim0 m0) σ) n)).map UInt64.toUInt8)).map UInt8.toUInt64 := by
  rcases delimInv_run (B := B) (m0 := m0) (mach := mach) hrx htx hs hrs hmax σ n with
    ⟨-, hr⟩ | ⟨hp, -⟩ | ⟨hp, -⟩ | ⟨hp, -⟩
  · rw [hr.out]
    rfl
  all_goals
    exfalso
    exact hread (dataIn_event hrx htx hs hrs (delimTick_req _ _ (by rw [hp]; decide)))

end

end LeanExe.Requests
