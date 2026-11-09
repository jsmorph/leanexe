import LeanExe.Requests.Delimited
import LeanExe.Pipeline.Implements

/-!
The delimited framing of `LeanExe/Requests/Delimited.lean` in the verified compiler's dialect,
for steps that hold a segment and an answer in words.  `Bytes40` holds 40 bytes in five words,
the first byte in the most significant byte of `w0`.  `push40` moves every byte one place toward
the start and puts a byte at the end, and `unshift40` moves every byte one place toward the end
and puts a byte at the start, each with five shifts and five additions.  The additions join bit
fields that do not overlap, so each byte of the result reduces to arithmetic on `toNat`.

`decodeWords seg n` decodes the last `n` bytes of `seg`, a segment that a step stored with
`push40`, with straight-line code: `decPos` takes the first byte of the buffer and either skips
it, for the `40 - n` positions before the segment, or passes it to `decByte`, one step of COBS's
decoder, and `decAll` applies `decPos` 40 times through nested calls.  `cobsDecode_fold` states
`cobsDecode` as a left fold of the list-level step `decStepL`, and `decodeWords_spec` relates the
program's result to that fold, so that `decodeWords_eq` gives `cobsDecode` of the stored bytes.

`encAll` encodes the last `cnt` bytes of a buffer from the last byte back, since a code byte is
the distance to the next zero: `encByte` puts each byte, or the distance in place of a zero, at
the start of the output, and `encFinish` puts the first code byte there.  `cobsEncode_back`
states `cobsEncode` of a record shorter than 254 bytes as the right fold of the list-level step
`encStepL`, and `encAll_spec`, `encByte_spec`, and `encFinish_spec` relate the program to that
fold.  Neither part has a loop or a recursive call, so `staticCost` bounds a step that uses them.
-/

namespace LeanExe.Requests

open LeanExe.Pipeline (Flat)

/-! ## Bytes in words -/

/-- Forty bytes in five words, the first byte the most significant byte of `w0`. -/
structure Bytes40 where
  w0 : UInt64
  w1 : UInt64
  w2 : UInt64
  w3 : UInt64
  w4 : UInt64

instance : Flat Bytes40 (UInt64 × UInt64 × UInt64 × UInt64 × UInt64) :=
  ⟨fun b => (b.w0, b.w1, b.w2, b.w3, b.w4)⟩

/-- The eight bytes of a word, the most significant first. -/
def wordBytes8 (w : UInt64) : List UInt8 :=
  [(w >>> 56).toUInt8, (w >>> 48).toUInt8, (w >>> 40).toUInt8, (w >>> 32).toUInt8,
    (w >>> 24).toUInt8, (w >>> 16).toUInt8, (w >>> 8).toUInt8, w.toUInt8]

/-- The 40 bytes of a buffer. -/
def Bytes40.bytes (b : Bytes40) : List UInt8 :=
  wordBytes8 b.w0 ++ wordBytes8 b.w1 ++ wordBytes8 b.w2 ++ wordBytes8 b.w3 ++ wordBytes8 b.w4

/-- The buffer of 40 zero bytes. -/
def zero40 : Bytes40 := ⟨0, 0, 0, 0, 0⟩

/-- The buffer with every byte moved one place toward the start and the low byte of `x` at the
end. -/
def push40 (b : Bytes40) (x : UInt64) : Bytes40 :=
  ⟨(b.w0 <<< 8) + (b.w1 >>> 56), (b.w1 <<< 8) + (b.w2 >>> 56), (b.w2 <<< 8) + (b.w3 >>> 56),
    (b.w3 <<< 8) + (b.w4 >>> 56), (b.w4 <<< 8) + (x &&& 255)⟩

/-- The buffer with every byte moved one place toward the end and the low byte of `x` at the
start. -/
def unshift40 (b : Bytes40) (x : UInt64) : Bytes40 :=
  ⟨((x &&& 255) <<< 56) + (b.w0 >>> 8), (b.w0 <<< 56) + (b.w1 >>> 8),
    (b.w1 <<< 56) + (b.w2 >>> 8), (b.w2 <<< 56) + (b.w3 >>> 8), (b.w3 <<< 56) + (b.w4 >>> 8)⟩

/-- The first byte of the buffer. -/
def first40 (b : Bytes40) : UInt64 := b.w0 >>> 56

/-- The last byte of the buffer. -/
def last40 (b : Bytes40) : UInt64 := b.w4 &&& 255

theorem wordBytes8_shl {v w z : UInt64} (hz : z.toNat < 256)
    (hv : v.toNat = w.toNat % 2 ^ 56 * 256 + z.toNat) :
    wordBytes8 v = (wordBytes8 w).tail ++ [z.toUInt8] := by
  have hw := UInt64.toNat_lt w
  simp only [wordBytes8, List.tail_cons, List.cons_append, List.nil_append, List.cons.injEq,
    and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply UInt8.toNat_inj.mp <;>
    simp [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, hv] <;>
    omega

theorem wordBytes8_shr {v w y : UInt64}
    (hv : v.toNat = y.toNat % 256 * 2 ^ 56 + w.toNat / 256) :
    wordBytes8 v = y.toUInt8 :: (wordBytes8 w).dropLast := by
  have hw := UInt64.toNat_lt w
  simp only [wordBytes8, List.dropLast_cons_cons, List.dropLast_singleton, List.cons.injEq,
    and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply UInt8.toNat_inj.mp <;>
    simp [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, hv] <;>
    omega

theorem toNat_shl8_add (w z : UInt64) (hz : z.toNat < 256) :
    ((w <<< 8) + z).toNat = w.toNat % 2 ^ 56 * 256 + z.toNat := by
  have hw := UInt64.toNat_lt w
  rw [UInt64.toNat_add, UInt64.toNat_shiftLeft, Nat.shiftLeft_eq]
  show (w.toNat * 2 ^ 8 % 2 ^ 64 + z.toNat) % 2 ^ 64 = _
  omega

theorem toNat_shl56_add (w y : UInt64) :
    ((y <<< 56) + (w >>> 8)).toNat = y.toNat % 256 * 2 ^ 56 + w.toNat / 256 := by
  have hw := UInt64.toNat_lt w
  have hy := UInt64.toNat_lt y
  rw [UInt64.toNat_add, UInt64.toNat_shiftLeft, Nat.shiftLeft_eq, UInt64.toNat_shiftRight,
    Nat.shiftRight_eq_div_pow]
  show (y.toNat * 2 ^ 56 % 2 ^ 64 + w.toNat / 2 ^ 8) % 2 ^ 64 = _
  omega

theorem toNat_shr56 (w : UInt64) : (w >>> 56).toNat < 256 := by
  have hw := UInt64.toNat_lt w
  rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  show w.toNat / 2 ^ 56 < 256
  omega

theorem toUInt8_and255 (x : UInt64) : (x &&& 255).toUInt8 = x.toUInt8 := by
  apply UInt8.toNat_inj.mp
  rw [UInt64.toNat_toUInt8, UInt64.toNat_toUInt8, UInt64.toNat_and,
    show (255 : UInt64).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod]

theorem length_bytes (b : Bytes40) : b.bytes.length = 40 := rfl

theorem push40_bytes (b : Bytes40) (x : UInt64) :
    (push40 b x).bytes = b.bytes.tail ++ [x.toUInt8] := by
  have e0 := wordBytes8_shl (w := b.w0) (toNat_shr56 b.w1) (toNat_shl8_add _ _ (toNat_shr56 _))
  have e1 := wordBytes8_shl (w := b.w1) (toNat_shr56 b.w2) (toNat_shl8_add _ _ (toNat_shr56 _))
  have e2 := wordBytes8_shl (w := b.w2) (toNat_shr56 b.w3) (toNat_shl8_add _ _ (toNat_shr56 _))
  have e3 := wordBytes8_shl (w := b.w3) (toNat_shr56 b.w4) (toNat_shl8_add _ _ (toNat_shr56 _))
  have e4 := wordBytes8_shl (w := b.w4) (and255_lt x) (toNat_shl8_add _ _ (and255_lt x))
  simp only [Bytes40.bytes, push40, e0, e1, e2, e3, e4, toUInt8_and255]
  simp [wordBytes8]

theorem unshift40_bytes (b : Bytes40) (x : UInt64) :
    (unshift40 b x).bytes = x.toUInt8 :: b.bytes.dropLast := by
  have e0 := wordBytes8_shr (y := x &&& 255) (toNat_shl56_add b.w0 _)
  have e1 := wordBytes8_shr (y := b.w0) (toNat_shl56_add b.w1 _)
  have e2 := wordBytes8_shr (y := b.w1) (toNat_shl56_add b.w2 _)
  have e3 := wordBytes8_shr (y := b.w2) (toNat_shl56_add b.w3 _)
  have e4 := wordBytes8_shr (y := b.w3) (toNat_shl56_add b.w4 _)
  simp only [Bytes40.bytes, unshift40, e0, e1, e2, e3, e4, toUInt8_and255]
  simp [wordBytes8]

theorem first40_eq (b : Bytes40) : (first40 b).toUInt8 = b.bytes.headD 0 := rfl

theorem first40_lt (b : Bytes40) : (first40 b).toNat < 256 := toNat_shr56 _

theorem last40_eq (b : Bytes40) : (last40 b).toUInt8 = b.bytes.getLastD 0 := by
  rw [last40, toUInt8_and255]
  rfl

theorem zero40_bytes : zero40.bytes = List.replicate 40 0 := rfl

/-! ## Decoding as a fold -/

/-- The state of COBS's decoder over a list: the bytes so far without the zero that the current
block gives at its end, the data bytes left in the current block, whether that block's code lies
below `0xFF`, and whether no error has occurred. -/
structure DecL where
  out : List UInt8
  rem : Nat
  zero : Bool
  ok : Bool

/-- The decoder after the byte `b`: a zero byte is an error, a byte at the end of a block starts
the next block, after the zero of the block before when its code lay below `0xFF`, and any
other byte is data. -/
def decStepL (d : DecL) (b : UInt8) : DecL :=
  if b = 0 then { d with ok := false }
  else if d.rem = 0 then ⟨d.out ++ (if d.zero then [0] else []), b.toNat - 1, b != 255, d.ok⟩
  else { d with out := d.out ++ [b], rem := d.rem - 1 }

/-- The decoder's state before the first byte. -/
def decInitL : DecL := ⟨[], 0, false, true⟩

/-- The record that the decoder's state `d` gives at the end of a segment. -/
def decFinish (d : DecL) : Option (List UInt8) :=
  if d.ok ∧ d.rem = 0 ∧ d.zero then some d.out else none

/-- The bytes so far with the zero of the current block. -/
def decZ (d : DecL) : List UInt8 := d.out ++ (if d.zero then [0] else [])

/-- The bytes that `cobsUnstuff` gives for the bytes so far, when no block is open. -/
def decFull (d : DecL) : Option (List UInt8) := if d.ok ∧ d.rem = 0 then some (decZ d) else none

theorem foldl_decStepL_notOk : ∀ (s : List UInt8) (d : DecL), d.ok = false →
    (s.foldl decStepL d).ok = false
  | [], _, h => h
  | b :: s, d, h => by
      apply foldl_decStepL_notOk s
      unfold decStepL
      split
      · rfl
      · split <;> exact h

theorem foldl_decStepL_data : ∀ (data : List UInt8) (d : DecL), 0 ∉ data →
    data.length ≤ d.rem →
      data.foldl decStepL d = ⟨d.out ++ data, d.rem - data.length, d.zero, d.ok⟩
  | [], d, _, _ => by simp
  | b :: data, d, hz, hl => by
      rw [List.mem_cons, not_or] at hz
      simp only [List.length_cons] at hl
      have hs : decStepL d b = ⟨d.out ++ [b], d.rem - 1, d.zero, d.ok⟩ := by
        unfold decStepL
        rw [ite_eq_right (Ne.symm hz.1), ite_eq_right (by omega)]
      rw [List.foldl_cons, hs, foldl_decStepL_data data _ hz.2 (by simp only; omega)]
      congr 1
      · simp
      · simp only [List.length_cons]
        omega

theorem foldl_decStepL_zero : ∀ (s : List UInt8) (d : DecL), 0 ∈ s.take d.rem →
    (s.foldl decStepL d).ok = false
  | [], d, h => by simp at h
  | b :: s, d, h => by
      rw [List.foldl_cons]
      by_cases hb : b = 0
      · apply foldl_decStepL_notOk
        unfold decStepL
        rw [ite_eq_left hb]
      · have hr : d.rem ≠ 0 := by
          intro h0
          rw [h0] at h
          simp at h
        obtain ⟨r, hr'⟩ : ∃ r, d.rem = r + 1 := ⟨d.rem - 1, by omega⟩
        rw [hr', List.take_succ_cons, List.mem_cons] at h
        apply foldl_decStepL_zero s
        unfold decStepL
        rw [ite_eq_right hb, ite_eq_right hr]
        simp only
        rw [show d.rem - 1 = r by omega]
        exact h.resolve_left (Ne.symm hb)

theorem decFull_foldl : ∀ (n : Nat) (s : List UInt8) (d : DecL), s.length ≤ n → d.ok = true →
    d.rem = 0 → decFull (s.foldl decStepL d) = (cobsUnstuff s).map (decZ d ++ ·)
  | _, [], d, _, hok, hrem => by
      simp [decFull, hok, hrem, cobsUnstuff]
  | 0, _ :: _, _, hn, _, _ => by simp at hn
  | n + 1, c :: rest, d, hn, hok, hrem => by
      rw [List.foldl_cons]
      by_cases hc : c = 0
      · have h1 : (rest.foldl decStepL (decStepL d c)).ok = false :=
          foldl_decStepL_notOk _ _ (by unfold decStepL; rw [ite_eq_left hc])
        rw [cobsUnstuff, ite_eq_left (Or.inl hc)]
        simp [decFull, h1]
      · have hd1 : decStepL d c = ⟨decZ d, c.toNat - 1, c != 255, true⟩ := by
          unfold decStepL
          rw [ite_eq_right hc, ite_eq_left hrem, hok]
          rfl
        rw [hd1]
        by_cases hbad : rest.length < c.toNat - 1 ∨ 0 ∈ rest.take (c.toNat - 1)
        · rw [cobsUnstuff, ite_eq_left (Or.inr hbad), Option.map_none]
          by_cases hz : 0 ∈ rest.take (c.toNat - 1)
          · have := foldl_decStepL_zero rest ⟨decZ d, c.toNat - 1, c != 255, true⟩ hz
            simp [decFull, this]
          · have hs : rest.length < c.toNat - 1 := hbad.resolve_right hz
            have hz' : 0 ∉ rest := by
              rwa [List.take_of_length_le (by omega)] at hz
            rw [foldl_decStepL_data rest _ hz' (by simp only; omega)]
            simp only [decFull]
            split
            · next h =>
              obtain ⟨-, h2⟩ := h
              omega
            · rfl
        · rw [not_or] at hbad
          have hdl : (rest.take (c.toNat - 1)).length = c.toNat - 1 := by
            rw [List.length_take]
            omega
          rw [← List.take_append_drop (c.toNat - 1) rest, List.foldl_append,
            foldl_decStepL_data _ _ hbad.2 (Nat.le_of_eq hdl),
            cobsUnstuff_block _ hc hdl hbad.2]
          simp only [hdl, Nat.sub_self]
          have hm : (rest.drop (c.toNat - 1)).length ≤ n := by
            simp only [List.length_cons] at hn
            rw [List.length_drop]
            omega
          rw [decFull_foldl n _ _ hm rfl rfl]
          cases cobsUnstuff (rest.drop (c.toNat - 1)) with
          | none => rfl
          | some u =>
              simp only [Option.map_some, decZ, List.append_assoc, Option.some.injEq]
              by_cases h255 : c = 255
              · simp [h255]
              · simp [h255]

/-- The decoder's states from `decInitL` that end no block with a code below `0xFF` end with a
nonzero byte or with no byte. -/
def DecLast (d : DecL) : Prop := d.rem = 0 → d.zero = false → d.out.getLast? ≠ some 0

theorem decLast_step (d : DecL) (b : UInt8) (h : DecLast d) : DecLast (decStepL d b) := by
  unfold decStepL DecLast
  split
  · exact h
  · next hb =>
    split
    · intro hr hz
      simp only at hr hz
      have : b = 255 := by simpa using hz
      have hb1 : b.toNat = 255 := by rw [this]; rfl
      omega
    · intro _ _
      simp only [List.getLast?_append, List.getLast?_singleton]
      simpa using hb

theorem decLast_foldl : ∀ (s : List UInt8) (d : DecL), DecLast d → DecLast (s.foldl decStepL d)
  | [], _, h => h
  | b :: s, d, h => decLast_foldl s _ (decLast_step d b h)

/-- `cobsDecode` as the left fold of `decStepL`. -/
theorem cobsDecode_fold (s : List UInt8) :
    cobsDecode s = decFinish (s.foldl decStepL decInitL) := by
  have hA := decFull_foldl s.length s decInitL (Nat.le_refl _) rfl rfl
  have hL := decLast_foldl s decInitL (fun _ _ => by simp [decInitL])
  have hmap : (cobsUnstuff s).map (decZ decInitL ++ ·) = cobsUnstuff s := by
    cases cobsUnstuff s <;> rfl
  rw [hmap] at hA
  generalize s.foldl decStepL decInitL = D at hA hL
  rw [cobsDecode, ← hA]
  unfold decFull decFinish decZ
  by_cases hok : D.ok = true ∧ D.rem = 0
  · rw [ite_eq_left hok]
    by_cases hz : D.zero = true
    · simp [hz, hok]
    · have hz' : D.zero = false := by simpa using hz
      have := hL hok.2 hz'
      simp [hz', this]
  · rw [ite_eq_right hok, ite_eq_right (fun h => hok ⟨h.1, h.2.1⟩)]

theorem length_foldl_decStepL : ∀ (s : List UInt8) (d : DecL),
    (s.foldl decStepL d).out.length ≤ d.out.length + s.length
  | [], d => by simp
  | b :: s, d => by
      have := length_foldl_decStepL s (decStepL d b)
      have h1 : (decStepL d b).out.length ≤ d.out.length + 1 := by
        unfold decStepL
        split
        · simp
        · split
          · simp only [List.length_append]
            split <;> simp
          · simp
      simp only [List.foldl_cons, List.length_cons]
      omega

/-! ## Decoding in words -/

/-- The state of the decoder in words: the buffer `src`, whose first byte is the next, the
positions `skip` to pass before the segment, the decoded bytes `out`, of which the last `olen`
count, the data bytes `rem` left in the current block, `zero` 1 when that block's code lies below
`0xFF`, and `ok` 1 while no error has occurred. -/
structure CobsDec where
  src : Bytes40
  skip : UInt64
  out : Bytes40
  olen : UInt64
  rem : UInt64
  zero : UInt64
  ok : UInt64

instance : Flat CobsDec (Bytes40 × UInt64 × Bytes40 × UInt64 × UInt64 × UInt64 × UInt64) :=
  ⟨fun d => (d.src, d.skip, d.out, d.olen, d.rem, d.zero, d.ok)⟩

/-- `decStepL` on the byte `x`. -/
def decByte (d : CobsDec) (x : UInt64) : CobsDec :=
  if x == 0 then { d with ok := 0 }
  else if d.rem == 0 then
    { d with
      out := if d.zero == 1 then push40 d.out 0 else d.out,
      olen := if d.zero == 1 then d.olen + 1 else d.olen,
      rem := x - 1,
      zero := if x == 255 then 0 else 1 }
  else { d with out := push40 d.out x, olen := d.olen + 1, rem := d.rem - 1 }

/-- One position of the buffer: skipped before the segment, decoded within it. -/
def decPos (d : CobsDec) : CobsDec :=
  if d.skip == 0 then decByte { d with src := push40 d.src 0 } (first40 d.src)
  else { d with src := push40 d.src 0, skip := d.skip - 1 }

/-- Eight positions. -/
def dec8 (d : CobsDec) : CobsDec :=
  decPos (decPos (decPos (decPos (decPos (decPos (decPos (decPos d)))))))

/-- The 40 positions of the buffer. -/
def decAll (d : CobsDec) : CobsDec := dec8 (dec8 (dec8 (dec8 (dec8 d))))

/-- The decoder's state after the last `n` bytes of `seg`. -/
def decodeWords (seg : Bytes40) (n : UInt64) : CobsDec :=
  decAll ⟨seg, 40 - n, zero40, 0, 0, 0, 1⟩

/-- The decoder in words holds the list-level decoder's state `dl`. -/
structure DecRel (d : CobsDec) (dl : DecL) : Prop where
  out : d.out.bytes.drop (40 - d.olen.toNat) = dl.out
  olen : d.olen.toNat = dl.out.length
  len : dl.out.length ≤ 40
  rem : d.rem.toNat = dl.rem
  rem_lt : dl.rem < 255
  zero : d.zero = if dl.zero then 1 else 0
  ok : d.ok = if dl.ok then 1 else 0

theorem toNat_add_one {x : UInt64} (h : x.toNat < 2 ^ 63) : (x + 1).toNat = x.toNat + 1 := by
  rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
  omega

theorem toNat_sub_one {x : UInt64} (h : x.toNat ≠ 0) : (x - 1).toNat = x.toNat - 1 :=
  UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by show 1 ≤ x.toNat; omega))

theorem push40_drop (b : Bytes40) {k : Nat} (hk : k < 40) (x : UInt64) :
    (push40 b x).bytes.drop (40 - (k + 1)) = b.bytes.drop (40 - k) ++ [x.toUInt8] := by
  rw [push40_bytes, show 40 - (k + 1) = 40 - k - 1 by omega]
  exact drop_tail_append _ _ (by omega) (by rw [length_bytes]; omega)

theorem toUInt8_ne_255 {x : UInt64} (hx : x.toNat < 256) (h : x ≠ 255) : x.toUInt8 ≠ 255 := by
  intro e
  apply h
  apply UInt64.toNat_inj.mp
  have := congrArg UInt8.toNat e
  rw [UInt64.toNat_toUInt8] at this
  show x.toNat = 255
  simp at this
  omega

theorem decByte_rel {d : CobsDec} {dl : DecL} (h : DecRel d dl) {x : UInt64}
    (hx : x.toNat < 256) (hl : dl.out.length < 40) :
    DecRel (decByte d x) (decStepL dl x.toUInt8) ∧ (decByte d x).src = d.src ∧
      (decByte d x).skip = d.skip := by
  have hx8 : x.toUInt8.toNat = x.toNat := by rw [UInt64.toNat_toUInt8]; omega
  have hol := h.olen
  have hrm := h.rem_lt
  by_cases h0 : x = 0
  · have h0' : x.toUInt8 = 0 := by rw [h0]; rfl
    have e1 : decByte d x = { d with ok := 0 } := by
      unfold decByte
      rw [ite_eq_left (by simp [h0])]
    have e2 : decStepL dl x.toUInt8 = { dl with ok := false } := by
      unfold decStepL
      rw [ite_eq_left h0']
    rw [e1, e2]
    exact ⟨⟨h.out, h.olen, h.len, h.rem, h.rem_lt, h.zero, rfl⟩, rfl, rfl⟩
  have h0' : x.toUInt8 ≠ 0 := fun e => h0 ((toUInt8_eq_zero hx).mp e)
  have hxn : x.toNat ≠ 0 := fun e => h0 (UInt64.toNat_inj.mp e)
  have hx0 : (x == 0) = false := by simpa using h0
  by_cases hr : dl.rem = 0
  · have hr' : (d.rem == 0) = true := by
      rw [beq_iff_eq]
      exact UInt64.toNat_inj.mp (by rw [h.rem, hr]; rfl)
    have e2 : decStepL dl x.toUInt8 = ⟨dl.out ++ (if dl.zero then [0] else []),
        x.toUInt8.toNat - 1, x.toUInt8 != 255, dl.ok⟩ := by
      unfold decStepL
      rw [ite_eq_right h0', ite_eq_left hr]
    have hz255 : (if x == 255 then (0 : UInt64) else 1) =
        if (x.toUInt8 != 255) = true then 1 else 0 := by
      by_cases e : x = 255
      · subst e
        rfl
      · have e' := toUInt8_ne_255 hx e
        simp [e, e']
    by_cases hz : dl.zero = true
    · have hz' : (d.zero == 1) = true := by rw [h.zero, hz]; rfl
      have e1 : decByte d x = { d with
          out := push40 d.out 0, olen := d.olen + 1, rem := x - 1,
          zero := if x == 255 then 0 else 1 } := by
        unfold decByte
        rw [hx0, hr', hz']
        rfl
      rw [e1, e2]
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, h.ok⟩, rfl, rfl⟩
      · show (push40 d.out 0).bytes.drop (40 - (d.olen + 1).toNat) = _
        rw [toNat_add_one (by omega), push40_drop _ (by omega), h.out, ite_eq_left hz]
        rfl
      · show (d.olen + 1).toNat = _
        rw [toNat_add_one (by omega), ite_eq_left hz, List.length_append, hol]
        rfl
      · show (dl.out ++ (if dl.zero then [0] else [])).length ≤ 40
        rw [ite_eq_left hz, List.length_append, List.length_singleton]
        omega
      · show (x - 1).toNat = _
        rw [toNat_sub_one hxn, hx8]
      · show x.toUInt8.toNat - 1 < 255
        omega
      · exact hz255
    · have hz' : (d.zero == 1) = false := by
        rw [h.zero, ite_eq_right hz]
        rfl
      have e1 : decByte d x = { d with rem := x - 1, zero := if x == 255 then 0 else 1 } := by
        unfold decByte
        rw [hx0, hr', hz']
        rfl
      rw [e1, e2]
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, h.ok⟩, rfl, rfl⟩
      · show d.out.bytes.drop (40 - d.olen.toNat) = _
        rw [h.out, ite_eq_right hz, List.append_nil]
      · show d.olen.toNat = _
        rw [ite_eq_right hz, List.append_nil, hol]
      · show (dl.out ++ (if dl.zero then [0] else [])).length ≤ 40
        rw [ite_eq_right hz, List.append_nil]
        omega
      · show (x - 1).toNat = _
        rw [toNat_sub_one hxn, hx8]
      · show x.toUInt8.toNat - 1 < 255
        omega
      · exact hz255
  · have hr' : (d.rem == 0) = false := by
      rw [beq_eq_false_iff_ne]
      intro e
      apply hr
      rw [← h.rem, e]
      rfl
    have e1 : decByte d x =
        { d with out := push40 d.out x, olen := d.olen + 1, rem := d.rem - 1 } := by
      unfold decByte
      rw [hx0, hr']
      rfl
    have e2 : decStepL dl x.toUInt8 =
        { dl with out := dl.out ++ [x.toUInt8], rem := dl.rem - 1 } := by
      unfold decStepL
      rw [ite_eq_right h0', ite_eq_right hr]
    rw [e1, e2]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, h.zero, h.ok⟩, rfl, rfl⟩
    · show (push40 d.out x).bytes.drop (40 - (d.olen + 1).toNat) = _
      rw [toNat_add_one (by omega), push40_drop _ (by omega), h.out]
    · show (d.olen + 1).toNat = _
      rw [toNat_add_one (by omega), List.length_append, hol]
      rfl
    · show (dl.out ++ [x.toUInt8]).length ≤ 40
      rw [List.length_append, List.length_singleton]
      omega
    · show (d.rem - 1).toNat = _
      rw [toNat_sub_one (by rw [h.rem]; exact hr), h.rem]
    · show dl.rem - 1 < 255
      omega

theorem headD_drop_append {S : List UInt8} {j : Nat} (hj : j < S.length) (z : List UInt8) :
    (S.drop j ++ z).headD 0 = (S.drop j).headD 0 := by
  rw [List.drop_eq_getElem_cons hj]
  rfl

theorem tail_drop_append {S : List UInt8} {j : Nat} (hj : j < S.length) :
    (S.drop j ++ List.replicate j 0).tail ++ [0] = S.drop (j + 1) ++ List.replicate (j + 1) 0 := by
  rw [List.drop_eq_getElem_cons hj, List.cons_append, List.tail_cons, List.append_assoc,
    List.replicate_succ']

theorem take_succ_drop {S : List UInt8} {j s : Nat} (hj : j < S.length) (hs : s ≤ j) :
    (S.take (j + 1)).drop s = (S.take j).drop s ++ [(S.drop j).headD 0] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some,
    List.drop_append_of_le_length (by rw [List.length_take]; omega),
    List.drop_eq_getElem_cons hj]
  rfl

theorem decPos_iter (d0 : CobsDec) {s : Nat} (hs : s ≤ 40) (hsk : d0.skip.toNat = s)
    (h0 : DecRel d0 decInitL) : ∀ j, j ≤ 40 →
      DecRel (decPos^[j] d0) (((d0.src.bytes.take j).drop s).foldl decStepL decInitL) ∧
        (decPos^[j] d0).src.bytes = d0.src.bytes.drop j ++ List.replicate j 0 ∧
        (decPos^[j] d0).skip.toNat = s - j
  | 0, _ => ⟨by simpa using h0, by simp, by simp [hsk]⟩
  | j + 1, hj => by
      obtain ⟨hr, hsrc, hskip⟩ := decPos_iter d0 hs hsk h0 j (by omega)
      rw [Function.iterate_succ_apply']
      generalize decPos^[j] d0 = d at hr hsrc hskip
      have hS : d0.src.bytes.length = 40 := length_bytes _
      have hsrc' : (push40 d.src 0).bytes = d0.src.bytes.drop (j + 1) ++
          List.replicate (j + 1) 0 := by
        rw [push40_bytes, hsrc, show ((0 : UInt64).toUInt8) = 0 from rfl,
          tail_drop_append (by omega)]
      by_cases hk : j < s
      · have hd : (d.skip == 0) = false := by
          rw [beq_eq_false_iff_ne]
          intro e
          rw [e] at hskip
          simp at hskip
          omega
        have e : decPos d = { d with src := push40 d.src 0, skip := d.skip - 1 } := by
          unfold decPos
          rw [hd]
          rfl
        rw [e]
        refine ⟨?_, hsrc', ?_⟩
        · rw [List.drop_eq_nil_of_le (by rw [List.length_take]; omega)]
          rw [List.drop_eq_nil_of_le (by rw [List.length_take]; omega)] at hr
          exact ⟨hr.out, hr.olen, hr.len, hr.rem, hr.rem_lt, hr.zero, hr.ok⟩
        · show (d.skip - 1).toNat = _
          rw [toNat_sub_one (by omega), hskip]
          omega
      · have hd : (d.skip == 0) = true := by
          rw [beq_iff_eq]
          exact UInt64.toNat_inj.mp (by rw [hskip]; show s - j = 0; omega)
        have e : decPos d = decByte { d with src := push40 d.src 0 } (first40 d.src) := by
          unfold decPos
          rw [hd]
          rfl
        have hlen : (((d0.src.bytes.take j).drop s).foldl decStepL decInitL).out.length < 40 := by
          have := length_foldl_decStepL ((d0.src.bytes.take j).drop s) decInitL
          rw [List.length_drop, List.length_take, show decInitL.out.length = 0 from rfl] at this
          omega
        have hfirst : (first40 d.src).toUInt8 = (d0.src.bytes.drop j).headD 0 := by
          rw [first40_eq, hsrc, headD_drop_append (by omega)]
        obtain ⟨hr', hsrc2, hskip2⟩ := decByte_rel (d := { d with src := push40 d.src 0 })
          ⟨hr.out, hr.olen, hr.len, hr.rem, hr.rem_lt, hr.zero, hr.ok⟩ (first40_lt _) hlen
        rw [e]
        refine ⟨?_, by rw [hsrc2]; exact hsrc', by rw [hskip2]; show d.skip.toNat = _; omega⟩
        rw [take_succ_drop (by omega) (by omega), List.foldl_append, List.foldl_cons,
          List.foldl_nil, ← hfirst]
        exact hr'

theorem iterate_eight {β : Type} (f : β → β) (x : β) :
    f^[8] x = f (f (f (f (f (f (f (f x))))))) := rfl

theorem iterate_five {β : Type} (f : β → β) (x : β) : f^[5] x = f (f (f (f (f x)))) := rfl

theorem dec8_iter : dec8 = decPos^[8] := by
  funext d
  rw [iterate_eight]
  rfl

theorem decAll_iter (d : CobsDec) : decAll d = decPos^[40] d := by
  rw [show (40 : Nat) = 8 * 5 from rfl, Function.iterate_mul, ← dec8_iter, iterate_five]
  rfl

/-- The decoder in words, after the last `n` bytes of `seg`, holds the list-level decoder's state
after those bytes. -/
theorem decodeWords_spec (seg : Bytes40) {n : UInt64} (hn : n.toNat ≤ 40) :
    DecRel (decodeWords seg n) ((seg.bytes.drop (40 - n.toNat)).foldl decStepL decInitL) := by
  have hsk : (⟨seg, 40 - n, zero40, 0, 0, 0, 1⟩ : CobsDec).skip.toNat = 40 - n.toNat := by
    show (40 - n).toNat = _
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hn)]
    rfl
  have h := (decPos_iter ⟨seg, 40 - n, zero40, 0, 0, 0, 1⟩ (by omega) hsk
    ⟨rfl, rfl, by simp [decInitL], rfl, by simp [decInitL], rfl, rfl⟩ 40 (Nat.le_refl _)).1
  rw [decodeWords, decAll_iter]
  rwa [List.take_of_length_le (by rw [length_bytes])] at h

/-- `cobsDecode` of the last `n` bytes of `seg` from the decoder in words. -/
theorem decodeWords_eq (seg : Bytes40) {n : UInt64} (hn : n.toNat ≤ 40) :
    cobsDecode (seg.bytes.drop (40 - n.toNat)) =
      if (decodeWords seg n).ok = 1 ∧ (decodeWords seg n).rem = 0 ∧ (decodeWords seg n).zero = 1
      then some ((decodeWords seg n).out.bytes.drop (40 - (decodeWords seg n).olen.toNat))
      else none := by
  have h := decodeWords_spec seg hn
  rw [cobsDecode_fold]
  generalize decodeWords seg n = d at h
  generalize (seg.bytes.drop (40 - n.toNat)).foldl decStepL decInitL = dl at h
  unfold decFinish
  have e : (d.ok = 1 ∧ d.rem = 0 ∧ d.zero = 1) ↔ (dl.ok = true ∧ dl.rem = 0 ∧ dl.zero = true) := by
    rw [h.ok, h.zero]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨?_, ?_, ?_⟩
      · cases hh : dl.ok
        · rw [hh] at h1; exact absurd h1 (by decide)
        · rfl
      · rw [← h.rem, h2]; rfl
      · cases hh : dl.zero
        · rw [hh] at h3; exact absurd h3 (by decide)
        · rfl
    · rintro ⟨h1, h2, h3⟩
      refine ⟨by rw [h1]; rfl, UInt64.toNat_inj.mp (by rw [h.rem, h2]; rfl), by rw [h3]; rfl⟩
  by_cases hv : dl.ok = true ∧ dl.rem = 0 ∧ dl.zero = true
  · rw [ite_eq_left hv, ite_eq_left (e.mpr hv), h.out]
  · rw [ite_eq_right hv, ite_eq_right (fun h' => hv (e.mp h'))]

/-- The decoded bytes number at most the bytes of the segment. -/
theorem decodeWords_olen (seg : Bytes40) {n : UInt64} (hn : n.toNat ≤ 40) :
    (decodeWords seg n).olen.toNat ≤ n.toNat := by
  have h := decodeWords_spec seg hn
  have := length_foldl_decStepL (seg.bytes.drop (40 - n.toNat)) decInitL
  rw [h.olen]
  rw [List.length_drop, length_bytes, show decInitL.out.length = 0 from rfl] at this
  omega

/-! ## Encoding from the end -/

/-- The encoder after the byte `x`, which precedes the bytes already encoded: the encoded bytes
`p.1` after the first code byte, and `p.2`, the distance from `x`'s successor to the next zero or
to the end. -/
def encStepL (x : UInt8) (p : List UInt8 × Nat) : List UInt8 × Nat :=
  if x = 0 then (UInt8.ofNat p.2 :: p.1, 1) else (x :: p.1, p.2 + 1)

/-- The encoder's state after the bytes `r`, from the last back. -/
def encBack (r : List UInt8) : List UInt8 × Nat := r.foldr encStepL ([], 1)

theorem encBack_cons (x : UInt8) (r : List UInt8) : encBack (x :: r) = encStepL x (encBack r) :=
  rfl

theorem encBack_bounds : ∀ r : List UInt8,
    (encBack r).1.length = r.length ∧ 1 ≤ (encBack r).2 ∧ (encBack r).2 ≤ r.length + 1
  | [] => by simp [encBack]
  | x :: r => by
      obtain ⟨h1, h2, h3⟩ := encBack_bounds r
      rw [encBack_cons, encStepL]
      split <;> simp <;> omega

theorem cobsStuff_back : ∀ (bs blk : List UInt8), blk.length + bs.length ≤ 253 →
    cobsStuff bs blk = UInt8.ofNat (blk.length + (encBack bs).2) :: (blk ++ (encBack bs).1)
  | [], blk, _ => by simp [cobsStuff, encBack]
  | b :: bs, blk, hl => by
      simp only [List.length_cons] at hl
      rw [cobsStuff, encBack_cons, encStepL]
      by_cases hb : b = 0
      · rw [ite_eq_left hb, ite_eq_left hb, cobsStuff_back bs [] (by simp; omega)]
        simp
      · rw [ite_eq_right hb, ite_eq_right hb, ite_eq_right (by omega),
          cobsStuff_back bs (blk ++ [b]) (by simp; omega)]
        simp only [List.length_append, List.length_singleton, List.append_assoc,
          List.singleton_append, List.cons.injEq, and_true]
        congr 1
        omega

/-- `cobsEncode` of a record shorter than 254 bytes as the right fold of `encStepL`. -/
theorem cobsEncode_back {r : List UInt8} (h : r.length < 254) :
    cobsEncode r = UInt8.ofNat (encBack r).2 :: (encBack r).1 := by
  rw [cobsEncode, cobsStuff_back r [] (by simp; omega)]
  simp

/-! ## Encoding in words -/

/-- The state of the encoder in words: the buffer `src`, of whose bytes the last `cnt` remain to
encode, the distance `dist` to the next zero or to the end, and the encoded bytes `dst`, of which
the first `dlen` count. -/
structure CobsEnc where
  src : Bytes40
  cnt : UInt64
  dist : UInt64
  dst : Bytes40
  dlen : UInt64

instance : Flat CobsEnc (Bytes40 × UInt64 × UInt64 × Bytes40 × UInt64) :=
  ⟨fun e => (e.src, e.cnt, e.dist, e.dst, e.dlen)⟩

/-- `encStepL` on the byte `x`. -/
def encByte (e : CobsEnc) (x : UInt64) : CobsEnc :=
  if x == 0 then { e with dst := unshift40 e.dst e.dist, dist := 1, dlen := e.dlen + 1 }
  else { e with dst := unshift40 e.dst x, dist := e.dist + 1, dlen := e.dlen + 1 }

/-- The last remaining byte of the source, if any. -/
def encPos (e : CobsEnc) : CobsEnc :=
  if e.cnt == 0 then e
  else encByte { e with src := unshift40 e.src 0, cnt := e.cnt - 1 } (last40 e.src)

/-- Eight positions. -/
def enc8 (e : CobsEnc) : CobsEnc :=
  encPos (encPos (encPos (encPos (encPos (encPos (encPos (encPos e)))))))

/-- The 40 positions of the source. -/
def encAll (e : CobsEnc) : CobsEnc := enc8 (enc8 (enc8 (enc8 (enc8 e))))

/-- The encoder before any byte, with the last `n` bytes of `src` to encode. -/
def encStart (src : Bytes40) (n : UInt64) : CobsEnc := ⟨src, n, 1, zero40, 0⟩

/-- The encoded bytes: the first code byte and the bytes after it. -/
def encFinish (e : CobsEnc) : Bytes40 := unshift40 e.dst e.dist

/-- The encoder in words holds the list-level encoder's state `p`. -/
structure EncRel (e : CobsEnc) (p : List UInt8 × Nat) : Prop where
  dst : e.dst.bytes = p.1 ++ List.replicate (40 - p.1.length) 0
  len : p.1.length ≤ 40
  dlen : e.dlen.toNat = p.1.length
  dist : e.dist.toNat = p.2
  dist_le : p.2 ≤ p.1.length + 1

theorem unshift40_rel {b : Bytes40} {t : List UInt8} (hb : b.bytes = t ++ List.replicate (40 - t.length) 0)
    (ht : t.length < 40) (y : UInt64) :
    (unshift40 b y).bytes = (y.toUInt8 :: t) ++ List.replicate (40 - (t.length + 1)) 0 := by
  rw [unshift40_bytes, hb, List.dropLast_append_of_ne_nil (by simp; omega),
    show 40 - t.length = 40 - (t.length + 1) + 1 by omega, List.replicate_succ',
    List.dropLast_concat]
  rfl

theorem toUInt8_eq_ofNat (x : UInt64) : x.toUInt8 = UInt8.ofNat x.toNat := by
  apply UInt8.toNat_inj.mp
  rw [UInt64.toNat_toUInt8, UInt8.toNat_ofNat']

theorem encByte_rel {e : CobsEnc} {p : List UInt8 × Nat} (h : EncRel e p) {x : UInt64}
    (hx : x.toNat < 256) (hl : p.1.length < 40) :
    EncRel (encByte e x) (encStepL x.toUInt8 p) ∧ (encByte e x).src = e.src ∧
      (encByte e x).cnt = e.cnt := by
  have hd := h.dist_le
  have hdl := h.dlen
  by_cases h0 : x = 0
  · have h0' : x.toUInt8 = 0 := by rw [h0]; rfl
    have e1 : encByte e x =
        { e with dst := unshift40 e.dst e.dist, dist := 1, dlen := e.dlen + 1 } := by
      unfold encByte
      rw [ite_eq_left (by simp [h0])]
    rw [e1, encStepL, ite_eq_left h0']
    refine ⟨⟨?_, ?_, ?_, rfl, ?_⟩, rfl, rfl⟩
    · show (unshift40 e.dst e.dist).bytes = _
      rw [unshift40_rel h.dst (by omega), toUInt8_eq_ofNat, h.dist]
      rfl
    · show p.1.length + 1 ≤ 40
      omega
    · show (e.dlen + 1).toNat = p.1.length + 1
      rw [toNat_add_one (by omega), hdl]
    · show 1 ≤ p.1.length + 1 + 1
      omega
  · have h0' : x.toUInt8 ≠ 0 := fun e => h0 ((toUInt8_eq_zero hx).mp e)
    have e1 : encByte e x =
        { e with dst := unshift40 e.dst x, dist := e.dist + 1, dlen := e.dlen + 1 } := by
      unfold encByte
      rw [ite_eq_right (by simpa using h0)]
    rw [e1, encStepL, ite_eq_right h0']
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, rfl, rfl⟩
    · show (unshift40 e.dst x).bytes = _
      rw [unshift40_rel h.dst (by omega)]
      rfl
    · show p.1.length + 1 ≤ 40
      omega
    · show (e.dlen + 1).toNat = p.1.length + 1
      rw [toNat_add_one (by omega), hdl]
    · show (e.dist + 1).toNat = p.2 + 1
      rw [toNat_add_one (by rw [h.dist]; omega), h.dist]
    · show p.2 + 1 ≤ p.1.length + 1 + 1
      omega

theorem getLastD_rep_take {S : List UInt8} {j : Nat} (h : 40 - (j + 1) < S.length) (hj : j < 40) :
    (List.replicate j 0 ++ S.take (40 - j)).getLastD 0 = S[40 - (j + 1)] := by
  rw [show 40 - j = 40 - (j + 1) + 1 by omega, List.take_add_one, List.getElem?_eq_getElem h,
    Option.toList_some, ← List.append_assoc, List.getLastD_eq_getLast?, List.getLast?_concat,
    Option.getD_some]

theorem rep_take_unshift {S : List UInt8} {j : Nat} (h : 40 - (j + 1) < S.length) (hj : j < 40) :
    0 :: (List.replicate j 0 ++ S.take (40 - j)).dropLast =
      List.replicate (j + 1) 0 ++ S.take (40 - (j + 1)) := by
  rw [show 40 - j = 40 - (j + 1) + 1 by omega, List.take_add_one, List.getElem?_eq_getElem h,
    Option.toList_some, ← List.append_assoc, List.dropLast_concat, List.replicate_succ]
  rfl

theorem drop_pred_cons {S : List UInt8} {j : Nat} (h : 40 - (j + 1) < S.length) (hj : j < 40) :
    S.drop (40 - (j + 1)) = S[40 - (j + 1)] :: S.drop (40 - j) := by
  rw [List.drop_eq_getElem_cons h, show 40 - (j + 1) + 1 = 40 - j by omega]

theorem encPos_iter (e0 : CobsEnc) {c : Nat} (hc : c ≤ 40) (hcnt : e0.cnt.toNat = c)
    (h0 : EncRel e0 ([], 1)) : ∀ j, j ≤ 40 →
      EncRel (encPos^[j] e0) (encBack (e0.src.bytes.drop (40 - min j c))) ∧
        (encPos^[j] e0).src.bytes = List.replicate (min j c) 0 ++
          e0.src.bytes.take (40 - min j c) ∧
        (encPos^[j] e0).cnt.toNat = c - min j c
  | 0, _ => by
      refine ⟨?_, by simp [length_bytes], by simp [hcnt]⟩
      rw [Nat.zero_min, Nat.sub_zero, List.drop_eq_nil_of_le (by rw [length_bytes])]
      exact h0
  | j + 1, hj => by
      obtain ⟨hr, hsrc, hcn⟩ := encPos_iter e0 hc hcnt h0 j (by omega)
      rw [Function.iterate_succ_apply']
      generalize encPos^[j] e0 = e at hr hsrc hcn
      have hS : e0.src.bytes.length = 40 := length_bytes _
      by_cases hk : c ≤ j
      · have hm : min (j + 1) c = min j c := by omega
        have hd : (e.cnt == 0) = true := by
          rw [beq_iff_eq]
          exact UInt64.toNat_inj.mp (by rw [hcn]; show c - min j c = 0; omega)
        have e1 : encPos e = e := by
          unfold encPos
          rw [hd]
          rfl
        rw [e1, hm]
        exact ⟨hr, hsrc, hcn⟩
      · have hm : min (j + 1) c = j + 1 := by omega
        have hm' : min j c = j := by omega
        rw [hm'] at hr hsrc hcn
        rw [hm]
        have hd : (e.cnt == 0) = false := by
          rw [beq_eq_false_iff_ne]
          intro h
          rw [h] at hcn
          simp at hcn
          omega
        have e1 : encPos e = encByte { e with src := unshift40 e.src 0, cnt := e.cnt - 1 }
            (last40 e.src) := by
          unfold encPos
          rw [hd]
          rfl
        have hlast : (last40 e.src).toUInt8 = e0.src.bytes[40 - (j + 1)]'(by omega) := by
          rw [last40_eq, hsrc, getLastD_rep_take (by omega) (by omega)]
        have hlen := (encBack_bounds (e0.src.bytes.drop (40 - j))).1
        rw [List.length_drop, hS] at hlen
        obtain ⟨hr', hsrc2, hcnt2⟩ := encByte_rel
          (e := { e with src := unshift40 e.src 0, cnt := e.cnt - 1 }) (x := last40 e.src)
          ⟨hr.dst, hr.len, hr.dlen, hr.dist, hr.dist_le⟩
          (and255_lt e.src.w4) (by rw [hlen]; omega)
        rw [e1]
        refine ⟨?_, ?_, ?_⟩
        · rw [drop_pred_cons (by omega) (by omega), encBack_cons, ← hlast]
          exact hr'
        · rw [hsrc2]
          show (unshift40 e.src 0).bytes = _
          rw [unshift40_bytes, hsrc]
          exact rep_take_unshift (by omega) (by omega)
        · rw [hcnt2]
          show (e.cnt - 1).toNat = _
          rw [toNat_sub_one (by omega), hcn]
          omega

theorem enc8_iter : enc8 = encPos^[8] := by
  funext e
  rw [iterate_eight]
  rfl

theorem encAll_iter (e : CobsEnc) : encAll e = encPos^[40] e := by
  rw [show (40 : Nat) = 8 * 5 from rfl, Function.iterate_mul, ← enc8_iter, iterate_five]
  rfl

theorem encStart_rel (src : Bytes40) (n : UInt64) : EncRel (encStart src n) ([], 1) :=
  ⟨zero40_bytes, by simp, rfl, rfl, by simp⟩

/-- The encoder in words, after the last `n` bytes of `src`, holds the list-level encoder's state
after those bytes. -/
theorem encAll_spec (src : Bytes40) {n : UInt64} (hn : n.toNat ≤ 40) :
    EncRel (encAll (encStart src n)) (encBack (src.bytes.drop (40 - n.toNat))) := by
  have h := (encPos_iter (encStart src n) hn rfl (encStart_rel src n) 40 (Nat.le_refl _)).1
  rw [encAll_iter]
  rwa [show min 40 n.toNat = n.toNat by omega] at h

/-- The byte `x` before the bytes encoded so far. -/
theorem encByte_spec {e : CobsEnc} {r : List UInt8} (h : EncRel e (encBack r)) {x : UInt64}
    (hx : x.toNat < 256) (hr : r.length < 40) :
    EncRel (encByte e x) (encBack (x.toUInt8 :: r)) := by
  rw [encBack_cons]
  exact (encByte_rel h hx (by rw [(encBack_bounds r).1]; exact hr)).1

/-- The encoded bytes followed by a `0x00`, for a record of at most 38 bytes. -/
theorem encFinish_spec {e : CobsEnc} {r : List UInt8} (h : EncRel e (encBack r))
    (hr : r.length ≤ 38) :
    (encFinish e).bytes.take (e.dlen.toNat + 2) = cobsEncode r ++ [0] := by
  obtain ⟨hl, hd1, hd2⟩ := encBack_bounds r
  rw [encFinish, unshift40_rel h.dst (by rw [hl]; omega), h.dlen, hl, cobsEncode_back (by omega),
    toUInt8_eq_ofNat, h.dist, show 40 - (r.length + 1) =
      (40 - (r.length + 2)) + 1 by omega, List.replicate_succ]
  rw [show (UInt8.ofNat (encBack r).2 :: (encBack r).1) ++ 0 :: List.replicate (40 - (r.length + 2)) 0 =
      ((UInt8.ofNat (encBack r).2 :: (encBack r).1) ++ [0]) ++ List.replicate (40 - (r.length + 2)) 0
      by simp]
  rw [List.take_append_of_le_length (by simp [hl]), List.take_of_length_le (by simp [hl])]

/-- The number of bytes that `encFinish` gives with the delimiter, as a word. -/
theorem encFinish_count {e : CobsEnc} {r : List UInt8} (h : EncRel e (encBack r))
    (hr : r.length ≤ 38) : (e.dlen + 2).toNat = r.length + 2 := by
  rw [UInt64.toNat_add, h.dlen, (encBack_bounds r).1]
  show (r.length + 2) % 2 ^ 64 = _
  omega

end LeanExe.Requests
