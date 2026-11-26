module

public import Demos.RandomChoice.PicksSpec
public import Demos.RandomChoice.Proof
public import Demos.RandomHistogram.CommandProof

@[expose] public section

/-! `putPicks` equals its specification on every draw of fewer than `2^32` bytes
(`putPicks_eq`).

`Bytes.set` replaces one byte of the list of a buffer's bytes, or none past its end
(`set_getD`).  `putLineBytes` writes the bytes of `lineWords v`, the digits of `v` and a newline,
from a position and keeps the other bytes (`putLineBytes_getD`).  The loop of `putPicks` keeps the
invariant that after `k` words its state holds the first `limit` values of those words, `P k`, the
number of bytes of their lines, and the buffer whose bytes are those lines followed by the bytes of
`out` after them.  A word that is rejected, or that comes when `limit` values are already held,
leaves `P k` and the state unchanged, and an accepted word below the limit appends its value to
`P k` and its line to the buffer.  The words that `putPicks` reads with `wordAt` are those of
`wordsOf`, which is the random histogram's `words`. -/

namespace Demos.RandomChoice

open LeanExe Library.Numerics.Decimal.Int64Text

/-! ## Bytes -/

theorem getD_eq_of_lt {α : Type} {l : List α} {i : Nat} {d : α} (h : i < l.length) :
    l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

/-- Two byte lists of the same length with the same bytes are equal. -/
theorem list_eq_of_getD {l l' : List UInt8} (hlen : l.length = l'.length)
    (h : ∀ i < l.length, l.getD i 0 = l'.getD i 0) : l = l' := by
  apply List.ext_getElem hlen
  intro i h1 h2
  have := h i h1
  rwa [getD_eq_of_lt h1, getD_eq_of_lt h2] at this

/-- A buffer is the buffer of its byte list. -/
theorem bytes_eq_of_toList {b : Bytes} {l : List UInt8} (h : b.data.data.toList = l) :
    b = ⟨⟨l.toArray⟩⟩ := by
  obtain ⟨⟨arr⟩⟩ := b
  subst h
  simp

/-- `Bytes.set` replaces byte `p` of the buffer's bytes when `p` lies below its size and keeps every
other byte. -/
theorem set_getD (b : Bytes) (p x : UInt64) (i : Nat) :
    (b.set p x).data.data.toList.getD i 0 =
      if i = p.toNat ∧ i < b.data.size then x.toUInt8 else b.data.data.toList.getD i 0 := by
  have hlen : b.data.data.toList.length = b.data.size := by simp
  unfold Bytes.set
  split
  · rename_i hp
    simp only [ByteArray.data_set, Array.toList_set]
    rw [List.getD_eq_getElem?_getD, List.getElem?_set, List.getD_eq_getElem?_getD]
    by_cases he : i = p.toNat
    · subst he
      rw [ite_eq_left rfl, ite_eq_left (by rw [hlen]; exact hp), ite_eq_left ⟨rfl, hp⟩, Option.getD_some]
    · rw [ite_eq_right (Ne.symm he), ite_eq_right (fun h => he h.1)]
  · rename_i hp
    rw [ite_eq_right (show ¬(i = p.toNat ∧ i < b.data.size) by omega)]

/-! ## The values of the words -/

/-- A pick is 0 exactly when the word is rejected. -/
theorem pickSpec_eq_zero (n w : UInt64) : pickSpec (n, w) = 0 ↔ accepts n w = false := by
  unfold pickSpec
  dsimp only
  by_cases ha : accepts n w = true
  · rw [ite_eq_left ha]
    have hn : n ≠ 0 := by
      intro h
      subst h
      simp [accepts] at ha
    have hpos : 0 < n.toNat := by
      rcases Nat.eq_zero_or_pos n.toNat with e | e
      · exact absurd (UInt64.toNat_inj.mp (by simpa using e)) hn
      · exact e
    have hmod : w.toNat % n.toNat < n.toNat := Nat.mod_lt _ hpos
    have hlt : n.toNat < 2 ^ 64 := n.toNat_lt
    have hsz : UInt64.size = 2 ^ 64 := rfl
    constructor
    · intro h
      have := congrArg UInt64.toNat h
      rw [UInt64.toNat_ofNat_of_lt' (by omega)] at this
      simp at this
    · intro h
      rw [ha] at h
      exact absurd h (by decide)
  · rw [ite_eq_right ha]
    simpa using ha

theorem valuesOf_append (n : UInt64) (a b : List UInt64) :
    valuesOf n (a ++ b) = valuesOf n a ++ valuesOf n b := by
  simp [valuesOf, List.filter_append]

theorem valuesOf_single (n w : UInt64) :
    valuesOf n [w] = if accepts n w = true then [pickSpec (n, w)] else [] := by
  by_cases h : accepts n w = true <;> simp [valuesOf, List.filter, h]

theorem valuesOf_length_le (n : UInt64) (ws : List UInt64) : (valuesOf n ws).length ≤ ws.length := by
  simpa [valuesOf] using List.length_filter_le _ ws

/-- The words of `wordsOf` are the random histogram's `words`. -/
theorem wordsOf_eq (bytes : List UInt8) : wordsOf bytes = RandomHistogram.words bytes := rfl

/-- The bytes of `renderSpec` of a list of values are those of its `textWords`. -/
theorem renderSpec_toList (values : List UInt64) :
    (renderSpec values.toArray).data.data.toList = (textWords values).map UInt64.toUInt8 := by
  show (values.toArray.toList.flatMap fun v =>
      (toString v.toNat).toList.map (fun c => c.toNat.toUInt8) ++ [10]).toArray.toList = _
  rw [List.toList_toArray, List.toList_toArray, textWords, List.map_flatMap]
  refine congrArg (fun f => List.flatMap f values) (funext fun v => ?_)
  rw [lineWords, List.map_append, RandomHistogram.digitWords_bytes]
  rfl

/-! ## putLineBytes -/

/-- `putLineBytes` writes the bytes of the line of `v` from `pos`, those that lie below the
buffer's size, and keeps every other byte. -/
theorem putLineBytes_getD (text : Bytes) (pos v : UInt64)
    (hsmall : pos.toNat + (lineWords v).length < 2 ^ 64) :
    (putLineBytes text pos v).data.size = text.data.size ∧
      ∀ i, (putLineBytes text pos v).data.data.toList.getD i 0 =
        if pos.toNat ≤ i ∧ i < pos.toNat + (lineWords v).length ∧ i < text.data.size then
          ((lineWords v).getD (i - pos.toNat) 0).toUInt8
        else text.data.data.toList.getD i 0 := by
  have hlen := lineWords_length v
  have hdw : (digitWords v.toNat).length = (digitCount v).toNat := (digitCount_toNat v).symm
  generalize hL : (digitCount v).toNat = L at hlen hdw
  have key := LeanExe.Dialect.loop_induction (n := digitCount v) (init := text)
    (f := fun k t => t.set (pos + k) (digitByte v (digitCount v - 1 - k)))
    (fun k t => t.data.size = text.data.size ∧ ∀ i, t.data.data.toList.getD i 0 =
      if pos.toNat ≤ i ∧ i < pos.toNat + k ∧ i < text.data.size then
        ((digitWords v.toNat).getD (i - pos.toNat) 0).toUInt8
      else text.data.data.toList.getD i 0)
    ⟨rfl, fun i => by rw [ite_eq_right (by omega)]⟩
    (by
      intro k t hk ⟨hsize, hget⟩
      rw [hL] at hk
      have hk64 : k < 2 ^ 64 := by omega
      have hpos : (pos + UInt64.ofNat k).toNat = pos.toNat + k := by
        rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' hk64]
        omega
      have hdigit := digitByte_word v (UInt64.ofNat k)
        (by rw [UInt64.toNat_ofNat_of_lt' hk64, hL]; omega)
      rw [UInt64.toNat_ofNat_of_lt' hk64] at hdigit
      refine ⟨by rw [Bytes.data_size_set, hsize], fun i => ?_⟩
      show (t.set (pos + UInt64.ofNat k) _).data.data.toList.getD i 0 = _
      rw [set_getD, hpos, hdigit, hsize, hget i]
      by_cases he : i = pos.toNat + k ∧ i < text.data.size
      · rw [ite_eq_left he, ite_eq_left ⟨by omega, by omega, he.2⟩, he.1, Nat.add_sub_cancel_left]
      · rw [ite_eq_right he]
        by_cases hin : pos.toNat ≤ i ∧ i < pos.toNat + k ∧ i < text.data.size
        · rw [ite_eq_left hin, ite_eq_left ⟨hin.1, by omega, hin.2.2⟩]
        · rw [ite_eq_right hin, ite_eq_right (by omega)])
  rw [hL] at key
  obtain ⟨hsize, hget⟩ := key
  have hnl : (pos + digitCount v).toNat = pos.toNat + L := by
    rw [UInt64.toNat_add, hL]
    omega
  unfold putLineBytes
  simp only
  refine ⟨by rw [Bytes.data_size_set, hsize], fun i => ?_⟩
  rw [set_getD, hnl, hsize, hget i]
  by_cases he : i = pos.toNat + L ∧ i < text.data.size
  · rw [ite_eq_left he, ite_eq_left ⟨by omega, by omega, he.2⟩, lineWords,
      List.getD_append_right _ _ _ _ (by omega)]
    simp [he.1, hdw]
  · rw [ite_eq_right he]
    by_cases hin : pos.toNat ≤ i ∧ i < pos.toNat + L ∧ i < text.data.size
    · rw [ite_eq_left hin, ite_eq_left ⟨hin.1, by omega, hin.2.2⟩, lineWords,
        List.getD_append _ _ _ _ (by omega)]
    · rw [ite_eq_right hin, ite_eq_right (by omega)]

/-! ## putPicks -/

/-- `putPicks` computes `putPicksSpec` on every draw of fewer than `2^32` bytes. -/
theorem putPicks_eq (out : Bytes) (n : UInt64) (draw : Bytes) (limit : UInt64)
    (hdraw : draw.data.size < 2 ^ 32) :
    putPicks out n draw limit = putPicksSpec (out, n, draw, limit) := by
  have hdlen : draw.data.data.toList.length = draw.data.size := by simp
  have hW : (draw.size / 8).toNat = (RandomHistogram.words draw.data.data.toList).length := by
    rw [UInt64.toNat_div, Bytes.size_toNat draw (by omega), RandomHistogram.words_length, hdlen]
    rfl
  generalize hws : RandomHistogram.words draw.data.data.toList = ws at hW
  have hwl : ws.length < 2 ^ 29 := by
    rw [← hws, RandomHistogram.words_length, hdlen]
    omega
  have hol : out.data.data.toList.length = out.data.size := by simp
  -- `P k`: the first `limit` values of the first `k` words.
  let P : Nat → List UInt64 := fun k => (valuesOf n (ws.take k)).take limit.toNat
  have hPlen : ∀ k, (P k).length ≤ k := fun k => by
    have h1 := valuesOf_length_le n (ws.take k)
    show ((valuesOf n (ws.take k)).take limit.toNat).length ≤ k
    rw [List.length_take] at h1 ⊢
    omega
  have hTlen : ∀ k, (textWords (P k)).length ≤ 21 * k := fun k =>
    (textWords_length_le (P k)).trans (by have := hPlen k; omega)
  have key := LeanExe.Dialect.loop_induction (n := draw.size / 8)
    (init := (out, (0 : UInt64), (0 : UInt64)))
    (f := fun j s =>
      let v := pick n (RandomHistogram.wordAt draw (8 * j))
      if v != 0 && s.2.2 < limit then
        (putLineBytes s.1 s.2.1 v, s.2.1 + digitCount v + 1, s.2.2 + 1)
      else (s.1, s.2.1, s.2.2))
    (fun k s => s.2.2.toNat = (P k).length ∧ s.2.1.toNat = (textWords (P k)).length ∧
      s.1.data.size = out.data.size ∧ ∀ i, s.1.data.data.toList.getD i 0 =
        if i < (textWords (P k)).length ∧ i < out.data.size then
          ((textWords (P k)).getD i 0).toUInt8
        else out.data.data.toList.getD i 0)
    ⟨by simp [P, valuesOf], by simp [P, valuesOf, textWords], rfl,
      fun i => by simp [P, valuesOf, textWords]⟩
    (by
      intro k s hk ⟨hcount, hpos, hsize, hget⟩
      rw [hW] at hk
      have h8 : (8 : UInt64) * UInt64.ofNat k = UInt64.ofNat (8 * k) := by
        apply UInt64.toNat_inj.mp
        simp only [UInt64.toNat_mul, UInt64.toNat_ofNat', UInt64.reduceToNat, Nat.reducePow]
        omega
      have hword : RandomHistogram.wordAt draw (8 * UInt64.ofNat k) = ws[k] := by
        have hw := RandomHistogram.words_getElem draw.data.data.toList k (by rw [hws]; exact hk)
        rw [h8, RandomHistogram.wordAt_eq draw (8 * k) (by
          have := RandomHistogram.words_length draw.data.data.toList
          rw [hws, hdlen] at this
          omega) (by omega)]
        simp only [hws] at hw
        rw [hw]
      have htake : ws.take (k + 1) = ws.take k ++ [ws[k]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hk]
        rfl
      generalize ws[k] = w at hword htake
      have hV : valuesOf n (ws.take (k + 1)) = valuesOf n (ws.take k) ++
          (if accepts n w = true then [pickSpec (n, w)] else []) := by
        rw [htake, valuesOf_append, valuesOf_single]
      have hVk := valuesOf_length_le n (ws.take k)
      have hPk : (P k).length = min (valuesOf n (ws.take k)).length limit.toNat := by
        show ((valuesOf n (ws.take k)).take limit.toNat).length = _
        rw [List.length_take, Nat.min_comm]
      have hTk := hTlen k
      have hPk' := hPlen k
      dsimp only
      rw [hword, pick_eq]
      have hless : (s.2.2 < limit) ↔ (P k).length < limit.toNat := by
        rw [UInt64.lt_iff_toNat_lt, hcount]
      by_cases hacc : accepts n w = true
      · have hnz : (pickSpec (n, w) != 0) = true := by
          have := (pickSpec_eq_zero n w).not.mpr (by simp [hacc])
          simpa using this
        by_cases hroom : (P k).length < limit.toNat
        · -- An accepted word below the limit: its value and its line are appended.
          have hcond : (pickSpec (n, w) != 0 && s.2.2 < limit) = true := by
            simp [hnz, hless.mpr hroom]
          rw [ite_eq_left hcond]
          have hnext : P (k + 1) = P k ++ [pickSpec (n, w)] := by
            show (valuesOf n (ws.take (k + 1))).take limit.toNat =
              (valuesOf n (ws.take k)).take limit.toNat ++ [pickSpec (n, w)]
            rw [hV, ite_eq_left hacc, List.take_of_length_le (by simp; omega),
              List.take_of_length_le (l := valuesOf n (ws.take k)) (by omega)]
          have hline := lineWords_length (pickSpec (n, w))
          have hdig : (digitCount (pickSpec (n, w))).toNat ≤ 20 := by
            rw [digitCount_toNat]
            exact digitWords_length_le _ (pickSpec (n, w)).toNat_lt
          obtain ⟨hsize', hget'⟩ := putLineBytes_getD s.1 s.2.1 (pickSpec (n, w))
            (by rw [hpos, hline]; omega)
          have hPL : (P k ++ [pickSpec (n, w)]).length = (P k).length + 1 := by simp
          have hTL : (textWords (P k) ++ lineWords (pickSpec (n, w))).length =
              (textWords (P k)).length + (lineWords (pickSpec (n, w))).length :=
            List.length_append ..
          rw [hnext, textWords_snoc]
          refine ⟨?_, ?_, by rw [hsize', hsize], fun i => ?_⟩
          · rw [UInt64.toNat_add, hcount, hPL, UInt64.toNat_one]
            omega
          · rw [UInt64.toNat_add, UInt64.toNat_add, hpos, hTL, hline, UInt64.toNat_one]
            omega
          · rw [hget', hpos, hsize, hget i]
            by_cases hlt : i < (textWords (P k)).length
            · rw [ite_eq_right (by omega)]
              by_cases hio : i < out.data.size
              · rw [ite_eq_left ⟨hlt, hio⟩, ite_eq_left ⟨by omega, hio⟩, List.getD_append _ _ _ _ hlt]
              · rw [ite_eq_right (fun h => hio h.2), ite_eq_right (fun h => hio h.2)]
            · by_cases hin : (textWords (P k)).length ≤ i ∧
                  i < (textWords (P k)).length + (lineWords (pickSpec (n, w))).length ∧
                  i < out.data.size
              · rw [ite_eq_left hin, ite_eq_left ⟨by omega, hin.2.2⟩,
                  List.getD_append_right _ _ _ _ (by omega)]
              · rw [ite_eq_right hin, ite_eq_right (fun h => hlt h.1), ite_eq_right (by omega)]
        · -- An accepted word at the limit: nothing changes.
          have hcond : ¬(pickSpec (n, w) != 0 && s.2.2 < limit) = true := by
            simp [hless, hroom]
          rw [ite_eq_right hcond]
          have hsame : P (k + 1) = P k := by
            show (valuesOf n (ws.take (k + 1))).take limit.toNat =
              (valuesOf n (ws.take k)).take limit.toNat
            rw [hV, ite_eq_left hacc, List.take_append_of_le_length (by omega)]
          rw [hsame]
          exact ⟨hcount, hpos, hsize, hget⟩
      · -- A rejected word: nothing changes.
        have hzero : pickSpec (n, w) = 0 := (pickSpec_eq_zero n w).mpr (by simpa using hacc)
        have hcond : ¬(pickSpec (n, w) != 0 && s.2.2 < limit) = true := by
          simp [hzero]
        rw [ite_eq_right hcond]
        have hsame : P (k + 1) = P k := by
          show (valuesOf n (ws.take (k + 1))).take limit.toNat =
            (valuesOf n (ws.take k)).take limit.toNat
          rw [hV, ite_eq_right hacc, List.append_nil]
        rw [hsame]
        exact ⟨hcount, hpos, hsize, hget⟩)
  rw [hW] at key
  have hPW : P ws.length = (valuesOf n (wordsOf draw.data.data.toList)).take limit.toNat := by
    show (valuesOf n (ws.take ws.length)).take limit.toNat = _
    rw [List.take_length, wordsOf_eq, hws]
  have hVl := hPlen ws.length
  have hTW := hTlen ws.length
  have hsz : UInt64.size = 2 ^ 64 := rfl
  have final : ∀ s : Bytes × UInt64 × UInt64,
      s.2.2.toNat = (P ws.length).length → s.2.1.toNat = (textWords (P ws.length)).length →
      s.1.data.size = out.data.size → (∀ i, s.1.data.data.toList.getD i 0 =
        if i < (textWords (P ws.length)).length ∧ i < out.data.size then
          ((textWords (P ws.length)).getD i 0).toUInt8
        else out.data.data.toList.getD i 0) →
      s = putPicksSpec (out, n, draw, limit) := by
    intro ⟨b, pos, count⟩ hcount hpos hsize hget
    dsimp only at hcount hpos hsize hget
    unfold putPicksSpec
    dsimp only
    rw [renderSpec_toList, ← hPW]
    generalize P ws.length = values at hcount hpos hget hTW hVl ⊢
    generalize hT : textWords values = T at hpos hget hTW ⊢
    have hlenT : (T.map UInt64.toUInt8).length = T.length := List.length_map ..
    have hbl : b.data.data.toList.length = b.data.size := by simp
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · apply bytes_eq_of_toList
      apply list_eq_of_getD
      · rw [List.length_append, List.length_take, List.length_drop, hlenT, hol, hbl, hsize]
        omega
      · intro i hi
        have hib : i < out.data.size := by rw [hbl, hsize] at hi; exact hi
        rw [hget i]
        by_cases hlt : i < T.length
        · have hA : i < (List.take out.data.data.toList.length (T.map UInt64.toUInt8)).length := by
            rw [List.length_take, hlenT, hol]
            omega
          rw [ite_eq_left ⟨hlt, hib⟩, List.getD_append _ _ _ _ hA, getD_eq_of_lt hA, List.getElem_take,
            List.getElem_map, getD_eq_of_lt hlt]
        · have hA : (List.take out.data.data.toList.length (T.map UInt64.toUInt8)).length =
              T.length := by
            rw [List.length_take, hlenT, hol]
            omega
          have hB : i - T.length <
              (out.data.data.toList.drop (T.map UInt64.toUInt8).length).length := by
            rw [List.length_drop, hlenT, hol]
            omega
          rw [ite_eq_right (fun h => hlt h.1), List.getD_append_right _ _ _ _ (by omega), hA,
            getD_eq_of_lt hB, List.getElem_drop, getD_eq_of_lt (by rw [hol]; exact hib)]
          have hidx : (T.map UInt64.toUInt8).length + (i - T.length) = i := by
            rw [hlenT]
            omega
          simp only [hidx]
    · apply UInt64.toNat_inj.mp
      rw [hpos, List.length_map, UInt64.toNat_ofNat_of_lt' (by omega)]
    · apply UInt64.toNat_inj.mp
      rw [hcount, UInt64.toNat_ofNat_of_lt' (by omega)]
  exact final _ key.1 key.2.1 key.2.2.1 key.2.2.2

end Demos.RandomChoice
