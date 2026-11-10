import Demos.Bms.Theorems

/-!
The machine's theorems over every byte stream.  The delimited framing of
`LeanExe/Requests/Delimited.lean` calls `machine` once for each non-empty segment of the bytes
read, so `delimAnswers machine maxSegment init bs` is the specification of the board's answers to
the bytes `bs`.  `records bs` lists the non-empty segments of `bs`, and `inputs bs t` is the result
that the framing passes for the `t`-th of them.  `delimAnswers_eq` states the answers as the
encoded answers of the run over `inputs bs`, each followed by `0x00`, and `answer_stream` states
that the `n`-th segment of the bytes written decodes to the raw answer `answerAt (inputs bs) n`.
Every theorem of `Demos/Bms/Theorems.lean` therefore holds of the answers in the bytes written,
since each holds for every sequence of segment results and in particular for `inputs bs`.
`m1_stream`, `m2_stream`, and `m11_stream` state M1, M2, and M11 for an answer read from those
bytes, and `m12_stream` states M12 for a segment that is the encoding of a scan record with one
byte removed, through `length_cobsDecode`: COBS decoding of `k` bytes gives fewer than `k`.
-/

namespace Demos.Bms.Spec

open LeanExe.Requests

/-- The non-empty segments of the bytes `bs`, which the framing passes to the machine. -/
def records (bs : List UInt8) : List (List UInt8) := (segments bs).filter (· ≠ [])

/-- The result that the framing passes for the `t`-th non-empty segment of `segs`. -/
def inputsOf (segs : List (List UInt8)) (t : Nat) : Input :=
  segResult maxSegment ((segs.filter (· ≠ [])).getD t [])

/-- The results that the framing passes to the machine for the bytes `bs`. -/
def inputs (bs : List UInt8) : Nat → Input := inputsOf (segments bs)

theorem stateFrom_congr {s0 : State} {x y : Nat → Input} :
    ∀ {t : Nat}, (∀ u < t, x u = y u) → stateFrom s0 x t = stateFrom s0 y t
  | 0, _ => rfl
  | t + 1, h => by
    show (step (stateFrom s0 x t) (x t)).1 = (step (stateFrom s0 y t) (y t)).1
    rw [stateFrom_congr fun u hu => h u (by omega), h t (by omega)]

theorem answerAt_congr {x y : Nat → Input} {t : Nat} (h : ∀ u ≤ t, x u = y u) :
    answerAt x t = answerAt y t := by
  show (step (stateAt x t) (x t)).2 = (step (stateAt y t) (y t)).2
  rw [show stateAt x t = stateAt y t from stateFrom_congr fun u hu => h u (by omega),
    h t le_rfl]

/-- The framing's run of `machine` over the segments `segs` gives the state and the encoded
answers of the run over the results of the non-empty segments. -/
theorem answerRun_eq (segs : List (List UInt8)) :
    answerRun machine maxSegment init segs =
      (stateAt (inputsOf segs) (segs.filter (· ≠ [])).length,
        (List.range (segs.filter (· ≠ [])).length).flatMap fun t =>
          cobsEncode (encodeAnswer (answerAt (inputsOf segs) t)) ++ [0]) := by
  induction segs using List.reverseRecOn with
  | nil => rfl
  | append_singleton L s ih =>
    rw [answerRun_append]
    by_cases hs : s = []
    · subst hs
      have hf : (L ++ [[]]).filter (· ≠ []) = L.filter (· ≠ []) := by simp [List.filter_append]
      have hx : inputsOf (L ++ [[]]) = inputsOf L := by
        funext t
        simp only [inputsOf, hf]
      rw [ite_eq_left rfl, ih, hf, hx]
    · have hf : (L ++ [s]).filter (· ≠ []) = L.filter (· ≠ []) ++ [s] := by
        simp [List.filter_append, hs]
      have hagree : ∀ u < (L.filter (· ≠ [])).length, inputsOf (L ++ [s]) u = inputsOf L u := by
        intro u hu
        simp only [inputsOf, hf, List.getD_eq_getElem?_getD, List.getElem?_append_left hu]
      have hlast : inputsOf (L ++ [s]) (L.filter (· ≠ [])).length = segResult maxSegment s := by
        simp only [inputsOf, hf, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero,
          Option.getD_some]
      have hstate : stateAt (inputsOf (L ++ [s])) (L.filter (· ≠ [])).length =
          stateAt (inputsOf L) (L.filter (· ≠ [])).length :=
        stateFrom_congr fun u hu => hagree u hu
      rw [ite_eq_right hs, ih, hf, List.length_append,
        List.length_singleton, List.range_succ,
        List.flatMap_append, List.flatMap_singleton]
      refine Prod.ext ?_ ?_
      · show (step (stateAt (inputsOf L) (L.filter (· ≠ [])).length)
            (segResult maxSegment s)).1 =
          (step (stateAt (inputsOf (L ++ [s])) (L.filter (· ≠ [])).length)
            (inputsOf (L ++ [s]) (L.filter (· ≠ [])).length)).1
        rw [hstate, hlast]
      · simp only [List.append_assoc]
        congr 1
        · apply List.flatMap_congr
          intro t ht
          rw [answerAt_congr fun u hu => hagree u (by have := List.mem_range.mp ht; omega)]
        · rw [answerAt_eq, hstate, hlast]
          rfl

/-- The answers to the bytes `bs`: the encoded answers of the run over `inputs bs`, each followed
by `0x00`. -/
theorem delimAnswers_eq (bs : List UInt8) :
    delimAnswers machine maxSegment init bs =
      (List.range (records bs).length).flatMap fun t =>
        cobsEncode (encodeAnswer (answerAt (inputs bs) t)) ++ [0] := by
  rw [delimAnswers, answerRun_eq]
  rfl

theorem split_flatMap (e : Nat → List UInt8) (he : ∀ t, 0 ∉ e t) :
    ∀ N, split ((List.range N).flatMap fun t => e t ++ [0]) = ⟨(List.range N).map e, []⟩
  | 0 => rfl
  | N + 1 => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.map_append,
      List.map_singleton, ← List.append_assoc, split_append]
    have h1 : split ((List.range N).flatMap (fun t => e t ++ [0]) ++ e N) =
        (e N).foldl splitByte (split ((List.range N).flatMap fun t => e t ++ [0])) := by
      simp only [split, List.foldl_append]
    rw [h1, split_flatMap e he N, foldl_splitByte, split_nonzero _ _ (he N)]
    simp [splitByte]

/-- The segments of the answers to the bytes `bs` are the encoded answers. -/
theorem segments_delimAnswers (bs : List UInt8) :
    segments (delimAnswers machine maxSegment init bs) =
      (List.range (records bs).length).map fun t =>
        cobsEncode (encodeAnswer (answerAt (inputs bs) t)) := by
  rw [delimAnswers_eq, segments, split_flatMap _ fun t => zero_not_mem_cobsEncode _]

/-- The `n`-th segment of the answers to the bytes `bs` decodes to the raw answer `a_n` of the run
over the non-empty segments of `bs`. -/
theorem answer_stream (bs : List UInt8) (n : Nat) (s : List UInt8)
    (h : (segments (delimAnswers machine maxSegment init bs))[n]? = some s) :
    n < (records bs).length ∧ cobsDecode s = some (encodeAnswer (answerAt (inputs bs) n)) := by
  rw [segments_delimAnswers, List.getElem?_map] at h
  by_cases hn : n < (records bs).length
  · rw [List.getElem?_range hn] at h
    simp only [Option.map_some, Option.some.injEq] at h
    exact ⟨hn, by rw [← h, cobsDecode_encode]⟩
  · rw [List.getElem?_eq_none (by simp; omega)] at h
    simp at h

theorem field_encodeAnswer_permit (a : Answer) : field (encodeAnswer a) 9 1 = a.permit % 2 ^ 8 := by
  rw [encodeAnswer, field_append_of_ge (by simp [length_answerBody])]
  exact (field_answerBody a).2.2.1

/-- M1 over every byte stream: an answer among the bytes written with a nonzero permit byte is the
answer `a_n` of the run over the non-empty segments of the bytes read, and M1 holds of it. -/
theorem m1_stream (bs : List UInt8) (n : Nat) (s raw : List UInt8)
    (hs : (segments (delimAnswers machine maxSegment init bs))[n]? = some s)
    (hd : cobsDecode s = some raw) (hp : field raw 9 1 ≠ 0) :
    n < (records bs).length ∧ raw = encodeAnswer (answerAt (inputs bs) n) ∧
      ∃ i j, Permitted (inputs bs) n i j := by
  obtain ⟨hn, he⟩ := answer_stream bs n s hs
  rw [hd, Option.some.injEq] at he
  refine ⟨hn, he, m1 (inputs bs) n fun h0 => hp ?_⟩
  rw [he, field_encodeAnswer_permit, h0]
  rfl

/-- M2 over every byte stream: the permit byte of every answer among the bytes written is `0x00`,
`0x03`, or `0x05`. -/
theorem m2_stream (bs : List UInt8) (n : Nat) (s raw : List UInt8)
    (hs : (segments (delimAnswers machine maxSegment init bs))[n]? = some s)
    (hd : cobsDecode s = some raw) :
    field raw 9 1 = 0x00 ∨ field raw 9 1 = 0x03 ∨ field raw 9 1 = 0x05 := by
  obtain ⟨-, he⟩ := answer_stream bs n s hs
  rw [hd, Option.some.injEq] at he
  rw [he, field_encodeAnswer_permit]
  rcases (m2 (inputs bs) n).2.1 with h | h | h <;> rw [h] <;> simp

/-- M11 over every byte stream: the `n`-th segment of the bytes written decodes to 17 bytes that
`decodeAnswer` accepts, with the tag `0x80` and the CRC of `LINK` and the first 13 bytes, and the
answer they hold has the board sequence number `n` modulo `2 ^ 32`. -/
theorem m11_stream (bs : List UInt8) (n : Nat) (s : List UInt8)
    (hs : (segments (delimAnswers machine maxSegment init bs))[n]? = some s) :
    ∃ raw, cobsDecode s = some raw ∧ raw.length = answerLength ∧
      decodeAnswer raw = some (answerAt (inputs bs) n) ∧
      (answerAt (inputs bs) n).board = n % 2 ^ 32 := by
  obtain ⟨-, he⟩ := answer_stream bs n s hs
  obtain ⟨-, h2, h3, h4, -⟩ := m11 (inputs bs) n
  exact ⟨_, he, h2, h3, h4⟩

theorem length_cobsStuff_gt :
    ∀ (bs blk : List UInt8), blk.length + bs.length < (cobsStuff bs blk).length
  | [], blk => by simp [cobsStuff]
  | b :: bs, blk => by
    rw [cobsStuff]
    split_ifs
    · have := length_cobsStuff_gt bs []
      simp only [List.length_append, List.length_cons, List.length_nil] at this ⊢
      omega
    · have := length_cobsStuff_gt bs []
      simp only [List.length_append, List.length_cons, List.length_nil] at this ⊢
      omega
    · have := length_cobsStuff_gt bs (blk ++ [b])
      simp only [List.length_append, List.length_cons, List.length_nil] at this ⊢
      omega

/-- COBS decoding of `k` bytes gives at most `k - 1` bytes. -/
theorem length_cobsDecode {s r : List UInt8} (h : cobsDecode s = some r) :
    r.length < s.length := by
  rw [cobsDecode_eq_some_iff] at h
  rw [← h, cobsEncode]
  simpa using length_cobsStuff_gt r []

/-- The framing's result for the encoding of a 35-byte record with one byte removed is a decode
error or a record of fewer than 35 bytes. -/
theorem segResult_eraseIdx (r : List UInt8) (hr : r.length = scanLength) (k : Nat) (hk : k < 36) :
    segResult maxSegment ((cobsEncode r).eraseIdx k) = .error .decode ∨
      ∃ r', segResult maxSegment ((cobsEncode r).eraseIdx k) = .ok r' ∧ r'.length < scanLength := by
  have hl : (cobsEncode r).length = 36 := by
    rw [length_cobsEncode (by unfold scanLength at hr; omega), hr]
    rfl
  have hl' : ((cobsEncode r).eraseIdx k).length = 35 := by
    rw [List.length_eraseIdx, hl]
    simp [hk]
  unfold segResult
  rw [ite_eq_right (by unfold maxSegment; omega)]
  cases hd : cobsDecode ((cobsEncode r).eraseIdx k) with
  | none => exact Or.inl rfl
  | some r' =>
    refine Or.inr ⟨r', rfl, ?_⟩
    have := length_cobsDecode hd
    unfold scanLength
    omega

/-- M12 over every byte stream: the answer to a non-empty segment that is the encoding of a 35-byte
record with one byte removed has code `0x1001` or `0x1003` when the state before was not
`FAULT`. -/
theorem m12_stream (bs : List UInt8) (n : Nat) (r : List UInt8) (hr : r.length = scanLength)
    (k : Nat) (hk : k < 36) (hseg : (records bs)[n]? = some ((cobsEncode r).eraseIdx k))
    (hf : stateBefore (inputs bs) n ≠ .fault) :
    (answerAt (inputs bs) n).permit = 0 ∧ (answerAt (inputs bs) n).state = .fault ∧
      ((answerAt (inputs bs) n).code = codeDecode ∨ (answerAt (inputs bs) n).code = codeLength) := by
  have hx : inputs bs n = segResult maxSegment ((cobsEncode r).eraseIdx k) := by
    simp only [inputs, inputsOf, List.getD_eq_getElem?_getD]
    rw [show (segments bs).filter (· ≠ []) = records bs from rfl, hseg]
    rfl
  apply m12 (inputs bs) n _ hf
  rcases segResult_eraseIdx r hr k hk with h | ⟨r', h, hl⟩
  · exact Or.inl (hx.trans h)
  · exact Or.inr ⟨r', hx.trans h, hl⟩

end Demos.Bms.Spec
