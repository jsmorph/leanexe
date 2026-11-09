import TestSupport.M7.Delim
import LeanExe.Requests.DelimitedSteps

/-!
The echo of records of `tests/TestSupport/M7/Delim.lean` against the delimited framing of
`LeanExe/Requests/Delimited.lean`.  `dlAbs` maps the step's state to `delimTick`'s: the segment's
bytes are the last `min len 36` bytes of `seg`, and the bytes to write the first `k` bytes of
`out`.  `dlPhases_abs` states that `dlPhases` computes `delimTick` of `echoMach` with segments of
at most 36 bytes under `dlAbs`, for every register map, on the states of `DlInv`, which bounds
`k` by 40 and requires it to be positive in the phases that write.  The step keeps `DlInv`, and
`dlInit` satisfies it.  `dlAnswer_spec` gives the window of a `0x00` from `decodeWords_eq`,
`encAll_spec`, `encByte_spec`, and `encFinish_spec` of `LeanExe/Requests/DelimitedWords.lean`.

`dl_prefix` and `dl_answered` carry F3, `delim_prefix` and `delim_answered`, to any step that
`dlPhases_abs` covers through `reqTrace_mapOn`, and `dl_usart3_prefix`, `dl_usart3_answered`,
`dl_cmsdk_prefix`, and `dl_cmsdk_answered` instantiate them for `dlUsart3Tick` and `dlCmsdkTick`:
for every bus and every sequence of the values read, the bytes that the windows write begin the
encoded answers of `echoMach` to the nonempty segments of the bytes read, and they are all those
answers whenever a window reads a byte.
-/

namespace TestSupport.M7.Delim

open LeanExe.Native (readReq writeReq)
open LeanExe.Requests

/-- USART3's registers in `dlUsart3Tick`. -/
def dlUsart3 : Uart := ⟨0x1209, 0x120A, 0x1207, 0x20, 0x80, 0x80⟩

/-- UART0's registers in `dlCmsdkTick`. -/
def dlCmsdk : Uart := ⟨0x1000, 0x1000, 0x1001, 2, 1, 0⟩

/-- The framing's state over lists. -/
def dlAbs (f : DlFrame) : Delim UInt64 :=
  ⟨f.phase, f.len, f.seg.bytes.drop (40 - min f.len.toNat 36), f.out.bytes.take f.k.toNat,
    f.count⟩

/-- The states on which `dlAbs` commutes with the step. -/
def DlInv (f : DlFrame) : Prop := f.k.toNat ≤ 40 ∧ (f.phase ≠ 0 → f.phase ≠ 1 → 1 ≤ f.k.toNat)

theorem dlInit_inv : DlInv dlInit := ⟨by decide, fun h => absurd rfl h⟩

theorem dlAbs_init : dlAbs dlInit = delim0 0 := rfl

theorem echoMach_fst (c : UInt64) (r : Except SegErr (List UInt8)) : (echoMach c r).1 = c + 1 := by
  cases r with
  | ok r => rfl
  | error e => cases e <;> rfl

/-- The encoded answer whose bytes are `code`, the low byte of `c`, and the last `n` bytes of
`src`. -/
theorem answer_of (src : Bytes40) {n : UInt64} (c : UInt64) {code : UInt64} (hn : n.toNat ≤ 36)
    (hcode : code.toNat < 256) :
    (encFinish (encByte (encByte (encAll (encStart src n)) (c &&& 255)) code)).bytes.take
        ((encByte (encByte (encAll (encStart src n)) (c &&& 255)) code).dlen + 2).toNat =
      cobsEncode (code.toUInt8 :: c.toUInt8 :: src.bytes.drop (40 - n.toNat)) ++ [0] ∧
      2 ≤ ((encByte (encByte (encAll (encStart src n)) (c &&& 255)) code).dlen + 2).toNat ∧
      ((encByte (encByte (encAll (encStart src n)) (c &&& 255)) code).dlen + 2).toNat ≤ 40 := by
  have hl : (src.bytes.drop (40 - n.toNat)).length = n.toNat := by
    rw [List.length_drop, length_bytes]
    omega
  have h1 := encByte_spec (encAll_spec src (n := n) (by omega)) (and255_lt c) (by rw [hl]; omega)
  rw [toUInt8_and255] at h1
  have h2 := encByte_spec h1 hcode (by rw [List.length_cons, hl]; omega)
  exact answer_rel h2 (by rw [List.length_cons, List.length_cons, hl]; omega)

theorem dlValid_eq (seg : Bytes40) (len : UInt64) :
    dlValid (decodeWords seg len) len =
      if len ≤ 36 ∧ (decodeWords seg len).ok = 1 ∧ (decodeWords seg len).rem = 0 ∧
        (decodeWords seg len).zero = 1 then 1 else 0 := by
  unfold dlValid
  by_cases hl : len ≤ 36
  · have hn : len.toNat ≤ 40 := by
      have := UInt64.le_iff_toNat_le.mp hl
      simp at this
      omega
    have hz01 : (decodeWords seg len).zero = 0 ∨ (decodeWords seg len).zero = 1 := by
      rw [(decodeWords_spec seg hn).zero]
      split <;> simp
    generalize decodeWords seg len = d at hz01 ⊢
    rw [ite_eq_left hl]
    by_cases h1 : d.ok = 1
    · by_cases h2 : d.rem = 0
      · rcases hz01 with h | h <;> simp [h1, h2, hl, h]
      · simp [h1, h2]
    · simp [h1]
  · rw [ite_eq_right hl, ite_eq_right (fun h => hl h.1)]

/-- The window of a `0x00` after a segment of `len` bytes: the answer that `dlAnswer` encodes is
`echoMach`'s answer to the segment's result. -/
theorem dlAnswer_spec (seg : Bytes40) (len c : UInt64) :
    (encFinish (dlAnswer seg len c)).bytes.take ((dlAnswer seg len c).dlen + 2).toNat =
      cobsEncode (echoMach c (if UInt64.ofNat 36 < len then .error .overflow
        else segResult 36 (seg.bytes.drop (40 - min len.toNat 36)))).2 ++ [0] ∧
      2 ≤ ((dlAnswer seg len c).dlen + 2).toNat ∧ ((dlAnswer seg len c).dlen + 2).toNat ≤ 40 := by
  have h36 : UInt64.ofNat 36 = 36 := rfl
  have h01 : ((0 : UInt64) == 1) = false := rfl
  have h11 : ((1 : UInt64) == 1) = true := rfl
  have e : dlAnswer seg len c = encByte (encByte (encAll (encStart (decodeWords seg len).out
      (if dlValid (decodeWords seg len) len == 1 then (decodeWords seg len).olen else 0)))
      (c &&& 255)) (if 36 < len then 2 else
        if dlValid (decodeWords seg len) len == 1 then 0 else 1) := rfl
  rw [e, h36]
  by_cases ho : 36 < len
  · have hl : ¬len ≤ 36 := by
      intro h
      have h1 := UInt64.lt_iff_toNat_lt.mp ho
      have h2 := UInt64.le_iff_toNat_le.mp h
      exact absurd (Nat.lt_of_lt_of_le h1 h2) (Nat.lt_irrefl _)
    have hv : dlValid (decodeWords seg len) len = 0 := by
      rw [dlValid_eq, ite_eq_right (fun h => hl h.1)]
    rw [hv, h01, ite_eq_left ho, ite_eq_left ho, ite_eq_right Bool.false_ne_true]
    have h := answer_of (decodeWords seg len).out c (n := 0) (code := 2) (by decide) (by decide)
    rw [show (0 : UInt64).toNat = 0 from rfl, Nat.sub_zero, drop40] at h
    exact h
  · have hn : len.toNat ≤ 36 := by
      have := UInt64.lt_iff_toNat_lt.not.mp ho
      simp at this
      omega
    have hl : len ≤ 36 := UInt64.le_iff_toNat_le.mpr (by simp; omega)
    have hmin : min len.toNat 36 = len.toNat := by omega
    have hL : (seg.bytes.drop (40 - len.toNat)).length = len.toNat := by
      rw [List.length_drop, length_bytes]
      omega
    have hno : ¬36 < (seg.bytes.drop (40 - len.toNat)).length := by
      rw [hL]
      omega
    rw [ite_eq_right ho, ite_eq_right ho, hmin, segResult, ite_eq_right hno,
      decodeWords_eq seg (by omega)]
    have hol := decodeWords_olen seg (n := len) (by omega)
    by_cases hv : (decodeWords seg len).ok = 1 ∧ (decodeWords seg len).rem = 0 ∧
        (decodeWords seg len).zero = 1
    · have hv1 : dlValid (decodeWords seg len) len = 1 := by
        rw [dlValid_eq, ite_eq_left ⟨hl, hv⟩]
      rw [hv1, h11, ite_eq_left rfl, ite_eq_left rfl, ite_eq_left hv]
      have h := answer_of (decodeWords seg len).out c (n := (decodeWords seg len).olen)
        (code := 0) (by omega) (by decide)
      rw [show (0 : UInt64).toUInt8 = 0 by decide] at h
      generalize (decodeWords seg len).out.bytes.drop (40 - (decodeWords seg len).olen.toNat) = R
        at h ⊢
      exact h
    · have hv0 : dlValid (decodeWords seg len) len = 0 := by
        rw [dlValid_eq, ite_eq_right (fun h => hv h.2)]
      rw [hv0, h01, ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true,
        ite_eq_right hv]
      have h := answer_of (decodeWords seg len).out c (n := 0) (code := 1) (by decide) (by decide)
      rw [show (0 : UInt64).toNat = 0 from rfl, Nat.sub_zero, drop40] at h
      exact h

/-- `dlPhases` computes `delimTick` of `echoMach` under `dlAbs` on the states of `DlInv`, and it
keeps `DlInv`. -/
theorem dlPhases_abs (rx tx status rxFull txMask txRoom : UInt64) (f : DlFrame) (v : UInt64)
    (hI : DlInv f) :
    DlInv (dlPhases rx tx status rxFull txMask txRoom f v).1 ∧
      delimTick ⟨rx, tx, status, rxFull, txMask, txRoom⟩ 36 echoMach (dlAbs f) v =
        (dlAbs (dlPhases rx tx status rxFull txMask txRoom f v).1,
          (dlPhases rx tx status rxFull txMask txRoom f v).2) := by
  obtain ⟨hk, hk1⟩ := hI
  have h36 : UInt64.ofNat 36 = 36 := rfl
  by_cases p0 : (f.phase == 0) = true
  · by_cases hx : (v &&& rxFull != 0) = true
    · have e1 : dlPhases rx tx status rxFull txMask txRoom f v =
          ({ f with phase := 1 }, readReq rx) := by
        unfold dlPhases
        rw [ite_eq_left p0, ite_eq_left hx]
      have e2 : delimTick ⟨rx, tx, status, rxFull, txMask, txRoom⟩ 36 echoMach (dlAbs f) v =
          ({ dlAbs f with phase := 1 }, readReq rx) := by
        unfold delimTick dlAbs
        dsimp only
        rw [ite_eq_left p0, ite_eq_left hx]
      rw [e1, e2]
      exact ⟨⟨hk, fun _ h => absurd rfl h⟩, rfl⟩
    · have e1 : dlPhases rx tx status rxFull txMask txRoom f v = (f, readReq status) := by
        unfold dlPhases
        rw [ite_eq_left p0, ite_eq_right hx]
      have e2 : delimTick ⟨rx, tx, status, rxFull, txMask, txRoom⟩ 36 echoMach (dlAbs f) v =
          (dlAbs f, readReq status) := by
        unfold delimTick dlAbs
        dsimp only
        rw [ite_eq_left p0, ite_eq_right hx]
      rw [e1, e2]
      exact ⟨⟨hk, hk1⟩, rfl⟩
  by_cases p1 : (f.phase == 1) = true
  · by_cases hb : (v &&& 255 != 0) = true
    · have e1 : dlPhases rx tx status rxFull txMask txRoom f v =
          ({ f with
              phase := 0,
              len := if f.len ≤ 36 then f.len + 1 else f.len,
              seg := if f.len < 36 then push40 f.seg v else f.seg }, readReq status) := by
        unfold dlPhases
        rw [ite_eq_right p0, ite_eq_left p1, ite_eq_left hb]
      have e2 : delimTick ⟨rx, tx, status, rxFull, txMask, txRoom⟩ 36 echoMach (dlAbs f) v =
          ({ dlAbs f with
              phase := 0,
              len := if f.len ≤ 36 then f.len + 1 else f.len,
              seg := if f.len < 36 then f.seg.bytes.drop (40 - min f.len.toNat 36) ++
                [(v &&& 255).toUInt8] else f.seg.bytes.drop (40 - min f.len.toNat 36) },
            readReq status) := by
        unfold delimTick dlAbs
        dsimp only
        rw [ite_eq_right p0, ite_eq_left p1, ite_eq_left hb, h36]
      rw [e1, e2]
      refine ⟨⟨hk, fun h => absurd rfl h⟩, ?_⟩
      simp only [dlAbs, Prod.mk.injEq, Delim.mk.injEq, and_true, true_and]
      exact (seg_store f.seg f.len v).symm
    · have hb0 : v &&& 255 = 0 := by simpa using hb
      by_cases hl : (f.len == 0) = true
      · have e1 : dlPhases rx tx status rxFull txMask txRoom f v =
            ({ f with phase := 0 }, readReq status) := by
          unfold dlPhases
          rw [ite_eq_right p0, ite_eq_left p1, ite_eq_right hb, ite_eq_left hl]
        have e2 : delimTick ⟨rx, tx, status, rxFull, txMask, txRoom⟩ 36 echoMach (dlAbs f) v =
            ({ dlAbs f with phase := 0 }, readReq status) := by
          unfold delimTick dlAbs
          dsimp only
          rw [ite_eq_right p0, ite_eq_left p1, ite_eq_right hb, ite_eq_left hl]
        rw [e1, e2]
        exact ⟨⟨hk, fun h => absurd rfl h⟩, rfl⟩
      · obtain ⟨hA, hA2, hA40⟩ := dlAnswer_spec f.seg f.len f.count
        have e1 : dlPhases rx tx status rxFull txMask txRoom f v =
            ({ phase := 2, len := 0, seg := f.seg, out := encFinish (dlAnswer f.seg f.len f.count),
                k := (dlAnswer f.seg f.len f.count).dlen + 2, count := f.count + 1 },
              readReq status) := by
          unfold dlPhases
          rw [ite_eq_right p0, ite_eq_left p1, ite_eq_right hb, ite_eq_right hl]
        have e2 : delimTick ⟨rx, tx, status, rxFull, txMask, txRoom⟩ 36 echoMach (dlAbs f) v =
            ({ phase := 2, len := 0, seg := [],
                out := cobsEncode (echoMach f.count (if UInt64.ofNat 36 < f.len then .error .overflow
                  else segResult 36 (f.seg.bytes.drop (40 - min f.len.toNat 36)))).2 ++ [0],
                m := (echoMach f.count (if UInt64.ofNat 36 < f.len then .error .overflow
                  else segResult 36 (f.seg.bytes.drop (40 - min f.len.toNat 36)))).1 },
              readReq status) := by
          unfold delimTick dlAbs
          dsimp only
          rw [ite_eq_right p0, ite_eq_left p1, ite_eq_right hb, ite_eq_right hl]
        rw [e1, e2]
        refine ⟨⟨hA40, fun _ _ => Nat.le_trans (by decide) hA2⟩, ?_⟩
        simp only [dlAbs, Prod.mk.injEq, Delim.mk.injEq, and_true, true_and]
        refine ⟨?_, ?_, echoMach_fst _ _⟩
        · rw [show (0 : UInt64).toNat = 0 from rfl, Nat.zero_min, Nat.sub_zero, drop40]
        · exact hA.symm
  have p0' : f.phase ≠ 0 := by simpa using p0
  have p1' : f.phase ≠ 1 := by simpa using p1
  have hk1' := hk1 p0' p1'
  by_cases p2 : (f.phase == 2) = true
  · by_cases hx : (v &&& txMask == txRoom) = true
    · have e1 : dlPhases rx tx status rxFull txMask txRoom f v =
          ({ f with phase := 3 }, writeReq tx (first40 f.out)) := by
        unfold dlPhases
        rw [ite_eq_right p0, ite_eq_right p1, ite_eq_left p2, ite_eq_left hx]
      have e2 : delimTick ⟨rx, tx, status, rxFull, txMask, txRoom⟩ 36 echoMach (dlAbs f) v =
          ({ dlAbs f with phase := 3 },
            writeReq tx ((f.out.bytes.take f.k.toNat).headD 0).toUInt64) := by
        unfold delimTick dlAbs
        dsimp only
        rw [ite_eq_right p0, ite_eq_right p1, ite_eq_left p2, ite_eq_left hx]
      rw [e1, e2, headD_take hk1', first40_val]
      exact ⟨⟨hk, fun _ _ => hk1'⟩, rfl⟩
    · have e1 : dlPhases rx tx status rxFull txMask txRoom f v = (f, readReq status) := by
        unfold dlPhases
        rw [ite_eq_right p0, ite_eq_right p1, ite_eq_left p2, ite_eq_right hx]
      have e2 : delimTick ⟨rx, tx, status, rxFull, txMask, txRoom⟩ 36 echoMach (dlAbs f) v =
          (dlAbs f, readReq status) := by
        unfold delimTick dlAbs
        dsimp only
        rw [ite_eq_right p0, ite_eq_right p1, ite_eq_left p2, ite_eq_right hx]
      rw [e1, e2]
      exact ⟨⟨hk, hk1⟩, rfl⟩
  · have hkm : (f.k - 1).toNat = f.k.toNat - 1 := toNat_sub_one (by omega)
    have hlen : (f.out.bytes.take f.k.toNat).length = f.k.toNat := by
      rw [List.length_take, length_bytes]
      omega
    have hc : (f.k ≤ 1) ↔ ((f.out.bytes.take f.k.toNat).length ≤ 1) := by
      rw [hlen, UInt64.le_iff_toNat_le]
      rfl
    have e1 : dlPhases rx tx status rxFull txMask txRoom f v =
        ({ f with phase := if f.k ≤ 1 then 0 else 2, out := push40 f.out 0, k := f.k - 1 },
          readReq status) := by
      unfold dlPhases
      rw [ite_eq_right p0, ite_eq_right p1, ite_eq_right p2]
    have e2 : delimTick ⟨rx, tx, status, rxFull, txMask, txRoom⟩ 36 echoMach (dlAbs f) v =
        ({ dlAbs f with
            phase := if f.k ≤ 1 then 0 else 2, out := (f.out.bytes.take f.k.toNat).tail },
          readReq status) := by
      unfold delimTick dlAbs
      dsimp only
      rw [ite_eq_right p0, ite_eq_right p1, ite_eq_right p2]
      by_cases h : f.k ≤ 1
      · rw [ite_eq_left (hc.mp h), ite_eq_left h]
      · rw [ite_eq_right (fun e => h (hc.mpr e)), ite_eq_right h]
    rw [e1, e2]
    refine ⟨⟨by rw [hkm]; omega, fun h _ => ?_⟩, ?_⟩
    · show 1 ≤ (f.k - 1).toNat
      by_cases hk2 : f.k ≤ 1
      · rw [ite_eq_left hk2] at h
        exact absurd rfl h
      · rw [hkm]
        have := UInt64.le_iff_toNat_le.not.mp hk2
        simp at this
        omega
    · simp only [dlAbs, Prod.mk.injEq, Delim.mk.injEq, and_true, true_and]
      rw [push40_bytes, hkm, show ((0 : UInt64).toUInt8) = 0 from rfl,
        tail_take_push (length_bytes _) hk1' hk]

theorem dlUsart3_abs (f : DlFrame) (v : UInt64) (h : DlInv f) :
    DlInv (dlUsart3Tick f v).1 ∧
      delimTick dlUsart3 36 echoMach (dlAbs f) v =
        (dlAbs (dlUsart3Tick f v).1, (dlUsart3Tick f v).2) :=
  dlPhases_abs 0x1209 0x120A 0x1207 0x20 0x80 0x80 f v h

theorem dlCmsdk_abs (f : DlFrame) (v : UInt64) (h : DlInv f) :
    DlInv (dlCmsdkTick f v).1 ∧
      delimTick dlCmsdk 36 echoMach (dlAbs f) v =
        (dlAbs (dlCmsdkTick f v).1, (dlCmsdkTick f v).2) :=
  dlPhases_abs 0x1000 0x1000 0x1001 2 1 0 f v h

section

variable {α : Type} (B : Bus α) {u : Uart} {tick : DlFrame → UInt64 → DlFrame × UInt64}
  (htick : ∀ f v, DlInv f → DlInv (tick f v).1 ∧
    delimTick u 36 echoMach (dlAbs f) v = (dlAbs (tick f v).1, (tick f v).2))
  (hrx : u.rx.toNat < 65536) (htx : u.tx.toNat < 65536) (hs : u.status.toNat < 65536)
  (hrs : u.rx ≠ u.status) (σ : Nat → UInt32) (n : Nat)

include htick hrx htx hs hrs in
/-- F3 for a step that `dlPhases_abs` covers: the bytes that the first `n` windows write begin the
encoded answers of `echoMach` to the nonempty segments of the bytes that they read. -/
theorem dl_prefix :
    dataOut B u (windows (reqTrace B tick dlInit σ) n) <+:
      (delimAnswers echoMach 36 0 ((dataIn B u (windows (reqTrace B tick dlInit σ) n)).map
        UInt64.toUInt8)).map UInt8.toUInt64 := by
  rw [← reqTrace_mapOn dlAbs DlInv htick dlInit dlInit_inv σ, dlAbs_init]
  exact delim_prefix hrx htx hs hrs (by decide) σ n

include htick hrx htx hs hrs in
/-- F3 for a window that reads a byte, for a step that `dlPhases_abs` covers. -/
theorem dl_answered (hread : dataIn B u (reqTrace B tick dlInit σ n) ≠ []) :
    dataOut B u (windows (reqTrace B tick dlInit σ) n) =
      (delimAnswers echoMach 36 0 ((dataIn B u (windows (reqTrace B tick dlInit σ) n)).map
        UInt64.toUInt8)).map UInt8.toUInt64 := by
  rw [← reqTrace_mapOn dlAbs DlInv htick dlInit dlInit_inv σ, dlAbs_init] at hread ⊢
  exact delim_answered hrx htx hs hrs (by decide) σ n hread

end

theorem dl_usart3_prefix {α : Type} (B : Bus α) (σ : Nat → UInt32) (n : Nat) :
    dataOut B dlUsart3 (windows (reqTrace B dlUsart3Tick dlInit σ) n) <+:
      (delimAnswers echoMach 36 0 ((dataIn B dlUsart3 (windows (reqTrace B dlUsart3Tick dlInit σ)
        n)).map UInt64.toUInt8)).map UInt8.toUInt64 :=
  dl_prefix B dlUsart3_abs (by decide) (by decide) (by decide) (by decide) σ n

theorem dl_usart3_answered {α : Type} (B : Bus α) (σ : Nat → UInt32) (n : Nat)
    (hread : dataIn B dlUsart3 (reqTrace B dlUsart3Tick dlInit σ n) ≠ []) :
    dataOut B dlUsart3 (windows (reqTrace B dlUsart3Tick dlInit σ) n) =
      (delimAnswers echoMach 36 0 ((dataIn B dlUsart3 (windows (reqTrace B dlUsart3Tick dlInit σ)
        n)).map UInt64.toUInt8)).map UInt8.toUInt64 :=
  dl_answered B dlUsart3_abs (by decide) (by decide) (by decide) (by decide) σ n hread

theorem dl_cmsdk_prefix {α : Type} (B : Bus α) (σ : Nat → UInt32) (n : Nat) :
    dataOut B dlCmsdk (windows (reqTrace B dlCmsdkTick dlInit σ) n) <+:
      (delimAnswers echoMach 36 0 ((dataIn B dlCmsdk (windows (reqTrace B dlCmsdkTick dlInit σ)
        n)).map UInt64.toUInt8)).map UInt8.toUInt64 :=
  dl_prefix B dlCmsdk_abs (by decide) (by decide) (by decide) (by decide) σ n

theorem dl_cmsdk_answered {α : Type} (B : Bus α) (σ : Nat → UInt32) (n : Nat)
    (hread : dataIn B dlCmsdk (reqTrace B dlCmsdkTick dlInit σ n) ≠ []) :
    dataOut B dlCmsdk (windows (reqTrace B dlCmsdkTick dlInit σ) n) =
      (delimAnswers echoMach 36 0 ((dataIn B dlCmsdk (windows (reqTrace B dlCmsdkTick dlInit σ)
        n)).map UInt64.toUInt8)).map UInt8.toUInt64 :=
  dl_answered B dlCmsdk_abs (by decide) (by decide) (by decide) (by decide) σ n hread

end TestSupport.M7.Delim
