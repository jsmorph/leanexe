import Demos.RandomChoice.CommandSpec
import Demos.RandomChoice.Proof
import Demos.RandomChoice.Unbiased
import Demos.RandomHistogram.CommandProof

/-! Facts for the WASI command's theorem that depend on no call.  `choose_eq` states that `choose`
keeps the picks of the accepted little-endian words of a buffer, in order, at most a given number
of them.  `cap_count` states that at most a `2^-512` part of the sequences of the `512 · passes K`
words of the cap's passes hold fewer than K accepted words, from `short_count`, since
`512 · (K / 128 + 3) ≥ 4 K + 1024`. -/

namespace Demos.RandomChoice

open LeanExe LeanExe.Wasi

/-! ## The picks of a buffer -/

theorem accepted_append (n : UInt64) (a b : List UInt64) :
    accepted n (a ++ b) = accepted n a ++ accepted n b := by
  simp [accepted, List.filter_append]

theorem accepted_single (n w : UInt64) :
    accepted n [w] = if pickSpec (n, w) != 0 then [pickSpec (n, w)] else [] := by
  by_cases h : (pickSpec (n, w) != 0) = true <;> simp [accepted, List.filter, h]

/-- `choose` takes the picks of the accepted words of a buffer, at most `limit` of them. -/
theorem choose_eq (n : UInt64) (bytes : Bytes) (limit : UInt64) (hs : bytes.data.size < 2 ^ 64) :
    (choose n bytes limit).toList =
      (accepted n (RandomHistogram.words bytes.data.data.toList)).take limit.toNat := by
  have hn : (bytes.size / 8).toNat = bytes.data.size / 8 := by
    rw [UInt64.toNat_div, Bytes.size_toNat bytes hs]
    rfl
  have hlen : (RandomHistogram.words bytes.data.data.toList).length = bytes.data.size / 8 := by
    simp [RandomHistogram.words_length]
  have key := LeanExe.Dialect.loop_induction (n := bytes.size / 8) (init := (#[] : Array UInt64))
    (f := fun j picks =>
      let v := pick n (RandomHistogram.wordAt bytes (8 * j))
      if v != 0 && picks.size.toUInt64 < limit then picks.push v else picks)
    (fun k picks => picks.toList =
      (accepted n ((RandomHistogram.words bytes.data.data.toList).take k)).take limit.toNat)
    (by simp [accepted])
    (by
      intro k picks hk hpicks
      rw [hn] at hk
      have h8 : (8 : UInt64) * UInt64.ofNat k = UInt64.ofNat (8 * k) := by
        apply UInt64.toNat_inj.mp
        simp only [UInt64.toNat_mul, UInt64.toNat_ofNat', UInt64.reduceToNat, Nat.reducePow]
        omega
      have hw := RandomHistogram.words_getElem bytes.data.data.toList k (by omega)
      have hword : RandomHistogram.wordAt bytes (8 * UInt64.ofNat k) =
          (RandomHistogram.words bytes.data.data.toList)[k]'(by omega) := by
        rw [h8, RandomHistogram.wordAt_eq bytes (8 * k) (by omega) hs, hw]
      have htake : (RandomHistogram.words bytes.data.data.toList).take (k + 1) =
          (RandomHistogram.words bytes.data.data.toList).take k ++
            [(RandomHistogram.words bytes.data.data.toList)[k]'(by omega)] := by
        rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]
        rfl
      generalize (RandomHistogram.words bytes.data.data.toList)[k]'(by omega) = w at hword htake
      show (if pick n (RandomHistogram.wordAt bytes (8 * UInt64.ofNat k)) != 0 &&
          picks.size.toUInt64 < limit then
          picks.push (pick n (RandomHistogram.wordAt bytes (8 * UInt64.ofNat k))) else picks).toList = _
      rw [hword, pick_eq, htake, accepted_append, accepted_single]
      have hsize : picks.size =
          min (accepted n ((RandomHistogram.words bytes.data.data.toList).take k)).length
            limit.toNat := by
        rw [← Array.length_toList, hpicks, List.length_take, Nat.min_comm]
      have hsmall : picks.size < 2 ^ 64 := by
        have := limit.toNat_lt
        omega
      have hlt : (picks.size.toUInt64 < limit) ↔
          (accepted n ((RandomHistogram.words bytes.data.data.toList).take k)).length <
            limit.toNat := by
        rw [UInt64.lt_iff_toNat_lt, LeanExe.Dialect.size_toUInt64 _ hsmall, hsize]
        omega
      generalize accepted n ((RandomHistogram.words bytes.data.data.toList).take k) = acc
        at hpicks hsize hlt
      by_cases hv : (pickSpec (n, w) != 0) = true
      · by_cases hroom : acc.length < limit.toNat
        · have hc : (pickSpec (n, w) != 0 && picks.size.toUInt64 < limit) = true := by
            simp [hv, hlt.mpr hroom]
          rw [ite_eq_left hc, ite_eq_left hv, Array.toList_push, hpicks,
            List.take_of_length_le (by omega : acc.length ≤ limit.toNat),
            List.take_of_length_le (l := acc ++ [pickSpec (n, w)]) (by simp; omega)]
        · have hc : ¬(pickSpec (n, w) != 0 && picks.size.toUInt64 < limit) = true := by
            simp [hv, mt hlt.mp hroom]
          rw [ite_eq_right hc, ite_eq_left hv, hpicks,
            List.take_append_of_le_length (by omega : limit.toNat ≤ acc.length)]
      · have hc : ¬(pickSpec (n, w) != 0 && picks.size.toUInt64 < limit) = true := by
          simp [hv]
        rw [ite_eq_right hc, ite_eq_right hv, List.append_nil, hpicks])
  rw [hn] at key
  rw [show choose n bytes limit = LeanExe.loop (bytes.size / 8) (#[] : Array UInt64)
      (fun j picks =>
        let v := pick n (RandomHistogram.wordAt bytes (8 * j))
        if v != 0 && picks.size.toUInt64 < limit then picks.push v else picks) from rfl,
    key, List.take_of_length_le (l := RandomHistogram.words bytes.data.data.toList) (by omega)]

/-! ## The cap -/

theorem passes_toNat (k : UInt64) : (passes k).toNat = k.toNat / 128 + 3 := by
  have := k.toNat_lt
  rw [passes, UInt64.toNat_add, UInt64.toNat_div]
  simp only [UInt64.reduceToNat]
  omega

/-- At most a `2^-512` part of the sequences of the `512 · passes k` words of the cap's passes hold
fewer than `k` words that `n ≥ 1` accepts. -/
theorem cap_count (n k : UInt64) (hn : n ≠ 0) :
    2 ^ 512 * (Finset.univ.filter fun ws : Fin (512 * (passes k).toNat) → UInt64 =>
      (Finset.univ.filter fun i => accepts n (ws i) = true).card < k.toNat).card ≤
        2 ^ (64 * (512 * (passes k).toNat)) :=
  short_count n hn k.toNat _ (by rw [passes_toNat]; omega)

end Demos.RandomChoice
