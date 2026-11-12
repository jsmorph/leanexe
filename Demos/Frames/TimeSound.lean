import Demos.Frames.Time
import Demos.Frames.Soundness
import LeanExe.Dialect.Lemmas

/-!
What an accepted result of `timeScales` states.  `scan_inv` carries the facts of the pass over
the table through the loop: the entries read so far have values below `2³²` and increasing dates,
the last date is the state's, and each of the state's offsets is that of the last entry read whose
date is at most `d` or `d + 1`.  `timeScales_sound` states that an accepted result has a valid
table, a day within it, TAI − UTC by `Model.LeapOffset`, UTC seconds within the length of the day,
and intervals that contain the seconds of the day in TAI, TT, and UT1.
-/

namespace Demos.Frames

open Library.Numerics.Bounds Library.Numerics.Interval LeanExe.ProofKit
open CodeLib.IEEE64 (value Finite)
open Model

/-- `v` is the offset of the last of the first `k` entries whose date is at most `d`, or no such
entry exists. -/
def Found (xs : Array UInt64) (d : UInt64) (k : ℕ) (v : UInt64) : Prop :=
  (∃ i < k, date xs i ≤ d ∧ offset xs i = v ∧ ∀ j < k, i < j → d < date xs j) ∨
    ∀ j < k, d < date xs j

/-- The facts of the pass over the first `k` entries of a table. -/
def ScanInv (xs : Array UInt64) (d : UInt64) (k : ℕ) (sc : Scan) : Prop :=
  sc.status = 0 →
    (∀ j < k, (date xs j).toNat < 2 ^ 32 ∧ (offset xs j).toNat < 2 ^ 32) ∧
    (∀ i j, i < j → j < k → date xs i < date xs j) ∧
    (0 < k → sc.last = date xs (k - 1)) ∧
    Found xs d k sc.dat0 ∧ Found xs (d + 1) k sc.dat1

theorem found_step {xs : Array UInt64} {d : UInt64} {k : ℕ} {v : UInt64} (hf : Found xs d k v) :
    Found xs d (k + 1) (if date xs k ≤ d then offset xs k else v) := by
  by_cases hk : date xs k ≤ d
  · simp only [hk, ite_true]
    exact Or.inl ⟨k, by omega, hk, rfl, fun j hj hkj => by omega⟩
  · simp only [hk, ite_false]
    have hk' : d < date xs k := UInt64.not_le.1 hk
    rcases hf with ⟨i, hi, hd, ho, hlater⟩ | hnone
    · refine Or.inl ⟨i, by omega, hd, ho, fun j hj hij => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
      · exact hlater j hj hij
      · subst hj; exact hk'
    · refine Or.inr fun j hj => ?_
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
      · exact hnone j hj
      · subst hj; exact hk'

theorem index_toNat {k : ℕ} (hk : 2 * k + 2 < 2 ^ 64) (c : ℕ) (hc : c ≤ 2) :
    (2 * UInt64.ofNat k + UInt64.ofNat c).toNat = 2 * k + c := by
  rw [UInt64.toNat_add, UInt64.toNat_mul,
    UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega),
    UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]
  have h2 : (2 : UInt64).toNat = 2 := rfl
  simp only [h2]
  omega

/-- One entry of the pass keeps the facts. -/
theorem scan_step {xs : Array UInt64} {d : UInt64} {k : ℕ} {sc : Scan} (hk : 2 * k + 2 < 2 ^ 64)
    (h : ScanInv xs d k sc) : ScanInv xs d (k + 1) (scanStep xs d (UInt64.ofNat k) sc) := by
  have e1 : (2 * UInt64.ofNat k + 1).toNat = 2 * k + 1 := index_toNat hk 1 (by norm_num)
  have e2 : (2 * UInt64.ofNat k + 2).toNat = 2 * k + 2 := index_toNat hk 2 (by norm_num)
  unfold scanStep
  rw [e1, e2]
  change ScanInv xs d (k + 1)
    (if sc.status == 0 then
      if decide (date xs k < 4294967296) && decide (offset xs k < 4294967296) &&
          (UInt64.ofNat k == 0 || decide (sc.last < date xs k)) then
        ⟨0, date xs k, if date xs k ≤ d then offset xs k else sc.dat0,
          if date xs k ≤ d + 1 then offset xs k else sc.dat1⟩
      else ⟨1, sc.last, sc.dat0, sc.dat1⟩
    else sc)
  by_cases hs : sc.status = 0
  · simp only [hs, beq_self_eq_true, ite_true]
    by_cases hc : (decide (date xs k < 4294967296) && decide (offset xs k < 4294967296) &&
        (UInt64.ofNat k == 0 || decide (sc.last < date xs k))) = true
    · simp only [hc, ite_true]
      intro _
      obtain ⟨hb, hsorted, hlast, hf0, hf1⟩ := h hs
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨hd, ho⟩, hcase⟩ := hc
      refine ⟨fun j hj => ?_, fun i j hij hj => ?_, fun _ => by simp, found_step hf0,
        found_step hf1⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
        · exact hb j hj
        · subst hj
          exact ⟨UInt64.lt_iff_toNat_lt.1 hd, UInt64.lt_iff_toNat_lt.1 ho⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
        · exact hsorted i j hij hj
        · subst hj
          have hk0 : 0 < j := by omega
          have hl : sc.last < date xs j := by
            rcases hcase with hz | hl
            · have : (UInt64.ofNat j).toNat = j :=
                UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
              rw [hz] at this; simp at this; omega
            · exact hl
          rw [hlast hk0] at hl
          rcases Nat.lt_or_ge i (j - 1) with hi | hi
          · exact UInt64.lt_trans (hsorted i (j - 1) hi (by omega)) hl
          · have : i = j - 1 := by omega
            subst this; exact hl
    · simp only [hc, Bool.false_eq_true, ite_false]
      intro h1; exact absurd h1 (by simp)
  · simp only [beq_iff_eq, hs, ite_false]
    intro h1; exact absurd h1 hs

/-- The pass over every entry gives the facts for all of them. -/
theorem scan_inv (xs : Array UInt64) (d n : UInt64) :
    ScanInv xs d (n / 2).toNat (LeanExe.loop (n / 2) ⟨0, 0, 0, 0⟩ (scanStep xs d)) := by
  refine LeanExe.Dialect.loop_induction (P := ScanInv xs d) ?_ ?_
  · intro _
    exact ⟨fun j hj => absurd hj (by omega), fun i j _ hj => absurd hj (by omega),
      fun h => absurd h (by omega), Or.inr fun j hj => absurd hj (by omega),
      Or.inr fun j hj => absurd hj (by omega)⟩
  · intro k s hk hinv
    have hn := UInt64.toNat_lt n
    have h2 : (n / 2).toNat = n.toNat / 2 := UInt64.toNat_div n 2
    exact scan_step (by omega) hinv

/-- An offset found among all entries of a table whose first date is at most `d` is TAI − UTC on
the day `d`. -/
theorem leapOffset_of_found {xs : Array UInt64} {d v : UInt64} (hc : 0 < count xs)
    (h0 : date xs 0 ≤ d) (hf : Found xs d (count xs) v) : LeapOffset xs d v := by
  rcases hf with ⟨i, hi, hd, ho, hl⟩ | hnone
  · exact ⟨i, hi, hd, ho, hl⟩
  · exact absurd h0 (UInt64.not_le.2 (hnone 0 hc))

/-- The integer of a word below `2³²` read as an `Int64`. -/
theorem toInt_small {w : UInt64} (h : w.toNat < 2 ^ 32) : w.toInt64.toInt = (w.toNat : ℤ) := by
  rw [Signed64Value.toInt_toInt64]; split <;> omega

/-- An offset of a valid entry is one of the entries' offsets. -/
theorem found_bound {xs : Array UInt64} {d v : UInt64} {k : ℕ}
    (hb : ∀ j < k, (date xs j).toNat < 2 ^ 32 ∧ (offset xs j).toNat < 2 ^ 32)
    (hc : 0 < k) (h0 : date xs 0 ≤ d) (hf : Found xs d k v) : v.toNat < 2 ^ 32 := by
  rcases hf with ⟨i, hi, -, ho, -⟩ | hnone
  · rw [← ho]; exact (hb i hi).2
  · exact absurd h0 (UInt64.not_le.2 (hnone 0 hc))

/-- The length of a day in seconds, `86400 + Δ₁ − Δ₀`, of offsets below `2³²`. -/
theorem len_toInt {a b : UInt64} (ha : a.toNat < 2 ^ 32) (hb : b.toNat < 2 ^ 32) :
    (86400 + b.toInt64 - a.toInt64).toInt = 86400 + (b.toNat : ℤ) - a.toNat := by
  rw [Int64.toInt_sub, Int64.toInt_add, toInt_small ha, toInt_small hb]
  have e : (86400 : Int64).toInt = 86400 := by decide
  have hin : ((86400 : ℤ) + (b.toNat : ℤ)).bmod (2 ^ 64) = 86400 + b.toNat :=
    Int.bmod_eq_of_le (by omega) (by omega)
  rw [e, hin]
  exact Int.bmod_eq_of_le (by omega) (by omega)

/-- **Time scales.**  An accepted result of `timeScales` has a valid table and a day `d` with
`d₀ ≤ d` and `d + 1 < E`.  Its `dat` is TAI − UTC on the day `d`, the UTC seconds `s` lie in
`[0, L(d))` with `L(d) = 86400 + ΔAT(d + 1) − ΔAT(d)`, and its intervals contain the seconds of the
day `d` in TAI, `s + ΔAT(d)`, in TT, `s + ΔAT(d) + 32.184`, and in UT1, `s + δ` for every `δ` of
the interval of UT1 − UTC. -/
theorem timeScales_sound {xs : Array UInt64} {d : UInt64} {s dlo dhi : Float}
    (hsize : xs.size < 2 ^ 64) (h : (timeScales xs d s dlo dhi).status = 0) :
    ValidTable xs ∧ date xs 0 ≤ d ∧ d.toNat + 1 < xs[0]!.toNat ∧
      LeapOffset xs d (timeScales xs d s dlo dhi).dat ∧
      ∃ dat1, LeapOffset xs (d + 1) dat1 ∧ Finite s.toBits ∧ 0 ≤ value s.toBits ∧
        value s.toBits < 86400 + (dat1.toNat : ℝ) - (timeScales xs d s dlo dhi).dat.toNat ∧
        Contains (timeScales xs d s dlo dhi).tai
          (value s.toBits + (timeScales xs d s dlo dhi).dat.toNat) ∧
        Contains (timeScales xs d s dlo dhi).tt
          (value s.toBits + (timeScales xs d s dlo dhi).dat.toNat + 32.184) ∧
        ∀ δ, Within dlo dhi δ → Contains (timeScales xs d s dlo dhi).ut1 (value s.toBits + δ) := by
  unfold timeScales at h ⊢
  have i0 : (0 : UInt64).toNat = 0 := rfl
  have i1 : (1 : UInt64).toNat = 1 := rfl
  simp only [i0, i1] at h ⊢
  have hn : xs.size.toUInt64.toNat = xs.size := by
    rw [Nat.toUInt64_eq]
    exact UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
  by_cases h1 : (decide (3 ≤ xs.size.toUInt64) && xs.size.toUInt64 % 2 == 1 &&
      decide (xs[0]! < 4294967296)) = true
  · simp only [h1, ite_true] at h ⊢
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h1
    obtain ⟨⟨hn3, hodd⟩, he⟩ := h1
    have hn3' : 3 ≤ xs.size := by have := UInt64.le_iff_toNat_le.1 hn3; simpa [hn] using this
    have hodd' : xs.size % 2 = 1 := by
      have := congrArg UInt64.toNat hodd
      rw [UInt64.toNat_mod, hn] at this; simpa using this
    have he' : xs[0]!.toNat < 2 ^ 32 := by have := UInt64.lt_iff_toNat_lt.1 he; simpa using this
    have hcount : ((xs.size.toUInt64 - 1) / 2).toNat = count xs := by
      rw [UInt64.toNat_div, UInt64.toNat_sub_of_le _ _ (by
        rw [UInt64.le_iff_toNat_le, hn]; simp; omega), hn]
      simp [count]
    have inv := scan_inv xs d (xs.size.toUInt64 - 1)
    rw [hcount] at inv
    generalize LeanExe.loop ((xs.size.toUInt64 - 1) / 2) ⟨0, 0, 0, 0⟩ (scanStep xs d) = sc
      at h inv ⊢
    have hc0 : 0 < count xs := by unfold count; omega
    by_cases h2 : (sc.status == 0 && decide (sc.last < xs[0]!)) = true
    · simp only [h2, ite_true] at h ⊢
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h2
      obtain ⟨hs0, hlastE⟩ := h2
      obtain ⟨hb, hsorted, hlast, hf0, hf1⟩ := inv hs0
      by_cases h3 : (decide (xs[1]! ≤ d) && decide (d < xs[0]! - 1)) = true
      · simp only [h3, ite_true] at h ⊢
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h3
        obtain ⟨hd0, hdE⟩ := h3
        have hdate0 : date xs 0 = xs[1]! := rfl
        have hE1 : 1 ≤ xs[0]!.toNat := by
          have := UInt64.lt_iff_toNat_lt.1 hlastE; omega
        have hdE' : d.toNat + 1 < xs[0]!.toNat := by
          have := UInt64.lt_iff_toNat_lt.1 hdE
          have h1' : (1 : UInt64).toNat = 1 := rfl
          rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, h1']; exact hE1), h1']
            at this
          omega
        have hd1 : date xs 0 ≤ d + 1 := by
          rw [hdate0, UInt64.le_iff_toNat_le, UInt64.toNat_add]
          have h1' : (1 : UInt64).toNat = 1 := rfl
          rw [h1', Nat.mod_eq_of_lt (by omega)]
          have := UInt64.le_iff_toNat_le.1 hd0; omega
        have L0 := leapOffset_of_found hc0 (hdate0 ▸ hd0) hf0
        have L1 := leapOffset_of_found hc0 hd1 hf1
        have b0 := found_bound hb hc0 (hdate0 ▸ hd0) hf0
        have b1 := found_bound hb hc0 hd1 hf1
        have hvalid : ValidTable xs := by
          refine ⟨hn3', hodd', fun i hi => ?_, hsorted, ?_⟩
          · rcases Nat.eq_zero_or_pos i with h0 | hpos
            · subst h0; exact he'
            · rcases Nat.even_or_odd i with ⟨j, hj⟩ | ⟨j, hj⟩
              · have := (hb (j - 1) (by unfold count; omega)).2
                have e : 2 * (j - 1) + 2 = i := by omega
                simpa [offset, e] using this
              · have := (hb j (by unfold count; omega)).1
                have e : 2 * j + 1 = i := by omega
                simpa [date, e] using this
          · rw [← hlast hc0]; exact hlastE
        generalize hlen : (86400 + sc.dat1.toInt64 - sc.dat0.toInt64 : Int64) = len at h ⊢
        have hlenv : len.toInt = 86400 + (sc.dat1.toNat : ℤ) - sc.dat0.toNat :=
          hlen ▸ len_toInt b0 b1
        by_cases h4 : (finite s && decide (0 ≤ s) && decide (s < len.toFloat) &&
            (make dlo dhi).status == 0) = true
        · simp only [h4, ite_true] at h ⊢
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h4
          obtain ⟨⟨⟨hfin, hnn⟩, hlt⟩, hu⟩ := h4
          have fs := (finite_iff s).1 (decide_eq_true hfin)
          obtain ⟨z0, zv⟩ := zero_value
          have hs0' : 0 ≤ value s.toBits := by
            have := (le_iff_value z0 fs).mp hnn; rwa [zv] at this
          obtain ⟨flen, vlen⟩ := Signed64Value.toFloat_exact len (by rw [hlenv]; omega)
          have hslt : value s.toBits < len.toInt := by
            have := (lt_iff_value fs flen).mp hlt; rwa [vlen] at this
          have hS : Encloses (point s) (value s.toBits) := fun h => (point_sound h).2
          have hD : Encloses (ofInt sc.dat0.toInt64) (sc.dat0.toNat : ℝ) :=
            encloses_ofInt' (m := (sc.dat0.toNat : ℤ)) (toInt_small b0)
              (by rw [Int.natAbs_natCast]; omega) (by push_cast; rfl)
          have htai := encloses_add hS hD
          have htt := encloses_add htai (encloses_ratio' (n := 32184) (d := 1000) (m := 32184)
            (k := 1000) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by decide +kernel) (q := 32.184) (by norm_num))
          have hut1 : ∀ δ, Within dlo dhi δ → Encloses (add (point s) (make dlo dhi))
              (value s.toBits + δ) := fun δ hδ => encloses_add hS (fun _ => contains_make hu hδ)
          by_cases h5 : ((add (point s) (ofInt sc.dat0.toInt64)).status == 0 &&
              (add (add (point s) (ofInt sc.dat0.toInt64)) (ratio 32184 1000)).status == 0 &&
              (add (point s) (make dlo dhi)).status == 0) = true
          · simp only [h5, ite_true]
            simp only [Bool.and_eq_true, beq_iff_eq] at h5
            obtain ⟨⟨t1, t2⟩, t3⟩ := h5
            refine ⟨hvalid, hdate0 ▸ hd0, hdE', L0, sc.dat1, L1, fs, hs0', ?_, htai t1, htt t2,
              fun δ hδ => hut1 δ hδ t3⟩
            rw [hlenv] at hslt; push_cast at hslt; linarith
          · simp only [h5, Bool.false_eq_true, ite_false, noTimes] at h
            exact absurd h (by decide)
        · simp only [h4, Bool.false_eq_true, ite_false, noTimes] at h
          exact absurd h (by decide)
      · simp only [h3, Bool.false_eq_true, ite_false, noTimes] at h
        exact absurd h (by decide)
    · simp only [h2, Bool.false_eq_true, ite_false, noTimes] at h
      exact absurd h (by decide)
  · simp only [h1, Bool.false_eq_true, ite_false, noTimes] at h
    exact absurd h (by decide)

end Demos.Frames
