import Demos.Energy.Arith
import Demos.Energy.Window

/-! The theorems about `authorizeWith` under a valid profile table.  `authorizeWith_iff` states
that the authorizer accepts exactly when the input is valid and the conditions of the acceptance
rule hold, `authorizeWith_sound` that an accepted setpoint gives the bounds of the acceptance rule
at each time of the window for every trajectory admitted until that time, and
`authorizeWith_accepted` the setpoint and expiry of an accepted result. -/

namespace Demos.Energy.Authorize

open Spec Words Arith

variable {site xs : Array UInt64}

/-! ### The interval in force and the window's power interval -/

theorem inForceLow_eq (hs : ProfileValid site) (hv : InputValid site xs) :
    (inForceLow site xs).toNat =
      if xs[4]! = 1 then site[10]!.toNat else xs[5]!.toNat - site[9]!.toNat := by
  have h9 := hs.tolerance
  have h5 := hv.inForce.1
  unfold inForceLow
  simp only [word_eq, UInt64.toNat_ofNat, Nat.reduceMod, Nat.reducePow, beq_iff_eq]
  split_ifs
  · rfl
  · exact toNat_sub (a := xs[5]!) (b := site[9]!) (by omega)

theorem inForceHigh_eq (hs : ProfileValid site) (hv : InputValid site xs) :
    (inForceHigh site xs).toNat =
      if xs[4]! = 1 then site[11]!.toNat else xs[5]!.toNat + site[9]!.toNat := by
  have h9 := hs.tolerance
  have h5 := hv.inForce.2
  unfold inForceHigh
  simp only [word_eq, UInt64.toNat_ofNat, Nat.reduceMod, Nat.reducePow, beq_iff_eq]
  split_ifs
  · rfl
  · exact toNat_add (a := xs[5]!) (b := site[9]!) (by omega)

theorem lowB_eq (hs : ProfileValid site) (hv : InputValid site xs) :
    (lowB site xs).toNat =
      min (min (inForceLow site xs).toNat (xs[10]!.toNat - site[9]!.toNat)) site[10]!.toNat := by
  have h9 := hs.tolerance
  have h10 := hv.setpoint.1
  unfold lowB
  rw [toNat_min, toNat_min]
  simp only [word_eq, UInt64.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
  rw [toNat_sub (a := xs[10]!) (b := site[9]!) (by omega)]

theorem highB_eq (hs : ProfileValid site) (hv : InputValid site xs) :
    (highB site xs).toNat =
      max (max (inForceHigh site xs).toNat (xs[10]!.toNat + site[9]!.toNat)) site[11]!.toNat := by
  have h9 := hs.tolerance
  have h10 := hv.setpoint.2
  unfold highB
  rw [toNat_max, toNat_max]
  simp only [word_eq, UInt64.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
  rw [toNat_add (a := xs[10]!) (b := site[9]!) (by omega)]

theorem lowB_signed (hs : ProfileValid site) (hv : InputValid site xs) :
    signed (lowB site xs) = powerLow (profileOf site) (snapshotOf xs) (setpointOf xs) := by
  have h9 := hs.tolerance
  have h10 := hv.setpoint.1
  have h5 := hv.inForce.1
  rw [signed, lowB_eq hs hv, inForceLow_eq hs hv]
  unfold powerLow setpointOf snapshotOf profileOf signed
  dsimp only
  split_ifs <;> simp only [State.low] <;> push_cast <;> omega

theorem highB_signed (hs : ProfileValid site) (hv : InputValid site xs) :
    signed (highB site xs) = powerHigh (profileOf site) (snapshotOf xs) (setpointOf xs) := by
  rw [signed, highB_eq hs hv, inForceHigh_eq hs hv]
  unfold powerHigh setpointOf snapshotOf profileOf signed
  dsimp only
  split_ifs <;> simp only [State.high] <;> push_cast <;> omega

theorem lowB_le (hs : ProfileValid site) (hv : InputValid site xs) :
    (lowB site xs).toNat ≤ 4294967296 := by
  have := hs.fallbackLow.2
  rw [lowB_eq hs hv]
  omega

theorem lowB_ge (hs : ProfileValid site) (hv : InputValid site xs) :
    4294967296 - 2097152 ≤ (lowB site xs).toNat := by
  have h9 := hs.tolerance
  have h10 := hv.setpoint.1
  have h5 := hv.inForce.1
  have hf := hs.fallbackLow.1
  rw [lowB_eq hs hv, inForceLow_eq hs hv]
  split_ifs <;> omega

theorem highB_ge (hs : ProfileValid site) (hv : InputValid site xs) :
    4294967296 ≤ (highB site xs).toNat := by
  have := hs.fallbackHigh.1
  rw [highB_eq hs hv]
  omega

theorem highB_le (hs : ProfileValid site) (hv : InputValid site xs) :
    (highB site xs).toNat ≤ 4294967296 + 2097152 := by
  have h9 := hs.tolerance
  have h10 := hv.setpoint.2
  have h5 := hv.inForce.2
  have hf := hs.fallbackHigh.2
  rw [highB_eq hs hv, inForceHigh_eq hs hv]
  split_ifs <;> omega

theorem lower_iff (hs : ProfileValid site) (hv : InputValid site xs) :
    lowB site xs < word site 10 ↔
      lowerTested (profileOf site) (snapshotOf xs) (setpointOf xs) := by
  rw [lowerTested, ← lowB_signed hs hv, UInt64.lt_iff_toNat_lt]
  simp only [word_eq, UInt64.toNat_ofNat, Nat.reduceMod, Nat.reducePow, profileOf, signed]
  omega

theorem upper_iff (hs : ProfileValid site) (hv : InputValid site xs) :
    word site 11 < highB site xs ↔
      upperTested (profileOf site) (snapshotOf xs) (setpointOf xs) := by
  rw [upperTested, ← highB_signed hs hv, UInt64.lt_iff_toNat_lt]
  simp only [word_eq, UInt64.toNat_ofNat, Nat.reduceMod, Nat.reducePow, profileOf, signed]
  omega

/-! ### The tests of each side -/

theorem toNat_offset : (4294967296 : UInt64).toNat = 4294967296 := rfl

theorem exportOk_iff (hs : ProfileValid site) (hv : InputValid site xs) :
    exportOk site xs (lowB site xs) = true ↔
      ((snapshotOf xs).pvHigh : ℤ) ≤ (snapshotOf xs).loadLow +
        powerLow (profileOf site) (snapshotOf xs) (setpointOf xs) + (profileOf site).exportCap := by
  have hb := lowB_le hs hv
  have h9 := hv.pv.2
  have h6 := hv.load
  have hx := hs.exportCap
  rw [← lowB_signed hs hv]
  unfold exportOk
  simp only [word_eq, UInt64.toNat_ofNat, Nat.reduceMod, Nat.reducePow, decide_eq_true_eq,
    UInt64.le_iff_toNat_le, offset]
  have e1 : (xs[9]! + (4294967296 : UInt64)).toNat = xs[9]!.toNat + 4294967296 := by
    rw [toNat_add (by rw [toNat_offset]; omega), toNat_offset]
  have e2 : (xs[6]! + lowB site xs).toNat = xs[6]!.toNat + (lowB site xs).toNat :=
    toNat_add (by omega)
  have e3 : (xs[6]! + lowB site xs + site[6]!).toNat =
      xs[6]!.toNat + (lowB site xs).toNat + site[6]!.toNat := by
    rw [toNat_add (by rw [e2]; omega), e2]
  rw [e1, e3]
  simp only [snapshotOf, profileOf, signed]
  omega

theorem importOk_iff (hs : ProfileValid site) (hv : InputValid site xs) :
    importOk site xs (highB site xs) = true ↔
      ((snapshotOf xs).loadHigh : ℤ) + powerHigh (profileOf site) (snapshotOf xs) (setpointOf xs) ≤
        (profileOf site).importCap + (snapshotOf xs).pvLow := by
  have hb := highB_le hs hv
  have h7 := hv.load.2
  have h8 := hv.pv
  have hi := hs.importCap
  rw [← highB_signed hs hv]
  unfold importOk
  simp only [word_eq, UInt64.toNat_ofNat, Nat.reduceMod, Nat.reducePow, decide_eq_true_eq,
    UInt64.le_iff_toNat_le, offset]
  have e1 : (xs[7]! + highB site xs).toNat = xs[7]!.toNat + (highB site xs).toNat :=
    toNat_add (by omega)
  have e2 : (site[5]! + xs[8]!).toNat = site[5]!.toNat + xs[8]!.toNat := toNat_add (by omega)
  have e3 : (site[5]! + xs[8]! + (4294967296 : UInt64)).toNat =
      site[5]!.toNat + xs[8]!.toNat + 4294967296 := by
    rw [toNat_add (by rw [e2, toNat_offset]; omega), e2, toNat_offset]
  rw [e1, e3]
  simp only [snapshotOf, profileOf, signed]
  omega

theorem lowDrain_toNat (hs : ProfileValid site) (hv : InputValid site xs) :
    (lowDrain site (lowB site xs)).toNat =
      ((4294967296 - (lowB site xs).toNat) * site[13]!.toNat * 1000000 + site[7]!.toNat - 1) /
        site[7]!.toNat + site[8]!.toNat * site[13]!.toNat := by
  have hb := lowB_le hs hv
  have hb' := lowB_ge hs hv
  have hW := hs.window
  have he1 := hs.etaLow
  have he2 := hs.etaHigh
  have hl := hs.loss
  unfold lowDrain
  simp only [word_eq, UInt64.toNat_ofNat, Nat.reduceMod, Nat.reducePow, offset, million]
  have hn : 4294967296 - (lowB site xs).toNat ≤ 2097152 := by omega
  have m1 : (4294967296 - (lowB site xs).toNat) * site[13]!.toNat ≤ 2097152 * 3600 :=
    Nat.mul_le_mul hn hW
  have m2 : (4294967296 - (lowB site xs).toNat) * site[13]!.toNat * 1000000 ≤
      2097152 * 3600 * 1000000 := Nat.mul_le_mul_right _ m1
  have m3 : site[8]!.toNat * site[13]!.toNat ≤ 1048576 * 3600 := Nat.mul_le_mul hl hW
  have q : (((4294967296 - (lowB site xs).toNat) * site[13]!.toNat * 1000000 + site[7]!.toNat - 1) /
      site[7]!.toNat) ≤ (4294967296 - (lowB site xs).toNat) * site[13]!.toNat * 1000000 +
        site[7]!.toNat := Nat.le_trans (Nat.div_le_self _ _) (by omega)
  have e1 : ((4294967296 : UInt64) - lowB site xs).toNat = 4294967296 - (lowB site xs).toNat := by
    rw [toNat_sub (by rw [toNat_offset]; omega), toNat_offset]
  have e2 : ((4294967296 : UInt64) - lowB site xs) * site[13]! =
      ((4294967296 : UInt64) - lowB site xs) * site[13]! := rfl
  have e3 : (((4294967296 : UInt64) - lowB site xs) * site[13]!).toNat =
      (4294967296 - (lowB site xs).toNat) * site[13]!.toNat := by
    rw [toNat_mul (by rw [e1]; omega), e1]
  have e4 : (((4294967296 : UInt64) - lowB site xs) * site[13]! * (1000000 : UInt64)).toNat =
      (4294967296 - (lowB site xs).toNat) * site[13]!.toNat * 1000000 := by
    rw [toNat_mul (by rw [e3, show (1000000 : UInt64).toNat = 1000000 from rfl]; omega), e3]
    rfl
  have e5 : (((4294967296 : UInt64) - lowB site xs) * site[13]! * (1000000 : UInt64) +
      site[7]!).toNat =
      (4294967296 - (lowB site xs).toNat) * site[13]!.toNat * 1000000 + site[7]!.toNat := by
    rw [toNat_add (by rw [e4]; omega), e4]
  have e6 : (((4294967296 : UInt64) - lowB site xs) * site[13]! * (1000000 : UInt64) +
      site[7]! - 1).toNat =
      (4294967296 - (lowB site xs).toNat) * site[13]!.toNat * 1000000 + site[7]!.toNat - 1 := by
    rw [toNat_sub (by rw [e5, show (1 : UInt64).toNat = 1 from rfl]; omega), e5]
    rfl
  have e7 : (site[8]! * site[13]!).toNat = site[8]!.toNat * site[13]!.toNat :=
    toNat_mul (by omega)
  rw [toNat_add (by rw [UInt64.toNat_div, e6, e7]; omega), UInt64.toNat_div, e6, e7]

theorem highGain_toNat (hs : ProfileValid site) (hv : InputValid site xs) :
    (highGain site (highB site xs)).toNat =
      ((highB site xs).toNat - 4294967296) * site[13]!.toNat := by
  have hb := highB_le hs hv
  have hb' := highB_ge hs hv
  have hW := hs.window
  unfold highGain
  simp only [word_eq, UInt64.toNat_ofNat, Nat.reduceMod, Nat.reducePow, offset]
  have hn : (highB site xs).toNat - 4294967296 ≤ 2097152 := by omega
  have m1 : ((highB site xs).toNat - 4294967296) * site[13]!.toNat ≤ 2097152 * 3600 :=
    Nat.mul_le_mul hn hW
  have e1 : (highB site xs - (4294967296 : UInt64)).toNat = (highB site xs).toNat - 4294967296 := by
    rw [toNat_sub (by rw [toNat_offset]; omega), toNat_offset]
  rw [toNat_mul (by rw [e1]; omega), e1]

theorem drainLow_cast (hs : ProfileValid site) (hv : InputValid site xs) :
    ((lowDrain site (lowB site xs)).toNat : ℤ) =
      drainLow (profileOf site) (powerLow (profileOf site) (snapshotOf xs) (setpointOf xs)) := by
  have hb := lowB_le hs hv
  have he1 := hs.etaLow
  rw [lowDrain_toNat hs hv, ← lowB_signed hs hv]
  unfold drainLow profileOf signed
  dsimp only
  have hpos : 1 ≤ (4294967296 - (lowB site xs).toNat) * site[13]!.toNat * 1000000 +
      site[7]!.toNat := by omega
  rw [Nat.cast_add, Int.natCast_div, Nat.cast_sub hpos]
  push_cast [Nat.cast_sub hb]
  ring_nf

theorem floorOk_iff (hs : ProfileValid site) (hv : InputValid site xs) :
    floorOk site xs (lowB site xs) = true ↔
      ((profileOf site).floor : ℤ) ≤ (snapshotOf xs).energyLow ∧
        ((profileOf site).floor : ℤ) +
          drainLow (profileOf site) (powerLow (profileOf site) (snapshotOf xs) (setpointOf xs)) ≤
            (snapshotOf xs).energyLow := by
  have hb := lowB_le hs hv
  have hb' := lowB_ge hs hv
  have hW := hs.window
  have he1 := hs.etaLow
  have he2 := hs.etaHigh
  have hl := hs.loss
  have hf := hs.floor
  have hc := hs.ceiling
  have hd := lowDrain_toNat hs hv
  have hn : 4294967296 - (lowB site xs).toNat ≤ 2097152 := by omega
  have m1 : (4294967296 - (lowB site xs).toNat) * site[13]!.toNat ≤ 2097152 * 3600 :=
    Nat.mul_le_mul hn hW
  have m2 : (4294967296 - (lowB site xs).toNat) * site[13]!.toNat * 1000000 ≤
      2097152 * 3600 * 1000000 := Nat.mul_le_mul_right _ m1
  have m3 : site[8]!.toNat * site[13]!.toNat ≤ 1048576 * 3600 := Nat.mul_le_mul hl hW
  have q : (((4294967296 - (lowB site xs).toNat) * site[13]!.toNat * 1000000 + site[7]!.toNat - 1) /
      site[7]!.toNat) ≤ (4294967296 - (lowB site xs).toNat) * site[13]!.toNat * 1000000 +
        site[7]!.toNat := Nat.le_trans (Nat.div_le_self _ _) (by omega)
  rw [← drainLow_cast hs hv]
  unfold floorOk
  simp only [word_eq, UInt64.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Bool.and_eq_true,
    decide_eq_true_eq, UInt64.le_iff_toNat_le]
  rw [toNat_add (by rw [hd]; omega)]
  simp only [snapshotOf, profileOf]
  omega

theorem ceilingOk_iff (hs : ProfileValid site) (hv : InputValid site xs) :
    ceilingOk site xs (highB site xs) = true ↔
      ((snapshotOf xs).energyHigh : ℤ) ≤ (profileOf site).ceiling ∧
        ((snapshotOf xs).energyHigh : ℤ) +
          powerHigh (profileOf site) (snapshotOf xs) (setpointOf xs) * (profileOf site).window ≤
            (profileOf site).ceiling := by
  have hb := highB_le hs hv
  have hb' := highB_ge hs hv
  have hW := hs.window
  have he := hv.energy.2
  have hg := highGain_toNat hs hv
  have hn : (highB site xs).toNat - 4294967296 ≤ 2097152 := by omega
  have m1 : ((highB site xs).toNat - 4294967296) * site[13]!.toNat ≤ 2097152 * 3600 :=
    Nat.mul_le_mul hn hW
  rw [← highB_signed hs hv]
  unfold ceilingOk
  simp only [word_eq, UInt64.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Bool.and_eq_true,
    decide_eq_true_eq, UInt64.le_iff_toNat_le]
  rw [toNat_add (by rw [hg]; omega), hg]
  simp only [snapshotOf, profileOf, signed]
  have hcast : (((highB site xs).toNat - 4294967296 : ℕ) : ℤ) =
      ((highB site xs).toNat : ℤ) - 4294967296 := by omega
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by exact_mod_cast h1, ?_⟩
    have : ((xs[3]!.toNat + ((highB site xs).toNat - 4294967296) * site[13]!.toNat : ℕ) : ℤ) ≤
        (site[2]!.toNat : ℤ) := by exact_mod_cast h2
    push_cast [hcast] at this
    linarith
  · rintro ⟨h1, h2⟩
    refine ⟨by exact_mod_cast h1, ?_⟩
    have : ((xs[3]!.toNat + ((highB site xs).toNat - 4294967296) * site[13]!.toNat : ℕ) : ℤ) ≤
        (site[2]!.toNat : ℤ) := by
      push_cast [hcast]
      linarith
    exact_mod_cast this

/-! ### Acceptance -/

theorem accepted_iff (site xs : Array UInt64) :
    (authorizeWith site xs).status = .accepted ↔
      xs.size.toUInt64 = 11 ∧ word xs 0 = 1 ∧ rangeOk xs = true ∧ orderOk xs = true ∧
        limitOk site xs = true ∧
        (lowB site xs < word site 10 →
          exportOk site xs (lowB site xs) = true ∧ floorOk site xs (lowB site xs) = true) ∧
        (word site 11 < highB site xs →
          importOk site xs (highB site xs) = true ∧ ceilingOk site xs (highB site xs) = true) := by
  unfold authorizeWith reject
  dsimp only
  by_cases hl : lowB site xs < word site 10 <;> by_cases hu : word site 11 < highB site xs <;>
    simp only [hl, hu, decide_true, decide_false, Bool.true_and, Bool.false_and] <;>
    split_ifs <;> simp_all

theorem inputValid_iff (hs : ProfileValid site) :
    (xs.size.toUInt64 = 11 ∧ word xs 0 = 1 ∧ rangeOk xs = true ∧ orderOk xs = true ∧
      limitOk site xs = true) ↔ InputValid site xs := by
  rw [rangeOk_iff, orderOk_iff, limitOk_iff hs]
  simp only [word_eq, show (0 : UInt64).toNat = 0 from rfl]
  constructor
  · rintro ⟨h1, h2, ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10⟩, ⟨o1, o2, o3⟩, l⟩
    exact ⟨h1, h2, r1, ⟨o1, r3⟩, r4, r5, ⟨o2, r7⟩, ⟨o3, r9⟩, r10, l⟩
  · intro hv
    exact ⟨hv.size, hv.version, ⟨hv.time, by have := hv.energy; omega, hv.energy.2, hv.mode,
      hv.inForce, by have := hv.load; omega, hv.load.2, by have := hv.pv; omega, hv.pv.2,
      hv.setpoint⟩, ⟨hv.energy.1, hv.load.1, hv.pv.1⟩, hv.limit⟩

/-- The authorizer accepts exactly when the input is valid and the conditions of the acceptance
rule hold. -/
theorem authorizeWith_iff (hs : ProfileValid site) :
    (authorizeWith site xs).status = .accepted ↔
      InputValid site xs ∧ Conditions (profileOf site) (snapshotOf xs) (setpointOf xs) := by
  rw [accepted_iff]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, hlo, hhi⟩
    have hv := (inputValid_iff hs).mp ⟨h1, h2, h3, h4, h5⟩
    refine ⟨hv, ⟨fun hl => ?_, fun hl => ?_, fun hu => ?_, fun hu => ?_⟩⟩
    · exact (exportOk_iff hs hv).mp (hlo ((lower_iff hs hv).mpr hl)).1
    · exact (floorOk_iff hs hv).mp (hlo ((lower_iff hs hv).mpr hl)).2
    · exact (importOk_iff hs hv).mp (hhi ((upper_iff hs hv).mpr hu)).1
    · exact (ceilingOk_iff hs hv).mp (hhi ((upper_iff hs hv).mpr hu)).2
  · rintro ⟨hv, hc⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := (inputValid_iff hs).mpr hv
    refine ⟨h1, h2, h3, h4, h5, fun hl => ?_, fun hu => ?_⟩
    · have hl' := (lower_iff hs hv).mp hl
      exact ⟨(exportOk_iff hs hv).mpr (hc.exportCap hl'), (floorOk_iff hs hv).mpr (hc.floor hl')⟩
    · have hu' := (upper_iff hs hv).mp hu
      exact ⟨(importOk_iff hs hv).mpr (hc.importCap hu'),
        (ceilingOk_iff hs hv).mpr (hc.ceiling hu')⟩

/-- An accepted result holds the proposed setpoint and the expiry `t_m + W - τ`. -/
theorem authorizeWith_accepted (hs : ProfileValid site)
    (h : (authorizeWith site xs).status = .accepted) :
    (authorizeWith site xs).setpoint = xs[10]! ∧
      (authorizeWith site xs).expiry.toNat =
        (snapshotOf xs).time + (profileOf site).window - (profileOf site).transition := by
  have hv := ((authorizeWith_iff hs).mp h).1
  have ht := hv.time
  have hW := hs.window
  have hT := hs.timing
  have hres : authorizeWith site xs =
      Decision.mk .accepted (word xs 10) (word xs 1 + word site 13 - word site 12) := by
    unfold authorizeWith reject at h ⊢
    dsimp only at h ⊢
    split_ifs at h ⊢
    simp_all
  rw [hres]
  simp only [word_eq, UInt64.toNat_ofNat, Nat.reduceMod, Nat.reducePow, snapshotOf, profileOf,
    true_and]
  have e1 : (xs[1]! + site[13]!).toNat = xs[1]!.toNat + site[13]!.toNat := toNat_add (by omega)
  rw [toNat_sub (by rw [e1]; omega), e1]

/-- An accepted setpoint gives the bounds of the acceptance rule at each time of the window for
every trajectory admitted until that time. -/
theorem authorizeWith_sound (hs : ProfileValid site)
    (h : (authorizeWith site xs).status = .accepted) {x : Trajectory} {t : ℝ}
    (ht : t ∈ window (profileOf site) (snapshotOf xs))
    (hx : x.AdmittedUntil (profileOf site) (snapshotOf xs) (setpointOf xs) t) :
    x.WithinOrFallback (profileOf site) (snapshotOf xs) t := by
  have heta : 0 < (profileOf site).eta := by
    have := hs.etaLow
    simp only [profileOf]
    omega
  have hF : (profileOf site).fallbackLow ≤ 0 ∧ 0 ≤ (profileOf site).fallbackHigh := by
    have h1 := hs.fallbackLow.2
    have h2 := hs.fallbackHigh.1
    simp only [profileOf, signed]
    omega
  exact window_sound heta hF ((authorizeWith_iff hs).mp h).2 ht hx

end Demos.Energy.Authorize
