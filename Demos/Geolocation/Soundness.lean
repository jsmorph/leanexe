import Demos.Geolocation.Search
import Demos.Frames.Soundness

/-!
The theorems of `locate` over its input array.  An admissible parameter (`Admissible`) is a choice
of an Earth-fixed state in each receiver's intervals and of a carrier frequency in its interval,
and a point fits the measurements (`Fits`) when every measurement's model lies within its bound of
the measured value.  For a valid input, `locate_cover` states that every triple of the region
whose position fits the measurements for some admissible parameter lies in a returned box (G1),
`locate_inner` that every point of a box labeled 1 fits them for every admissible parameter (G2),
`locate_within` that the boxes lie in the region and number at most `C` (G3), and
`locate_status` what the status and the levels state (G4).  `locate_invalid` states that status 3
marks the inputs that `valid` rejects (G5).
-/

namespace Demos.Geolocation

open LeanExe.ProofKit LeanExe.Dialect Library.Numerics.Bounds Library.Numerics.Interval
open Library.Numerics.Float64
open Demos.Screening (val rd allFinite isWhole encloses_make encloses_point allFinite_spec
  append_get_left append_get_right)
open CodeLib.IEEE64 (value Finite)
open Model (V3)

/-! ### The model of an input -/

/-- The number of receivers of an input. -/
def nOf (xs : Array Float) : UInt64 := (rd xs 2).toUInt64

/-- The number of measurements of an input. -/
def mOf (xs : Array Float) : UInt64 := (rd xs 3).toUInt64

/-- The index of the first measurement's entries. -/
def baseOf (xs : Array Float) : UInt64 := 20 + 14 * nOf xs

/-- The intervals of the receivers' Earth-fixed states. -/
def rxOf (xs : Array Float) : Array Interval := receivers Trig.invPi Trig.halfPi xs (nOf xs)

/-- The day of the TEME frame as a real number. -/
noncomputable def dayOf (xs : Array Float) : ℝ := ((rd xs 4).toUInt64.toNat : ℝ)

/-- The real number lies in the interval of the input values at `q` and `q + 1`. -/
def InPair (xs : Array Float) (q : UInt64) (x : ℝ) : Prop :=
  val (rd xs q) ≤ x ∧ x ≤ val (rd xs (q + 1))

/-- A parameter: an Earth-fixed position and velocity for each receiver, and a carrier
frequency. -/
structure Params where
  s : ℕ → V3
  u : ℕ → V3
  f : ℝ

/-- The state `(s, u)` lies in the intervals of the receiver whose entries start at `b`. -/
def InState (xs : Array Float) (b : UInt64) (s u : V3) : Prop :=
  InPair xs (b + 2) s.1 ∧ InPair xs (b + 4) s.2.1 ∧ InPair xs (b + 6) s.2.2 ∧
    InPair xs (b + 8) u.1 ∧ InPair xs (b + 10) u.2.1 ∧ InPair xs (b + 12) u.2.2

/-- The Earth-fixed state `(s, u)` is that of a TEME state in the intervals of the receiver whose
entries start at `b`, at a time `t` of UT1 in its interval, with the polar motion `xp` and `yp`:
`s = E(θ(t)) r` and `u = E(θ(t)) (v + ω(t) (r₂, −r₁, 0))`. -/
def FromTeme (xs : Array Float) (b : UInt64) (xp yp : ℝ) (s u : V3) : Prop :=
  ∃ t r v, InPair xs b t ∧ InState xs b r v ∧
    s = Frames.Model.earthFixed (Model.theta (dayOf xs) t) xp yp r ∧
    u = Model.earthVelocity (Model.theta (dayOf xs) t) (Model.spin (dayOf xs) t) xp yp r v

/-- An admissible parameter: the frequency in its interval, and each receiver's Earth-fixed
state in its intervals for the Earth-fixed frame, or arising from its TEME intervals with one
polar motion in its intervals for the TEME frame. -/
def Admissible (xs : Array Float) (P : Params) : Prop :=
  InPair xs 9 P.f ∧
    if rd xs 1 == 0.0 then
      ∀ i < (nOf xs).toNat, InState xs (20 + 14 * UInt64.ofNat i) (P.s i) (P.u i)
    else ∃ xp yp, InPair xs 5 xp ∧ InPair xs 7 yp ∧
      ∀ i < (nOf xs).toNat, FromTeme xs (20 + 14 * UInt64.ofNat i) xp yp (P.s i) (P.u i)

/-- The model of the measurement whose entries start at `q`, at the emitter position `x`. -/
noncomputable def predicted (xs : Array Float) (P : Params) (q : UInt64) (x : V3) : ℝ :=
  let i := (rd xs (q + 1)).toUInt64.toNat
  let j := (rd xs (q + 2)).toUInt64.toNat
  if rd xs q == 1.0 then Model.tdoa (P.s i) (P.s j) x
  else Model.fdoa P.f (P.s i) (P.u i) (P.s j) (P.u j) x

/-- The position `x` fits the measurements for the parameter `P`: each model lies within its
bound of the measured value. -/
def Fits (xs : Array Float) (P : Params) (x : V3) : Prop :=
  ∀ k < (mOf xs).toNat,
    |predicted xs P (baseOf xs + 5 * UInt64.ofNat k) x -
        val (rd xs (baseOf xs + 5 * UInt64.ofNat k + 3))| ≤
      val (rd xs (baseOf xs + 5 * UInt64.ofNat k + 4))

/-- The triple lies in the region of the input. -/
def InRegion (xs : Array Float) (φ lam h : ℝ) : Prop := InBox (regionOf xs) φ lam h

/-- The position of the triple fits the measurements for some admissible parameter. -/
def Consistent (xs : Array Float) (φ lam h : ℝ) : Prop :=
  ∃ P, Admissible xs P ∧ Fits xs P (Frames.Model.position φ lam h)

/-- Every point of the box fits the measurements for every admissible parameter. -/
def Inner (xs : Array Float) (b : Box) : Prop :=
  ∀ P, Admissible xs P → ∀ φ lam h, InBox b φ lam h →
    Fits xs P (Frames.Model.position φ lam h)

/-- The output's status is `s`. -/
def HasStatus (out : Array Float) (s : UInt64) : Prop := out[0]!.toBits = s.toFloat.toBits

/-! ### The facts of a valid input -/

theorem whole_le {x : Float} {lo hi : UInt64} (h : isWhole x lo hi = true) :
    lo ≤ x.toUInt64 ∧ x.toUInt64 ≤ hi := by
  simp only [isWhole, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.2, h.2⟩

theorem loop_all {n : UInt64} {p : UInt64 → Bool}
    (h : LeanExe.loop n true (fun i ok => ok && p i) = true) :
    ∀ i < n.toNat, p (UInt64.ofNat i) = true := by
  have key := loop_induction (n := n) (init := true) (f := fun i ok => ok && p i)
    (fun k ok => ok = true → ∀ i < k, p (UInt64.ofNat i) = true)
    (fun _ i hi => absurd hi (Nat.not_lt_zero i))
    (fun k ok _ ih hk i hi => by
      simp only [Bool.and_eq_true] at hk
      by_cases hik : i < k
      · exact ih hk.1 i hik
      · have : i = k := by omega
        subst this
        exact hk.2)
  exact key h

/-- The facts that `valid` establishes. -/
structure Facts (xs : Array Float) : Prop where
  n2 : 2 ≤ (nOf xs).toNat
  n16 : (nOf xs).toNat ≤ 16
  m64 : (mOf xs).toNat ≤ 64
  size : xs.size.toUInt64.toNat = 20 + 14 * (nOf xs).toNat + 5 * (mOf xs).toNat
  fin : ∀ q < xs.size.toUInt64.toNat, Finite (rd xs (UInt64.ofNat q)).toBits
  cap1 : 1 ≤ (rd xs 19).toUInt64.toNat
  cap : (rd xs 19).toUInt64.toNat ≤ 65536
  rx : ∀ i < (nOf xs).toNat, receiverOk xs (20 + 14 * UInt64.ofNat i) = true
  meas : ∀ k < (mOf xs).toNat,
    measurementOk xs (nOf xs) (baseOf xs + 5 * UInt64.ofNat k) = true
  day : (rd xs 4).toUInt64.toNat < 2 ^ 32

theorem valid_facts {xs : Array Float} (h : valid xs = true) : Facts xs := by
  simp only [valid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hfin⟩, -⟩, -⟩, hn⟩, hm⟩, hsz⟩, hday⟩, -⟩, -⟩, -⟩, -⟩, -⟩,
    -⟩, -⟩, -⟩, -⟩, hc⟩, he⟩ := h
  have day : (rd xs 4).toUInt64.toNat < 2 ^ 32 := by
    have := UInt64.le_iff_toNat_le.mp (whole_le hday).2
    simp only [UInt64.reduceToNat] at this
    omega
  obtain ⟨n2, n16⟩ := whole_le hn
  obtain ⟨-, m64⟩ := whole_le hm
  obtain ⟨c1, c2⟩ := whole_le hc
  have n2' : 2 ≤ (rd xs 2).toUInt64.toNat := UInt64.le_iff_toNat_le.mp n2
  have n16' : (rd xs 2).toUInt64.toNat ≤ 16 := UInt64.le_iff_toNat_le.mp n16
  have m64' : (rd xs 3).toUInt64.toNat ≤ 64 := UInt64.le_iff_toNat_le.mp m64
  simp only [entriesOk, Bool.and_eq_true] at he
  have e : (20 + 14 * (rd xs 2).toUInt64 + 5 * (rd xs 3).toUInt64).toNat =
      20 + 14 * (rd xs 2).toUInt64.toNat + 5 * (rd xs 3).toUInt64.toNat := by
    simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.reduceToNat]
    omega
  exact ⟨n2', n16', m64', by rw [hsz, e]; rfl, allFinite_spec hfin,
    UInt64.le_iff_toNat_le.mp c1, UInt64.le_iff_toNat_le.mp c2,
    fun i hi => loop_all he.1 i hi, fun k hk => loop_all he.2 k hk, day⟩

/-- An entry below the size of a valid input is finite. -/
theorem Facts.entry {xs : Array Float} (F : Facts xs) {q : UInt64}
    (hq : q.toNat < 20 + 14 * (nOf xs).toNat + 5 * (mOf xs).toNat) : Finite (rd xs q).toBits := by
  have := F.fin q.toNat (by rw [F.size]; exact hq)
  rwa [UInt64.ofNat_toNat] at this

/-- The index of entry `c` of measurement `k`. -/
theorem meas_index {xs : Array Float} (F : Facts xs) {k : ℕ} (hk : k < (mOf xs).toNat) {c : ℕ}
    (hc : c < 5) :
    (baseOf xs + 5 * UInt64.ofNat k + UInt64.ofNat c).toNat =
      20 + 14 * (nOf xs).toNat + 5 * k + c := by
  have := F.n16
  have := F.m64
  simp only [baseOf, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat', UInt64.reduceToNat]
  omega

/-- The facts of measurement `k` of a valid input: its receivers lie below `n`, and its bound is
finite. -/
theorem meas_facts {xs : Array Float} (F : Facts xs) {k : ℕ} (hk : k < (mOf xs).toNat) :
    let q := baseOf xs + 5 * UInt64.ofNat k
    (rd xs (q + 1)).toUInt64.toNat < (nOf xs).toNat ∧
      (rd xs (q + 2)).toUInt64.toNat < (nOf xs).toNat ∧
      Finite (rd xs (q + 4)).toBits := by
  intro q
  have h := F.meas k hk
  simp only [measurementOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨-, hi⟩, hj⟩, -⟩, -⟩ := h
  have hi' := (whole_le hi).2
  have hj' := (whole_le hj).2
  have n2 := F.n2
  have l : ∀ x : UInt64, x ≤ nOf xs - 1 → x.toNat < (nOf xs).toNat := fun x hx => by
    have := UInt64.le_iff_toNat_le.mp hx
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))] at this
    simp at this
    omega
  refine ⟨l _ hi', l _ hj', F.entry ?_⟩
  have := meas_index F hk (c := 4) (by norm_num)
  simp only [UInt64.reduceOfNat] at this
  rw [this]
  omega

/-! ### The receivers -/

/-- The six intervals of each of the first `n` receivers enclose the components of its state. -/
def RxSound (rx : Array Interval) (P : Params) (n : ℕ) : Prop :=
  ∀ i < n, Encloses rx[6 * i]! (P.s i).1 ∧ Encloses rx[6 * i + 1]! (P.s i).2.1 ∧
    Encloses rx[6 * i + 2]! (P.s i).2.2 ∧ Encloses rx[6 * i + 3]! (P.u i).1 ∧
    Encloses rx[6 * i + 4]! (P.u i).2.1 ∧ Encloses rx[6 * i + 5]! (P.u i).2.2

theorem receivers_get {xs : Array Float} {n : UInt64} (hn : n.toNat ≤ 16) {i c : ℕ}
    (hi : i < n.toNat) (hc : c < 6) :
    (receivers Trig.invPi Trig.halfPi xs n)[6 * i + c]! =
      component (stateOf Trig.invPi Trig.halfPi xs (20 + 14 * UInt64.ofNat i))
        (UInt64.ofNat c) := by
  unfold receivers
  have hn6 : (6 * n).toNat = 6 * n.toNat := by
    rw [UInt64.toNat_mul]; simp only [UInt64.reduceToNat]; omega
  rw [build_get (by rw [hn6]; omega)]
  have small : ∀ a : ℕ, a < 100 → (UInt64.ofNat a).toNat = a := fun a ha => by
    rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (lt_of_lt_of_le ha (by norm_num))
  have hd : UInt64.ofNat (6 * i + c) / 6 = UInt64.ofNat i := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_div, small _ (by omega), small _ (by omega)]
    have : (6 : UInt64).toNat = 6 := rfl
    rw [this]
    omega
  have hm : UInt64.ofNat (6 * i + c) % 6 = UInt64.ofNat c := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_mod, small _ (by omega), small _ (by omega)]
    have : (6 : UInt64).toNat = 6 := rfl
    rw [this]
    omega
  rw [hd, hm]

theorem component_stateOf {xs : Array Float} (hf : (rd xs 1 == 0.0) = true) (b : UInt64) :
    let s := stateOf Trig.invPi Trig.halfPi xs b
    component s (UInt64.ofNat 0) = pair xs (b + 2) ∧
      component s (UInt64.ofNat 1) = pair xs (b + 4) ∧
      component s (UInt64.ofNat 2) = pair xs (b + 6) ∧
      component s (UInt64.ofNat 3) = pair xs (b + 8) ∧
      component s (UInt64.ofNat 4) = pair xs (b + 10) ∧
      component s (UInt64.ofNat 5) = pair xs (b + 12) := by
  intro s
  have e : s = ⟨pair xs (b + 2), pair xs (b + 4), pair xs (b + 6), pair xs (b + 8),
      pair xs (b + 10), pair xs (b + 12)⟩ := by
    show stateOf Trig.invPi Trig.halfPi xs b = _
    unfold stateOf
    rw [if_pos hf]
  rw [e]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem component_eq (s : State) :
    component s (UInt64.ofNat 0) = s.x ∧ component s (UInt64.ofNat 1) = s.y ∧
      component s (UInt64.ofNat 2) = s.z ∧ component s (UInt64.ofNat 3) = s.u ∧
      component s (UInt64.ofNat 4) = s.v ∧ component s (UInt64.ofNat 5) = s.w :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The state of a TEME receiver, as the TEME branch of `stateOf` computes it. -/
def temeState (xs : Array Float) (b : UInt64) : State :=
  let d := (rd xs 4).toUInt64
  let t := pair xs b
  let th := Frames.angleWith Trig.invPi Trig.halfPi d t
  let w := spinI Trig.invPi Trig.halfPi Trig.invPi Trig.halfPi (ofInt d.toInt64) t
  let p := Frames.toEarthI Trig.invPi Trig.halfPi Trig.invPi Trig.halfPi th (pair xs 5)
    (pair xs 7) (pair xs (b + 2)) (pair xs (b + 4)) (pair xs (b + 6))
  let v := earthVelI Trig.invPi Trig.halfPi Trig.invPi Trig.halfPi th w (pair xs 5) (pair xs 7)
    (pair xs (b + 2)) (pair xs (b + 4)) (pair xs (b + 6)) (pair xs (b + 8)) (pair xs (b + 10))
    (pair xs (b + 12))
  ⟨p.1, p.2.1, p.2.2, v.1, v.2.1, v.2.2⟩

theorem stateOf_teme {xs : Array Float} (hf : ¬ (rd xs 1 == 0.0) = true) (b : UInt64) :
    stateOf Trig.invPi Trig.halfPi xs b = temeState xs b := by
  unfold stateOf
  exact if_neg hf

theorem make_ok {lo hi : Float} (h1 : Finite lo.toBits) (h2 : Finite hi.toBits) (h : lo ≤ hi) :
    (make lo hi).status = 0 := by
  unfold make
  simp [(finite_iff lo).mpr h1, (finite_iff hi).mpr h2, h]

/-- The index of entry `c` of receiver `i`. -/
theorem rx_index {xs : Array Float} (F : Facts xs) {i : ℕ} (hi : i < (nOf xs).toNat)
    {c : UInt64} (hc : c.toNat ≤ 13) :
    (20 + 14 * UInt64.ofNat i + c).toNat = 20 + 14 * i + c.toNat := by
  have := F.n16
  simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat', UInt64.reduceToNat]
  omega

/-- The interval of entries `c` and `c + 1` of receiver `i` is accepted when they are ordered. -/
theorem rx_pair {xs : Array Float} (F : Facts xs) {i : ℕ} (hi : i < (nOf xs).toNat)
    {c : UInt64} (hc : c.toNat ≤ 12)
    (hle : rd xs (20 + 14 * UInt64.ofNat i + c) ≤ rd xs (20 + 14 * UInt64.ofNat i + c + 1)) :
    (pair xs (20 + 14 * UInt64.ofNat i + c)).status = 0 := by
  have s := F.size
  have h1 : (c + 1).toNat = c.toNat + 1 := by
    rw [UInt64.toNat_add]
    exact Nat.mod_eq_of_lt (by have : (1 : UInt64).toNat = 1 := rfl; rw [this]; omega)
  have f0 := F.entry (q := 20 + 14 * UInt64.ofNat i + c) (by rw [rx_index F hi (by omega)]; omega)
  have f1 := F.entry (q := 20 + 14 * UInt64.ofNat i + (c + 1))
    (by rw [rx_index F hi (by omega), h1]; omega)
  rw [← UInt64.add_assoc] at f1
  exact make_ok f0 f1 hle

theorem receivers_sound {xs : Array Float} (F : Facts xs) {P : Params} (hP : Admissible xs P) :
    RxSound (rxOf xs) P (nOf xs).toNat := by
  intro i hi
  have g := fun c (hc : c < 6) => receivers_get (xs := xs) F.n16 hi hc
  have g0 := g 0 (by norm_num)
  rw [Nat.add_zero] at g0
  have hA := hP.2
  by_cases hf : (rd xs 1 == 0.0) = true
  · rw [if_pos hf] at hA
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hA i hi
    obtain ⟨c0, c1, c2, c3, c4, c5⟩ := component_stateOf hf (20 + 14 * UInt64.ofNat i)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · show Encloses (receivers Trig.invPi Trig.halfPi xs (nOf xs))[6 * i]! _
      rw [g0, c0]; exact encloses_make a1.1 a1.2
    · rw [rxOf, g 1 (by norm_num), c1]; exact encloses_make a2.1 a2.2
    · rw [rxOf, g 2 (by norm_num), c2]; exact encloses_make a3.1 a3.2
    · rw [rxOf, g 3 (by norm_num), c3]; exact encloses_make a4.1 a4.2
    · rw [rxOf, g 4 (by norm_num), c4]; exact encloses_make a5.1 a5.2
    · rw [rxOf, g 5 (by norm_num), c5]; exact encloses_make a6.1 a6.2
  · rw [if_neg hf] at hA
    obtain ⟨xp, yp, hxp, hyp, hA⟩ := hA
    obtain ⟨t, r, v, ht, ⟨a1, a2, a3, a4, a5, a6⟩, hs, hu⟩ := hA i hi
    have ok := F.rx i hi
    simp only [receiverOk, ordered, Bool.and_eq_true, decide_eq_true_eq] at ok
    have hpt : (pair xs (20 + 14 * UInt64.ofNat i)).status = 0 := by
      have := rx_pair F hi (c := 0) (by decide) (by simpa using ok.1.1.1.1.1.1)
      simpa using this
    generalize hb : (20 : UInt64) + 14 * UInt64.ofNat i = b at ht a1 a2 a3 a4 a5 a6 g g0 hpt ⊢
    obtain ⟨c0, c1, c2, c3, c4, c5⟩ :=
      component_eq (stateOf Trig.invPi Trig.halfPi xs b)
    have e := stateOf_teme hf b
    obtain ⟨k, hk⟩ := Frames.angleWith_encloses (s := pair xs b) F.day
    have hθ := hk t (Frames.contains_make hpt ht)
    have et : Encloses (pair xs b) t := encloses_make ht.1 ht.2
    have hw := spin.encloses (powLog := Trig.invPi) (powExp := Trig.halfPi)
      (Frames.encloses_day F.day) et
    rw [spin_eq] at hw
    have ex : Encloses (pair xs 5) xp := encloses_make hxp.1 hxp.2
    have ey : Encloses (pair xs 7) yp := encloses_make hyp.1 hyp.2
    have e1 : Encloses (pair xs (b + 2)) r.1 := encloses_make a1.1 a1.2
    have e2 : Encloses (pair xs (b + 4)) r.2.1 := encloses_make a2.1 a2.2
    have e3 : Encloses (pair xs (b + 6)) r.2.2 := encloses_make a3.1 a3.2
    have e4 : Encloses (pair xs (b + 8)) v.1 := encloses_make a4.1 a4.2
    have e5 : Encloses (pair xs (b + 10)) v.2.1 := encloses_make a5.1 a5.2
    have e6 : Encloses (pair xs (b + 12)) v.2.2 := encloses_make a6.1 a6.2
    have hp := Frames.toEarth.encloses (powLog := Trig.invPi) (powExp := Trig.halfPi) hθ ex ey
      e1 e2 e3
    rw [Frames.toEarth_periodic, Frames.toEarth_eq] at hp
    have hv := earthVel.encloses (powLog := Trig.invPi) (powExp := Trig.halfPi) hθ hw ex ey
      e1 e2 e3 e4 e5 e6
    rw [earthVel_eq] at hv
    rw [hs, hu]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · show Encloses (receivers Trig.invPi Trig.halfPi xs (nOf xs))[6 * i]! _
      rw [g0, c0, e]; simp only [temeState]; exact hp.1
    · rw [rxOf, g 1 (by norm_num), c1, e]; simp only [temeState]; exact hp.2.1
    · rw [rxOf, g 2 (by norm_num), c2, e]; simp only [temeState]; exact hp.2.2
    · rw [rxOf, g 3 (by norm_num), c3, e]; simp only [temeState]; exact hv.1
    · rw [rxOf, g 4 (by norm_num), c4, e]; simp only [temeState]; exact hv.2.1
    · rw [rxOf, g 5 (by norm_num), c5, e]; simp only [temeState]; exact hv.2.2

/-! ### The box test -/

theorem six_index {I : UInt64} (hI : I.toNat < 16) (c : ℕ) (hc : c < 6) :
    (6 * I + UInt64.ofNat c).toNat = 6 * I.toNat + c := by
  simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat', UInt64.reduceToNat]
  omega

theorem residual_encloses {xs : Array Float} {rx : Array Interval} {fq : Interval} {P : Params}
    {n : ℕ} (hn : n ≤ 16) (hrx : RxSound rx P n) (hf : Encloses fq P.f) {q : UInt64}
    (hi : (rd xs (q + 1)).toUInt64.toNat < n) (hj : (rd xs (q + 2)).toUInt64.toNat < n)
    {px py pz : Interval} {x : V3} (h1 : Encloses px x.1) (h2 : Encloses py x.2.1)
    (h3 : Encloses pz x.2.2) :
    Encloses (residual Trig.invPi Trig.halfPi rx fq xs q px py pz)
      (predicted xs P q x - val (rd xs (q + 3))) := by
  unfold residual predicted
  dsimp only
  generalize hI : (rd xs (q + 1)).toUInt64 = I at hi ⊢
  generalize hJ : (rd xs (q + 2)).toUInt64 = J at hj ⊢
  have i0 : (6 * I).toNat = 6 * I.toNat := by
    rw [UInt64.toNat_mul]; simp only [UInt64.reduceToNat]; omega
  have j0 : (6 * J).toNat = 6 * J.toNat := by
    rw [UInt64.toNat_mul]; simp only [UInt64.reduceToNat]; omega
  have i1 := six_index (I := I) (by omega) 1 (by norm_num)
  have i2 := six_index (I := I) (by omega) 2 (by norm_num)
  have i3 := six_index (I := I) (by omega) 3 (by norm_num)
  have i4 := six_index (I := I) (by omega) 4 (by norm_num)
  have i5 := six_index (I := I) (by omega) 5 (by norm_num)
  have j1 := six_index (I := J) (by omega) 1 (by norm_num)
  have j2 := six_index (I := J) (by omega) 2 (by norm_num)
  have j3 := six_index (I := J) (by omega) 3 (by norm_num)
  have j4 := six_index (I := J) (by omega) 4 (by norm_num)
  have j5 := six_index (I := J) (by omega) 5 (by norm_num)
  simp only [UInt64.reduceOfNat] at i1 i2 i3 i4 i5 j1 j2 j3 j4 j5
  rw [i0, i1, i2, i3, i4, i5, j0, j1, j2, j3, j4, j5]
  obtain ⟨s1, s2, s3, u1, u2, u3⟩ := hrx _ hi
  obtain ⟨t1, t2, t3, v1, v2, v3⟩ := hrx _ hj
  split_ifs
  · have e := tdoaRes.encloses (powLog := Trig.invPi) (powExp := Trig.halfPi) s1 s2 s3 t1 t2 t3
      h1 h2 h3 (encloses_point (rd xs (q + 3)))
    rwa [tdoaRes_eq] at e
  · have e := fdoaRes.encloses (powLog := Trig.invPi) (powExp := Trig.halfPi) hf s1 s2 s3 u1 u2
      u3 t1 t2 t3 v1 v2 v3 h1 h2 h3 (encloses_point (rd xs (q + 3)))
    rwa [fdoaRes_eq] at e

/-- What the measurements' loop of a box test concludes from enclosures `ρ k` of the residuals. -/
theorem verdict_spec {rx : Array Interval} {fq : Interval} {xs : Array Float} {base m : UInt64}
    {px py pz : Interval} {ρ : ℕ → ℝ}
    (hres : ∀ k < m.toNat, Encloses (residual Trig.invPi Trig.halfPi rx fq xs
      (base + 5 * UInt64.ofNat k) px py pz) (ρ k))
    (heps : ∀ k < m.toNat, Finite (rd xs (base + 5 * UInt64.ofNat k + 4)).toBits) :
    let v := LeanExe.loop m (⟨false, true⟩ : Verdict) fun k v =>
      verdictStep Trig.invPi Trig.halfPi rx fq xs base px py pz k v
    (v.out = true → ∃ k < m.toNat, val (rd xs (base + 5 * UInt64.ofNat k + 4)) < |ρ k|) ∧
      (v.out = false → v.inner = true →
        ∀ k < m.toNat, |ρ k| ≤ val (rd xs (base + 5 * UInt64.ofNat k + 4))) := by
  intro v
  refine loop_induction (n := m) (init := (⟨false, true⟩ : Verdict))
    (f := fun k v => verdictStep Trig.invPi Trig.halfPi rx fq xs base px py pz k v)
    (fun k v => (v.out = true →
        ∃ k' < k, val (rd xs (base + 5 * UInt64.ofNat k' + 4)) < |ρ k'|) ∧
      (v.out = false → v.inner = true →
        ∀ k' < k, |ρ k'| ≤ val (rd xs (base + 5 * UInt64.ofNat k' + 4))))
    ⟨fun h => absurd h (by decide), fun _ _ k' hk' => absurd hk' (Nat.not_lt_zero _)⟩ ?_
  intro k w hk ⟨ho, hin⟩
  unfold verdictStep
  by_cases hw : w.out = true
  · rw [if_pos hw]
    refine ⟨fun _ => ?_, fun h => absurd (hw.symm.trans h) (by decide)⟩
    obtain ⟨k', hk', e⟩ := ho hw
    exact ⟨k', by omega, e⟩
  · rw [if_neg hw]
    dsimp only
    have he := hres k hk
    have fe := heps k hk
    generalize residual Trig.invPi Trig.halfPi rx fq xs (base + 5 * UInt64.ofNat k) px py pz = e
      at he ⊢
    have hw' : w.out = false := by simpa using hw
    by_cases hs : e.status = 0
    · obtain ⟨-, fl, fh, l, u⟩ := he hs
      rw [if_pos (by simp [hs])]
      by_cases hx : (decide (rd xs (base + 5 * UInt64.ofNat k + 4) < e.lo) ||
          decide (e.hi < -rd xs (base + 5 * UInt64.ofNat k + 4))) = true
      · rw [if_pos hx]
        refine ⟨fun _ => ⟨k, by omega, ?_⟩, fun h => absurd h (by decide)⟩
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hx
        rcases hx with hx | hx
        · have := (lt_iff_value fe fl).mp hx
          exact lt_of_lt_of_le (by linarith) (le_abs_self _)
        · obtain ⟨fn, vn⟩ := neg_value fe
          have := (lt_iff_value fh fn).mp hx
          rw [vn] at this
          exact lt_of_lt_of_le (by linarith) (neg_le_abs _)
      · rw [if_neg hx]
        refine ⟨fun h => absurd (show false = true from h) (by decide), fun _ hi k' hk' => ?_⟩
        dsimp only at hi
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hi
        obtain ⟨⟨hprev, hlo⟩, hhi⟩ := hi
        by_cases hkk : k' < k
        · exact hin hw' hprev k' hkk
        · have : k' = k := by omega
          subst this
          obtain ⟨fn, vn⟩ := neg_value fe
          have a := (le_iff_value fn fl).mp hlo
          have b := (le_iff_value fh fe).mp hhi
          rw [vn] at a
          exact abs_le.mpr ⟨by linarith, by linarith⟩
    · rw [if_neg (by simp [hs])]
      exact ⟨fun h => absurd h (by decide), fun _ h => absurd h (by decide)⟩

/-- The box test of a valid input: a box whose test gives 0 holds no position that fits the
measurements for an admissible parameter, and every position of a box whose test gives 2 fits
them for every admissible parameter. -/
theorem boxTest_spec {xs : Array Float} (F : Facts xs) {P : Params} (hP : Admissible xs P)
    {b : Box} {φ lam h : ℝ} (hb : InBox b φ lam h) :
    (boxTest Trig.invPi Trig.halfPi (rxOf xs) (pair xs 9) xs (baseOf xs) (mOf xs)
        b = 0 → ¬ Fits xs P (Frames.Model.position φ lam h)) ∧
      (boxTest Trig.invPi Trig.halfPi (rxOf xs) (pair xs 9) xs (baseOf xs)
        (mOf xs) b = 2 → Fits xs P (Frames.Model.position φ lam h)) := by
  have hrx := receivers_sound F hP
  have hf : Encloses (pair xs 9) P.f := encloses_make hP.1.1 hP.1.2
  have hp := Frames.cartesian.encloses (powLog := Trig.invPi) (powExp := Trig.halfPi)
    (encloses_make hb.1 hb.2.1) (encloses_make hb.2.2.1 hb.2.2.2.1)
    (encloses_make hb.2.2.2.2.1 hb.2.2.2.2.2)
  rw [Frames.cartesian_eq] at hp
  unfold boxTest
  dsimp only
  generalize Frames.cartesianI Trig.invPi Trig.halfPi Trig.invPi Trig.halfPi (make b.plo b.phi)
    (make b.llo b.lhi) (make b.hlo b.hhi) = p at hp ⊢
  have V := verdict_spec (rx := rxOf xs) (fq := pair xs 9) (xs := xs)
    (base := baseOf xs) (m := mOf xs) (px := p.1) (py := p.2.1) (pz := p.2.2)
    (ρ := fun k => predicted xs P (baseOf xs + 5 * UInt64.ofNat k)
      (Frames.Model.position φ lam h) - val (rd xs (baseOf xs + 5 * UInt64.ofNat k + 3)))
    (fun k hk => residual_encloses F.n16 hrx hf (meas_facts F hk).1 (meas_facts F hk).2.1
      hp.1 hp.2.1 hp.2.2)
    (fun k hk => (meas_facts F hk).2.2)
  generalize LeanExe.loop (mOf xs) (⟨false, true⟩ : Verdict) (fun k v =>
    verdictStep Trig.invPi Trig.halfPi (rxOf xs) (pair xs 9) xs (baseOf xs) p.1
      p.2.1 p.2.2 k v) = v at V ⊢
  obtain ⟨Vo, Vi⟩ := V
  refine ⟨fun h0 hF => ?_, fun h2 => ?_⟩
  · by_cases ho : v.out = true
    · obtain ⟨k, hk, e⟩ := Vo ho
      exact absurd (hF k hk) (not_le.mpr e)
    · rw [if_neg ho] at h0
      split_ifs at h0 <;> exact absurd h0 (by decide)
  · by_cases ho : v.out = true
    · rw [if_pos ho] at h2; exact absurd h2 (by decide)
    · rw [if_neg ho] at h2
      by_cases hi : v.inner = true
      · exact Vi (by simpa using ho) hi
      · rw [if_neg hi] at h2; exact absurd h2 (by decide)

theorem test_sound {xs : Array Float} (F : Facts xs) :
    TestSound (rxOf xs) (pair xs 9) xs (baseOf xs) (mOf xs) (Consistent xs)
      (Inner xs) where
  zero _ ht _ _ _ hb := fun ⟨_, hP, hF⟩ => (boxTest_spec F hP hb).1 ht hF
  two _ ht _ hP _ _ _ hb := (boxTest_spec F hP hb).2 ht
  ends _ _ hg := fun P hP φ lam h hb => hg P hP φ lam h hb

/-! ### The output -/

/-- The search of an input. -/
def searchOf (xs : Array Float) : Search :=
  search Trig.invPi Trig.halfPi (rxOf xs) (pair xs 9) xs (baseOf xs) (mOf xs)
    (rd xs 17) (regionOf xs) (rd xs 18).toUInt64 (rd xs 19).toUInt64

/-- The boxes that the final pass keeps. -/
def finalOf (xs : Array Float) : Array Box :=
  finalBoxes Trig.invPi Trig.halfPi (rxOf xs) (pair xs 9) xs (baseOf xs) (mOf xs)
    (searchOf xs).boxes

theorem locate_eq {xs : Array Float} (hv : valid xs = true) :
    locate xs = if allAccepted (rxOf xs) then outputOf (searchOf xs) (finalOf xs)
      else #[4.0, 0.0, 0.0, 0.0] := by
  simp only [locate, locateWith, hv, ite_true]
  rfl

theorem outputOf_get (s : Search) (bs : Array Box) (h : bs.size ≤ 65536) :
    (outputOf s bs).size = 4 + 7 * bs.size ∧ (outputOf s bs)[0]! = s.status.toFloat ∧
      (outputOf s bs)[3]! = s.levels.toFloat ∧
      ∀ j < bs.size, (outputOf s bs)[4 + 7 * j]! = bs[j]!.plo ∧
        (outputOf s bs)[5 + 7 * j]! = bs[j]!.phi ∧ (outputOf s bs)[6 + 7 * j]! = bs[j]!.llo ∧
        (outputOf s bs)[7 + 7 * j]! = bs[j]!.lhi ∧ (outputOf s bs)[8 + 7 * j]! = bs[j]!.hlo ∧
        (outputOf s bs)[9 + 7 * j]! = bs[j]!.hhi ∧
        (outputOf s bs)[10 + 7 * j]! = (if bs[j]!.mark == 2 then 1.0 else 0.0) := by
  unfold outputOf
  generalize hh : (#[s.status.toFloat, bs.size.toUInt64.toFloat, (s.tests + fresh s.boxes).toFloat,
    s.levels.toFloat] : Array Float) = head
  have hs : head.size = 4 := by rw [← hh]; rfl
  have sz := sevens_size bs h
  refine ⟨by simp [hs, sz], by rw [append_get_left _ _ 0 (by omega), ← hh]; rfl,
    by rw [append_get_left _ _ 3 (by omega), ← hh]; rfl, fun j hj => ?_⟩
  obtain ⟨g0, g1, g2, g3, g4, g5, g6⟩ := sevens_box bs h hj
  have r : ∀ c, c < 7 →
      (head ++ sevens bs)[head.size + (7 * j + c)]! = (sevens bs)[7 * j + c]! :=
    fun c hc => append_get_right _ _ _ (by omega)
  rw [hs] at r
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := r 0 (by norm_num); rw [Nat.add_zero] at this; rw [← g0, ← this]
  · rw [← g1, ← r 1 (by norm_num)]; congr 1; omega
  · rw [← g2, ← r 2 (by norm_num)]; congr 1; omega
  · rw [← g3, ← r 3 (by norm_num)]; congr 1; omega
  · rw [← g4, ← r 4 (by norm_num)]; congr 1; omega
  · rw [← g5, ← r 5 (by norm_num)]; congr 1; omega
  · rw [← g6, ← r 6 (by norm_num)]; congr 1; omega

theorem region_finite {xs : Array Float} (F : Facts xs) : FiniteBox (regionOf xs) := by
  have e : ∀ q : UInt64, q.toNat ≤ 16 → Finite (rd xs q).toBits :=
    fun q hq => F.entry (by omega)
  exact ⟨e 11 (by decide), e 12 (by decide), e 13 (by decide), e 14 (by decide), e 15 (by decide),
    e 16 (by decide)⟩

/-- The search, its final boxes, and their facts, for a valid input. -/
theorem search_facts {xs : Array Float} (F : Facts xs) :
    Inv (regionOf xs) (Consistent xs) (Inner xs) (rd xs 17) (rd xs 19).toUInt64.toNat
        (searchOf xs) ∧
      (finalOf xs).size ≤ (searchOf xs).boxes.size ∧
      (∀ j < (finalOf xs).size, KeepF (regionOf xs) (Inner xs) (rd xs 17)
        (∀ i < (searchOf xs).boxes.size, (searchOf xs).boxes[i]!.mark ≠ 0) (finalOf xs)[j]!) ∧
      ∀ φ lam h, InRegion xs φ lam h → Consistent xs φ lam h →
        ∃ j < (finalOf xs).size, InBox (finalOf xs)[j]! φ lam h := by
  have T := test_sound F
  have I : Inv (regionOf xs) (Consistent xs) (Inner xs) (rd xs 17) (rd xs 19).toUInt64.toNat
      (searchOf xs) := search_inv T F.cap1 F.cap (region_finite F) rfl
  obtain ⟨fsz, fkeep, fcov⟩ := finalBoxes_spec (R := regionOf xs) (r := rd xs 17) T
    (by have := I.size; have := F.cap; omega) I.keep
  exact ⟨I, fsz, fkeep, fun φ lam h hR hc => fcov φ lam h (I.cover φ lam h hR hc) hc⟩

/-- Box `j` of the output holds the same points as final box `j`. -/
theorem out_box {xs : Array Float} (F : Facts xs) {j : ℕ} (hj : j < (finalOf xs).size) :
    let out := outputOf (searchOf xs) (finalOf xs)
    (∀ φ lam h, InOut out j φ lam h ↔ InBox (finalOf xs)[j]! φ lam h) ∧
      boxAt out j = { (finalOf xs)[j]! with
        mark := if out[10 + 7 * j]! == 1.0 then 2 else 1 } ∧
      out[10 + 7 * j]! = (if (finalOf xs)[j]!.mark == 2 then 1.0 else 0.0) := by
  intro out
  obtain ⟨-, fsz, -, -⟩ := search_facts F
  have I := (search_facts F).1
  have hb : (finalOf xs).size ≤ 65536 := by have := I.size; have := F.cap; omega
  obtain ⟨osz, -, -, oget⟩ := outputOf_get (searchOf xs) (finalOf xs) hb
  obtain ⟨g0, g1, g2, g3, g4, g5, g6⟩ := oget j hj
  refine ⟨fun φ lam h => ?_, ?_, g6⟩
  · simp only [InOut, InBox, out, g0, g1, g2, g3, g4, g5, osz]
    constructor
    · intro e; exact e.2
    · intro e; exact ⟨by omega, e⟩
  · simp only [boxAt, out, g0, g1, g2, g3, g4, g5]

theorem within_mark (R b : Box) (k : UInt64) : Within R { b with mark := k } ↔ Within R b :=
  Iff.rfl

theorem label_one {b : Box} (h : (if b.mark == 2 then (1.0 : Float) else 0.0) = 1.0) :
    b.mark = 2 := by
  by_cases hm : b.mark = 2
  · exact hm
  · simp only [beq_iff_eq, hm, ite_false] at h
    exact absurd (congrArg Float.toBits h) (by decide +kernel)

/-! ### The theorems -/

/-- **G1.**  For a valid input whose status is not 4, every triple of the region whose position
fits the measurements for some admissible parameter lies in a returned box. -/
theorem locate_cover {xs : Array Float} (hv : valid xs = true)
    (h4 : ¬ HasStatus (locate xs) 4) {φ lam h : ℝ} (hR : InRegion xs φ lam h)
    (hc : Consistent xs φ lam h) : Returned (locate xs) φ lam h := by
  have F := valid_facts hv
  rw [locate_eq hv] at h4 ⊢
  split_ifs at h4 ⊢ with ha
  · obtain ⟨-, -, -, cov⟩ := search_facts F
    obtain ⟨j, hj, hm⟩ := cov φ lam h hR hc
    exact ⟨j, ((out_box F hj).1 φ lam h).mpr hm⟩
  · exact absurd (show HasStatus #[4.0, 0.0, 0.0, 0.0] 4 by unfold HasStatus; decide +kernel) h4

/-- **G2.**  For a valid input, every point of a box labeled 1 fits the measurements for every
admissible parameter. -/
theorem locate_inner {xs : Array Float} (hv : valid xs = true) {j : ℕ}
    (hj : 10 + 7 * j < (locate xs).size) (hl : (locate xs)[10 + 7 * j]! = 1.0) :
    ∀ P, Admissible xs P → ∀ φ lam h, InOut (locate xs) j φ lam h →
      Fits xs P (Frames.Model.position φ lam h) := by
  have F := valid_facts hv
  rw [locate_eq hv] at hj hl ⊢
  split_ifs at hj hl ⊢ with ha
  · obtain ⟨-, fsz, fkeep, -⟩ := search_facts F
    have hb : (finalOf xs).size ≤ 65536 := by
      have := (search_facts F).1.size; have := F.cap; omega
    obtain ⟨osz, -, -, -⟩ := outputOf_get (searchOf xs) (finalOf xs) hb
    have hj' : j < (finalOf xs).size := by omega
    obtain ⟨hin, -, h6⟩ := out_box F hj'
    rw [h6] at hl
    have K := fkeep j hj'
    intro P hP φ lam h hm
    exact K.good (label_one hl) P hP φ lam h ((hin φ lam h).mp hm)
  · simp at hj; omega

/-- **G3.**  For a valid input, every returned box lies in the region, and there are at most `C`
boxes. -/
theorem locate_within {xs : Array Float} (hv : valid xs = true) :
    (locate xs).size ≤ 4 + 7 * (rd xs 19).toUInt64.toNat ∧
      ∀ j, 10 + 7 * j < (locate xs).size → Within (regionOf xs) (boxAt (locate xs) j) := by
  have F := valid_facts hv
  rw [locate_eq hv]
  split_ifs with ha
  · obtain ⟨I, fsz, fkeep, -⟩ := search_facts F
    have hb : (finalOf xs).size ≤ 65536 := by have := I.size; have := F.cap; omega
    obtain ⟨osz, -, -, -⟩ := outputOf_get (searchOf xs) (finalOf xs) hb
    refine ⟨by rw [osz]; have := I.size; omega, fun j hj => ?_⟩
    have hj' : j < (finalOf xs).size := by omega
    obtain ⟨-, e, -⟩ := out_box F hj'
    rw [e]
    exact (within_mark _ _ _).mpr (fkeep j hj').within
  · exact ⟨by simp, fun j hj => by simp at hj; omega⟩

/-! ### Statuses -/

theorem allAccepted_of {ys : Array Interval} (h64 : ys.size < 2 ^ 64)
    (h : ∀ j < ys.size, ys[j]!.status = 0) : allAccepted ys = true := by
  unfold allAccepted
  have hn := LeanExe.Dialect.size_toUInt64 ys h64
  have key := loop_induction (n := ys.size.toUInt64) (init := true)
    (f := fun i ok => ok && ys[i.toNat]!.status == 0) (fun k ok => k ≤ ys.size → ok = true)
    (fun _ => rfl)
    (fun k ok hk ih hle => by
      rw [hn] at hk
      have hk' : (UInt64.ofNat k).toNat = k := by rw [UInt64.toNat_ofNat']; omega
      simp only [hk', ih (by omega), h k hk, beq_self_eq_true, Bool.and_self])
  rw [hn] at key
  exact key le_rfl

/-- The receivers' intervals of a valid input with Earth-fixed receivers are accepted. -/
theorem receivers_accepted {xs : Array Float} (F : Facts xs) (hf : (rd xs 1 == 0.0) = true) :
    allAccepted (rxOf xs) = true := by
  have n16 := F.n16
  have hsz : (rxOf xs).size = 6 * (nOf xs).toNat := by
    unfold rxOf receivers
    rw [build_size, UInt64.toNat_mul]
    simp only [UInt64.reduceToNat]
    omega
  refine allAccepted_of (by omega) fun q hq => ?_
  rw [hsz] at hq
  have hi : q / 6 < (nOf xs).toNat := by omega
  have hc : q % 6 < 6 := Nat.mod_lt _ (by norm_num)
  have hq' : q = 6 * (q / 6) + q % 6 := (Nat.div_add_mod q 6).symm
  rw [hq', rxOf, receivers_get n16 hi hc]
  have ok := F.rx (q / 6) hi
  simp only [receiverOk, ordered, Bool.and_eq_true, decide_eq_true_eq] at ok
  obtain ⟨⟨⟨⟨⟨⟨-, o1⟩, o2⟩, o3⟩, o4⟩, o5⟩, o6⟩ := ok
  obtain ⟨c0, c1, c2, c3, c4, c5⟩ := component_stateOf hf (20 + 14 * UInt64.ofNat (q / 6))
  interval_cases h : q % 6
  · rw [c0]; exact rx_pair F hi (c := 2) (by decide) o1
  · rw [c1]; exact rx_pair F hi (c := 4) (by decide) o2
  · rw [c2]; exact rx_pair F hi (c := 6) (by decide) o3
  · rw [c3]; exact rx_pair F hi (c := 8) (by decide) o4
  · rw [c4]; exact rx_pair F hi (c := 10) (by decide) o5
  · rw [c5]; exact rx_pair F hi (c := 12) (by decide) o6

theorem status_bits (a b : UInt64) (ha : a ≤ 4) (hb : b ≤ 4)
    (h : a.toFloat.toBits = b.toFloat.toBits) :
    a = b := by
  have ha' : a.toNat ≤ 4 := UInt64.le_iff_toNat_le.mp ha
  have hb' : b.toNat ≤ 4 := UInt64.le_iff_toNat_le.mp hb
  obtain ⟨x, rfl⟩ : ∃ x : Fin 5, a = UInt64.ofNat x := ⟨⟨a.toNat, by omega⟩, by simp⟩
  obtain ⟨y, rfl⟩ : ∃ y : Fin 5, b = UInt64.ofNat y := ⟨⟨b.toNat, by omega⟩, by simp⟩
  revert h
  revert x y
  decide +kernel

/-- **G4.**  For a valid input, the status is 0, 1, 2, or 4, and 4 only for the TEME frame.  At
status 0 at most `N` levels are completed, and every box labeled 0 is not split: its size is at
most `r`, or its longest side has no binary64 middle strictly inside.  At status 1 fewer than `N`
levels are completed, and at status 2 all `N`. -/
theorem locate_status {xs : Array Float} (hv : valid xs = true) :
    let out := locate xs
    let N := (rd xs 18).toUInt64
    (HasStatus out 0 ∨ HasStatus out 1 ∨ HasStatus out 2 ∨ HasStatus out 4) ∧
      ((rd xs 1 == 0.0) = true → ¬ HasStatus out 4) ∧
      (HasStatus out 0 → (∃ L ≤ N, out[3]! = L.toFloat) ∧
        ∀ j, 10 + 7 * j < out.size → out[10 + 7 * j]! ≠ 1.0 →
          splits Trig.invPi Trig.halfPi (rd xs 17) (boxAt out j) = false) ∧
      (HasStatus out 1 → ∃ L < N, out[3]! = L.toFloat) ∧
      (HasStatus out 2 → out[3]! = N.toFloat) := by
  intro out N
  have F := valid_facts hv
  by_cases ha : allAccepted (rxOf xs) = true
  swap
  · have ho : out = #[4.0, 0.0, 0.0, 0.0] := by
      show locate xs = _
      rw [locate_eq hv, if_neg ha]
    have h4 : HasStatus out 4 := by rw [ho]; unfold HasStatus; decide +kernel
    unfold HasStatus at h4
    refine ⟨Or.inr (Or.inr (Or.inr h4)), fun hf _ => ha (receivers_accepted F hf),
      fun h0 => ?_, fun h1 => ?_, fun h2 => ?_⟩
    · unfold HasStatus at h0; exact absurd (h4.symm.trans h0) (by decide +kernel)
    · unfold HasStatus at h1; exact absurd (h4.symm.trans h1) (by decide +kernel)
    · unfold HasStatus at h2; exact absurd (h4.symm.trans h2) (by decide +kernel)
  have ho : out = outputOf (searchOf xs) (finalOf xs) := by
    show locate xs = _
    rw [locate_eq hv, if_pos ha]
  obtain ⟨I, fsz, fkeep, -⟩ := search_facts F
  have hb : (finalOf xs).size ≤ 65536 := by have := I.size; have := F.cap; omega
  obtain ⟨osz, o0, o3, oget⟩ := outputOf_get (searchOf xs) (finalOf xs) hb
  have st : ((searchOf xs).status = 2 ∧ (searchOf xs).levels = N) ∨
      ((searchOf xs).status = 0 ∧ (searchOf xs).levels ≤ N ∧
        fresh (searchOf xs).boxes = 0) ∨
      ((searchOf xs).status = 1 ∧ (searchOf xs).levels < N) :=
    search_status (regionOf xs) (rd xs 19).toUInt64 (rd xs 18).toUInt64
  have hs : HasStatus out (searchOf xs).status := by unfold HasStatus; rw [ho, o0]
  have small : (searchOf xs).status ≤ 2 := by
    rcases st with ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ <;> rw [e] <;> decide
  have small4 : (searchOf xs).status ≤ 4 := by
    rcases st with ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ <;> rw [e] <;> decide
  have eq : ∀ k : UInt64, k ≤ 4 → HasStatus out k → (searchOf xs).status = k :=
    fun k hk h => by
      unfold HasStatus at hs h
      exact status_bits _ _ small4 hk (hs.symm.trans h)
  refine ⟨?_, fun _ h4 => ?_, fun h0 => ?_, fun h1 => ?_, fun h2 => ?_⟩
  · rcases st with ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ <;> rw [e] at hs
    · exact Or.inr (Or.inr (Or.inl hs))
    · exact Or.inl hs
    · exact Or.inr (Or.inl hs)
  · have := eq 4 (by decide) h4
    rw [this] at small
    exact absurd small (by decide)
  · have e0 := eq 0 (by decide) h0
    have h3 : out[3]! = (searchOf xs).levels.toFloat := by rw [ho, o3]
    rcases st with ⟨e, -⟩ | ⟨-, hl, hf⟩ | ⟨e, -⟩
    · rw [e] at e0; exact absurd e0 (by decide)
    · refine ⟨⟨_, hl, h3⟩, fun j hj hne => ?_⟩
      have hsz : (searchOf xs).boxes.size < 2 ^ 64 := by have := I.size; have := F.cap; omega
      have U := fresh_zero hsz hf
      rw [ho, osz] at hj
      have hj' : j < (finalOf xs).size := by omega
      obtain ⟨-, eb, h6⟩ := out_box F hj'
      have K := fkeep j hj'
      have hm1 : (finalOf xs)[j]!.mark = 1 := by
        rcases K.mark with e | e
        · exact e
        · exfalso
          apply hne
          rw [ho, h6, e]
          rfl
      rw [ho, eb, splits_mark]
      exact K.unsplit U hm1
    · rw [e] at e0; exact absurd e0 (by decide)
  · have e1 := eq 1 (by decide) h1
    rcases st with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, hl⟩
    · rw [e] at e1; exact absurd e1 (by decide)
    · rw [e] at e1; exact absurd e1 (by decide)
    · exact ⟨_, hl, by rw [ho, o3]⟩
  · have e2 := eq 2 (by decide) h2
    rcases st with ⟨-, hl⟩ | ⟨e, -⟩ | ⟨e, -⟩
    · rw [ho, o3, hl]
    · rw [e] at e2; exact absurd e2 (by decide)
    · rw [e] at e2; exact absurd e2 (by decide)

/-- **G5.**  The status is 3 exactly for the inputs that break a requirement of the interface. -/
theorem locate_invalid (xs : Array Float) : HasStatus (locate xs) 3 ↔ valid xs = false := by
  by_cases hv : valid xs = true
  · simp only [hv, Bool.true_eq_false, iff_false]
    intro h3
    obtain ⟨hst, -⟩ := locate_status hv
    unfold HasStatus at hst h3
    rcases hst with h | h | h | h <;>
      exact absurd (h.symm.trans h3) (by decide +kernel)
  · simp only [Bool.not_eq_true] at hv
    simp only [hv, iff_true]
    unfold HasStatus locate locateWith
    simp only [hv, Bool.false_eq_true, ite_false]
    decide +kernel

end Demos.Geolocation
