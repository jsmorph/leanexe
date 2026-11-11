import Demos.Avoidance.Program
import Demos.Avoidance.Geometry
import Demos.Conjunction.BoxSoundness
import LeanExe.Dialect.Lemmas

/-!
Soundness of the authorizer.  `encounter xs j dv d` is the model's encounter of conjunction `j`
for the real values of the input, the velocity change `dv`, and the displacement `d`, and
`pcAfter xs j dv d` its probability of collision.  `authorize_sound` (A1) states that status 0
implies, for every conjunction, every velocity change of the box, and every displacement within
the padding, the conditions under which the model's propagation solves Newton's equation and the
plane's axes are orthonormal, and a probability below the threshold.  `authorize_enclosure` (A2)
states the interval and the verdict of each conjunction.  The proof follows the program:
`afterAt_encloses` encloses the encounter by `after.encloses`, `assessOne_sound` adds the checks
and `Demos.Conjunction.pcBoxWith_enclosure`, and `allBelow_spec` collects the conjunctions.
-/

namespace Demos.Avoidance

open LeanExe.ProofKit Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64
open CodeLib.IEEE64 (value Finite)
open Demos.Orbit LeanExe.Dialect

/-- The real value of element `i` of the input. -/
noncomputable def val (xs : Array Float) (i : Nat) : ℝ := value (xs[i]!).toBits

theorem val_rd (xs : Array Float) (i : UInt64) : value (rd xs i).toBits = val xs i.toNat := rfl

/-- The real result of `after` for conjunction `j`, the velocity change `dv`, and the
displacement `d`. -/
noncomputable def afterIn (xs : Array Float) (j : Nat) (dv d : V3) :
    ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ :=
  let b := 15 + 20 * j
  after (val xs 0) (val xs 1) (val xs 2) (val xs 3) (val xs 4) (val xs 5) (val xs 6) dv.x dv.y
    dv.z (val xs b) (val xs (b + 1)) (val xs (b + 2)) (val xs (b + 3)) (val xs (b + 4))
    (val xs (b + 5)) (val xs (b + 6)) (val xs (b + 7)) (val xs (b + 8)) (val xs (b + 9))
    (val xs (b + 10)) (val xs (b + 11)) (val xs (b + 12)) (val xs (b + 13)) (val xs (b + 14))
    (val xs (b + 15)) (val xs (b + 16)) (val xs (b + 17)) (val xs (b + 18)) d.x d.y d.z

/-- The model's encounter: the miss vector, the projected covariance, `α` and `e²` of the state
after the burn and of the nominal state, `|r₁ × ν|²`, and `|ν|²`. -/
structure Encounter where
  m1 : ℝ
  m2 : ℝ
  c11 : ℝ
  c12 : ℝ
  c22 : ℝ
  alpha1 : ℝ
  e1 : ℝ
  alpha0 : ℝ
  e0 : ℝ
  xn2 : ℝ
  zn2 : ℝ

noncomputable def encounter (xs : Array Float) (j : Nat) (dv d : V3) : Encounter :=
  let a := afterIn xs j dv d
  ⟨a.1, a.2.1, a.2.2.1, a.2.2.2.1, a.2.2.2.2.1, a.2.2.2.2.2.1, a.2.2.2.2.2.2.1, a.2.2.2.2.2.2.2.1,
    a.2.2.2.2.2.2.2.2.1, a.2.2.2.2.2.2.2.2.2.1, a.2.2.2.2.2.2.2.2.2.2⟩

/-- The model's probability of collision of conjunction `j` after the velocity change `dv`, with
the displacement `d`. -/
noncomputable def pcAfter (xs : Array Float) (j : Nat) (dv d : V3) : ℝ :=
  Demos.Conjunction.Model.pc (encounter xs j dv d).m1 (encounter xs j dv d).m2
    (encounter xs j dv d).c11 (encounter xs j dv d).c12 (encounter xs j dv d).c22
    (val xs (34 + 20 * j))

/-- The velocity change `dv` lies in the box. -/
def InBox (xs : Array Float) (dv : V3) : Prop :=
  val xs 7 ≤ dv.x ∧ dv.x ≤ val xs 8 ∧ val xs 9 ≤ dv.y ∧ dv.y ≤ val xs 10 ∧ val xs 11 ≤ dv.z ∧
    dv.z ≤ val xs 12

/-- Each component of the displacement `d` is at most the padding in absolute value. -/
def InPad (xs : Array Float) (d : V3) : Prop :=
  |d.x| ≤ val xs 13 ∧ |d.y| ≤ val xs 13 ∧ |d.z| ≤ val xs 13

/-- The conditions of the model's theorems for an encounter: both propagated states bound with
`e² < 1`, the plane's axes defined, the projected covariance positive definite, and a positive
radius. -/
structure Good (xs : Array Float) (j : Nat) (dv d : V3) : Prop where
  alpha1 : 0 < (encounter xs j dv d).alpha1
  e1 : (encounter xs j dv d).e1 < 1
  alpha0 : 0 < (encounter xs j dv d).alpha0
  e0 : (encounter xs j dv d).e0 < 1
  xn2 : 0 < (encounter xs j dv d).xn2
  zn2 : 0 < (encounter xs j dv d).zn2
  c11 : 0 < (encounter xs j dv d).c11
  det : 0 < Demos.Conjunction.Model.det (encounter xs j dv d).c11 (encounter xs j dv d).c12
    (encounter xs j dv d).c22
  radius : 0 < val xs (34 + 20 * j)

/-! ### One conjunction -/

theorem idx {j : UInt64} (hj : j.toNat < 64) (c : UInt64) (hc : c.toNat ≤ 19) :
    (15 + 20 * j + c).toNat = 15 + 20 * j.toNat + c.toNat := by
  simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.reduceToNat]
  omega

theorem idx0 {j : UInt64} (hj : j.toNat < 64) : (15 + 20 * j).toNat = 15 + 20 * j.toNat := by
  simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.reduceToNat]
  omega

theorem encloses_point (x : Float) : Encloses (point x) (value x.toBits) :=
  fun h => (point_sound h).2

/-- The intervals of `afterAt` enclose the model's encounter for every velocity change of the box
and every displacement within the padding. -/
theorem afterAt_encloses {xs : Array Float} {j : UInt64} (hj : j.toNat < 64)
    (hP : Finite (rd xs 13).toBits) {dv d : V3} (hb : InBox xs dv) (hd : InPad xs d) :
    (enclosure_relation% 11) (afterAt Trig.invPi Trig.halfPi xs j) (afterIn xs j.toNat dv d) := by
  have pb : ∀ c : UInt64, c.toNat ≤ 19 →
      Encloses (point (rd xs (15 + 20 * j + c))) (val xs (15 + 20 * j.toNat + c.toNat)) :=
    fun c hc => by rw [← idx hj c hc]; exact encloses_point _
  have p0 : Encloses (point (rd xs (15 + 20 * j))) (val xs (15 + 20 * j.toNat)) := by
    rw [← idx0 hj]; exact encloses_point _
  obtain ⟨fn, vn⟩ := neg_value hP
  have pad : ∀ x : ℝ, |x| ≤ val xs 13 → Encloses (make (-rd xs 13) (rd xs 13)) x := fun x hx =>
    Demos.Conjunction.encloses_make
      (by rw [vn]; exact (abs_le.mp hx).1)
      (abs_le.mp hx).2
  exact after.encloses (encloses_point _) (encloses_point _) (encloses_point _)
    (encloses_point _) (encloses_point _) (encloses_point _) (encloses_point _)
    (Demos.Conjunction.encloses_make hb.1 hb.2.1)
    (Demos.Conjunction.encloses_make hb.2.2.1 hb.2.2.2.1)
    (Demos.Conjunction.encloses_make hb.2.2.2.2.1 hb.2.2.2.2.2) p0
    (pb 1 (by decide)) (pb 2 (by decide)) (pb 3 (by decide)) (pb 4 (by decide))
    (pb 5 (by decide)) (pb 6 (by decide)) (pb 7 (by decide)) (pb 8 (by decide))
    (pb 9 (by decide)) (pb 10 (by decide)) (pb 11 (by decide)) (pb 12 (by decide))
    (pb 13 (by decide)) (pb 14 (by decide)) (pb 15 (by decide)) (pb 16 (by decide))
    (pb 17 (by decide)) (pb 18 (by decide)) (pad _ hd.1) (pad _ hd.2.1) (pad _ hd.2.2)

/-- An accepted enclosure of conjunction `j` gives the conditions of the model's theorems and
contains the model's probability for every velocity change of the box and every displacement
within the padding. -/
theorem assessOne_sound {xs : Array Float} {n j : UInt64} (hj : j.toNat < 64)
    (hP : Finite (rd xs 13).toBits)
    (h : (assessOne Exp.expTable Trig.invPi Trig.halfPi xs n j).status = 0)
    {dv d : V3} (hb : InBox xs dv) (hd : InPad xs d) :
    Good xs j.toNat dv d ∧
      Contains (assessOne Exp.expTable Trig.invPi Trig.halfPi xs n j) (pcAfter xs j.toNat dv d) := by
  have E := afterAt_encloses hj hP hb hd
  have hR : value (rd xs (15 + 20 * j + 19)).toBits = val xs (34 + 20 * j.toNat) := by
    rw [val_rd, idx hj 19 (by decide)]
    congr 1
    simp only [UInt64.reduceToNat]
    omega
  unfold assessOne at h ⊢
  dsimp only at h ⊢
  generalize afterAt Trig.invPi Trig.halfPi xs j = A at h E ⊢
  by_cases g : (A.2.2.2.2.2.1.status == 0 && 0 < A.2.2.2.2.2.1.lo &&
      A.2.2.2.2.2.2.1.status == 0 && A.2.2.2.2.2.2.1.hi < 1.0 &&
      A.2.2.2.2.2.2.2.1.status == 0 && 0 < A.2.2.2.2.2.2.2.1.lo &&
      A.2.2.2.2.2.2.2.2.1.status == 0 && A.2.2.2.2.2.2.2.2.1.hi < 1.0 &&
      A.2.2.2.2.2.2.2.2.2.1.status == 0 && 0 < A.2.2.2.2.2.2.2.2.2.1.lo &&
      A.2.2.2.2.2.2.2.2.2.2.status == 0 && 0 < A.2.2.2.2.2.2.2.2.2.2.lo) = true
  · simp only [g, ite_true] at h ⊢
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at g
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨g1, g2⟩, g3⟩, g4⟩, g5⟩, g6⟩, g7⟩, g8⟩, g9⟩, g10⟩, g11⟩, g12⟩ := g
    obtain ⟨hc, hdet, hr, hcon⟩ :=
      Demos.Conjunction.pcBoxWith_enclosure h E.1 E.2.1 E.2.2.1 E.2.2.2.1 E.2.2.2.2.1
    rw [hR] at hr hcon
    refine ⟨⟨(E.2.2.2.2.2.1 g1).pos_of_lo g2, (E.2.2.2.2.2.2.1 g3).lt_one_of_hi g4,
      (E.2.2.2.2.2.2.2.1 g5).pos_of_lo g6, (E.2.2.2.2.2.2.2.2.1 g7).lt_one_of_hi g8,
      (E.2.2.2.2.2.2.2.2.2.1 g9).pos_of_lo g10, (E.2.2.2.2.2.2.2.2.2.2 g11).pos_of_lo g12,
      hc, hdet, hr⟩, hcon⟩
  · simp only [g, Bool.false_eq_true, ite_false] at h
    exact absurd h (by decide)

/-! ### The input and the output -/

theorem allFinite_spec {xs : Array Float} (h : allFinite xs = true) :
    ∀ i < xs.size.toUInt64.toNat, Finite (rd xs (UInt64.ofNat i)).toBits := by
  have key := loop_induction (n := xs.size.toUInt64) (init := true)
    (f := fun i ok => ok && finite (rd xs i))
    (fun k ok => ok = true → ∀ i < k, Finite (rd xs (UInt64.ofNat i)).toBits)
    (fun _ i hi => absurd hi (Nat.not_lt_zero i))
    (fun k ok _ ih hk i hi => by
      simp only [Bool.and_eq_true] at hk
      by_cases hik : i < k
      · exact ih hk.1 i hik
      · have : i = k := by omega
        subst this
        exact (finite_iff _).mp hk.2)
  exact key h

theorem blocksOk_spec {xs : Array Float} {k : UInt64} (hk : k.toNat ≤ 64)
    (h : blocksOk xs k = true) :
    ∀ j < k.toNat, 0.0 < rd xs (15 + 20 * UInt64.ofNat j) ∧
      0.0 < rd xs (34 + 20 * UInt64.ofNat j) := by
  have key := loop_induction (n := k) (init := true)
    (f := fun j ok => ok && 0.0 < rd xs (15 + 20 * j) && 0.0 < rd xs (34 + 20 * j))
    (fun m ok => ok = true → ∀ j < m, 0.0 < rd xs (15 + 20 * UInt64.ofNat j) ∧
      0.0 < rd xs (34 + 20 * UInt64.ofNat j))
    (fun _ j hj => absurd hj (Nat.not_lt_zero j))
    (fun m ok _ ih hm j hj => by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
      by_cases hjm : j < m
      · exact ih hm.1.1 j hjm
      · have : j = m := by omega
        subst this
        exact ⟨hm.1.2, hm.2⟩)
  exact key h

theorem allBelow_spec {rs : Array Interval} {t : Float} (h : allBelow rs t = true) :
    ∀ j < rs.size.toUInt64.toNat, rs[(UInt64.ofNat j).toNat]!.status = 0 ∧
      rs[(UInt64.ofNat j).toNat]!.hi < t := by
  have key := loop_induction (n := rs.size.toUInt64) (init := true)
    (f := fun j ok => ok && (rs[j.toNat]!.status == 0 && rs[j.toNat]!.hi < t))
    (fun m ok => ok = true → ∀ j < m, rs[(UInt64.ofNat j).toNat]!.status = 0 ∧
      rs[(UInt64.ofNat j).toNat]!.hi < t)
    (fun _ j hj => absurd hj (Nat.not_lt_zero j))
    (fun m ok _ ih hm j hj => by
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm
      by_cases hjm : j < m
      · exact ih hm.1 j hjm
      · have : j = m := by omega
        subst this
        exact hm.2)
  exact key h

/-- The facts of a valid input. -/
structure Facts (xs : Array Float) (n : UInt64) : Prop where
  size : 35 ≤ xs.size.toUInt64.toNat ∧ xs.size.toUInt64.toNat ≤ 1295 ∧
    (xs.size.toUInt64.toNat - 15) % 20 = 0
  hcount : (count xs).toNat = (xs.size.toUInt64.toNat - 15) / 20
  fin : ∀ i < xs.size.toUInt64.toNat, Finite (xs[i]!).toBits
  mu : 0 < val xs 0
  pad : 0 ≤ val xs 13
  panels : 1 ≤ n ∧ n ≤ 1048576
  blocks : ∀ j < (count xs).toNat, 0 < val xs (15 + 20 * j) ∧ 0 < val xs (34 + 20 * j)

theorem pos_of_lt {x : Float} (hx : Finite x.toBits) (h : 0.0 < x) : 0 < value x.toBits := by
  have := (lt_iff_value Demos.Conjunction.lit_zero.1 hx).mp h
  rwa [Demos.Conjunction.lit_zero.2] at this

theorem nonneg_of_le {x : Float} (hx : Finite x.toBits) (h : 0.0 ≤ x) : 0 ≤ value x.toBits := by
  have := (le_iff_value Demos.Conjunction.lit_zero.1 hx).mp h
  rwa [Demos.Conjunction.lit_zero.2] at this

theorem valid_facts {xs : Array Float} {n : UInt64} (h : valid xs n = true) : Facts xs n := by
  simp only [valid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, hfin⟩, hmu⟩, -⟩, -⟩, -⟩, hp⟩, hn1⟩, hn2⟩, hbl⟩ := h
  have s1 := UInt64.le_iff_toNat_le.mp h1
  have s2 := UInt64.le_iff_toNat_le.mp h2
  simp only [UInt64.reduceToNat] at s1 s2
  have h15 : (15 : UInt64) ≤ xs.size.toUInt64 :=
    UInt64.le_iff_toNat_le.mpr (by simp only [UInt64.reduceToNat]; omega)
  have hsub : (xs.size.toUInt64 - 15).toNat = xs.size.toUInt64.toNat - 15 := by
    rw [UInt64.toNat_sub_of_le _ _ h15]
    rfl
  have s3 : (xs.size.toUInt64.toNat - 15) % 20 = 0 := by
    have := congrArg UInt64.toNat h3
    rw [UInt64.toNat_mod, hsub] at this
    simpa using this
  have hc : (count xs).toNat = (xs.size.toUInt64.toNat - 15) / 20 := by
    unfold count
    rw [UInt64.toNat_div, hsub]
    rfl
  have fin := allFinite_spec hfin
  have fin' : ∀ i < xs.size.toUInt64.toNat, Finite (xs[i]!).toBits := by
    intro i hi
    have := fin i hi
    unfold rd at this
    rwa [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)] at this
  have f : ∀ i < 35, Finite (xs[i]!).toBits := fun i hi => fin' i (by omega)
  have hbl' := blocksOk_spec (by omega) hbl
  refine ⟨⟨s1, s2, s3⟩, hc, fin', pos_of_lt (f 0 (by norm_num)) hmu,
    nonneg_of_le (f 13 (by norm_num)) hp, ⟨hn1, hn2⟩, fun j hj => ?_⟩
  have hj' : j < 64 := by omega
  have e0 : (15 + 20 * UInt64.ofNat j).toNat = 15 + 20 * j := by
    have := idx0 (j := UInt64.ofNat j) (by rw [UInt64.toNat_ofNat']; omega)
    rwa [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)] at this
  have e1 : (34 + 20 * UInt64.ofNat j).toNat = 34 + 20 * j := by
    simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.reduceToNat, UInt64.toNat_ofNat']
    omega
  obtain ⟨b1, b2⟩ := hbl' j hj
  constructor
  · have := pos_of_lt (fin' _ (by omega)) (show 0.0 < xs[15 + 20 * j]! by
      have h := b1; unfold rd at h; rwa [e0] at h)
    exact this
  · exact pos_of_lt (fin' _ (by omega)) (show 0.0 < xs[34 + 20 * j]! by
      have h := b2; unfold rd at h; rwa [e1] at h)

theorem append_get_left {α : Type} [Inhabited α] (a b : Array α) (k : Nat) (hk : k < a.size) :
    (a ++ b)[k]! = a[k]! := by
  rw [getElem!_pos (a ++ b) k (by simp; omega), getElem!_pos a k hk]
  simp [Array.getElem_append_left hk]

theorem append_get_right {α : Type} [Inhabited α] (a b : Array α) (k : Nat) (hk : k < b.size) :
    (a ++ b)[a.size + k]! = b[k]! := by
  rw [getElem!_pos (a ++ b) (a.size + k) (by simp; omega), getElem!_pos b k hk]
  simp [Array.getElem_append_right]

/-- The results of the conjunctions. -/
theorem results_get {xs : Array Float} {n : UInt64} (F : Facts xs n) {j : Nat}
    (hj : j < (count xs).toNat) :
    (LeanExe.build (count xs) fun j => assessOne Exp.expTable Trig.invPi Trig.halfPi xs n j)[
        (UInt64.ofNat j).toNat]! =
      assessOne Exp.expTable Trig.invPi Trig.halfPi xs n (UInt64.ofNat j) := by
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by have := F.hcount; have := F.size; omega)]
  exact build_get hj

/-! ### The theorems -/

/-- **A1.**  When `authorize` returns status 0, the input is valid, and for every conjunction,
every velocity change of the box, and every displacement within the padding, the model's
conditions hold and its probability of collision lies below the threshold. -/
theorem authorize_sound {xs : Array Float} {n : UInt64} (h : (authorize xs n)[0]! = 0.0) :
    valid xs n = true ∧ ∀ j < (count xs).toNat, ∀ dv d : V3, InBox xs dv → InPad xs d →
      Good xs j dv d ∧ pcAfter xs j dv d < val xs 14 := by
  unfold authorize authorizeWith at h
  by_cases hv : valid xs n = true
  · simp only [hv, ite_true] at h
    have F := valid_facts hv
    refine ⟨hv, fun j hj dv d hb hd => ?_⟩
    generalize hrs : (LeanExe.build (count xs) fun j =>
      assessOne Exp.expTable Trig.invPi Trig.halfPi xs n j) = rs at h
    rw [append_get_left _ _ 0 (by simp),
      show ∀ x y : Float, (#[x, y] : Array Float)[0]! = x from fun _ _ => rfl] at h
    have hall : allBelow rs (rd xs 14) = true := by
      by_contra hc
      simp only [Bool.not_eq_true] at hc
      simp only [hc, Bool.false_eq_true, ite_false] at h
      split_ifs at h with h2
      · exact absurd (congrArg Float.toBits h) (by decide +kernel)
      · exact absurd (congrArg Float.toBits h) (by decide +kernel)
    have hsz : rs.size.toUInt64.toNat = (count xs).toNat := by
      rw [← hrs, build_size]
      simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']
      exact Nat.mod_eq_of_lt (by have := F.hcount; have := F.size; omega)
    obtain ⟨hs, hhi⟩ := allBelow_spec hall j (by rw [hsz]; exact hj)
    rw [← hrs, results_get F hj] at hs hhi
    have hj64 : (UInt64.ofNat j).toNat < 64 := by
      rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by have := F.hcount; have := F.size; omega)]
      have := F.hcount; have := F.size; omega
    have hjn : (UInt64.ofNat j).toNat = j := by
      rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by have := F.hcount; have := F.size; omega)]
    have hP : Finite (rd xs 13).toBits := F.fin 13 (by have := F.size; omega)
    obtain ⟨G, C⟩ := assessOne_sound hj64 hP hs hb hd
    rw [hjn] at G C
    have ht : Finite (rd xs 14).toBits := F.fin 14 (by have := F.size; omega)
    refine ⟨G, lt_of_le_of_lt C.2.2.2.2 ?_⟩
    exact (lt_iff_value C.2.2.1 ht).mp hhi
  · simp only [hv, Bool.false_eq_true, ite_false] at h
    exact absurd (congrArg Float.toBits h) (by decide +kernel)

#print axioms authorize_sound

theorem pair_append_get {a b : Float} {arr : Array Float} {k : Nat} (hk : k < arr.size) :
    (#[a, b] ++ arr)[2 + k]! = arr[k]! :=
  append_get_right #[a, b] arr k hk

theorem tri_idx {j c : Nat} (hj : j < 64) (hc : c < 3) :
    (UInt64.ofNat (3 * j + c) / 3).toNat = j ∧ (UInt64.ofNat (3 * j + c) % 3).toNat = c := by
  have h : (UInt64.ofNat (3 * j + c)).toNat = 3 * j + c := by
    rw [UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  constructor
  · rw [UInt64.toNat_div, h]
    simp only [UInt64.reduceToNat]
    omega
  · rw [UInt64.toNat_mod, h]
    simp only [UInt64.reduceToNat]
    omega

/-- Entry `2 + 3j + c` of the output of a valid input: the verdict of conjunction `j` for
`c = 0`, and the ends of its enclosure for `c = 1` and `c = 2` when it is accepted. -/
theorem output_get {xs : Array Float} {n : UInt64} (hv : valid xs n = true) {j c : Nat}
    (hj : j < (count xs).toNat) (hc : c < 3) :
    (authorize xs n)[2 + 3 * j + c]! =
      if c = 0 then verdict (assessOne Exp.expTable Trig.invPi Trig.halfPi xs n (UInt64.ofNat j))
        (rd xs 14)
      else if (assessOne Exp.expTable Trig.invPi Trig.halfPi xs n (UInt64.ofNat j)).status = 0 then
        (if c = 1 then (assessOne Exp.expTable Trig.invPi Trig.halfPi xs n (UInt64.ofNat j)).lo
          else (assessOne Exp.expTable Trig.invPi Trig.halfPi xs n (UInt64.ofNat j)).hi)
      else 0.0 := by
  have F := valid_facts hv
  have hk := F.hcount
  have hs := F.size
  unfold authorize authorizeWith
  simp only [hv, ite_true]
  generalize hrs : (LeanExe.build (count xs) fun j =>
    assessOne Exp.expTable Trig.invPi Trig.halfPi xs n j) = rs
  have hsz : rs.size = (count xs).toNat := by rw [← hrs, build_size]
  have hsz' : rs.size.toUInt64.toNat = (count xs).toNat := by
    rw [hsz]
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  have h3 : 3 * j + c < (3 * rs.size.toUInt64).toNat := by
    rw [UInt64.toNat_mul, hsz']
    simp only [UInt64.reduceToNat]
    omega
  have hj64 : j < 64 := by omega
  obtain ⟨i1, i2⟩ := tri_idx hj64 hc
  have hr : rs[j]! = assessOne Exp.expTable Trig.invPi Trig.halfPi xs n (UInt64.ofNat j) := by
    rw [← hrs]
    exact build_get hj
  rw [show 2 + 3 * j + c = 2 + (3 * j + c) by omega,
    pair_append_get (by unfold triples; rw [build_size]; exact h3)]
  unfold triples
  rw [build_get h3]
  dsimp only
  rw [i1, hr]
  have e0 : (UInt64.ofNat (3 * j + c) % 3 == 0) = decide (c = 0) := by
    by_cases h0 : c = 0
    · subst h0
      simp only [decide_true, beq_iff_eq]
      exact UInt64.toNat_inj.mp (by rw [i2]; rfl)
    · simp only [h0, decide_false, beq_eq_false_iff_ne, ne_eq]
      intro he
      apply h0
      rw [← i2, he]
      rfl
  have e1 : (UInt64.ofNat (3 * j + c) % 3 == 1) = decide (c = 1) := by
    by_cases h1 : c = 1
    · subst h1
      simp only [decide_true, beq_iff_eq]
      exact UInt64.toNat_inj.mp (by rw [i2]; rfl)
    · simp only [h1, decide_false, beq_eq_false_iff_ne, ne_eq]
      intro he
      apply h1
      rw [← i2, he]
      rfl
  rw [e0, e1]
  by_cases h0 : c = 0
  · simp only [h0, decide_true, ite_true]
  · simp only [h0, decide_false, Bool.false_eq_true, ite_false, beq_iff_eq]
    by_cases h1 : c = 1
    · simp only [h1, decide_true, ite_true]
    · simp only [h1, decide_false, Bool.false_eq_true, ite_false]

/-- **A2.**  For a valid input, a conjunction whose verdict is not 2 has an enclosure that
contains the model's probability for every velocity change of the box and every displacement
within the padding, and verdict 0 places the probability below the threshold. -/
theorem authorize_enclosure {xs : Array Float} {n : UInt64} (hv : valid xs n = true) {j : Nat}
    (hj : j < (count xs).toNat) (hs : (authorize xs n)[2 + 3 * j]! ≠ 2.0) {dv d : V3}
    (hb : InBox xs dv) (hd : InPad xs d) :
    Good xs j dv d ∧ value ((authorize xs n)[3 + 3 * j]!).toBits ≤ pcAfter xs j dv d ∧
      pcAfter xs j dv d ≤ value ((authorize xs n)[4 + 3 * j]!).toBits ∧
      ((authorize xs n)[2 + 3 * j]! = 0.0 → pcAfter xs j dv d < val xs 14) := by
  have F := valid_facts hv
  have hk := F.hcount
  have hsz := F.size
  have v0 := output_get hv hj (c := 0) (by norm_num)
  have v1 := output_get hv hj (c := 1) (by norm_num)
  have v2 := output_get hv hj (c := 2) (by norm_num)
  rw [show 2 + 3 * j + 0 = 2 + 3 * j by omega] at v0
  rw [show 2 + 3 * j + 1 = 3 + 3 * j by omega] at v1
  rw [show 2 + 3 * j + 2 = 4 + 3 * j by omega] at v2
  simp only [ite_true, one_ne_zero, OfNat.ofNat_ne_zero, ite_false,
    show (2 : Nat) ≠ 1 by decide] at v0 v1 v2
  rw [v0, v1, v2]
  rw [v0] at hs
  generalize hr : assessOne Exp.expTable Trig.invPi Trig.halfPi xs n (UInt64.ofNat j) = r at hs ⊢
  have hst : r.status = 0 := by
    by_contra hne
    apply hs
    unfold verdict
    simp only [beq_iff_eq, hne, ite_false]
  have hj64 : (UInt64.ofNat j).toNat < 64 := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
    omega
  have hjn : (UInt64.ofNat j).toNat = j := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  have hP : Finite (rd xs 13).toBits := F.fin 13 (by omega)
  have ht : Finite (rd xs 14).toBits := F.fin 14 (by omega)
  obtain ⟨G, C⟩ := assessOne_sound hj64 hP (hr ▸ hst) hb hd
  rw [hjn] at G C
  rw [hr] at C
  simp only [hst, ite_true]
  refine ⟨G, C.2.2.2.1, C.2.2.2.2, fun h0 => ?_⟩
  have hlt : r.hi < rd xs 14 := by
    by_contra hge
    unfold verdict at h0
    simp only [hst, beq_self_eq_true, ite_true, hge, ite_false] at h0
    exact absurd (congrArg Float.toBits h0) (by decide +kernel)
  exact lt_of_le_of_lt C.2.2.2.2 ((lt_iff_value C.2.2.1 ht).mp hlt)

/-- Status 1 marks exactly the inputs that `valid` rejects. -/
theorem authorize_invalid {xs : Array Float} {n : UInt64} :
    (authorize xs n)[0]! = 1.0 ↔ valid xs n = false := by
  constructor
  · intro h
    by_contra hv
    have hv' : valid xs n = true := by simpa using hv
    unfold authorize authorizeWith at h
    simp only [hv', ite_true] at h
    rw [append_get_left _ _ 0 (by simp),
      show ∀ x y : Float, (#[x, y] : Array Float)[0]! = x from fun _ _ => rfl] at h
    split_ifs at h <;> exact absurd (congrArg Float.toBits h) (by decide +kernel)
  · intro h
    unfold authorize authorizeWith
    rw [if_neg (by simp [h])]
    rfl

/-! ### The model behind an accepted burn -/

set_option maxHeartbeats 4000000 in
/-- The fields of the model's encounter: the miss vector and the projected covariance in the axes
of the encounter plane, for the relative state `ρ`, `ν` of `relative` and the primary's nominal
position `r₁`, and `α` and `e²` of the state after the burn and of the nominal state. -/
theorem encounter_eq (xs : Array Float) (j : Nat) (dv d : V3) :
    let b := 15 + 20 * j
    let rb : V3 := ⟨val xs 1, val xs 2, val xs 3⟩
    let vb : V3 := ⟨val xs 4, val xs 5, val xs 6⟩
    let r1 : V3 := ⟨val xs (b + 1), val xs (b + 2), val xs (b + 3)⟩
    let rel := relative (val xs 0) rb.x rb.y rb.z vb.x vb.y vb.z dv.x dv.y dv.z (val xs b) r1.x
      r1.y r1.z (val xs (b + 4)) (val xs (b + 5)) (val xs (b + 6)) (val xs (b + 7))
      (val xs (b + 8)) (val xs (b + 9)) (val xs (b + 10)) (val xs (b + 11)) (val xs (b + 12)) d.x
      d.y d.z
    let ρ : V3 := ⟨rel.1, rel.2.1, rel.2.2.1⟩
    let ν : V3 := ⟨rel.2.2.2.1, rel.2.2.2.2.1, rel.2.2.2.2.2⟩
    let C := covMul (val xs (b + 13)) (val xs (b + 14)) (val xs (b + 15)) (val xs (b + 16))
      (val xs (b + 17)) (val xs (b + 18))
    encounter xs j dv d =
      ⟨V3.dot ρ (axisX ν r1), V3.dot ρ (axisY ν r1), V3.dot (axisX ν r1) (C (axisX ν r1)),
        V3.dot (axisX ν r1) (C (axisY ν r1)), V3.dot (axisY ν r1) (C (axisY ν r1)),
        (shape (val xs 0) rb.x rb.y rb.z (vb + dv).x (vb + dv).y (vb + dv).z).1,
        (shape (val xs 0) rb.x rb.y rb.z (vb + dv).x (vb + dv).y (vb + dv).z).2,
        (shape (val xs 0) rb.x rb.y rb.z vb.x vb.y vb.z).1,
        (shape (val xs 0) rb.x rb.y rb.z vb.x vb.y vb.z).2,
        V3.dot (V3.cross r1 ν) (V3.cross r1 ν), V3.dot ν ν⟩ := rfl

/-- **A1 with the model's theorems.**  When `authorize` returns status 0, for every conjunction,
every velocity change `dv` of the box, and every displacement `d` within the padding: the
two-body trajectories from the primary's state at the burn, with and without `dv`, solve Newton's
equation, the miss vector is the point of the line `ρ + τ ν` nearest the origin, and the
probability of collision lies below the threshold. -/
theorem authorize_model {xs : Array Float} {n : UInt64} (h : (authorize xs n)[0]! = 0.0) :
    ∀ j < (count xs).toNat, ∀ dv d : V3, InBox xs dv → InPad xs d →
      let b := 15 + 20 * j
      let rb : V3 := ⟨val xs 1, val xs 2, val xs 3⟩
      let vb : V3 := ⟨val xs 4, val xs 5, val xs 6⟩
      let r1 : V3 := ⟨val xs (b + 1), val xs (b + 2), val xs (b + 3)⟩
      let rel := relative (val xs 0) rb.x rb.y rb.z vb.x vb.y vb.z dv.x dv.y dv.z (val xs b) r1.x
        r1.y r1.z (val xs (b + 4)) (val xs (b + 5)) (val xs (b + 6)) (val xs (b + 7))
        (val xs (b + 8)) (val xs (b + 9)) (val xs (b + 10)) (val xs (b + 11)) (val xs (b + 12))
        d.x d.y d.z
      let ρ : V3 := ⟨rel.1, rel.2.1, rel.2.2.1⟩
      let ν : V3 := ⟨rel.2.2.2.1, rel.2.2.2.2.1, rel.2.2.2.2.2⟩
      Newton (val xs 0) (fun t => (stateAt (val xs 0) rb (vb + dv) t).1)
          (fun t => (stateAt (val xs 0) rb (vb + dv) t).2) ∧
        Newton (val xs 0) (fun t => (stateAt (val xs 0) rb vb t).1)
          (fun t => (stateAt (val xs 0) rb vb t).2) ∧
        (∀ τ : ℝ, V3.dot ρ (axisX ν r1) ^ 2 + V3.dot ρ (axisY ν r1) ^ 2 ≤ V3.dot (ρ + τ • ν) (ρ + τ • ν)) ∧
        pcAfter xs j dv d < val xs 14 := by
  obtain ⟨hv, hA⟩ := authorize_sound h
  have F := valid_facts hv
  intro j hj dv d hb hd
  obtain ⟨G, hlt⟩ := hA j hj dv d hb hd
  have E := encounter_eq xs j dv d
  refine ⟨propagate_newton F.mu ?_ ?_, propagate_newton F.mu ?_ ?_,
    (miss_closest ?_ ?_).1, hlt⟩
  · have := G.alpha1; rw [E] at this; exact this
  · have := G.e1; rw [E] at this; exact this
  · have := G.alpha0; rw [E] at this; exact this
  · have := G.e0; rw [E] at this; exact this
  · have := G.xn2; rw [E] at this; exact this
  · have := G.zn2; rw [E] at this; exact this

#print axioms authorize_enclosure
#print axioms authorize_invalid
#print axioms authorize_model

end Demos.Avoidance
