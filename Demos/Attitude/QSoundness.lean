import Demos.Attitude.QProgram
import Demos.Attitude.Eigen
import Demos.Attitude.Soundness
import LeanExe.Dialect.Lemmas

/-!
Soundness of the q-method program.  `qmethod_sound` (Q4) states what a result of status 0
implies about the real values of the input: Davenport's matrix `K` of the observations has a
maximizer of `qᵀ K q` on the unit sphere, unique up to sign, the output cut `c` separates its
largest eigenvalue from the rest of the spectrum, the attitude of the output quaternion `q̂` lies
within `errOpt` of the attitude of every maximizer, and within `err` of every attitude that the
error bounds admit.

The proof follows the program.  `accumulate_enc` carries the enclosure of Davenport's matrix and
of `Σ a sin ε` and `Σ a cos ε` through the loop over the observations, `pivots_enc` encloses the
pivots of the factorization that the program's choices of pivot define, whatever they are, and
`certify_sound` turns the accepted tests of the certificate into the hypotheses of
`inertia_cut`, `sin_sq_le_of_resid`, and `true_near`.  The Jacobi sweeps that propose `q̂` and the
cut enter only as the floats they return.
-/

namespace Demos.Attitude.QMethod

open LeanExe.ProofKit Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64
open CodeLib.IEEE64 (value Finite)
open Demos.Slew.Spec Demos.Slew.Arc Demos.Slew.Normalize Demos.Slew.Rotation Demos.Slew.Safety
open Demos.Slew.Premise Demos.Slew.Rounding Demos.Attitude Vec Real

set_option exponentiation.threshold 4096

/-! ### The real values of the input and the output -/

/-- The number of observations of the input. -/
def count (xs : Array Float) : ℕ := (rd xs 0).toUInt64.toNat

/-- The real observation `i` of the input: the measurement, the reference, the weight, and the
error bound of the record that starts at index `1 + 8 i`. -/
noncomputable def obsAt (xs : Array Float) (i : ℕ) : Obs :=
  ⟨vec3 xs[1 + 8 * i]! xs[2 + 8 * i]! xs[3 + 8 * i]!, vec3 xs[4 + 8 * i]! xs[5 + 8 * i]!
    xs[6 + 8 * i]!, val xs[7 + 8 * i]!, val xs[8 + 8 * i]!⟩

/-- Davenport's matrix of the input. -/
noncomputable def kOf (xs : Array Float) : Sym4 := davK (obsAt xs) (count xs)

/-- The real quaternion of four floats. -/
noncomputable def quatOf (q : Q4) : Quat := ⟨val q.w, val q.x, val q.y, val q.z⟩

/-! ### Floats and indices -/

theorem two_bits : (2.0 : Float).toBits = 0x4000000000000000 := by decide +kernel

theorem one_bits : (1.0 : Float).toBits = 0x3FF0000000000000 := by decide +kernel

theorem zero_bits : (0.0 : Float).toBits = 0 := by decide +kernel

theorem reject_ne (x : Float) (hx : x.toBits ≠ 0) : (rejectWith x)[0]! ≠ 0.0 := by
  intro h
  have : (rejectWith x)[0]! = x := rfl
  rw [this] at h
  rw [h, zero_bits] at hx
  exact hx rfl

theorem idx0 {i : ℕ} (hi : i < 16) : (1 + 8 * UInt64.ofNat i).toNat = 1 + 8 * i := by
  have h1 : (UInt64.ofNat i).toNat = i :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 2 ^ 64 from rfl]; omega)
  rw [UInt64.toNat_add, UInt64.toNat_mul, h1]
  simp only [UInt64.reduceToNat]
  omega

theorem rd_at0 (xs : Array Float) {i : ℕ} (hi : i < 16) :
    rd xs (1 + 8 * UInt64.ofNat i) = xs[1 + 8 * i]! := by
  rw [rd, idx0 hi]

/-- The value at offset `j` of the record that starts at index `1 + 8 i`. -/
theorem rd_at (xs : Array Float) {i : ℕ} (hi : i < 16) (j : UInt64) {m k : ℕ} (hj : j.toNat = m)
    (hm : m < 8) (hk : k = 1 + 8 * i + m) : rd xs (1 + 8 * UInt64.ofNat i + j) = xs[k]! := by
  rw [rd, UInt64.toNat_add, idx0 hi, hj, hk]
  congr 1
  omega

/-! ### Loops of tests -/

/-- A loop that accepts while every index passes a test accepts every index. -/
theorem loop_and {n : UInt64} {f : UInt64 → Bool}
    (h : LeanExe.loop n true (fun i ok => ok && f i) = true) :
    ∀ k < n.toNat, f (UInt64.ofNat k) = true := by
  have hl := LeanExe.Dialect.loop_induction (n := n) (init := true) (f := fun i ok => ok && f i)
    (fun k s => s = true → ∀ j < k, f (UInt64.ofNat j) = true)
    (fun _ j hj => absurd hj (Nat.not_lt_zero j))
    (fun k s _ hP hs => by
      simp only [Bool.and_eq_true] at hs
      intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
      · exact hP hs.1 j hj
      · subst hj; exact hs.2)
  exact hl h

/-- The conditions of a valid input. -/
theorem valid_cases {xs : Array Float} (h : valid xs = true) :
    2 ≤ count xs ∧ count xs ≤ 16 ∧
    ∀ i < count xs, 0 < val xs[7 + 8 * i]! ∧ 0 ≤ val xs[8 + 8 * i]! ∧
      val xs[8 + 8 * i]! ≤ 3 / 2 := by
  simp only [valid, isWhole, allFinite, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨_, h2⟩, h16⟩, hsz⟩, hfin⟩, hrec⟩ := h
  have hlo : 2 ≤ count xs := by
    simp only [count]; simpa using (UInt64.le_iff_toNat_le).mp h2
  have hhi : count xs ≤ 16 := by
    simp only [count]; simpa using (UInt64.le_iff_toNat_le).mp h16
  have hN : (1 + 8 * (rd xs 0).toUInt64).toNat = 1 + 8 * count xs := by
    rw [UInt64.toNat_add, UInt64.toNat_mul]
    simp only [UInt64.reduceToNat]
    simp only [count] at hhi ⊢
    omega
  rw [hsz] at hfin
  have hf : ∀ i < 1 + 8 * count xs, Finite xs[i]!.toBits := by
    intro i hi
    have hs : i < 2 ^ 64 := by omega
    have h1 := loop_and hfin i (by rw [hN]; exact hi)
    rw [rd, UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 2 ^ 64 from rfl]; exact hs)] at h1
    exact (finite_iff _).mp h1
  refine ⟨hlo, hhi, fun i hi => ?_⟩
  have hr := loop_and hrec i hi
  simp only [recordOk, Bool.and_eq_true, decide_eq_true_eq] at hr
  obtain ⟨⟨ha, he0⟩, he1⟩ := hr
  have hi16 : i < 16 := by simp only [count] at hhi hi; omega
  rw [rd_at xs hi16 6 (m := 6) rfl (by decide) (k := 7 + 8 * i) (by omega)] at ha
  rw [rd_at xs hi16 7 (m := 7) rfl (by decide) (k := 8 + 8 * i) (by omega)] at he0 he1
  have fa := hf (7 + 8 * i) (by omega)
  have fe := hf (8 + 8 * i) (by omega)
  refine ⟨?_, ?_, ?_⟩
  · have := (lt_iff_value zero_value.1 fa).mp ha; rwa [zero_value.2] at this
  · have := (le_iff_value zero_value.1 fe).mp he0; rwa [zero_value.2] at this
  · have := (le_iff_value fe lit_three_halves.1).mp he1; rwa [lit_three_halves.2] at this

/-! ### Matrices of intervals -/

/-- Each interval of `A` encloses its entry of `R`. -/
def EncM4 (A : M4) (R : Sym4) : Prop :=
  Encloses A.a00 R.a00 ∧ Encloses A.a01 R.a01 ∧ Encloses A.a02 R.a02 ∧ Encloses A.a03 R.a03 ∧
  Encloses A.a11 R.a11 ∧ Encloses A.a12 R.a12 ∧ Encloses A.a13 R.a13 ∧ Encloses A.a22 R.a22 ∧
  Encloses A.a23 R.a23 ∧ Encloses A.a33 R.a33

def EncM3 (B : M3) (R : Sym3) : Prop :=
  Encloses B.c00 R.c00 ∧ Encloses B.c01 R.c01 ∧ Encloses B.c02 R.c02 ∧ Encloses B.c11 R.c11 ∧
  Encloses B.c12 R.c12 ∧ Encloses B.c22 R.c22

def EncM2 (C : M2) (R : Sym2) : Prop :=
  Encloses C.d00 R.d00 ∧ Encloses C.d01 R.d01 ∧ Encloses C.d11 R.d11

theorem EncM4.swap {A : M4} {R : Sym4} (h : EncM4 A R) (p : UInt64) :
    EncM4 (swap4 p A) (R.swap p) := by
  obtain ⟨h00, h01, h02, h03, h11, h12, h13, h22, h23, h33⟩ := h
  unfold swap4 Sym4.swap
  split_ifs
  · exact ⟨h11, h01, h12, h13, h00, h02, h03, h22, h23, h33⟩
  · exact ⟨h22, h12, h02, h23, h11, h01, h13, h00, h03, h33⟩
  · exact ⟨h33, h13, h23, h03, h11, h12, h01, h22, h02, h00⟩
  · exact ⟨h00, h01, h02, h03, h11, h12, h13, h22, h23, h33⟩

theorem EncM3.swap {B : M3} {R : Sym3} (h : EncM3 B R) (p : UInt64) :
    EncM3 (swap3 p B) (R.swap p) := by
  obtain ⟨h00, h01, h02, h11, h12, h22⟩ := h
  unfold swap3 Sym3.swap
  split_ifs
  · exact ⟨h11, h01, h12, h00, h02, h22⟩
  · exact ⟨h22, h12, h02, h11, h01, h00⟩
  · exact ⟨h00, h01, h02, h11, h12, h22⟩

theorem EncM2.swap {C : M2} {R : Sym2} (h : EncM2 C R) (p : UInt64) :
    EncM2 (swap2 p C) (R.swap p) := by
  obtain ⟨h00, h01, h11⟩ := h
  unfold swap2 Sym2.swap
  split_ifs
  · exact ⟨h11, h01, h00⟩
  · exact ⟨h00, h01, h11⟩

theorem EncM4.shift {A : M4} {R : Sym4} (h : EncM4 A R) (c : Float) :
    EncM4 (shiftI A (point c)) (R.shift (val c)) := by
  obtain ⟨h00, h01, h02, h03, h11, h12, h13, h22, h23, h33⟩ := h
  have hc := encloses_point c
  exact ⟨encloses_sub h00 hc, h01, h02, h03, encloses_sub h11 hc, h12, h13, encloses_sub h22 hc,
    h23, encloses_sub h33 hc⟩

/-! ### The pivots -/

theorem stage4_enc {A : M4} {R : Sym4} (h : EncM4 A R) :
    ∃ p, Encloses (stage4 Trig.invPi Trig.halfPi A).1 (R.swap p).a00 ∧
      EncM3 (stage4 Trig.invPi Trig.halfPi A).2 (R.swap p).schur := by
  set p := top4 (mag A.a00) (mag A.a11) (mag A.a22) (mag A.a33) with hp
  refine ⟨p, ?_⟩
  obtain ⟨h00, h01, h02, h03, h11, h12, h13, h22, h23, h33⟩ := h.swap p
  have hs := Spec.schur4.encloses (powLog := Trig.invPi) (powExp := Trig.invPi) h00 h01 h02 h03
    h11 h12 h13 h22 h23 h33
  exact ⟨h00, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2⟩

theorem stage3_enc {B : M3} {R : Sym3} (h : EncM3 B R) :
    ∃ p, Encloses (stage3 Trig.invPi Trig.halfPi B).1 (R.swap p).c00 ∧
      EncM2 (stage3 Trig.invPi Trig.halfPi B).2 (R.swap p).schur := by
  set p : UInt64 := if mag B.c00 ≥ mag B.c11 && mag B.c00 ≥ mag B.c22 then 0
    else if mag B.c11 ≥ mag B.c22 then 1 else 2 with hp
  refine ⟨p, ?_⟩
  obtain ⟨h00, h01, h02, h11, h12, h22⟩ := h.swap p
  have hs := Spec.schur3.encloses (powLog := Trig.invPi) (powExp := Trig.invPi) h00 h01 h02 h11
    h12 h22
  exact ⟨h00, hs.1, hs.2.1, hs.2.2⟩

theorem stage2_enc {C : M2} {R : Sym2} (h : EncM2 C R) :
    ∃ p, Encloses (stage2 Trig.invPi Trig.halfPi C).1 (R.swap p).d00 ∧
      Encloses (stage2 Trig.invPi Trig.halfPi C).2 (R.swap p).schur := by
  set p : UInt64 := if mag C.d00 ≥ mag C.d11 then 0 else 1 with hp
  refine ⟨p, ?_⟩
  obtain ⟨h00, h01, h11⟩ := h.swap p
  exact ⟨h00, Spec.schur2.encloses (powLog := Trig.invPi) (powExp := Trig.invPi) h00 h01 h11⟩

/-- The pivot intervals enclose the pivots of the factorization that the program's choices of
pivot define. -/
theorem pivots_enc {A : M4} {R : Sym4} (h : EncM4 A R) :
    ∃ p1 p2 p3, Encloses (pivotsI Trig.invPi Trig.halfPi A).1 (pivots p1 p2 p3 R).1 ∧
      Encloses (pivotsI Trig.invPi Trig.halfPi A).2.1 (pivots p1 p2 p3 R).2.1 ∧
      Encloses (pivotsI Trig.invPi Trig.halfPi A).2.2.1 (pivots p1 p2 p3 R).2.2.1 ∧
      Encloses (pivotsI Trig.invPi Trig.halfPi A).2.2.2 (pivots p1 p2 p3 R).2.2.2 := by
  obtain ⟨p1, h1, hB⟩ := stage4_enc h
  obtain ⟨p2, h2, hC⟩ := stage3_enc hB
  obtain ⟨p3, h3, h4⟩ := stage2_enc hC
  exact ⟨p1, p2, p3, h1, h2, h3, h4⟩

/-- Accepted pivots with one positive and three negative signs. -/
theorem oneSign_of {d : Interval × Interval × Interval × Interval} {r : ℝ × ℝ × ℝ × ℝ}
    (h1 : Encloses d.1 r.1) (h2 : Encloses d.2.1 r.2.1) (h3 : Encloses d.2.2.1 r.2.2.1)
    (h4 : Encloses d.2.2.2 r.2.2.2) (h : signsOk d = true) : OneSign r := by
  have pos : ∀ {a : Interval} {x : ℝ}, Encloses a x → isPos a = true → 0 < x := by
    intro a x ha hp
    simp only [isPos, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hp
    exact (ha hp.1).pos_of_lo hp.2
  have neg : ∀ {a : Interval} {x : ℝ}, Encloses a x → isNeg a = true → x < 0 := by
    intro a x ha hn
    simp only [isNeg, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hn
    exact (ha hn.1).neg_of_hi hn.2
  simp only [signsOk, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with ((⟨⟨⟨a, b⟩, c⟩, d⟩ | ⟨⟨⟨a, b⟩, c⟩, d⟩) | ⟨⟨⟨a, b⟩, c⟩, d⟩) | ⟨⟨⟨a, b⟩, c⟩, d⟩
  · exact Or.inl ⟨pos h1 a, neg h2 b, neg h3 c, neg h4 d⟩
  · exact Or.inr (Or.inl ⟨neg h1 a, pos h2 b, neg h3 c, neg h4 d⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨neg h1 a, neg h2 b, pos h3 c, neg h4 d⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨neg h1 a, neg h2 b, neg h3 c, pos h4 d⟩))

/-! ### Davenport's matrix -/

theorem obsFirst_eq (o : Obs) :
    Spec.obsFirst o.b.x o.b.y o.b.z o.r.x o.r.y o.r.z (o.a / (norm o.b * norm o.r)) =
      (o.K.a00, o.K.a01, o.K.a02, o.K.a03) := by
  simp only [Spec.obsFirst, Obs.K, Sym4.smul, obsK, unit, smul, dot, cross, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring, by ring⟩

theorem obsRest_eq (o : Obs) :
    Spec.obsRest o.b.x o.b.y o.b.z o.r.x o.r.y o.r.z (o.a / (norm o.b * norm o.r)) o.K.a00 =
      (o.K.a11, o.K.a12, o.K.a13, o.K.a22, o.K.a23, o.K.a33) := by
  simp only [Spec.obsRest, Obs.K, Sym4.smul, obsK, unit, smul, dot, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring, by ring, by ring, by ring⟩

/-- The real observation of the record that starts at index `b`. -/
noncomputable def obsRd (xs : Array Float) (b : UInt64) : Obs :=
  ⟨vec3 (rd xs b) (rd xs (b + 1)) (rd xs (b + 2)), vec3 (rd xs (b + 3)) (rd xs (b + 4))
    (rd xs (b + 5)), val (rd xs (b + 6)), val (rd xs (b + 7))⟩

theorem obsRd_at (xs : Array Float) {i : ℕ} (hi : i < 16) :
    obsRd xs (1 + 8 * UInt64.ofNat i) = obsAt xs i := by
  unfold obsRd obsAt
  rw [rd_at0 xs hi, rd_at xs hi 1 (m := 1) rfl (by decide) (k := 2 + 8 * i) (by omega),
    rd_at xs hi 2 (m := 2) rfl (by decide) (k := 3 + 8 * i) (by omega),
    rd_at xs hi 3 (m := 3) rfl (by decide) (k := 4 + 8 * i) (by omega),
    rd_at xs hi 4 (m := 4) rfl (by decide) (k := 5 + 8 * i) (by omega),
    rd_at xs hi 5 (m := 5) rfl (by decide) (k := 6 + 8 * i) (by omega),
    rd_at xs hi 6 (m := 6) rfl (by decide) (k := 7 + 8 * i) (by omega),
    rd_at xs hi 7 (m := 7) rfl (by decide) (k := 8 + 8 * i) (by omega)]

/-- One step of the accumulation encloses Davenport's matrix and the two sums with the
observation added, and an accepted flag gives nonzero vectors. -/
theorem addObs_enc (xs : Array Float) (b : UInt64) (s : Acc) {K : Sym4} {ρ μ : ℝ}
    (hK : EncM4 s.k K) (hρ : Encloses s.rho ρ) (hμ : Encloses s.mu μ) :
    EncM4 (addObs Trig.invPi Trig.halfPi xs b s).k (K.add (obsRd xs b).K) ∧
    Encloses (addObs Trig.invPi Trig.halfPi xs b s).rho
      (ρ + (obsRd xs b).a * sin (obsRd xs b).ε) ∧
    Encloses (addObs Trig.invPi Trig.halfPi xs b s).mu
      (μ + (obsRd xs b).a * cos (obsRd xs b).ε) ∧
    ((addObs Trig.invPi Trig.halfPi xs b s).ok = true →
      s.ok = true ∧ 0 < norm (obsRd xs b).b ∧ 0 < norm (obsRd xs b).r) := by
  set o := obsRd xs b with ho
  have pb1 := encloses_point (rd xs b)
  have pb2 := encloses_point (rd xs (b + 1))
  have pb3 := encloses_point (rd xs (b + 2))
  have pr1 := encloses_point (rd xs (b + 3))
  have pr2 := encloses_point (rd xs (b + 4))
  have pr3 := encloses_point (rd xs (b + 5))
  have pa := encloses_point (rd xs (b + 6))
  have pe := encloses_point (rd xs (b + 7))
  have hsc := Spec.obsScale.encloses (powLog := Trig.invPi) (powExp := Trig.invPi) pb1 pb2 pb3
    pr1 pr2 pr3 pa
  have ht := Spec.obsTrue.encloses (powLog := Trig.invPi) (powExp := Trig.invPi) pa pe
  simp only [addObs]
  generalize Spec.obsScaleI Trig.invPi Trig.halfPi Trig.invPi Trig.invPi (point (rd xs b))
    (point (rd xs (b + 1))) (point (rd xs (b + 2))) (point (rd xs (b + 3)))
    (point (rd xs (b + 4))) (point (rd xs (b + 5))) (point (rd xs (b + 6))) = sc at hsc ⊢
  replace hsc : prodRel Encloses (prodRel Encloses Encloses) sc
      (norm o.b, norm o.r, o.a / (norm o.b * norm o.r)) := hsc
  have hf := Spec.obsFirst.encloses (powLog := Trig.invPi) (powExp := Trig.invPi) pb1 pb2 pb3
    pr1 pr2 pr3 hsc.2.2
  generalize Spec.obsFirstI Trig.invPi Trig.halfPi Trig.invPi Trig.invPi (point (rd xs b))
    (point (rd xs (b + 1))) (point (rd xs (b + 2))) (point (rd xs (b + 3)))
    (point (rd xs (b + 4))) (point (rd xs (b + 5))) sc.2.2 = f at hf ⊢
  replace hf : prodRel Encloses (prodRel Encloses (prodRel Encloses Encloses)) f
      (o.K.a00, o.K.a01, o.K.a02, o.K.a03) := by
    rw [← obsFirst_eq o]; exact hf
  have hg := Spec.obsRest.encloses (powLog := Trig.invPi) (powExp := Trig.invPi) pb1 pb2 pb3
    pr1 pr2 pr3 hsc.2.2 hf.1
  generalize Spec.obsRestI Trig.invPi Trig.halfPi Trig.invPi Trig.invPi (point (rd xs b))
    (point (rd xs (b + 1))) (point (rd xs (b + 2))) (point (rd xs (b + 3)))
    (point (rd xs (b + 4))) (point (rd xs (b + 5))) sc.2.2 f.1 = g at hg ⊢
  replace hg : prodRel Encloses (prodRel Encloses (prodRel Encloses (prodRel Encloses
      (prodRel Encloses Encloses)))) g
      (o.K.a11, o.K.a12, o.K.a13, o.K.a22, o.K.a23, o.K.a33) := by
    rw [← obsRest_eq o]; exact hg
  generalize Spec.obsTrueI Trig.invPi Trig.halfPi Trig.invPi Trig.invPi (point (rd xs (b + 6)))
    (point (rd xs (b + 7))) = t at ht ⊢
  replace ht : prodRel Encloses Encloses t (o.a * sin o.ε, o.a * cos o.ε) := ht
  obtain ⟨k00, k01, k02, k03, k11, k12, k13, k22, k23, k33⟩ := hK
  refine ⟨⟨encloses_add k00 hf.1, encloses_add k01 hf.2.1, encloses_add k02 hf.2.2.1,
    encloses_add k03 hf.2.2.2, encloses_add k11 hg.1, encloses_add k12 hg.2.1,
    encloses_add k13 hg.2.2.1, encloses_add k22 hg.2.2.2.1, encloses_add k23 hg.2.2.2.2.1,
    encloses_add k33 hg.2.2.2.2.2⟩, encloses_add hρ ht.1, encloses_add hμ ht.2, fun hok => ?_⟩
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨h0, s1⟩, l1⟩, s2⟩, l2⟩ := hok
  exact ⟨h0, (hsc.1 s1).pos_of_lo l1, (hsc.2.1 s2).pos_of_lo l2⟩

/-- The accumulation over the first `n` observations encloses Davenport's matrix and the sums
`Σ a sin ε` and `Σ a cos ε`, and an accepted flag gives nonzero vectors. -/
theorem accumulate_enc (xs : Array Float) {n : UInt64} (hn : n.toNat ≤ 16) :
    EncM4 (accumulate Trig.invPi Trig.halfPi xs n).k (davK (obsAt xs) n.toNat) ∧
    Encloses (accumulate Trig.invPi Trig.halfPi xs n).rho
      (∑ i ∈ Finset.range n.toNat, (obsAt xs i).a * sin (obsAt xs i).ε) ∧
    Encloses (accumulate Trig.invPi Trig.halfPi xs n).mu
      (∑ i ∈ Finset.range n.toNat, (obsAt xs i).a * cos (obsAt xs i).ε) ∧
    ((accumulate Trig.invPi Trig.halfPi xs n).ok = true →
      ∀ i < n.toNat, 0 < norm (obsAt xs i).b ∧ 0 < norm (obsAt xs i).r) := by
  have z : Encloses zeroI 0 := by
    have := encloses_point (0 : Float)
    rwa [show val (0 : Float) = 0 from zero_value.2] at this
  unfold accumulate
  refine LeanExe.Dialect.loop_induction (n := n)
    (P := fun k (s : Acc) => EncM4 s.k (davK (obsAt xs) k) ∧
      Encloses s.rho (∑ i ∈ Finset.range k, (obsAt xs i).a * sin (obsAt xs i).ε) ∧
      Encloses s.mu (∑ i ∈ Finset.range k, (obsAt xs i).a * cos (obsAt xs i).ε) ∧
      (s.ok = true → ∀ i < k, 0 < norm (obsAt xs i).b ∧ 0 < norm (obsAt xs i).r)) ?_ ?_
  · refine ⟨⟨z, z, z, z, z, z, z, z, z, z⟩, ?_, ?_, fun _ i hi => absurd hi (Nat.not_lt_zero i)⟩
    · simpa using z
    · simpa using z
  · intro k s hk hP
    beta_reduce at hP ⊢
    obtain ⟨hK, hρ, hμ, hok⟩ := hP
    have hk16 : k < 16 := by omega
    have h := addObs_enc xs (1 + 8 * UInt64.ofNat k) s hK hρ hμ
    rw [obsRd_at xs hk16] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    refine ⟨h1, ?_, ?_, fun hs i hi => ?_⟩
    · rw [Finset.sum_range_succ]; exact h2
    · rw [Finset.sum_range_succ]; exact h3
    · obtain ⟨hs0, hb, hr⟩ := h4 hs
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
      · exact hok hs0 i hi
      · subst hi; exact ⟨hb, hr⟩

theorem accepted_cases {s : Acc} (h : accepted s = true) :
    s.ok = true ∧ s.k.a00.status = 0 ∧ s.k.a01.status = 0 ∧ s.k.a02.status = 0 ∧
    s.k.a03.status = 0 ∧ s.k.a11.status = 0 ∧ s.k.a12.status = 0 ∧ s.k.a13.status = 0 ∧
    s.k.a22.status = 0 ∧ s.k.a23.status = 0 ∧ s.k.a33.status = 0 ∧ s.rho.status = 0 ∧
    s.mu.status = 0 := by
  simp only [accepted, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

/-! ### The certificate -/

/-- The arcsine of an interval accepts only arguments in `[-1, 1]`. -/
theorem asinI_range {a : Interval} {x : ℝ} (ha : Encloses a x) (h : (asinI a).status = 0) :
    -1 ≤ x ∧ x ≤ 1 := by
  unfold asinI at h
  by_cases g : (a.status == 0 && -1.0 ≤ a.lo && a.hi ≤ 1.0) = true
  · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at g
    obtain ⟨⟨gs, glo⟩, ghi⟩ := g
    obtain ⟨_, fl, fh, hl, hh⟩ := ha gs
    have hlo : -1 ≤ value a.lo.toBits := by
      have := (le_iff_value lit_neg_one.1 fl).mp glo
      rwa [lit_neg_one.2] at this
    have hhi : value a.hi.toBits ≤ 1 := by
      have := (le_iff_value fh lit_pos_one.1).mp ghi
      rwa [lit_pos_one.2] at this
    exact ⟨by linarith, by linarith⟩
  · simp only [g, Bool.false_eq_true, ite_false] at h
    exact absurd h rejected_status

/-- Clamping to the part of an interval at or above zero keeps the enclosure of a real that is
not negative. -/
theorem encloses_clamp0 {a : Interval} {x : ℝ} (ha : Encloses a x) (h0 : 0 ≤ x) :
    Encloses (clamp a 0 a.hi) x := by
  intro h
  obtain ⟨sa, hc⟩ := clamp_sound h
  have c := ha sa
  exact hc x c (by rw [zero_value.2]; exact h0) c.2.2.2.2

theorem two_enc : Encloses (ofInt 2) (2 : ℝ) :=
  encloses_ofInt' (m := 2) (by decide +kernel) (by decide +kernel) (by norm_num)

/-- **The certificate.**  For intervals that enclose a symmetric matrix `R` and the reals `ρt` and
`μt`, a result of status 0 of `certify` holds the quaternion `q`, two finite bounds, and the cut
`c`; the inertia certificate of `R - c I` holds; `q` is not zero and its Rayleigh quotient `μ`
lies above `c`; `c < μt`; and the sines `s = |R q - μ q| / (|q| (μ - c))` and
`t = ρt / (μt - c)` lie at most 1, with `2 arcsin s` at most the first bound and
`2 (arcsin s + arcsin t)` at most the second. -/
theorem certify_sound {K : M4} {R : Sym4} (hK : EncM4 K R) {rt mt : Interval} {ρt μt : ℝ}
    (hrt : Encloses rt ρt) (hmt : Encloses mt μt) {c : Float} {q : Q4}
    (h : (certify Trig.invPi Trig.halfPi K rt mt c q)[0]! = 0.0) :
    ∃ eo e : Float, certify Trig.invPi Trig.halfPi K rt mt c q =
      #[0.0, q.w, q.x, q.y, q.z, eo, e, c] ∧ Finite eo.toBits ∧ Finite e.toBits ∧
      (R.shift (val c)).OnePos ∧ 0 < Quat.norm2 (quatOf q) ∧
      val c < R.form (quatOf q) / Quat.norm2 (quatOf q) ∧ val c < μt ∧
      √(Quat.norm2 (qsub (R.apply (quatOf q))
          (Quat.smul (R.form (quatOf q) / Quat.norm2 (quatOf q)) (quatOf q))) /
          Quat.norm2 (quatOf q)) / (R.form (quatOf q) / Quat.norm2 (quatOf q) - val c) ≤ 1 ∧
      ρt / (μt - val c) ≤ 1 ∧
      2 * arcsin (√(Quat.norm2 (qsub (R.apply (quatOf q))
          (Quat.smul (R.form (quatOf q) / Quat.norm2 (quatOf q)) (quatOf q))) /
          Quat.norm2 (quatOf q)) / (R.form (quatOf q) / Quat.norm2 (quatOf q) - val c)) ≤
        val eo ∧
      2 * (arcsin (√(Quat.norm2 (qsub (R.apply (quatOf q))
          (Quat.smul (R.form (quatOf q) / Quat.norm2 (quatOf q)) (quatOf q))) /
          Quat.norm2 (quatOf q)) / (R.form (quatOf q) / Quat.norm2 (quatOf q) - val c)) +
        arcsin (ρt / (μt - val c))) ≤ val e := by
  -- the enclosures
  obtain ⟨p1, p2, p3, d1, d2, d3, d4⟩ := pivots_enc (hK.shift c)
  obtain ⟨k00, k01, k02, k03, k11, k12, k13, k22, k23, k33⟩ := hK
  have pw := encloses_point q.w
  have px := encloses_point q.x
  have py := encloses_point q.y
  have pz := encloses_point q.z
  have hu := Spec.applyK.encloses (powLog := Trig.invPi) (powExp := Trig.invPi) k00 k01 k02 k03
    k11 k12 k13 k22 k23 k33 pw px py pz
  have hr := Spec.residOf.encloses (powLog := Trig.invPi) (powExp := Trig.invPi) hu.1 hu.2.1
    hu.2.2.1 hu.2.2.2 pw px py pz
  -- the result
  unfold certify at h ⊢
  simp only at h ⊢
  generalize pivotsI Trig.invPi Trig.halfPi (shiftI K (point c)) = d at d1 d2 d3 d4 h ⊢
  generalize Spec.applyKI Trig.invPi Trig.halfPi Trig.invPi Trig.invPi K.a00 K.a01 K.a02 K.a03
    K.a11 K.a12 K.a13 K.a22 K.a23 K.a33 (point q.w) (point q.x) (point q.y) (point q.z) = u
    at hu hr h ⊢
  generalize Spec.residOfI Trig.invPi Trig.halfPi Trig.invPi Trig.invPi u.1 u.2.1 u.2.2.1 u.2.2.2
    (point q.w) (point q.x) (point q.y) (point q.z) = r at hr h ⊢
  -- the real quantities
  set p := quatOf q with hp
  set N := Quat.norm2 p with hNdef
  set μ := R.form p / N with hμdef
  set R2 := Quat.norm2 (qsub (R.apply p) (Quat.smul μ p)) with hR2def
  have hrN : Encloses r.1 N := hr.1
  have hrμ : Encloses r.2.1 μ := hr.2.1
  have hrR : Encloses r.2.2 (R2 / N) := hr.2.2
  have hR2 : 0 ≤ R2 / N := div_nonneg (norm2_nonneg _) (norm2_nonneg _)
  have hrho := encloses_sqrt (encloses_clamp0 hrR hR2)
  have hb := Spec.boundsOf.encloses (powLog := Trig.invPi) (powExp := Trig.invPi) hrμ hrho hrt
    hmt (encloses_point c)
  generalize Spec.boundsOfI Trig.invPi Trig.halfPi Trig.invPi Trig.invPi r.2.1
    (sqrt (clamp r.2.2 0 r.2.2.hi)) rt mt (point c) = b at hb h ⊢
  have hb1 : Encloses b.1 (μ - val c) := hb.1
  have hb2 : Encloses b.2.1 (μt - val c) := hb.2.1
  have hb3 : Encloses b.2.2.1 (√(R2 / N) / (μ - val c)) := hb.2.2.1
  have hb4 : Encloses b.2.2.2 (ρt / (μt - val c)) := hb.2.2.2
  split_ifs at h with hc
  · simp only [hc, ite_true]
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨hs, rs⟩, rl⟩, bs⟩, bl⟩, bs2⟩, bl2⟩, eos⟩, es⟩ := hc
    have hN : 0 < N := (hrN rs).pos_of_lo rl
    have hg : 0 < μ - val c := (hb1 bs).pos_of_lo bl
    have hgt : 0 < μt - val c := (hb2 bs2).pos_of_lo bl2
    have hS := encloses_asinI hb3
    have hT := encloses_asinI hb4
    have heo := encloses_mul two_enc hS
    have he := encloses_mul two_enc (encloses_add hS hT)
    obtain ⟨-, sS, -⟩ := mul_sound eos
    obtain ⟨-, sST, -⟩ := mul_sound es
    obtain ⟨-, sT, -⟩ := add_sound sST
    have rS := asinI_range hb3 sS
    have rT := asinI_range hb4 sT
    have ceo := heo eos
    have ce := he es
    refine ⟨_, _, rfl, ceo.2.2.1, ce.2.2.1, onePos_of_pivots (oneSign_of d1 d2 d3 d4 hs), hN,
      by linarith, by linarith, rS.2, rT.2, ceo.2.2.2.2, ce.2.2.2.2⟩
  · exact absurd h (reject_ne 2.0 (by rw [two_bits]; decide))

/-! ### The program -/

/-- The branches of a result of status 0. -/
theorem qmethod_cases {xs : Array Float} (h : (qmethod xs)[0]! = 0.0) :
    valid xs = true ∧ accepted (accumulate Trig.invPi Trig.halfPi xs (rd xs 0).toUInt64) = true ∧
    ∃ c q, qmethod xs = certify Trig.invPi Trig.halfPi
      (accumulate Trig.invPi Trig.halfPi xs (rd xs 0).toUInt64).k
      (accumulate Trig.invPi Trig.halfPi xs (rd xs 0).toUInt64).rho
      (accumulate Trig.invPi Trig.halfPi xs (rd xs 0).toUInt64).mu c q := by
  have r1 := reject_ne 1.0 (by rw [one_bits]; decide)
  unfold qmethod qmethodWith at h ⊢
  by_cases hv : valid xs = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hv)] at h ⊢
    simp only at h ⊢
    by_cases ha : accepted (accumulate Trig.invPi Trig.halfPi xs (rd xs 0).toUInt64) = true
    · rw [ite_eq_left_of_eq_true _ _ (eq_true ha)]
      exact ⟨hv, ha, _, _, rfl⟩
    · rw [ite_eq_right_of_eq_false _ _ (eq_false ha)] at h
      exact absurd h r1
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hv)] at h
    exact absurd h r1

theorem within_mono {F G : Vec → Vec} {a b : ℝ} (h : Within F G a) (hab : a ≤ b) :
    Within F G b := fun v hv => (h v hv).trans hab

/-- **Q4, the soundness of the q-method.**  If `qmethod` returns status 0, the input holds from 2
to 16 observations with nonzero vectors, positive weights, and error bounds in `[0, 1.5]`;
`errOpt` and `err` are finite; the inertia certificate of `K - c I` holds for the output cut `c`;
a maximizer `e` of `qᵀ K q` on the unit sphere exists and is unique up to sign; every maximizer
satisfies `c < eᵀ K e` and `qᵀ K q < c` for every unit `q ⊥ e`; the output quaternion `q̂` is not
zero; its attitude lies within `errOpt` of the attitude of every maximizer; and it lies within
`err` of the attitude of every nonzero `q` that carries each normalized measurement within its
error bound of the normalized reference. -/
theorem qmethod_sound {xs : Array Float} (h : (qmethod xs)[0]! = 0.0) :
    2 ≤ count xs ∧ count xs ≤ 16 ∧
    (∀ i < count xs, 0 < norm (obsAt xs i).b ∧ 0 < norm (obsAt xs i).r ∧ 0 < (obsAt xs i).a ∧
      0 ≤ (obsAt xs i).ε ∧ (obsAt xs i).ε ≤ 3 / 2) ∧
    Finite (qmethod xs)[5]!.toBits ∧ Finite (qmethod xs)[6]!.toBits ∧
    ((kOf xs).shift (val (qmethod xs)[7]!)).OnePos ∧
    (∃ e, IsMax (kOf xs) e) ∧
    (∀ e e', IsMax (kOf xs) e → IsMax (kOf xs) e' → e' = e ∨ e' = qneg e) ∧
    (∀ e, IsMax (kOf xs) e → val (qmethod xs)[7]! < (kOf xs).form e ∧
      ∀ q, Quat.norm2 q = 1 → qdot q e = 0 → (kOf xs).form q < val (qmethod xs)[7]!) ∧
    0 < Quat.norm2 (quatAt (qmethod xs) 1) ∧
    (∀ e, IsMax (kOf xs) e →
      Within (attitude (quatAt (qmethod xs) 1)) (attitude e) (val (qmethod xs)[5]!)) ∧
    ∀ q : Quat, 0 < Quat.norm2 q →
      (∀ i < count xs, vangle (attitude q (unit (obsAt xs i).b)) (unit (obsAt xs i).r) ≤
        (obsAt xs i).ε) →
      Within (attitude (quatAt (qmethod xs) 1)) (attitude q) (val (qmethod xs)[6]!) := by
  obtain ⟨hv, hacc, c, q, hq⟩ := qmethod_cases h
  obtain ⟨hlo, hhi, hrec⟩ := valid_cases hv
  rw [show count xs = (rd xs 0).toUInt64.toNat from rfl] at hlo hhi hrec ⊢
  rw [show kOf xs = davK (obsAt xs) (rd xs 0).toUInt64.toNat from rfl]
  obtain ⟨hK, hρ, hμ, hok⟩ := accumulate_enc xs hhi
  obtain ⟨aok, -⟩ := accepted_cases hacc
  have hvec := hok aok
  rw [hq] at h ⊢
  obtain ⟨eo, e, he, feo, fe, hpos, hN, hμc, hμt, hs1, ht1, heo, herr⟩ :=
    certify_sound hK hρ hμ h
  rw [he]
  have e1 : (#[0.0, q.w, q.x, q.y, q.z, eo, e, c] : Array Float)[5]! = eo := rfl
  have e2 : (#[0.0, q.w, q.x, q.y, q.z, eo, e, c] : Array Float)[6]! = e := rfl
  have e3 : (#[0.0, q.w, q.x, q.y, q.z, eo, e, c] : Array Float)[7]! = c := rfl
  have e4 : quatAt #[0.0, q.w, q.x, q.y, q.z, eo, e, c] 1 = quatOf q := rfl
  rw [e1, e2, e3, e4]
  set n := (rd xs 0).toUInt64.toNat
  set K := davK (obsAt xs) n
  -- the input
  have hobs : ∀ i < n, 0 < norm (obsAt xs i).b ∧ 0 < norm (obsAt xs i).r ∧ 0 < (obsAt xs i).a ∧
      0 ≤ (obsAt xs i).ε ∧ (obsAt xs i).ε ≤ 3 / 2 := fun i hi =>
    ⟨(hvec i hi).1, (hvec i hi).2, (hrec i hi).1, (hrec i hi).2.1, (hrec i hi).2.2⟩
  have hπ : (3 : ℝ) / 2 ≤ π / 2 := by linarith [pi_gt_three]
  obtain ⟨emax, hemax⟩ := exists_isMax K
  have hcut := fun e (he : IsMax K e) => inertia_cut hpos he
  -- the sines
  set s := √(Quat.norm2 (qsub (K.apply (quatOf q)) (Quat.smul (K.form (quatOf q) /
    Quat.norm2 (quatOf q)) (quatOf q))) / Quat.norm2 (quatOf q)) /
    (K.form (quatOf q) / Quat.norm2 (quatOf q) - val c)
  set ρt := ∑ i ∈ Finset.range n, (obsAt xs i).a * sin (obsAt xs i).ε
  set μt := ∑ i ∈ Finset.range n, (obsAt xs i).a * cos (obsAt xs i).ε
  have hs0 : 0 ≤ s := div_nonneg (Real.sqrt_nonneg _) (by linarith)
  have hρt : 0 ≤ ρt := Finset.sum_nonneg fun i hi => by
    have := hobs i (Finset.mem_range.mp hi)
    exact mul_nonneg this.2.2.1.le (sin_nonneg_of_nonneg_of_le_pi this.2.2.2.1
      (by linarith [this.2.2.2.2, pi_gt_three]))
  have ht0 : 0 ≤ ρt / (μt - val c) := div_nonneg hρt (by linarith)
  have hps : ∀ e, IsMax K e → 1 - qdot (Quat.unit (quatOf q)) e ^ 2 ≤ s ^ 2 := by
    intro e he
    refine sin_sq_le_of_resid he (hcut e he).2 hμc hN ?_
    rw [Real.sq_sqrt (div_nonneg (norm2_nonneg _) hN.le), div_mul_cancel₀ _ hN.ne']
  refine ⟨hlo, hhi, hobs, feo, fe, hpos, ⟨emax, hemax⟩,
    fun e e' he he' => isMax_unique hpos he he', hcut, hN, fun e he => ?_, fun qt hqt hb => ?_⟩
  · have hw := within_of_sin hN (by rw [he.1]; norm_num) he.1 hs0 hs1 le_rfl zero_le_one
      (hps e he) (by rw [unit_of_norm2_one he.1, qdot_self, he.1]; norm_num)
    rw [arcsin_zero, add_zero] at hw
    exact within_mono hw heo
  · have htn := true_near (o := obsAt xs) (n := n) (fun i hi => (hobs i hi).1)
      (fun i hi => (hobs i hi).2.1) (fun i hi => (hobs i hi).2.2.1.le)
      (fun i hi => (hobs i hi).2.2.2.1) (fun i hi => (hobs i hi).2.2.2.2.trans hπ) hemax
      (hcut emax hemax).2 hμt hqt hb
    have hw := within_of_sin hN hqt hemax.1 hs0 hs1 ht0 ht1 (hps emax hemax) htn
    exact within_mono hw herr

end Demos.Attitude.QMethod
