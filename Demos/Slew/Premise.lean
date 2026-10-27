import Demos.Slew.Safety
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! The premise theorem of the slew planner.  `plan_premise` relates a plan of status 1 to a
flown slew whose attitude, cone axes, and cone half-angles differ from the planned ones.  The
angle between two vectors is Mathlib's `InnerProductGeometry.angle` on `EuclideanSpace ℝ (Fin 3)`,
the arccosine of their inner product over the product of their lengths.  If the flown attitude
stays within angle `ε` of the commanded attitude, the true axis of a cone lies within angle `d`
of its normalized input axis, and the true half-angle `α` of a keep-out cone satisfies
`α + d + ε ≤ arccos c` for the input cosine `c`, then the flown image of the cone's normalized
body vector keeps an angle of at least `α` from the true axis.  A keep-in cone with
`arccos c + d + ε ≤ α` gives an angle of at most `α`.

The proof applies `plan_safe` to the commanded attitude, which lies at distance 0 from itself.
The commanded body vector and the normalized axis are unit vectors, so the cone's inequality on
their cosine is an inequality on their angle, and the triangle inequality for angles
(`InnerProductGeometry.angle_le_angle_add_angle`) adds `d` and `ε`. -/

namespace Demos.Slew.Premise

open Demos.Slew.Spec Demos.Slew.Rounding Demos.Slew.Error Demos.Slew.Cone Demos.Slew.Normalize
open Demos.Slew.Check Demos.Slew.Rotation Demos.Slew.Valid Demos.Slew.Search Demos.Slew.Safety
open CodeLib.IEEE64 LeanExe.ProofKit

/-- The vector `v` in Mathlib's three-dimensional Euclidean space. -/
noncomputable def toE (v : Vec) : EuclideanSpace ℝ (Fin 3) := !₂[v.x, v.y, v.z]

/-- The angle between `a` and `b`, in `[0, π]`, or `π / 2` when either is zero. -/
noncomputable def vangle (a b : Vec) : ℝ := InnerProductGeometry.angle (toE a) (toE b)

theorem inner_toE (a b : Vec) : inner ℝ (toE a) (toE b) = Vec.dot a b := by
  simp only [toE, PiLp.inner_apply, Fin.sum_univ_three, Real.inner_apply]
  rfl

theorem norm_toE (a : Vec) : ‖toE a‖ = Vec.norm a := by
  rw [norm_eq_sqrt_real_inner, inner_toE, Vec.norm]

theorem vangle_eq {a b : Vec} (ha : Vec.norm a = 1) (hb : Vec.norm b = 1) :
    vangle a b = Real.arccos (Vec.dot a b) := by
  rw [vangle, InnerProductGeometry.angle, inner_toE, norm_toE, norm_toE, ha, hb, mul_one, div_one]

theorem vangle_comm (a b : Vec) : vangle a b = vangle b a := InnerProductGeometry.angle_comm _ _

theorem vangle_triangle (a b c : Vec) : vangle a c ≤ vangle a b + vangle b c :=
  InnerProductGeometry.angle_le_angle_add_angle _ _ _

theorem norm_rod {n : Vec} (hn : Vec.dot n n = 1) (φ : ℝ) (v : Vec) :
    Vec.norm (rod n φ v) = Vec.norm v := by
  rw [rod_eq_act n φ v hn, norm_act, norm2_half n φ hn, one_mul]

/-- `attitude q` preserves length, also for `q = 0`, whose normalization is 0. -/
theorem norm_attitude_any (q : Quat) (v : Vec) : Vec.norm (attitude q v) = Vec.norm v := by
  rcases lt_or_eq_of_le (norm2_nonneg q) with hq | hq
  · exact norm_attitude hq v
  · have hu : Quat.unit q = ⟨0, 0, 0, 0⟩ := by
      rw [Quat.unit, ← hq, Real.sqrt_zero, div_zero]
      ext <;> simp [Quat.smul]
    have hr : attitude q v = v := by
      rw [attitude, hu]
      ext <;> simp [Quat.rot]
    rw [hr]

theorem norm_sub_self (a : Vec) : Vec.norm (Vec.sub a a) = 0 := by
  simp [Vec.norm, Vec.sub, Vec.dot]

/-- **Premises of the slew planner.**  Let an output of status 1 have `K` segments, and let
`φ` lie between 0 and the angle of segment `g`.  Let the flown map `A` move every unit vector
by an angle of at most `ε` from the commanded attitude: the rotation by `φ` about the segment's
normalized axis after the attitude of its start quaternion.  Let cone `k` of the input have the
true axis `u`, within angle `d` of its normalized input axis, and the true half-angle `α`.  For a
keep-out cone with `α + d + ε ≤ arccos c`, where `c` is the input cosine, the flown image of the
normalized body vector keeps an angle of at least `α` from `u`.  For a keep-in cone with
`arccos c + d + ε ≤ α`, the angle is at most `α`. -/
theorem plan_premise {xs : Array Float} {K g : Nat} (h : (plan xs)[0]! = 1.0)
    (hsz : (plan xs).size = 8 + 11 * K) (hg : g < K) {φ : ℝ} (hφ0 : 0 ≤ φ)
    (hφ : φ ≤ val (plan xs)[11 + 11 * g]!) {A : Vec → Vec} {ε : ℝ}
    (hA : ∀ b : Vec, Vec.dot b b = 1 → vangle (A b)
      (rod (Vec.unit (vecAt (plan xs) (8 + 11 * g))) φ
        (attitude (quatAt (plan xs) (4 + 11 * g)) b)) ≤ ε)
    {k : Nat} (hk : k < (dims xs).nc.toNat) {u : Vec} {d : ℝ}
    (hu : vangle u (Vec.unit (vecOf (coneAxis xs (dims xs) (UInt64.ofNat k)))) ≤ d) (α : ℝ) :
    ((coneKind xs (dims xs) (UInt64.ofNat k) == 0.0) = true →
      α + d + ε ≤ Real.arccos (val (coneCos xs (dims xs) (UInt64.ofNat k))) →
      α ≤ vangle (A (Vec.unit (vecOf (coneBody xs (dims xs) (UInt64.ofNat k))))) u) ∧
    ((coneKind xs (dims xs) (UInt64.ofNat k) == 0.0) = false →
      Real.arccos (val (coneCos xs (dims xs) (UInt64.ofNat k))) + d + ε ≤ α →
      vangle (A (Vec.unit (vecOf (coneBody xs (dims xs) (UInt64.ofNat k))))) u ≤ α) := by
  obtain ⟨K', _, hsz', _, hseg⟩ := plan_safe h
  obtain rfl : K' = K := by omega
  obtain ⟨hn, _, hsafe⟩ := hseg g hg
  obtain ⟨hgb, hgu, _, _⟩ := (valid_good (plan_cases h).1).2.1 k hk
  have hbb := dot_unit_self _ (norm_near_one _ 3e-12 (by norm_num) hgb.norm).2
  have huu := dot_unit_self _ (norm_near_one _ 3e-12 (by norm_num) hgu.norm).2
  set n := Vec.unit (vecAt (plan xs) (8 + 11 * g))
  set q := quatAt (plan xs) (4 + 11 * g)
  set bb := Vec.unit (vecOf (coneBody xs (dims xs) (UInt64.ofNat k)))
  set ub := Vec.unit (vecOf (coneAxis xs (dims xs) (UInt64.ofNat k)))
  set X := rod n φ (attitude q bb)
  have hH : Holds (!(coneKind xs (dims xs) (UInt64.ofNat k) == 0.0)) ub
      (val (coneCos xs (dims xs) (UInt64.ofNat k))) X :=
    hsafe φ hφ0 hφ (fun b => rod n φ (attitude q b))
      (fun b _ => by rw [norm_sub_self]; norm_num) k hk
  have hX : Vec.norm X = 1 := by rw [norm_rod hn, norm_attitude_any, norm_eq_one_of bb hbb]
  have hcos := vangle_eq (norm_eq_one_of ub huu) hX
  have hAb := hA bb hbb
  have t1 := vangle_triangle ub u X
  have t2 := vangle_triangle u (A bb) X
  have t3 := vangle_triangle u ub (A bb)
  have t4 := vangle_triangle ub X (A bb)
  rw [vangle_comm ub u] at t1
  rw [vangle_comm X (A bb)] at t4
  rw [vangle_comm (A bb) u]
  refine ⟨fun hkind hα => ?_, fun hkind hα => ?_⟩
  · simp only [Holds, hkind, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hH
    have hc := Real.arccos_le_arccos hH
    rw [← hcos] at hc
    linarith
  · simp only [Holds, hkind, Bool.not_false, ↓reduceIte] at hH
    have hc := Real.arccos_le_arccos hH
    rw [← hcos] at hc
    linarith

end Demos.Slew.Premise
