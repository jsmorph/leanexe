import Demos.Slew.Error
import Demos.Slew.Normalize

/-! The rounding errors of one cone of the edge check.  For an attitude `qa`, a body vector `b`,
and a cone axis `u` whose squared norms lie within `3e-12` of 1, and an axis `n` within `5.2 u`
of a unit axis `N`, `cone_values` bounds the program's `f₀ = u·v₀`, `B = u·(n × v₀)`,
`C = (n·u)(n·v₀)`, `A = f₀ - C`, `f₁ = A cos θ + B sin θ + C`, and `f′(θ) = B cos θ - A sin θ`
against the same formulas in exact arithmetic, where `v₀` is the rotation formula of `qa` and `b`
and `cos θ` and `sin θ` are given within `12.5 u`.  The errors stay below `1335 u`, about
`1.5e-13`. -/

namespace Demos.Slew.Cone

open Demos.Slew.Spec Demos.Slew.Rounding Demos.Slew.Error Demos.Slew.Normalize Demos.Slew.Arc

set_option exponentiation.threshold 4096

/-- A float vector with finite components and squared norm within `3e-12` of 1. -/
structure GoodV (v : V3) : Prop where
  fx : Fin v.x
  fy : Fin v.y
  fz : Fin v.z
  norm : |Vec.dot (vecOf v) (vecOf v) - 1| ≤ 3e-12

/-- A float quaternion with finite components and squared norm within `3e-12` of 1. -/
structure GoodQ (q : Q4) : Prop where
  fw : Fin q.w
  fx : Fin q.x
  fy : Fin q.y
  fz : Fin q.z
  norm : |Quat.norm2 (quatOf q) - 1| ≤ 3e-12

theorem GoodV.norm_le {v : V3} (h : GoodV v) : Vec.norm (vecOf v) ≤ 1 + 3e-12 := by
  have := norm_near_one (vecOf v) 3e-12 (by norm_num) h.norm
  linarith [abs_le.mp this.1]

theorem GoodV.bnd {v : V3} (h : GoodV v) : Bnd3 v (vecOf v) 0 1.001 := by
  obtain ⟨cx, cy, cz⟩ := abs_component_le (vecOf v)
  have hn := h.norm_le
  exact ⟨Bnd.of_val h.fx (show |(vecOf v).x| ≤ 1.001 by linarith),
    Bnd.of_val h.fy (show |(vecOf v).y| ≤ 1.001 by linarith),
    Bnd.of_val h.fz (show |(vecOf v).z| ≤ 1.001 by linarith)⟩

theorem GoodQ.components {q : Q4} (h : GoodQ q) :
    Bnd q.w (val q.w) 0 1.001 ∧ Bnd q.x (val q.x) 0 1.001 ∧ Bnd q.y (val q.y) 0 1.001 ∧
      Bnd q.z (val q.z) 0 1.001 := by
  have hn := abs_le.mp h.norm
  simp only [Quat.norm2, quatOf] at hn
  have b : ∀ t : ℝ, t * t ≤ 1 + 3e-12 → |t| ≤ 1.001 := by
    intro t ht
    rw [abs_le]; constructor <;> nlinarith
  refine ⟨Bnd.of_val h.fw (b _ ?_), Bnd.of_val h.fx (b _ ?_), Bnd.of_val h.fy (b _ ?_),
    Bnd.of_val h.fz (b _ ?_)⟩ <;>
    nlinarith [mul_self_nonneg (val q.w), mul_self_nonneg (val q.x), mul_self_nonneg (val q.y),
      mul_self_nonneg (val q.z)]

/-- The program's rotation of `b` by `qa`, with components of magnitude at most `1.0001`. -/
theorem v0_bnd {qa : Q4} {b : V3} (hq : GoodQ qa) (hb : GoodV b) :
    Bnd3 (Demos.Slew.qrot qa b) (Quat.rot (quatOf qa) (vecOf b)) (75 / 2 ^ 53) 1.0001 := by
  obtain ⟨hw, hx, hy, hz⟩ := hq.components
  obtain ⟨bx, byy, bz⟩ := hb.bnd
  have h := qrot_bnd qa b hw hx hy hz bx byy bz
  have hn := norm_rot_le (quatOf qa) (vecOf b) hq.norm hb.norm
  obtain ⟨cx, cy, cz⟩ := abs_component_le (Quat.rot (quatOf qa) (vecOf b))
  exact ⟨h.1.rebound (cx.trans hn), h.2.1.rebound (cy.trans hn), h.2.2.rebound (cz.trans hn)⟩

/-- The rounded values of one cone of the edge check. -/
theorem cone_values {qa : Q4} {b u n : V3} {ct st : Float} {N : Vec} {CT ST : ℝ}
    (hq : GoodQ qa) (hb : GoodV b) (hu : GoodV u) (hn : Bnd3 n N (5.2 / 2 ^ 53) 1)
    (hN : Vec.dot N N = 1) (hct : Bnd ct CT (12.5 / 2 ^ 53) 1.0001)
    (hst : Bnd st ST (12.5 / 2 ^ 53) 1.0001) :
    let U := vecOf u
    let V := Quat.rot (quatOf qa) (vecOf b)
    let A := Vec.dot U V - Vec.dot N U * Vec.dot N V
    let B := Vec.dot U (Vec.cross N V)
    let C := Vec.dot N U * Vec.dot N V
    Bnd (Demos.Slew.dot u (Demos.Slew.qrot qa b)) (Vec.dot U V) (233.5 / 2 ^ 53) 1.0002 ∧
    Bnd (Demos.Slew.dot u (Demos.Slew.cross n (Demos.Slew.qrot qa b))) B (503 / 2 ^ 53) 1.0003 ∧
    Bnd (Demos.Slew.dot n u * Demos.Slew.dot n (Demos.Slew.qrot qa b)) C (274 / 2 ^ 53) 1.0003 ∧
    Bnd (Demos.Slew.dot u (Demos.Slew.qrot qa b) -
        Demos.Slew.dot n u * Demos.Slew.dot n (Demos.Slew.qrot qa b)) A (509.6 / 2 ^ 53) 2.0005 ∧
    Bnd ((Demos.Slew.dot u (Demos.Slew.qrot qa b) -
          Demos.Slew.dot n u * Demos.Slew.dot n (Demos.Slew.qrot qa b)) * ct +
        Demos.Slew.dot u (Demos.Slew.cross n (Demos.Slew.qrot qa b)) * st +
        Demos.Slew.dot n u * Demos.Slew.dot n (Demos.Slew.qrot qa b))
      (A * CT + B * ST + C) (1334.5 / 2 ^ 53) 4.0015 ∧
    Bnd (Demos.Slew.dot u (Demos.Slew.cross n (Demos.Slew.qrot qa b)) * ct -
        (Demos.Slew.dot u (Demos.Slew.qrot qa b) -
          Demos.Slew.dot n u * Demos.Slew.dot n (Demos.Slew.qrot qa b)) * st)
      (B * CT - A * ST) (1056.4 / 2 ^ 53) 3.0012 := by
  intro U V A B C
  have hv := v0_bnd hq hb
  have hub := hu.bnd
  have hUn := hu.norm_le
  have hVn := norm_rot_le (quatOf qa) (vecOf b) hq.norm hb.norm
  have hNn : Vec.norm N = 1 := norm_eq_one_of N hN
  -- the dot products
  have nu := dot_bnd (6.21 / 2 ^ 53) (14.43 / 2 ^ 53) (23.7 / 2 ^ 53) hn hub
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nu' : Bnd (Demos.Slew.dot n u) (Vec.dot N U) (23.7 / 2 ^ 53) 1.0001 := by
    refine nu.rebound ((abs_dot_le N U).trans ?_)
    rw [hNn, one_mul]; linarith
  have nv := dot_bnd (81.3 / 2 ^ 53) (164.7 / 2 ^ 53) (249.1 / 2 ^ 53) hn hv
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have nv' : Bnd (Demos.Slew.dot n (Demos.Slew.qrot qa b)) (Vec.dot N V) (249.1 / 2 ^ 53) 1.0001 := by
    refine nv.rebound ((abs_dot_le N V).trans ?_)
    rw [hNn, one_mul]; exact hVn
  have f0 := dot_bnd (76.1 / 2 ^ 53) (154.3 / 2 ^ 53) (233.5 / 2 ^ 53) hub hv
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have f0' : Bnd (Demos.Slew.dot u (Demos.Slew.qrot qa b)) (Vec.dot U V) (233.5 / 2 ^ 53) 1.0002 := by
    refine f0.rebound ((abs_dot_le U V).trans ?_)
    nlinarith [Arc.norm_nonneg U, Arc.norm_nonneg V]
  have cr := cross_bnd (81.3 / 2 ^ 53) (164.7 / 2 ^ 53) hn hv
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hcn : Vec.norm (Vec.cross N V) ≤ 1.0001 := by
    have := norm_cross_le N V
    rw [hNn, one_mul] at this; linarith
  have cr' : Bnd3 (Demos.Slew.cross n (Demos.Slew.qrot qa b)) (Vec.cross N V) (164.7 / 2 ^ 53) 1.0002 := by
    obtain ⟨cx, cy, cz⟩ := abs_component_le (Vec.cross N V)
    exact ⟨cr.1.rebound (by linarith), cr.2.1.rebound (by linarith), cr.2.2.rebound (by linarith)⟩
  have bb := dot_bnd (165.9 / 2 ^ 53) (333.9 / 2 ^ 53) (503 / 2 ^ 53) hub cr'
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have bb' : Bnd (Demos.Slew.dot u (Demos.Slew.cross n (Demos.Slew.qrot qa b))) B (503 / 2 ^ 53) 1.0003 := by
    refine bb.rebound ((abs_dot_le U (Vec.cross N V)).trans ?_)
    nlinarith [Arc.norm_nonneg U, Arc.norm_nonneg (Vec.cross N V)]
  have cc := Bnd.mul (274 / 2 ^ 53) nu' nv' (by norm_num) (by norm_num)
  have cc' := cc.mono le_rfl (show (1.0001 : ℝ) * 1.0001 ≤ 1.0003 by norm_num)
  have aa := Bnd.sub (509.6 / 2 ^ 53) f0' cc' (by norm_num) (by norm_num)
  have act := Bnd.mul (536.7 / 2 ^ 53) aa hct (by norm_num) (by norm_num)
  have bst := Bnd.mul (516.6 / 2 ^ 53) bb' hst (by norm_num) (by norm_num)
  have s1 := Bnd.add (1056.4 / 2 ^ 53) act bst (by norm_num) (by norm_num)
  have f1 := Bnd.add (1334.5 / 2 ^ 53) s1 cc' (by norm_num) (by norm_num)
  have bct := Bnd.mul (516.6 / 2 ^ 53) bb' hct (by norm_num) (by norm_num)
  have ast := Bnd.mul (536.7 / 2 ^ 53) aa hst (by norm_num) (by norm_num)
  have d1 := Bnd.sub (1056.4 / 2 ^ 53) bct ast (by norm_num) (by norm_num)
  exact ⟨f0', bb', cc', aa.mono le_rfl (by norm_num), f1.mono le_rfl (by norm_num),
    d1.mono le_rfl (by norm_num)⟩

end Demos.Slew.Cone
