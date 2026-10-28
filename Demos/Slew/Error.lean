import Demos.Slew.Arc
import Demos.Slew.Rounding

/-! Rounding-error bounds for the vector formulas of the edge check.  Each bound compares the
program's binary64 result with the same formula in exact arithmetic on the real values of the
program's inputs, so the inputs need not be normalized.  `qrot_bnd` bounds the rotation formula,
whose components lie within `75 u` of the exact ones for inputs of magnitude at most `1.001`, and
`dot_bnd` and `cross_bnd` carry bounds through dot and cross products.  The constants are crude,
and the margins of the check exceed them by several orders of magnitude. -/

namespace Demos.Slew.Error

open Demos.Slew.Spec Demos.Slew.Rounding

set_option exponentiation.threshold 4096

/-- The real vector of a float vector. -/
noncomputable def vecOf (v : V3) : Vec := ⟨val v.x, val v.y, val v.z⟩

/-- The real quaternion of a float quaternion. -/
noncomputable def quatOf (q : Q4) : Quat := ⟨val q.w, val q.x, val q.y, val q.z⟩

/-- Each component of `v` lies within `e` of `V`'s, and each of `V`'s components is at most `M`
in magnitude. -/
def Bnd3 (v : V3) (V : Vec) (e M : ℝ) : Prop := Bnd v.x V.x e M ∧ Bnd v.y V.y e M ∧ Bnd v.z V.z e M

/-! ### Dot and cross products -/

theorem dot_bnd {a b : V3} {A B : Vec} {ea eb Ma Mb : ℝ} (ep e1 e : ℝ) (ha : Bnd3 a A ea Ma)
    (hb : Bnd3 b B eb Mb) (hbig : (Ma + ea) * (Mb + eb) < 2 ^ 1022)
    (hp : ea * Mb + Ma * eb + ea * eb + (Ma + ea) * (Mb + eb) / 2 ^ 53 + 1 / 2 ^ 1075 ≤ ep)
    (hbig1 : Ma * Mb + Ma * Mb + (ep + ep) < 2 ^ 1023)
    (h1 : ep + ep + (Ma * Mb + Ma * Mb + (ep + ep)) / 2 ^ 53 ≤ e1)
    (hbig2 : Ma * Mb + Ma * Mb + Ma * Mb + (e1 + ep) < 2 ^ 1023)
    (h2 : e1 + ep + (Ma * Mb + Ma * Mb + Ma * Mb + (e1 + ep)) / 2 ^ 53 ≤ e) :
    Bnd (Demos.Slew.dot a b) (Vec.dot A B) e (Ma * Mb + Ma * Mb + Ma * Mb) := by
  have px := Bnd.mul ep ha.1 hb.1 hbig hp
  have py := Bnd.mul ep ha.2.1 hb.2.1 hbig hp
  have pz := Bnd.mul ep ha.2.2 hb.2.2 hbig hp
  have s1 := Bnd.add e1 px py hbig1 h1
  exact Bnd.add e s1 pz hbig2 h2

theorem cross_bnd {a b : V3} {A B : Vec} {ea eb Ma Mb : ℝ} (ep e : ℝ) (ha : Bnd3 a A ea Ma)
    (hb : Bnd3 b B eb Mb) (hbig : (Ma + ea) * (Mb + eb) < 2 ^ 1022)
    (hp : ea * Mb + Ma * eb + ea * eb + (Ma + ea) * (Mb + eb) / 2 ^ 53 + 1 / 2 ^ 1075 ≤ ep)
    (hbig1 : Ma * Mb + Ma * Mb + (ep + ep) < 2 ^ 1023)
    (h1 : ep + ep + (Ma * Mb + Ma * Mb + (ep + ep)) / 2 ^ 53 ≤ e) :
    Bnd3 (Demos.Slew.cross a b) (Vec.cross A B) e (Ma * Mb + Ma * Mb) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Bnd.sub e (Bnd.mul ep ha.2.1 hb.2.2 hbig hp) (Bnd.mul ep ha.2.2 hb.2.1 hbig hp) hbig1 h1
  · exact Bnd.sub e (Bnd.mul ep ha.2.2 hb.1 hbig hp) (Bnd.mul ep ha.1 hb.2.2 hbig hp) hbig1 h1
  · exact Bnd.sub e (Bnd.mul ep ha.1 hb.2.1 hbig hp) (Bnd.mul ep ha.2.1 hb.1 hbig hp) hbig1 h1

/-! ### The rotation formula -/

/-- One component of the rotation formula, `v + w t + (a t' - b t'')`, from exact inputs of
magnitude at most `1.001`. -/
theorem rot_component {w v qa qb qc qd qe qf qg qh k1 k2 k3 k4 k5 k6 : Float}
    (hw : Bnd w (val w) 0 1.001) (hv : Bnd v (val v) 0 1.001)
    (h1 : Bnd qa (val qa) 0 1.001) (h2 : Bnd qb (val qb) 0 1.001)
    (h3 : Bnd qc (val qc) 0 1.001) (h4 : Bnd qd (val qd) 0 1.001)
    (h5 : Bnd qe (val qe) 0 1.001) (h6 : Bnd qf (val qf) 0 1.001)
    (h7 : Bnd qg (val qg) 0 1.001) (h8 : Bnd qh (val qh) 0 1.001)
    (hk1 : Bnd k1 (val k1) 0 1.001) (hk2 : Bnd k2 (val k2) 0 1.001)
    (hk3 : Bnd k3 (val k3) 0 1.001) (hk4 : Bnd k4 (val k4) 0 1.001)
    (hk5 : Bnd k5 (val k5) 0 1.001) (hk6 : Bnd k6 (val k6) 0 1.001) :
    Bnd (v + w * (2.0 * (qa * qb - qc * qd)) +
        (k1 * (2.0 * (qe * qf - qg * qh)) - k2 * (2.0 * (k3 * k4 - k5 * k6))))
      (val v + val w * (2 * (val qa * val qb - val qc * val qd)) +
        (val k1 * (2 * (val qe * val qf - val qg * val qh)) -
          val k2 * (2 * (val k3 * val k4 - val k5 * val k6))))
      (75 / 2 ^ 53) 14 := by
  have p := fun {a b : Float} (ha : Bnd a (val a) 0 1.001) (hb : Bnd b (val b) 0 1.001) =>
    Bnd.mul (1.003 / 2 ^ 53) ha hb (by norm_num) (by norm_num)
  have d := fun {a b c e : Float} (ha : Bnd a (val a) 0 1.001) (hb : Bnd b (val b) 0 1.001)
      (hc : Bnd c (val c) 0 1.001) (he : Bnd e (val e) 0 1.001) =>
    Bnd.sub (4.02 / 2 ^ 53) (p ha hb) (p hc he) (by norm_num) (by norm_num)
  have t := fun {a b c e : Float} (ha : Bnd a (val a) 0 1.001) (hb : Bnd b (val b) 0 1.001)
      (hc : Bnd c (val c) 0 1.001) (he : Bnd e (val e) 0 1.001) =>
    Bnd.mul (12.1 / 2 ^ 53) Bnd.two (d ha hb hc he) (by norm_num) (by norm_num)
  have wt := Bnd.mul (16.2 / 2 ^ 53) hw (t h1 h2 h3 h4) (by norm_num) (by norm_num)
  have s1 := Bnd.add (21.3 / 2 ^ 53) hv wt (by norm_num) (by norm_num)
  have q1 := Bnd.mul (16.2 / 2 ^ 53) hk1 (t h5 h6 h7 h8) (by norm_num) (by norm_num)
  have q2 := Bnd.mul (16.2 / 2 ^ 53) hk2 (t hk3 hk4 hk5 hk6) (by norm_num) (by norm_num)
  have dq := Bnd.sub (40.5 / 2 ^ 53) q1 q2 (by norm_num) (by norm_num)
  have r := Bnd.add (75 / 2 ^ 53) s1 dq (by norm_num) (by norm_num)
  exact r.mono le_rfl (by norm_num)

/-- The rotation formula of the program, component by component, within `75 u` of the exact one
for inputs of magnitude at most `1.001`. -/
theorem qrot_bnd (q : Q4) (v : V3)
    (hw : Bnd q.w (val q.w) 0 1.001) (hx : Bnd q.x (val q.x) 0 1.001)
    (hy : Bnd q.y (val q.y) 0 1.001) (hz : Bnd q.z (val q.z) 0 1.001)
    (hvx : Bnd v.x (val v.x) 0 1.001) (hvy : Bnd v.y (val v.y) 0 1.001)
    (hvz : Bnd v.z (val v.z) 0 1.001) :
    Bnd3 (Demos.Slew.qrot q v) (Quat.rot (quatOf q) (vecOf v)) (75 / 2 ^ 53) 14 := by
  refine ⟨?_, ?_, ?_⟩
  · exact rot_component hw hvx hy hvz hz hvy hx hvy hy hvx hy hz hz hvx hx hvz
  · exact rot_component hw hvy hz hvx hx hvz hy hvz hz hvy hz hx hx hvy hy hvx
  · exact rot_component hw hvz hx hvy hy hvx hz hvx hx hvz hx hy hy hvz hz hvy

end Demos.Slew.Error
