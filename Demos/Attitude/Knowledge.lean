import Demos.Attitude.Soundness
import Demos.Attitude.QSoundness

/-! The knowledge-error share of the slew planner's `ε`.  `plan_premise` takes a flown map `A`
with `vangle (A b) (C b) ≤ ε` for every unit `b`, where `C` is the commanded attitude.  When the
controller keeps an estimate within `εc` of `C`, the true attitude lies within `εc + err` of `C`
by the triangle inequality for angles, so `ε = εc + err` meets that hypothesis with the true
attitude as the flown map.  `knowledge_share` states this for TRIAD's estimate `M`, any matrix in
the intervals of a result of status 0, and `qmethod_knowledge` for the q-method's estimate, the
attitude of the output quaternion `q̂`. -/

namespace Demos.Attitude

open Demos.Slew.Spec Demos.Slew.Premise Demos.Slew.Safety Demos.Slew.Rounding Vec

/-- **The knowledge-error share.**  For a result of status 0, an estimate `M` in its intervals, a
map `C` within `εc` of `M`, and a true attitude `R(q)` that meets the error bounds, `R(q)` lies
within `εc + err` of `C`. -/
theorem knowledge_share {b1x b1y b1z b2x b2y b2z r1x r1y r1z r2x r2y r2z e1 e2 : Float}
    (h : (triad b1x b1y b1z b2x b2y b2z r1x r1y r1z r2x r2y r2z e1 e2).status = 0)
    {M : Mat} (hM : InBox (triad b1x b1y b1z b2x b2y b2z r1x r1y r1z r2x r2y r2z e1 e2) M)
    {C : Vec → Vec} {εc : ℝ} (hC : ∀ v : Vec, dot v v = 1 → vangle (M.apply v) (C v) ≤ εc)
    {q : Quat} (hq : 0 < Quat.norm2 q)
    (h1 : vangle (attitude q (unit (vec3 b1x b1y b1z))) (unit (vec3 r1x r1y r1z)) ≤ val e1)
    (h2 : vangle (attitude q (unit (vec3 b2x b2y b2z))) (unit (vec3 r2x r2y r2z)) ≤ val e2) :
    ∀ v : Vec, dot v v = 1 → vangle (attitude q v) (C v) ≤
      εc + val (triad b1x b1y b1z b2x b2y b2z r1x r1y r1z r2x r2y r2z e1 e2).err := by
  intro v hv
  have hk := (triad_bound h).2.2.2.2 q hq h1 h2 M hM v hv
  have t := vangle_triangle (attitude q v) (M.apply v) (C v)
  rw [vangle_comm] at hk
  linarith [hC v hv]

namespace QMethod

/-- **Q6, the knowledge-error share of the q-method.**  For a result of status 0, a map `C` within
`εc` of the attitude of the output quaternion `q̂`, and a true attitude `R(q)` that meets the
error bounds, `R(q)` lies within `εc + err` of `C`. -/
theorem qmethod_knowledge {xs : Array Float} (h : (qmethod xs)[0]! = 0.0) {C : Vec → Vec}
    {εc : ℝ} (hC : Within (attitude (quatAt (qmethod xs) 1)) C εc) {q : Quat}
    (hq : 0 < Quat.norm2 q)
    (hb : ∀ i < count xs, vangle (attitude q (unit (obsAt xs i).b)) (unit (obsAt xs i).r) ≤
      (obsAt xs i).ε) :
    ∀ v : Vec, dot v v = 1 → vangle (attitude q v) (C v) ≤ εc + val (qmethod xs)[6]! := by
  intro v hv
  have hk := (qmethod_sound h).2.2.2.2.2.2.2.2.2.2.2 q hq hb v hv
  have t := vangle_triangle (attitude q v) (attitude (quatAt (qmethod xs) 1) v) (C v)
  rw [vangle_comm] at hk
  linarith [hC v hv]

end QMethod

end Demos.Attitude
