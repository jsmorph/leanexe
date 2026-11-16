import Demos.Conjunction.Projection
import Demos.Conjunction.BoxSoundness

/-!
Soundness of the conjunction-message form.  `pcMessage_enclosure` composes `projection_sound` with
`pcTail_sound`, so that an accepted result of `pcMessage` contains the probability of collision of
the encounter that `encounter` defines from the real values of the inputs, and
`assessMessage_sound` states what each verdict of `assessMessage` implies.
-/

namespace Demos.Conjunction

open LeanExe.ProofKit Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64
open CodeLib.IEEE64 (value Finite)

section

variable {x1 y1 z1 vx1 vy1 vz1 crr1 ctr1 ctt1 cnr1 cnt1 cnn1 x2 y2 z2 vx2 vy2 vz2 crr2 ctr2 ctt2
  cnr2 cnt2 cnn2 : Float}

/-- An accepted result of `pcMessage` contains the probability of collision `Model.pc` of the
encounter of the real inputs, whose covariance in the encounter plane is positive definite, for the
real radius, which is positive, and its upper endpoint is at most 1. -/
theorem pcMessage_enclosure {r : Float} {n : UInt64}
    (h : (pcMessage x1 y1 z1 vx1 vy1 vz1 crr1 ctr1 ctt1 cnr1 cnt1 cnn1 x2 y2 z2 vx2 vy2 vz2 crr2
      ctr2 ctt2 cnr2 cnt2 cnn2 r n).status = 0) :
    let e := encounterOf x1 y1 z1 vx1 vy1 vz1 crr1 ctr1 ctt1 cnr1 cnt1 cnn1 x2 y2 z2 vx2 vy2 vz2
      crr2 ctr2 ctt2 cnr2 cnt2 cnn2
    0 < e.2.2.1 ∧ 0 < Model.det e.2.2.1 e.2.2.2.1 e.2.2.2.2 ∧ 0 < value r.toBits ∧
      Contains (pcMessage x1 y1 z1 vx1 vy1 vz1 crr1 ctr1 ctt1 cnr1 cnt1 cnn1 x2 y2 z2 vx2 vy2 vz2
          crr2 ctr2 ctt2 cnr2 cnt2 cnn2 r n)
        (Model.pc e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2 (value r.toBits)) ∧
      value (pcMessage x1 y1 z1 vx1 vy1 vz1 crr1 ctr1 ctt1 cnr1 cnt1 cnn1 x2 y2 z2 vx2 vy2 vz2
        crr2 ctr2 ctt2 cnr2 cnt2 cnn2 r n).hi.toBits ≤ 1 := by
  intro e
  obtain ⟨E1, E2, E3, E4, E5⟩ := projection_sound x1 y1 z1 vx1 vy1 vz1 crr1 ctr1 ctt1 cnr1 cnt1
    cnn1 x2 y2 z2 vx2 vy2 vz2 crr2 ctr2 ctt2 cnr2 cnt2 cnn2
  exact pcTail_sound (setupBox_sound (r := r) E1 E2 E3 E4 E5) E3 h

/-- An accepted assessment of a message holds the interval of `pcMessage`.  Verdict 1 implies that
the probability of collision of the encounter of the real inputs is below the threshold, and
verdict 2 that it is at least the threshold. -/
theorem assessMessage_sound {r t : Float} {n : UInt64}
    (h : (assessMessage x1 y1 z1 vx1 vy1 vz1 crr1 ctr1 ctt1 cnr1 cnt1 cnn1 x2 y2 z2 vx2 vy2 vz2
      crr2 ctr2 ctt2 cnr2 cnt2 cnn2 r t n).status = 0) :
    let e := encounterOf x1 y1 z1 vx1 vy1 vz1 crr1 ctr1 ctt1 cnr1 cnt1 cnn1 x2 y2 z2 vx2 vy2 vz2
      crr2 ctr2 ctt2 cnr2 cnt2 cnn2
    let p := pcMessage x1 y1 z1 vx1 vy1 vz1 crr1 ctr1 ctt1 cnr1 cnt1 cnn1 x2 y2 z2 vx2 vy2 vz2
      crr2 ctr2 ctt2 cnr2 cnt2 cnn2 r n
    let a := assessMessage x1 y1 z1 vx1 vy1 vz1 crr1 ctr1 ctt1 cnr1 cnt1 cnn1 x2 y2 z2 vx2 vy2 vz2
      crr2 ctr2 ctt2 cnr2 cnt2 cnn2 r t n
    p.status = 0 ∧ a.lo = p.lo ∧ a.hi = p.hi ∧
      (a.verdict = 1 →
        Model.pc e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2 (value r.toBits) < value t.toBits) ∧
      (a.verdict = 2 →
        value t.toBits ≤ Model.pc e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2 (value r.toBits)) := by
  intro e p a
  obtain ⟨gs, hlo, hhi, h1, h2⟩ := judge_sound (t := t)
    (p := pcMessage x1 y1 z1 vx1 vy1 vz1 crr1 ctr1 ctt1 cnr1 cnt1 cnn1 x2 y2 z2 vx2 vy2 vz2 crr2
      ctr2 ctt2 cnr2 cnt2 cnn2 r n) h
  have cp := (pcMessage_enclosure gs).2.2.2.1
  exact ⟨gs, hlo, hhi, fun hv => h1 hv _ cp, fun hv => h2 hv _ cp⟩

end

#print axioms pcMessage_enclosure
#print axioms assessMessage_sound

end Demos.Conjunction
