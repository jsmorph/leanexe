import Demos.Conjunction.Message
import Demos.Conjunction.BoxSoundness

/-!
Soundness of the conjunction-message form.  `projection_sound` states that each accepted interval
of `encounterAt` contains the corresponding quantity of `encounter` for the real values of the
inputs: the miss vector and the covariance in the encounter plane.  `pcMessage_enclosure` composes
it with `pcTail_sound`, so that an accepted result of `pcMessage` contains the probability of
collision of that encounter, and `assessMessage_sound` states what each verdict of
`assessMessage` implies.
-/

namespace Demos.Conjunction

open LeanExe.ProofKit Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64
open CodeLib.IEEE64 (value Finite)

theorem encloses_point (x : Float) : Encloses (point x) (value x.toBits) :=
  fun h => (point_sound h).2

/-- The encounter that `encounter` defines from the real values of the inputs. -/
noncomputable abbrev encounterOf (x1 y1 z1 vx1 vy1 vz1 crr1 ctr1 ctt1 cnr1 cnt1 cnn1 x2 y2 z2 vx2
    vy2 vz2 crr2 ctr2 ctt2 cnr2 cnt2 cnn2 : Float) : ℝ × ℝ × ℝ × ℝ × ℝ :=
  encounter (value x1.toBits) (value y1.toBits) (value z1.toBits) (value vx1.toBits)
    (value vy1.toBits) (value vz1.toBits) (value crr1.toBits) (value ctr1.toBits)
    (value ctt1.toBits) (value cnr1.toBits) (value cnt1.toBits) (value cnn1.toBits)
    (value x2.toBits) (value y2.toBits) (value z2.toBits) (value vx2.toBits) (value vy2.toBits)
    (value vz2.toBits) (value crr2.toBits) (value ctr2.toBits) (value ctt2.toBits)
    (value cnr2.toBits) (value cnt2.toBits) (value cnn2.toBits)

section

variable (x1 y1 z1 vx1 vy1 vz1 crr1 ctr1 ctt1 cnr1 cnt1 cnn1 x2 y2 z2 vx2 vy2 vz2 crr2 ctr2 ctt2
  cnr2 cnt2 cnn2 : Float)

/-- `encounterAt` with the tables of `sin` and `cos` that `encounter.encloses` names, which no
operation of the interval functions reads. -/
theorem encounterAt_eq :
    encounterAt Exp.expTable x1 y1 z1 vx1 vy1 vz1 crr1 ctr1 ctt1 cnr1 cnt1 cnn1 x2 y2 z2 vx2 vy2
      vz2 crr2 ctr2 ctt2 cnr2 cnt2 cnn2 =
    encounterI Trig.invPi Trig.halfPi Exp.expTable Exp.expTable (point x1) (point y1) (point z1)
      (point vx1) (point vy1) (point vz1) (point crr1) (point ctr1) (point ctt1) (point cnr1)
      (point cnt1) (point cnn1) (point x2) (point y2) (point z2) (point vx2) (point vy2)
      (point vz2) (point crr2) (point ctr2) (point ctt2) (point cnr2) (point cnt2)
      (point cnn2) := rfl

/-- Each accepted interval of `encounterAt` contains the corresponding quantity of the encounter
of the real inputs: the two components of the miss vector and the three entries of the
covariance in the encounter plane. -/
theorem projection_sound :
    Encloses (encounterAt Exp.expTable x1 y1 z1 vx1 vy1 vz1 crr1 ctr1 ctt1 cnr1 cnt1 cnn1 x2 y2 z2
        vx2 vy2 vz2 crr2 ctr2 ctt2 cnr2 cnt2 cnn2).1
      (encounterOf x1 y1 z1 vx1 vy1 vz1 crr1 ctr1 ctt1 cnr1 cnt1 cnn1 x2 y2 z2 vx2 vy2 vz2 crr2
        ctr2 ctt2 cnr2 cnt2 cnn2).1 ∧
    Encloses (encounterAt Exp.expTable x1 y1 z1 vx1 vy1 vz1 crr1 ctr1 ctt1 cnr1 cnt1 cnn1 x2 y2 z2
        vx2 vy2 vz2 crr2 ctr2 ctt2 cnr2 cnt2 cnn2).2.1
      (encounterOf x1 y1 z1 vx1 vy1 vz1 crr1 ctr1 ctt1 cnr1 cnt1 cnn1 x2 y2 z2 vx2 vy2 vz2 crr2
        ctr2 ctt2 cnr2 cnt2 cnn2).2.1 ∧
    Encloses (encounterAt Exp.expTable x1 y1 z1 vx1 vy1 vz1 crr1 ctr1 ctt1 cnr1 cnt1 cnn1 x2 y2 z2
        vx2 vy2 vz2 crr2 ctr2 ctt2 cnr2 cnt2 cnn2).2.2.1
      (encounterOf x1 y1 z1 vx1 vy1 vz1 crr1 ctr1 ctt1 cnr1 cnt1 cnn1 x2 y2 z2 vx2 vy2 vz2 crr2
        ctr2 ctt2 cnr2 cnt2 cnn2).2.2.1 ∧
    Encloses (encounterAt Exp.expTable x1 y1 z1 vx1 vy1 vz1 crr1 ctr1 ctt1 cnr1 cnt1 cnn1 x2 y2 z2
        vx2 vy2 vz2 crr2 ctr2 ctt2 cnr2 cnt2 cnn2).2.2.2.1
      (encounterOf x1 y1 z1 vx1 vy1 vz1 crr1 ctr1 ctt1 cnr1 cnt1 cnn1 x2 y2 z2 vx2 vy2 vz2 crr2
        ctr2 ctt2 cnr2 cnt2 cnn2).2.2.2.1 ∧
    Encloses (encounterAt Exp.expTable x1 y1 z1 vx1 vy1 vz1 crr1 ctr1 ctt1 cnr1 cnt1 cnn1 x2 y2 z2
        vx2 vy2 vz2 crr2 ctr2 ctt2 cnr2 cnt2 cnn2).2.2.2.2
      (encounterOf x1 y1 z1 vx1 vy1 vz1 crr1 ctr1 ctt1 cnr1 cnt1 cnn1 x2 y2 z2 vx2 vy2 vz2 crr2
        ctr2 ctt2 cnr2 cnt2 cnn2).2.2.2.2 := by
  rw [encounterAt_eq]
  exact encounter.encloses (powLog := Exp.expTable) (powExp := Exp.expTable) (encloses_point x1)
    (encloses_point y1) (encloses_point z1) (encloses_point vx1) (encloses_point vy1)
    (encloses_point vz1) (encloses_point crr1) (encloses_point ctr1) (encloses_point ctt1)
    (encloses_point cnr1) (encloses_point cnt1) (encloses_point cnn1) (encloses_point x2)
    (encloses_point y2) (encloses_point z2) (encloses_point vx2) (encloses_point vy2)
    (encloses_point vz2) (encloses_point crr2) (encloses_point ctr2) (encloses_point ctt2)
    (encloses_point cnr2) (encloses_point cnt2) (encloses_point cnn2)

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

#print axioms projection_sound
#print axioms pcMessage_enclosure
#print axioms assessMessage_sound

end Demos.Conjunction
