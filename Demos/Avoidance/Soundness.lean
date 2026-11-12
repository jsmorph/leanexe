import Demos.Avoidance.Program
import Demos.Avoidance.Geometry
import Demos.Conjunction.BoxSoundness
import Demos.PassiveSafety.Soundness
import LeanExe.Dialect.Lemmas
import LeanExe.Dialect.ArrayLemmas

/-!
Soundness of the authorizer.  `encounter xs j dv d` is the model's encounter of conjunction `j`
for the real values of the input, the velocity change `dv`, and the displacement `d`, and
`pcAfter xs j dv d` its probability of collision.  `authorize_sound` (A1) states that status 0
implies, for every conjunction, every velocity change of the box, and every displacement within
the padding, the conditions under which the model's propagation solves Newton's equation and the
plane's axes are orthonormal, and a probability below the threshold.  `authorize_enclosure` (A2)
states the interval and the verdict of each conjunction, and `authorize_above` (A4) that verdict
1 places the probability at or above the threshold for some velocity change of the box.  The
proof follows the program: `afterAt_encloses` encloses the encounter by `after.encloses`,
`assessCell_sound` adds the checks and `Demos.Conjunction.pcBoxWith_enclosure`, `search_inv`
keeps the invariant of the search over the cells, `finish_sound` collects the cells, and
`allBelow_spec` collects the conjunctions.
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

/-! ### One cell -/

theorem idx {j : UInt64} (hj : j.toNat < 64) (c : UInt64) (hc : c.toNat ≤ 19) :
    (15 + 20 * j + c).toNat = 15 + 20 * j.toNat + c.toNat := by
  simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.reduceToNat]
  omega

theorem idx0 {j : UInt64} (hj : j.toNat < 64) : (15 + 20 * j).toNat = 15 + 20 * j.toNat := by
  simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.reduceToNat]
  omega

theorem encloses_point (x : Float) : Encloses (point x) (value x.toBits) :=
  fun h => (point_sound h).2

/-- The centered projection with the middles of the axes' intervals as centers encloses the plain
projection on the axes. -/
theorem project_mid {px py pz c1 c2 c3 c4 c5 c6 : Interval}
    {A : Interval × Interval × Interval × Interval × Interval × Interval × Interval × Interval}
    {qx qy qz d1 d2 d3 d4 d5 d6 : ℝ} {a : ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ}
    (hx : Encloses px qx) (hy : Encloses py qy) (hz : Encloses pz qz)
    (ha : (enclosure_relation% 8) A a) (h1 : Encloses c1 d1) (h2 : Encloses c2 d2)
    (h3 : Encloses c3 d3) (h4 : Encloses c4 d4) (h5 : Encloses c5 d5) (h6 : Encloses c6 d6) :
    (enclosure_relation% 5)
      (projectI Trig.invPi Trig.halfPi Trig.invPi Trig.invPi px py pz A.1 A.2.1 A.2.2.1 A.2.2.2.1
        A.2.2.2.2.1 A.2.2.2.2.2.1 (point (mid A.1)) (point (mid A.2.1)) (point (mid A.2.2.1))
        (point (mid A.2.2.2.1)) (point (mid A.2.2.2.2.1)) (point (mid A.2.2.2.2.2.1)) c1 c2 c3 c4
        c5 c6)
      (qx * a.1 + qy * a.2.1 + qz * a.2.2.1, qx * a.2.2.2.1 + qy * a.2.2.2.2.1 + qz * a.2.2.2.2.2.1,
        a.1 * (d1 * a.1 + d2 * a.2.1 + d3 * a.2.2.1) + a.2.1 * (d2 * a.1 + d4 * a.2.1 + d5 * a.2.2.1) +
          a.2.2.1 * (d3 * a.1 + d5 * a.2.1 + d6 * a.2.2.1),
        a.1 * (d1 * a.2.2.2.1 + d2 * a.2.2.2.2.1 + d3 * a.2.2.2.2.2.1) +
          a.2.1 * (d2 * a.2.2.2.1 + d4 * a.2.2.2.2.1 + d5 * a.2.2.2.2.2.1) +
          a.2.2.1 * (d3 * a.2.2.2.1 + d5 * a.2.2.2.2.1 + d6 * a.2.2.2.2.2.1),
        a.2.2.2.1 * (d1 * a.2.2.2.1 + d2 * a.2.2.2.2.1 + d3 * a.2.2.2.2.2.1) +
          a.2.2.2.2.1 * (d2 * a.2.2.2.1 + d4 * a.2.2.2.2.1 + d5 * a.2.2.2.2.2.1) +
          a.2.2.2.2.2.1 * (d3 * a.2.2.2.1 + d5 * a.2.2.2.2.1 + d6 * a.2.2.2.2.2.1)) := by
  have h := project.encloses (powLog := Trig.invPi) (powExp := Trig.invPi) hx hy hz ha.1 ha.2.1
    ha.2.2.1 ha.2.2.2.1 ha.2.2.2.2.1 ha.2.2.2.2.2.1 (encloses_point (mid A.1))
    (encloses_point (mid A.2.1)) (encloses_point (mid A.2.2.1)) (encloses_point (mid A.2.2.2.1))
    (encloses_point (mid A.2.2.2.2.1)) (encloses_point (mid A.2.2.2.2.2.1)) h1 h2 h3 h4 h5 h6
  rw [project_eq] at h
  exact h

/-- The computation of `afterAt` over interval arguments: the relative state, the shapes of both
states, the axes, and the projection centered at the middles of the axes' intervals. -/
def afterCI (inv half : Array UInt64) (mu rbx rby rbz vbx vby vbz dvx dvy dvz dt r1x r1y r1z v1x v1y
    v1z r2x r2y r2z v2x v2y v2z cxx cxy cxz cyy cyz czz dx dy dz : Interval) :
    Interval × Interval × Interval × Interval × Interval × Interval × Interval × Interval ×
      Interval × Interval × Interval :=
  let rel := relativeI inv half inv inv mu rbx rby rbz vbx vby vbz dvx dvy dvz dt r1x r1y r1z v1x
    v1y v1z r2x r2y r2z v2x v2y v2z dx dy dz
  let s1 := shapeI inv half inv inv mu rbx rby rbz (add vbx dvx) (add vby dvy) (add vbz dvz)
  let s0 := shapeI inv half inv inv mu rbx rby rbz vbx vby vbz
  let ax := axesI inv half inv inv rel.2.2.2.1 rel.2.2.2.2.1 rel.2.2.2.2.2 r1x r1y r1z
  let pr := projectI inv half inv inv rel.1 rel.2.1 rel.2.2.1 ax.1 ax.2.1 ax.2.2.1 ax.2.2.2.1
    ax.2.2.2.2.1 ax.2.2.2.2.2.1 (point (mid ax.1)) (point (mid ax.2.1)) (point (mid ax.2.2.1))
    (point (mid ax.2.2.2.1)) (point (mid ax.2.2.2.2.1)) (point (mid ax.2.2.2.2.2.1)) cxx cxy cxz cyy
    cyz czz
  (pr.1, pr.2.1, pr.2.2.1, pr.2.2.2.1, pr.2.2.2.2, s1.1, s1.2, s0.1, s0.2, ax.2.2.2.2.2.2.1,
    ax.2.2.2.2.2.2.2)

theorem afterAt_eq (xs : Array Float) (j : UInt64) (dvx dvy dvz pad : Interval) :
    afterAt Trig.invPi Trig.halfPi xs j dvx dvy dvz pad =
      afterCI Trig.invPi Trig.halfPi (point (rd xs 0)) (point (rd xs 1)) (point (rd xs 2))
        (point (rd xs 3)) (point (rd xs 4)) (point (rd xs 5)) (point (rd xs 6)) dvx dvy dvz
        (point (rd xs (15 + 20 * j))) (point (rd xs (15 + 20 * j + 1)))
        (point (rd xs (15 + 20 * j + 2))) (point (rd xs (15 + 20 * j + 3)))
        (point (rd xs (15 + 20 * j + 4))) (point (rd xs (15 + 20 * j + 5)))
        (point (rd xs (15 + 20 * j + 6))) (point (rd xs (15 + 20 * j + 7)))
        (point (rd xs (15 + 20 * j + 8))) (point (rd xs (15 + 20 * j + 9)))
        (point (rd xs (15 + 20 * j + 10))) (point (rd xs (15 + 20 * j + 11)))
        (point (rd xs (15 + 20 * j + 12))) (point (rd xs (15 + 20 * j + 13)))
        (point (rd xs (15 + 20 * j + 14))) (point (rd xs (15 + 20 * j + 15)))
        (point (rd xs (15 + 20 * j + 16))) (point (rd xs (15 + 20 * j + 17)))
        (point (rd xs (15 + 20 * j + 18))) pad pad pad := rfl

/-- `after` with the plane written through `axes`: the miss vector and the plain projection of the
covariance on the axes of `axes`. -/
noncomputable def afterPlain (mu rbx rby rbz vbx vby vbz dvx dvy dvz dt r1x r1y r1z v1x v1y v1z r2x
    r2y r2z v2x v2y v2z cxx cxy cxz cyy cyz czz dx dy dz : ℝ) :
    ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ :=
  let rel := relative mu rbx rby rbz vbx vby vbz dvx dvy dvz dt r1x r1y r1z v1x v1y v1z r2x r2y r2z
    v2x v2y v2z dx dy dz
  let a := axes rel.2.2.2.1 rel.2.2.2.2.1 rel.2.2.2.2.2 r1x r1y r1z
  (rel.1 * a.1 + rel.2.1 * a.2.1 + rel.2.2.1 * a.2.2.1,
    rel.1 * a.2.2.2.1 + rel.2.1 * a.2.2.2.2.1 + rel.2.2.1 * a.2.2.2.2.2.1,
    a.1 * (cxx * a.1 + cxy * a.2.1 + cxz * a.2.2.1) + a.2.1 * (cxy * a.1 + cyy * a.2.1 + cyz * a.2.2.1) +
      a.2.2.1 * (cxz * a.1 + cyz * a.2.1 + czz * a.2.2.1),
    a.1 * (cxx * a.2.2.2.1 + cxy * a.2.2.2.2.1 + cxz * a.2.2.2.2.2.1) +
      a.2.1 * (cxy * a.2.2.2.1 + cyy * a.2.2.2.2.1 + cyz * a.2.2.2.2.2.1) +
      a.2.2.1 * (cxz * a.2.2.2.1 + cyz * a.2.2.2.2.1 + czz * a.2.2.2.2.2.1),
    a.2.2.2.1 * (cxx * a.2.2.2.1 + cxy * a.2.2.2.2.1 + cxz * a.2.2.2.2.2.1) +
      a.2.2.2.2.1 * (cxy * a.2.2.2.1 + cyy * a.2.2.2.2.1 + cyz * a.2.2.2.2.2.1) +
      a.2.2.2.2.2.1 * (cxz * a.2.2.2.1 + cyz * a.2.2.2.2.1 + czz * a.2.2.2.2.2.1),
    (shape mu rbx rby rbz (vbx + dvx) (vby + dvy) (vbz + dvz)).1,
    (shape mu rbx rby rbz (vbx + dvx) (vby + dvy) (vbz + dvz)).2,
    (shape mu rbx rby rbz vbx vby vbz).1, (shape mu rbx rby rbz vbx vby vbz).2,
    a.2.2.2.2.2.2.1, a.2.2.2.2.2.2.2)

theorem after_eq_plain (mu rbx rby rbz vbx vby vbz dvx dvy dvz dt r1x r1y r1z v1x v1y v1z r2x r2y
    r2z v2x v2y v2z cxx cxy cxz cyy cyz czz dx dy dz : ℝ) :
    after mu rbx rby rbz vbx vby vbz dvx dvy dvz dt r1x r1y r1z v1x v1y v1z r2x r2y r2z v2x v2y v2z
        cxx cxy cxz cyy cyz czz dx dy dz =
      afterPlain mu rbx rby rbz vbx vby vbz dvx dvy dvz dt r1x r1y r1z v1x v1y v1z r2x r2y r2z v2x
        v2y v2z cxx cxy cxz cyy cyz czz dx dy dz := by
  simp only [after, afterPlain, plane, axes]

/-- `afterCI` encloses `after` when each interval argument encloses the real argument. -/
theorem afterCI_encloses {mu rbx rby rbz vbx vby vbz dvx dvy dvz dt r1x r1y r1z v1x v1y v1z r2x r2y
    r2z v2x v2y v2z cxx cxy cxz cyy cyz czz dx dy dz : Interval}
    {mu' rbx' rby' rbz' vbx' vby' vbz' dvx' dvy' dvz' dt' r1x' r1y' r1z' v1x' v1y' v1z' r2x' r2y'
      r2z' v2x' v2y' v2z' cxx' cxy' cxz' cyy' cyz' czz' dx' dy' dz' : ℝ}
    (h_mu : Encloses mu mu') (h_rbx : Encloses rbx rbx') (h_rby : Encloses rby rby')
    (h_rbz : Encloses rbz rbz') (h_vbx : Encloses vbx vbx') (h_vby : Encloses vby vby')
    (h_vbz : Encloses vbz vbz') (h_dvx : Encloses dvx dvx') (h_dvy : Encloses dvy dvy')
    (h_dvz : Encloses dvz dvz') (h_dt : Encloses dt dt') (h_r1x : Encloses r1x r1x')
    (h_r1y : Encloses r1y r1y') (h_r1z : Encloses r1z r1z') (h_v1x : Encloses v1x v1x')
    (h_v1y : Encloses v1y v1y') (h_v1z : Encloses v1z v1z') (h_r2x : Encloses r2x r2x')
    (h_r2y : Encloses r2y r2y') (h_r2z : Encloses r2z r2z') (h_v2x : Encloses v2x v2x')
    (h_v2y : Encloses v2y v2y') (h_v2z : Encloses v2z v2z') (h_cxx : Encloses cxx cxx')
    (h_cxy : Encloses cxy cxy') (h_cxz : Encloses cxz cxz') (h_cyy : Encloses cyy cyy')
    (h_cyz : Encloses cyz cyz') (h_czz : Encloses czz czz') (h_dx : Encloses dx dx')
    (h_dy : Encloses dy dy') (h_dz : Encloses dz dz') :
    (enclosure_relation% 11)
      (afterCI Trig.invPi Trig.halfPi mu rbx rby rbz vbx vby vbz dvx dvy dvz dt r1x r1y r1z v1x v1y
        v1z r2x r2y r2z v2x v2y v2z cxx cxy cxz cyy cyz czz dx dy dz)
      (after mu' rbx' rby' rbz' vbx' vby' vbz' dvx' dvy' dvz' dt' r1x' r1y' r1z' v1x' v1y' v1z'
        r2x' r2y' r2z' v2x' v2y' v2z' cxx' cxy' cxz' cyy' cyz' czz' dx' dy' dz') := by
  have Er := relative.encloses (powLog := Trig.invPi) (powExp := Trig.invPi) h_mu h_rbx h_rby
    h_rbz h_vbx h_vby h_vbz h_dvx h_dvy h_dvz h_dt h_r1x h_r1y h_r1z h_v1x h_v1y h_v1z h_r2x h_r2y
    h_r2z h_v2x h_v2y h_v2z h_dx h_dy h_dz
  have Es1 := shape.encloses (powLog := Trig.invPi) (powExp := Trig.invPi) h_mu h_rbx h_rby h_rbz
    (encloses_add h_vbx h_dvx) (encloses_add h_vby h_dvy) (encloses_add h_vbz h_dvz)
  have Es0 := shape.encloses (powLog := Trig.invPi) (powExp := Trig.invPi) h_mu h_rbx h_rby h_rbz
    h_vbx h_vby h_vbz
  have Ea := axes.encloses (powLog := Trig.invPi) (powExp := Trig.invPi) Er.2.2.2.1 Er.2.2.2.2.1
    Er.2.2.2.2.2 h_r1x h_r1y h_r1z
  have Ep := project_mid Er.1 Er.2.1 Er.2.2.1 Ea h_cxx h_cxy h_cxz h_cyy h_cyz h_czz
  rw [after_eq_plain]
  unfold afterPlain afterCI
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only
  exacts [Ep.1, Ep.2.1, Ep.2.2.1, Ep.2.2.2.1, Ep.2.2.2.2, Es1.1, Es1.2, Es0.1, Es0.2,
    Ea.2.2.2.2.2.2.1, Ea.2.2.2.2.2.2.2]

/-- The intervals of `afterAt` enclose the model's encounter for every velocity change and every
displacement that the interval arguments enclose. -/
theorem afterAt_encloses {xs : Array Float} {j : UInt64} (hj : j.toNat < 64)
    {dvx dvy dvz pad : Interval} {dv d : V3} (hx : Encloses dvx dv.x) (hy : Encloses dvy dv.y)
    (hz : Encloses dvz dv.z) (hd : Encloses pad d.x ∧ Encloses pad d.y ∧ Encloses pad d.z) :
    (enclosure_relation% 11) (afterAt Trig.invPi Trig.halfPi xs j dvx dvy dvz pad)
      (afterIn xs j.toNat dv d) := by
  have pb : ∀ c : UInt64, c.toNat ≤ 19 →
      Encloses (point (rd xs (15 + 20 * j + c))) (val xs (15 + 20 * j.toNat + c.toNat)) :=
    fun c hc => by rw [← idx hj c hc]; exact encloses_point _
  have p0 : Encloses (point (rd xs (15 + 20 * j))) (val xs (15 + 20 * j.toNat)) := by
    rw [← idx0 hj]; exact encloses_point _
  rw [afterAt_eq]
  exact afterCI_encloses (encloses_point _) (encloses_point _) (encloses_point _)
    (encloses_point _) (encloses_point _) (encloses_point _) (encloses_point _) hx hy hz p0
    (pb 1 (by decide)) (pb 2 (by decide)) (pb 3 (by decide)) (pb 4 (by decide))
    (pb 5 (by decide)) (pb 6 (by decide)) (pb 7 (by decide)) (pb 8 (by decide))
    (pb 9 (by decide)) (pb 10 (by decide)) (pb 11 (by decide)) (pb 12 (by decide))
    (pb 13 (by decide)) (pb 14 (by decide)) (pb 15 (by decide)) (pb 16 (by decide))
    (pb 17 (by decide)) (pb 18 (by decide)) hd.1 hd.2.1 hd.2.2

/-- An accepted interval of `assessCell` gives the conditions of the model's theorems and
contains the model's probability for every velocity change and every displacement that the
interval arguments enclose. -/
theorem assessCell_sound {xs : Array Float} {n j : UInt64} (hj : j.toNat < 64)
    {dvx dvy dvz pad : Interval}
    (h : (assessCell Exp.expTable Trig.invPi Trig.halfPi xs n j dvx dvy dvz pad).status = 0)
    {dv d : V3} (hx : Encloses dvx dv.x) (hy : Encloses dvy dv.y) (hz : Encloses dvz dv.z)
    (hd : Encloses pad d.x ∧ Encloses pad d.y ∧ Encloses pad d.z) :
    Good xs j.toNat dv d ∧
      Contains (assessCell Exp.expTable Trig.invPi Trig.halfPi xs n j dvx dvy dvz pad)
        (pcAfter xs j.toNat dv d) := by
  have E := afterAt_encloses (xs := xs) hj hx hy hz hd
  have hR : value (rd xs (15 + 20 * j + 19)).toBits = val xs (34 + 20 * j.toNat) := by
    rw [val_rd, idx hj 19 (by decide)]
    congr 1
    simp only [UInt64.reduceToNat]
    omega
  unfold assessCell at h ⊢
  dsimp only at h ⊢
  generalize afterAt Trig.invPi Trig.halfPi xs j dvx dvy dvz pad = A at h E ⊢
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

/-! ### Cells -/

/-- The velocity change `dv` lies in the cell. -/
def InCell (c : Cell) (dv : V3) : Prop :=
  value c.lx.toBits ≤ dv.x ∧ dv.x ≤ value c.hx.toBits ∧ value c.ly.toBits ≤ dv.y ∧
    dv.y ≤ value c.hy.toBits ∧ value c.lz.toBits ≤ dv.z ∧ dv.z ≤ value c.hz.toBits

/-- An accepted `r` contains the probability of conjunction `j` for every velocity change of the
cell and every displacement within the padding, where the model's conditions hold. -/
def Sound (xs : Array Float) (j : Nat) (c : Cell) (r : Interval) : Prop :=
  r.status = 0 → ∀ dv d, InCell c dv → InPad xs d →
    Good xs j dv d ∧ Contains r (pcAfter xs j dv d)

theorem Sound.mono {xs : Array Float} {j : Nat} {c c' : Cell} {r : Interval}
    (h : ∀ dv, InCell c' dv → InCell c dv) (hs : Sound xs j c r) : Sound xs j c' r :=
  fun h0 dv d hc hd => hs h0 dv d (h dv hc) hd

/-- A cell of the search: finite ends in order, inside the box, with a sound interval. -/
structure CellOk (xs : Array Float) (j : Nat) (c : Cell) : Prop where
  fin : Finite c.lx.toBits ∧ Finite c.hx.toBits ∧ Finite c.ly.toBits ∧ Finite c.hy.toBits ∧
    Finite c.lz.toBits ∧ Finite c.hz.toBits
  order : value c.lx.toBits ≤ value c.hx.toBits ∧ value c.ly.toBits ≤ value c.hy.toBits ∧
    value c.lz.toBits ≤ value c.hz.toBits
  within : ∀ dv, InCell c dv → InBox xs dv
  bound : Sound xs j c c.bound

/-- The lower corner of a cell. -/
noncomputable def corner (c : Cell) : V3 :=
  ⟨value c.lx.toBits, value c.ly.toBits, value c.lz.toBits⟩

theorem corner_in {xs : Array Float} {j : Nat} {c : Cell} (h : CellOk xs j c) :
    InCell c (corner c) :=
  ⟨le_rfl, h.order.1, le_rfl, h.order.2.1, le_rfl, h.order.2.2⟩

theorem inPad_zero {xs : Array Float} (h : 0 ≤ val xs 13) : InPad xs 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> simpa using h

/-- An accepted sound interval of a cell has finite ends. -/
theorem Sound.finite {xs : Array Float} {j : Nat} {c : Cell} {r : Interval} (hc : CellOk xs j c)
    (hs : Sound xs j c r) (hP0 : 0 ≤ val xs 13) (h : r.status = 0) :
    Finite r.lo.toBits ∧ Finite r.hi.toBits :=
  let C := (hs h (corner c) 0 (corner_in hc) (inPad_zero hP0)).2
  ⟨C.2.1, C.2.2.1⟩

theorem evalCell_sound {xs : Array Float} {n j : UInt64} (hj : j.toNat < 64)
    (hP : Finite (rd xs 13).toBits) (c : Cell) :
    Sound xs j.toNat c (evalCell Exp.expTable Trig.invPi Trig.halfPi xs n j c) := by
  intro h dv d hc hd
  unfold evalCell at h ⊢
  obtain ⟨-, vn⟩ := neg_value hP
  have pad : ∀ x : ℝ, |x| ≤ val xs 13 → Encloses (make (-rd xs 13) (rd xs 13)) x := fun x hx =>
    Demos.Conjunction.encloses_make (by rw [vn]; exact (abs_le.mp hx).1) (abs_le.mp hx).2
  exact assessCell_sound hj h (Demos.Conjunction.encloses_make hc.1 hc.2.1)
    (Demos.Conjunction.encloses_make hc.2.2.1 hc.2.2.2.1)
    (Demos.Conjunction.encloses_make hc.2.2.2.2.1 hc.2.2.2.2.2)
    ⟨pad _ hd.1, pad _ hd.2.1, pad _ hd.2.2⟩

/-- The center of a cell. -/
noncomputable def center (c : Cell) : V3 :=
  ⟨value (Demos.Screening.middle c.lx c.hx).toBits, value (Demos.Screening.middle c.ly c.hy).toBits,
    value (Demos.Screening.middle c.lz c.hz).toBits⟩

theorem inside_spec {lo hi m : Float} (fl : Finite lo.toBits) (fh : Finite hi.toBits)
    (h : inside lo hi m = true) :
    value lo.toBits ≤ value m.toBits ∧ value m.toBits ≤ value hi.toBits := by
  simp only [inside, Bool.and_eq_true] at h
  obtain ⟨⟨hf, h1⟩, h2⟩ := h
  have fm := (finite_iff m).mp hf
  exact ⟨(le_iff_value fl fm).mp (of_decide_eq_true h1),
    (le_iff_value fm fh).mp (of_decide_eq_true h2)⟩

/-- An accepted probe gives the model's conditions and contains the probability at the center of
the cell with no displacement, and the center lies in the cell. -/
theorem probe_sound {xs : Array Float} {n j : UInt64} (hj : j.toNat < 64) {c : Cell}
    (hc : CellOk xs j.toNat c)
    (h : (probe Exp.expTable Trig.invPi Trig.halfPi xs n j c).status = 0) :
    InCell c (center c) ∧ Good xs j.toNat (center c) 0 ∧
      Contains (probe Exp.expTable Trig.invPi Trig.halfPi xs n j c)
        (pcAfter xs j.toNat (center c) 0) := by
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := hc.fin
  unfold probe at h ⊢
  dsimp only at h ⊢
  by_cases g : (inside c.lx c.hx (Demos.Screening.middle c.lx c.hx) &&
      inside c.ly c.hy (Demos.Screening.middle c.ly c.hy) &&
      inside c.lz c.hz (Demos.Screening.middle c.lz c.hz)) = true
  · simp only [g, ite_true] at h ⊢
    simp only [Bool.and_eq_true] at g
    obtain ⟨⟨gx, gy⟩, gz⟩ := g
    obtain ⟨x1, x2⟩ := inside_spec f1 f2 gx
    obtain ⟨y1, y2⟩ := inside_spec f3 f4 gy
    obtain ⟨z1, z2⟩ := inside_spec f5 f6 gz
    have h0 : Encloses (point 0.0) (0 : ℝ) := by
      have := encloses_point 0.0
      rwa [Demos.Conjunction.lit_zero.2] at this
    obtain ⟨G, C⟩ := assessCell_sound (dv := center c) (d := 0) hj h (encloses_point _)
      (encloses_point _) (encloses_point _) ⟨h0, h0, h0⟩
    exact ⟨⟨x1, x2, y1, y2, z1, z2⟩, G, C⟩
  · simp only [g, Bool.false_eq_true, ite_false] at h
    exact absurd h (by decide)

/-- The sides of a cell are finite. -/
theorem sideLo_finite {c : Cell} (hf : Finite c.lx.toBits ∧ Finite c.hx.toBits ∧
    Finite c.ly.toBits ∧ Finite c.hy.toBits ∧ Finite c.lz.toBits ∧ Finite c.hz.toBits)
    (k : UInt64) : Finite (sideLo c k).toBits ∧ Finite (sideHi c k).toBits := by
  unfold sideLo sideHi
  split_ifs
  · exact ⟨hf.1, hf.2.1⟩
  · exact ⟨hf.2.2.1, hf.2.2.2.1⟩
  · exact ⟨hf.2.2.2.2.1, hf.2.2.2.2.2⟩

/-- The facts of `splits`: a finite middle strictly inside the longest side. -/
theorem splits_facts {xs : Array Float} {j : Nat} {c : Cell} (hc : CellOk xs j c)
    (hs : splits c = true) :
    Finite (Demos.Screening.middle (sideLo c (side c)) (sideHi c (side c))).toBits ∧
      value (sideLo c (side c)).toBits <
        value (Demos.Screening.middle (sideLo c (side c)) (sideHi c (side c))).toBits ∧
      value (Demos.Screening.middle (sideLo c (side c)) (sideHi c (side c))).toBits <
        value (sideHi c (side c)).toBits := by
  simp only [splits, Bool.and_eq_true] at hs
  obtain ⟨⟨hf, h1⟩, h2⟩ := hs
  have fm := (finite_iff _).mp hf
  obtain ⟨fl, fh⟩ := sideLo_finite hc.fin (side c)
  exact ⟨fm, (lt_iff_value fl fm).mp (of_decide_eq_true h1),
    (lt_iff_value fm fh).mp (of_decide_eq_true h2)⟩

/-- The two halves of a cell at a finite `m` strictly inside a side are cells of the search with
the interval `r` of the cell, and every point of the cell lies in one of them. -/
theorem halves {xs : Array Float} {j : Nat} {c : Cell} (hc : CellOk xs j c) {k : UInt64}
    {m : Float} {r : Interval} (fm : Finite m.toBits)
    (l1 : value (sideLo c k).toBits < value m.toBits)
    (l2 : value m.toBits < value (sideHi c k).toBits) (hr : Sound xs j c r) :
    CellOk xs j (lowerHalf c k m r) ∧ CellOk xs j (upperHalf c k m r) ∧
      ∀ dv, InCell c dv → InCell (lowerHalf c k m r) dv ∨ InCell (upperHalf c k m r) dv := by
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := hc.fin
  obtain ⟨o1, o2, o3⟩ := hc.order
  unfold sideLo at l1
  unfold sideHi at l2
  unfold lowerHalf upperHalf
  split_ifs at l1 l2 ⊢
  · have sl : ∀ dv, InCell { c with hx := m, bound := r, depth := c.depth + 1 } dv → InCell c dv :=
      fun dv ⟨a1, a2, a3, a4, a5, a6⟩ => ⟨a1, a2.trans l2.le, a3, a4, a5, a6⟩
    have su : ∀ dv, InCell { c with lx := m, bound := r, depth := c.depth + 1 } dv → InCell c dv :=
      fun dv ⟨a1, a2, a3, a4, a5, a6⟩ => ⟨l1.le.trans a1, a2, a3, a4, a5, a6⟩
    refine ⟨⟨⟨f1, fm, f3, f4, f5, f6⟩, ⟨l1.le, o2, o3⟩, fun dv h => hc.within dv (sl dv h),
        hr.mono sl⟩,
      ⟨⟨fm, f2, f3, f4, f5, f6⟩, ⟨l2.le, o2, o3⟩, fun dv h => hc.within dv (su dv h),
        hr.mono su⟩, fun dv ⟨a1, a2, a3, a4, a5, a6⟩ => ?_⟩
    rcases le_total dv.x (value m.toBits) with e | e
    · exact Or.inl ⟨a1, e, a3, a4, a5, a6⟩
    · exact Or.inr ⟨e, a2, a3, a4, a5, a6⟩
  · have sl : ∀ dv, InCell { c with hy := m, bound := r, depth := c.depth + 1 } dv → InCell c dv :=
      fun dv ⟨a1, a2, a3, a4, a5, a6⟩ => ⟨a1, a2, a3, a4.trans l2.le, a5, a6⟩
    have su : ∀ dv, InCell { c with ly := m, bound := r, depth := c.depth + 1 } dv → InCell c dv :=
      fun dv ⟨a1, a2, a3, a4, a5, a6⟩ => ⟨a1, a2, l1.le.trans a3, a4, a5, a6⟩
    refine ⟨⟨⟨f1, f2, f3, fm, f5, f6⟩, ⟨o1, l1.le, o3⟩, fun dv h => hc.within dv (sl dv h),
        hr.mono sl⟩,
      ⟨⟨f1, f2, fm, f4, f5, f6⟩, ⟨o1, l2.le, o3⟩, fun dv h => hc.within dv (su dv h),
        hr.mono su⟩, fun dv ⟨a1, a2, a3, a4, a5, a6⟩ => ?_⟩
    rcases le_total dv.y (value m.toBits) with e | e
    · exact Or.inl ⟨a1, a2, a3, e, a5, a6⟩
    · exact Or.inr ⟨a1, a2, e, a4, a5, a6⟩
  · have sl : ∀ dv, InCell { c with hz := m, bound := r, depth := c.depth + 1 } dv → InCell c dv :=
      fun dv ⟨a1, a2, a3, a4, a5, a6⟩ => ⟨a1, a2, a3, a4, a5, a6.trans l2.le⟩
    have su : ∀ dv, InCell { c with lz := m, bound := r, depth := c.depth + 1 } dv → InCell c dv :=
      fun dv ⟨a1, a2, a3, a4, a5, a6⟩ => ⟨a1, a2, a3, a4, l1.le.trans a5, a6⟩
    refine ⟨⟨⟨f1, f2, f3, f4, f5, fm⟩, ⟨o1, o2, l1.le⟩, fun dv h => hc.within dv (sl dv h),
        hr.mono sl⟩,
      ⟨⟨f1, f2, f3, f4, fm, f6⟩, ⟨o1, o2, l2.le⟩, fun dv h => hc.within dv (su dv h),
        hr.mono su⟩, fun dv ⟨a1, a2, a3, a4, a5, a6⟩ => ?_⟩
    rcases le_total dv.z (value m.toBits) with e | e
    · exact Or.inl ⟨a1, a2, a3, a4, a5, e⟩
    · exact Or.inr ⟨a1, a2, a3, a4, e, a6⟩

theorem shown_spec {tab inv half : Array UInt64} {xs : Array Float} {n j : UInt64} {t : Float}
    {c : Cell} (h : shown tab inv half xs n j t c = true) :
    (probe tab inv half xs n j c).status = 0 ∧ t ≤ (probe tab inv half xs n j c).lo := by
  unfold shown at h
  dsimp only at h
  split_ifs at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact h

theorem action_two {tab inv half : Array UInt64} {xs : Array Float} {n j : UInt64} {t : Float}
    {c : Cell} {r : Interval} {b : UInt64} (h : action tab inv half xs n j t c r b = 2) :
    b ≠ 0 ∧ splits c = true := by
  unfold action at h
  split_ifs at h with h1 h2 h3 h4 h5 <;>
    first
    | exact absurd h (by decide)
    | (simp only [bne_iff_ne, ne_eq] at h3; exact ⟨h3, h5⟩)

theorem action_one {tab inv half : Array UInt64} {xs : Array Float} {n j : UInt64} {t : Float}
    {c : Cell} {r : Interval} {b : UInt64} (h : action tab inv half xs n j t c r b = 1) :
    (r.status = 0 ∧ t ≤ r.lo) ∨
      ((probe tab inv half xs n j c).status = 0 ∧ t ≤ (probe tab inv half xs n j c).lo) := by
  unfold action at h
  split_ifs at h with h1 h2 h3 h4 h5 <;>
    first
    | exact absurd h (by decide)
    | (simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h2; exact Or.inl h2)
    | exact Or.inr (shown_spec h4)

/-! ### The hull -/

/-- When the hull holds an interval and is accepted, its ends are finite. -/
def HullOk (h : Interval) (seen : Bool) : Prop :=
  seen = true → h.status = 0 → Finite h.lo.toBits ∧ Finite h.hi.toBits

/-- The hull holds an interval that contains the probability at `dv` for every displacement
within the padding, where the model's conditions hold, when it is accepted. -/
def Folded (xs : Array Float) (j : Nat) (h : Interval) (seen : Bool) (dv : V3) : Prop :=
  seen = true ∧ (h.status = 0 → ∀ d, InPad xs d → Good xs j dv d ∧ Contains h (pcAfter xs j dv d))

theorem contains_hull {a b : Interval} {x : ℝ} (fa : Finite a.lo.toBits ∧ Finite a.hi.toBits)
    (fb : Finite b.lo.toBits ∧ Finite b.hi.toBits) (h1 : value a.lo.toBits ≤ x)
    (h2 : x ≤ value a.hi.toBits) :
    Contains ⟨0, fmin a.lo b.lo, fmax a.hi b.hi⟩ x := by
  obtain ⟨g1, e1⟩ := fmin_value fa.1 fb.1
  obtain ⟨g2, e2⟩ := fmax_value fa.2 fb.2
  refine ⟨rfl, g1, g2, ?_, ?_⟩
  · rw [e1]; exact (min_le_left _ _).trans h1
  · rw [e2]; exact h2.trans (le_max_left _ _)

theorem contains_hull' {a b : Interval} {x : ℝ} (fa : Finite a.lo.toBits ∧ Finite a.hi.toBits)
    (fb : Finite b.lo.toBits ∧ Finite b.hi.toBits) (h1 : value b.lo.toBits ≤ x)
    (h2 : x ≤ value b.hi.toBits) :
    Contains ⟨0, fmin a.lo b.lo, fmax a.hi b.hi⟩ x := by
  obtain ⟨g1, e1⟩ := fmin_value fa.1 fb.1
  obtain ⟨g2, e2⟩ := fmax_value fa.2 fb.2
  refine ⟨rfl, g1, g2, ?_, ?_⟩
  · rw [e1]; exact (min_le_right _ _).trans h1
  · rw [e2]; exact h2.trans (le_max_right _ _)

/-- Adding an interval `r` that is sound for the points of `P` to the hull. -/
theorem hullOf_fold {xs : Array Float} {j : Nat} {h r : Interval} {seen : Bool} {P : V3 → Prop}
    (hh : HullOk h seen) (hf : r.status = 0 → Finite r.lo.toBits ∧ Finite r.hi.toBits)
    (hs : r.status = 0 → ∀ dv, P dv → ∀ d, InPad xs d →
      Good xs j dv d ∧ Contains r (pcAfter xs j dv d)) :
    HullOk (hullOf seen h r) true ∧ (∀ dv, P dv → Folded xs j (hullOf seen h r) true dv) ∧
      (∀ dv, Folded xs j h seen dv → Folded xs j (hullOf seen h r) true dv) := by
  cases seen with
  | false =>
    rw [show hullOf false h r = r from rfl]
    exact ⟨fun _ h0 => hf h0, fun dv hp => ⟨rfl, fun h0 d hd => hs h0 dv hp d hd⟩,
      fun _ hfo => absurd hfo.1 (by decide)⟩
  | true =>
    rw [show hullOf true h r = (if h.status == 0 && r.status == 0 then
      ⟨0, fmin h.lo r.lo, fmax h.hi r.hi⟩ else rejected) from rfl]
    by_cases g : (h.status == 0 && r.status == 0) = true
    · simp only [g, ↓reduceIte]
      simp only [Bool.and_eq_true, beq_iff_eq] at g
      have fa := hh rfl g.1
      have fb := hf g.2
      refine ⟨fun _ _ => ⟨(fmin_value fa.1 fb.1).1, (fmax_value fa.2 fb.2).1⟩,
        fun dv hp => ⟨rfl, fun _ d hd => ?_⟩, fun dv hfo => ⟨rfl, fun _ d hd => ?_⟩⟩
      · obtain ⟨G, C⟩ := hs g.2 dv hp d hd
        exact ⟨G, contains_hull' fa fb C.2.2.2.1 C.2.2.2.2⟩
      · obtain ⟨G, C⟩ := hfo.2 g.1 d hd
        exact ⟨G, contains_hull fa fb C.2.2.2.1 C.2.2.2.2⟩
    · simp only [g, Bool.false_eq_true, ↓reduceIte]
      exact ⟨fun _ h0 => absurd h0 (by decide), fun _ _ => ⟨rfl, fun h0 => absurd h0 (by decide)⟩,
        fun _ _ => ⟨rfl, fun h0 => absurd h0 (by decide)⟩⟩

/-! ### The search -/

theorem push2_fst {α : Type} [Inhabited α] (acc : Array α) (a b : α) :
    ((acc.push a).push b)[acc.size]! = a := by
  rw [push_get_lt _ _ (by simp), push_get_size]

theorem push2_snd {α : Type} [Inhabited α] (acc : Array α) (a b : α) :
    ((acc.push a).push b)[acc.size + 1]! = b := by
  rw [show acc.size + 1 = (acc.push a).size by simp, push_get_size]

theorem push2_lt {α : Type} [Inhabited α] (acc : Array α) (a b : α) {i : Nat}
    (hi : i < acc.size) : ((acc.push a).push b)[i]! = acc[i]! := by
  rw [push_get_lt _ _ (by simp; omega), push_get_lt _ _ hi]

section Search

variable {xs : Array Float} {n : UInt64} {t : Float} {S : Nat}

/-- The invariant of the search of conjunction `j` with at most `S` splits: the cells are cells
of the search, every velocity change of the box lies in a cell left to evaluate or is covered by
the hull, and an interval that showed the probability at or above `t` has a witness. -/
structure Inv (xs : Array Float) (j : Nat) (t : Float) (S : Nat) (q : Search) : Prop where
  next : q.next.toNat ≤ q.cells.size
  size : q.cells.size + 2 * q.budget.toNat ≤ 2 * S + 1
  cells : ∀ i < q.cells.size, CellOk xs j q.cells[i]!
  hull : HullOk q.hull q.seen
  cover : ∀ dv, InBox xs dv →
    (∃ i, q.next.toNat ≤ i ∧ i < q.cells.size ∧ InCell q.cells[i]! dv) ∨
      Folded xs j q.hull q.seen dv
  above : q.above = true →
    ∃ dv, InBox xs dv ∧ Good xs j dv 0 ∧ value t.toBits ≤ pcAfter xs j dv 0

/-- The facts of the input that the search uses. -/
structure Ready (xs : Array Float) (j : UInt64) (t : Float) (S : Nat) : Prop where
  hj : j.toNat < 64
  pad : Finite (rd xs 13).toBits
  pad0 : 0 ≤ val xs 13
  thr : Finite t.toBits
  budget : S ≤ 65536

theorem next_succ {q : Search} (hS : S ≤ 65536) (hi : q.cells.size + 2 * q.budget.toNat ≤ 2 * S + 1)
    (hn : q.next.toNat < q.cells.size) : (q.next + 1).toNat = q.next.toNat + 1 := by
  rw [UInt64.toNat_add]
  simp only [UInt64.reduceToNat]
  omega

/-- A witness of an interval at or above `t`: an accepted interval of the cell with a lower end at
or above `t`, or an accepted probe of the cell with such a lower end. -/
theorem witness {j : UInt64} (R : Ready xs j t S) {c : Cell} (hc : CellOk xs j.toNat c)
    {r : Interval} (hr : Sound xs j.toNat c r)
    (h : (r.status = 0 ∧ t ≤ r.lo) ∨
      ((probe Exp.expTable Trig.invPi Trig.halfPi xs n j c).status = 0 ∧
        t ≤ (probe Exp.expTable Trig.invPi Trig.halfPi xs n j c).lo)) :
    ∃ dv, InBox xs dv ∧ Good xs j.toNat dv 0 ∧ value t.toBits ≤ pcAfter xs j.toNat dv 0 := by
  rcases h with ⟨h0, hl⟩ | ⟨h0, hl⟩
  · obtain ⟨G, C⟩ := hr h0 (corner c) 0 (corner_in hc) (inPad_zero R.pad0)
    exact ⟨corner c, hc.within _ (corner_in hc), G,
      ((le_iff_value R.thr C.2.1).mp hl).trans C.2.2.2.1⟩
  · obtain ⟨hi, G, C⟩ := probe_sound R.hj hc h0
    exact ⟨center c, hc.within _ hi, G, ((le_iff_value R.thr C.2.1).mp hl).trans C.2.2.2.1⟩

theorem init_inv {j : UInt64} {s : UInt64} (hs : s.toNat = S)
    (fin : Finite (rd xs 7).toBits ∧ Finite (rd xs 8).toBits ∧ Finite (rd xs 9).toBits ∧
      Finite (rd xs 10).toBits ∧ Finite (rd xs 11).toBits ∧ Finite (rd xs 12).toBits)
    (box : val xs 7 ≤ val xs 8 ∧ val xs 9 ≤ val xs 10 ∧ val xs 11 ≤ val xs 12) :
    Inv xs j.toNat t S
      ⟨#[⟨rd xs 7, rd xs 8, rd xs 9, rd xs 10, rd xs 11, rd xs 12, rejected, 0⟩], 0, rejected,
        false, s, false⟩ := by
  refine ⟨by simp, by simp; omega, fun i hi => ?_,
    fun h => absurd (show false = true from h) (by decide), fun dv hb => ?_,
    fun h => absurd (show false = true from h) (by decide)⟩
  · have : i = 0 := by simpa using hi
    subst this
    show CellOk xs j.toNat ⟨rd xs 7, rd xs 8, rd xs 9, rd xs 10, rd xs 11, rd xs 12, rejected, 0⟩
    exact ⟨fin, box, fun dv h => h, fun h0 => absurd (show rejected.status = 0 from h0) (by decide)⟩
  · refine Or.inl ⟨0, by simp, by simp, ?_⟩
    show InCell ⟨rd xs 7, rd xs 8, rd xs 9, rd xs 10, rd xs 11, rd xs 12, rejected, 0⟩ dv
    exact hb

theorem step_split {j : UInt64} (R : Ready xs j t S) {q : Search} (hq : Inv xs j.toNat t S q)
    (hn : q.next.toNat < q.cells.size) (hb : q.budget ≠ 0) (hsp : splits q.cells[q.next.toNat]! = true)
    {r : Interval} (hr : Sound xs j.toNat q.cells[q.next.toNat]! r) :
    Inv xs j.toNat t S
      { q with
        cells := (q.cells.push (lowerHalf q.cells[q.next.toNat]! (side q.cells[q.next.toNat]!)
            (Demos.Screening.middle (sideLo q.cells[q.next.toNat]! (side q.cells[q.next.toNat]!))
              (sideHi q.cells[q.next.toNat]! (side q.cells[q.next.toNat]!))) r)).push
          (upperHalf q.cells[q.next.toNat]! (side q.cells[q.next.toNat]!)
            (Demos.Screening.middle (sideLo q.cells[q.next.toNat]! (side q.cells[q.next.toNat]!))
              (sideHi q.cells[q.next.toNat]! (side q.cells[q.next.toNat]!))) r)
        next := q.next + 1
        budget := q.budget - 1 } := by
  generalize hc : q.cells[q.next.toNat]! = c at hsp hr ⊢
  have hcok : CellOk xs j.toNat c := hc ▸ hq.cells _ hn
  obtain ⟨fm, l1, l2⟩ := splits_facts hcok hsp
  obtain ⟨kl, ku, cov⟩ := halves hcok fm l1 l2 hr
  generalize lowerHalf c (side c) (Demos.Screening.middle (sideLo c (side c))
    (sideHi c (side c))) r = L at kl ku cov ⊢
  generalize upperHalf c (side c) (Demos.Screening.middle (sideLo c (side c))
    (sideHi c (side c))) r = U at kl ku cov ⊢
  have hb0 : q.budget.toNat ≠ 0 := by
    intro h0
    apply hb
    exact UInt64.toNat_inj.mp (by rw [h0]; rfl)
  have hb1 : (q.budget - 1).toNat = q.budget.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr
      (by simp only [UInt64.reduceToNat]; omega))]
    rfl
  have hnext := next_succ R.budget hq.size hn
  have hbpos : 1 ≤ q.budget.toNat := by omega
  have get : ∀ i, i < q.cells.size + 2 → CellOk xs j.toNat ((q.cells.push L).push U)[i]! := by
    intro i hi
    by_cases h1 : i < q.cells.size
    · rw [push2_lt _ _ _ h1]; exact hq.cells i h1
    · by_cases h2 : i = q.cells.size
      · subst h2; rw [push2_fst]; exact kl
      · have : i = q.cells.size + 1 := by omega
        subst this; rw [push2_snd]; exact ku
  refine ⟨?_, ?_, ?_, hq.hull, ?_, hq.above⟩
  · show (q.next + 1).toNat ≤ ((q.cells.push L).push U).size
    simp only [Array.size_push]; omega
  · show ((q.cells.push L).push U).size + 2 * (q.budget - 1).toNat ≤ 2 * S + 1
    simp only [Array.size_push]; have := hq.size; omega
  · intro i hi
    simp only [Array.size_push] at hi
    exact get i (by omega)
  · intro dv hbox
    show (∃ i, (q.next + 1).toNat ≤ i ∧ i < ((q.cells.push L).push U).size ∧
        InCell ((q.cells.push L).push U)[i]! dv) ∨ Folded xs j.toNat q.hull q.seen dv
    rcases hq.cover dv hbox with ⟨i, h1, h2, h3⟩ | hf
    · left
      rw [hnext]
      by_cases hin : i = q.next.toNat
      · subst hin
        rw [hc] at h3
        rcases cov dv h3 with e | e
        · exact ⟨q.cells.size, by omega, by simp only [Array.size_push]; omega,
            by rw [push2_fst]; exact e⟩
        · exact ⟨q.cells.size + 1, by omega, by simp only [Array.size_push]; omega,
            by rw [push2_snd]; exact e⟩
      · exact ⟨i, by omega, by simp only [Array.size_push]; omega,
          by rw [push2_lt _ _ _ h2]; exact h3⟩
    · exact Or.inr hf

theorem step_fold {j : UInt64} (R : Ready xs j t S) {q : Search} (hq : Inv xs j.toNat t S q)
    (hn : q.next.toNat < q.cells.size) {r : Interval}
    (hr : Sound xs j.toNat q.cells[q.next.toNat]! r) {a : Bool}
    (ha : a = true → ∃ dv, InBox xs dv ∧ Good xs j.toNat dv 0 ∧
      value t.toBits ≤ pcAfter xs j.toNat dv 0) :
    Inv xs j.toNat t S
      { q with next := q.next + 1, hull := hullOf q.seen q.hull r, seen := true, above := a } := by
  generalize hc : q.cells[q.next.toNat]! = c at hr
  have hcok : CellOk xs j.toNat c := hc ▸ hq.cells _ hn
  obtain ⟨H1, H2, H3⟩ := hullOf_fold (P := InCell c) hq.hull (hr.finite hcok R.pad0)
    (fun h0 dv hp d hd => hr h0 dv d hp hd)
  have hnext := next_succ R.budget hq.size hn
  refine ⟨?_, hq.size, hq.cells, H1, ?_, ha⟩
  · show (q.next + 1).toNat ≤ q.cells.size
    omega
  · intro dv hbox
    show (∃ i, (q.next + 1).toNat ≤ i ∧ i < q.cells.size ∧ InCell q.cells[i]! dv) ∨
      Folded xs j.toNat (hullOf q.seen q.hull r) true dv
    rcases hq.cover dv hbox with ⟨i, h1, h2, h3⟩ | hf
    · by_cases hin : i = q.next.toNat
      · subst hin
        rw [hc] at h3
        exact Or.inr (H2 dv h3)
      · exact Or.inl ⟨i, by omega, h2, h3⟩
    · exact Or.inr (H3 dv hf)

/-- The invariant holds after the search. -/
theorem search_inv {j : UInt64} (R : Ready xs j t S) {s : UInt64} (hs : s.toNat = S)
    (fin : Finite (rd xs 7).toBits ∧ Finite (rd xs 8).toBits ∧ Finite (rd xs 9).toBits ∧
      Finite (rd xs 10).toBits ∧ Finite (rd xs 11).toBits ∧ Finite (rd xs 12).toBits)
    (box : val xs 7 ≤ val xs 8 ∧ val xs 9 ≤ val xs 10 ∧ val xs 11 ≤ val xs 12) :
    Inv xs j.toNat t S (search Exp.expTable Trig.invPi Trig.halfPi xs n j t s) := by
  unfold search
  refine Demos.PassiveSafety.repeatWhile_invariant _ _ _ _ (Inv xs j.toNat t S)
    (init_inv hs fin box) ?_
  · intro q hq hcond
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hcond
    have hn : q.next.toNat < q.cells.size := by
      have h1 := UInt64.lt_iff_toNat_lt.mp hcond.1
      rwa [size_toUInt64 q.cells (by have := hq.size; have := R.budget; omega)] at h1
    have hr := evalCell_sound (n := n) R.hj R.pad q.cells[q.next.toNat]!
    dsimp only
    generalize evalCell Exp.expTable Trig.invPi Trig.halfPi xs n j q.cells[q.next.toNat]! = r at hr ⊢
    generalize ha : action Exp.expTable Trig.invPi Trig.halfPi xs n j t q.cells[q.next.toNat]! r
      q.budget = a
    by_cases h2 : a = 2
    · subst h2
      simp only [beq_self_eq_true, ↓reduceIte]
      obtain ⟨hb, hsp⟩ := action_two ha
      exact step_split R hq hn hb hsp hr
    · simp only [show (a == 2) = false by simpa using h2, Bool.false_eq_true, ↓reduceIte]
      refine step_fold R hq hn hr fun h1 => ?_
      have h1' : a = 1 := by simpa using h1
      subst h1'
      exact witness R (hq.cells _ hn) hr (action_one ha)

/-- The hull of the finished search, with the intervals of the cells left unevaluated, contains
the probability for every velocity change of the box and every displacement within the padding
when it is accepted. -/
theorem finish_sound {j : UInt64} (R : Ready xs j t S) {q : Search} (hq : Inv xs j.toNat t S q)
    (h : (finish q).status = 0) :
    ∀ dv d, InBox xs dv → InPad xs d →
      Good xs j.toNat dv d ∧ Contains (finish q) (pcAfter xs j.toNat dv d) := by
  have h64 : q.cells.size < 2 ^ 64 := by have := hq.size; have := R.budget; omega
  have hsz := size_toUInt64 q.cells h64
  have hk : (q.cells.size.toUInt64 - q.next).toNat = q.cells.size - q.next.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hsz]; exact hq.next)),
      hsz]
  have key := loop_induction (n := q.cells.size.toUInt64 - q.next) (init := (q.hull, q.seen))
    (f := fun i h => (hullOf h.2 h.1 q.cells[(q.next + i).toNat]!.bound, true))
    (fun m h => HullOk h.1 h.2 ∧ ∀ dv, InBox xs dv →
      (∃ i, q.next.toNat + m ≤ i ∧ i < q.cells.size ∧ InCell q.cells[i]! dv) ∨
        Folded xs j.toNat h.1 h.2 dv)
    ⟨hq.hull, fun dv hb => by simpa using hq.cover dv hb⟩
    (fun m h hm ⟨hh, hcov⟩ => by
      rw [hk] at hm
      have hi : (q.next + UInt64.ofNat m).toNat = q.next.toNat + m := by
        rw [UInt64.toNat_add, UInt64.toNat_ofNat']
        have := hq.next
        omega
      simp only [hi]
      have hcok := hq.cells (q.next.toNat + m) (by omega)
      obtain ⟨H1, H2, H3⟩ := hullOf_fold (P := InCell q.cells[q.next.toNat + m]!) hh
        (hcok.bound.finite hcok R.pad0) (fun h0 dv hp d hd => hcok.bound h0 dv d hp hd)
      refine ⟨H1, fun dv hb => ?_⟩
      rcases hcov dv hb with ⟨i, h1, h2, h3⟩ | hf
      · by_cases hin : i = q.next.toNat + m
        · subst hin
          exact Or.inr (H2 dv h3)
        · exact Or.inl ⟨i, by omega, h2, h3⟩
      · exact Or.inr (H3 dv hf))
  unfold finish at h ⊢
  dsimp only at h ⊢
  generalize LeanExe.loop (q.cells.size.toUInt64 - q.next) (q.hull, q.seen)
    (fun i h => (hullOf h.2 h.1 q.cells[(q.next + i).toNat]!.bound, true)) = L at key h ⊢
  obtain ⟨-, hcov⟩ := key
  rw [hk] at hcov
  have := hq.next
  intro dv d hb hd
  rcases hcov dv hb with ⟨i, h1, h2, -⟩ | ⟨hs, hf⟩
  · omega
  · simp only [hs, ite_true] at h ⊢
    exact hf h d hd

end Search

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

theorem allBelow_spec {rs : Array Outcome} {t : Float} (h : allBelow rs t = true) :
    ∀ j < rs.size.toUInt64.toNat, rs[(UInt64.ofNat j).toNat]!.bound.status = 0 ∧
      rs[(UInt64.ofNat j).toNat]!.bound.hi < t := by
  have key := loop_induction (n := rs.size.toUInt64) (init := true)
    (f := fun j ok => ok && (rs[j.toNat]!.bound.status == 0 && rs[j.toNat]!.bound.hi < t))
    (fun m ok => ok = true → ∀ j < m, rs[(UInt64.ofNat j).toNat]!.bound.status = 0 ∧
      rs[(UInt64.ofNat j).toNat]!.bound.hi < t)
    (fun _ j hj => absurd hj (Nat.not_lt_zero j))
    (fun m ok _ ih hm j hj => by
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm
      by_cases hjm : j < m
      · exact ih hm.1 j hjm
      · have : j = m := by omega
        subst this
        exact hm.2)
  exact key h

theorem anyShown_spec {rs : Array Outcome} {t : Float} (h : anyShown rs t = true) :
    ∃ j < rs.size.toUInt64.toNat, rs[(UInt64.ofNat j).toNat]!.above = true := by
  have key := loop_induction (n := rs.size.toUInt64) (init := false)
    (f := fun j found => found || (rs[j.toNat]!.bound.status == 0 && !(rs[j.toNat]!.bound.hi < t) &&
      rs[j.toNat]!.above))
    (fun m found => found = true → ∃ j < m, rs[(UInt64.ofNat j).toNat]!.above = true)
    (fun h0 => absurd h0 (by decide))
    (fun m found _ ih hm => by
      simp only [Bool.or_eq_true, Bool.and_eq_true] at hm
      rcases hm with hf | ⟨-, ha⟩
      · obtain ⟨j, hj, e⟩ := ih hf
        exact ⟨j, by omega, e⟩
      · exact ⟨m, by omega, ha⟩)
  exact key h

/-- The facts of a valid input. -/
structure Facts (xs : Array Float) (n s : UInt64) : Prop where
  size : 35 ≤ xs.size.toUInt64.toNat ∧ xs.size.toUInt64.toNat ≤ 1295 ∧
    (xs.size.toUInt64.toNat - 15) % 20 = 0
  hcount : (count xs).toNat = (xs.size.toUInt64.toNat - 15) / 20
  fin : ∀ i < xs.size.toUInt64.toNat, Finite (xs[i]!).toBits
  mu : 0 < val xs 0
  box : val xs 7 ≤ val xs 8 ∧ val xs 9 ≤ val xs 10 ∧ val xs 11 ≤ val xs 12
  pad : 0 ≤ val xs 13
  panels : 1 ≤ n ∧ n ≤ 1048576
  budget : s.toNat ≤ 65536
  blocks : ∀ j < (count xs).toNat, 0 < val xs (15 + 20 * j) ∧ 0 < val xs (34 + 20 * j)

theorem pos_of_lt {x : Float} (hx : Finite x.toBits) (h : 0.0 < x) : 0 < value x.toBits := by
  have := (lt_iff_value Demos.Conjunction.lit_zero.1 hx).mp h
  rwa [Demos.Conjunction.lit_zero.2] at this

theorem nonneg_of_le {x : Float} (hx : Finite x.toBits) (h : 0.0 ≤ x) : 0 ≤ value x.toBits := by
  have := (le_iff_value Demos.Conjunction.lit_zero.1 hx).mp h
  rwa [Demos.Conjunction.lit_zero.2] at this

theorem valid_facts {xs : Array Float} {n s : UInt64} (h : valid xs n s = true) : Facts xs n s := by
  simp only [valid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, hfin⟩, hmu⟩, hb1⟩, hb2⟩, hb3⟩, hp⟩, hn1⟩, hn2⟩, hs⟩, hbl⟩ := h
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
  have hs' := UInt64.le_iff_toNat_le.mp hs
  simp only [UInt64.reduceToNat] at hs'
  refine ⟨⟨s1, s2, s3⟩, hc, fin', pos_of_lt (f 0 (by norm_num)) hmu,
    ⟨(le_iff_value (f 7 (by norm_num)) (f 8 (by norm_num))).mp hb1,
      (le_iff_value (f 9 (by norm_num)) (f 10 (by norm_num))).mp hb2,
      (le_iff_value (f 11 (by norm_num)) (f 12 (by norm_num))).mp hb3⟩,
    nonneg_of_le (f 13 (by norm_num)) hp, ⟨hn1, hn2⟩, hs', fun j hj => ?_⟩
  have hj' : j < 64 := by omega
  have e0 : (15 + 20 * UInt64.ofNat j).toNat = 15 + 20 * j := by
    have := idx0 (j := UInt64.ofNat j) (by rw [UInt64.toNat_ofNat']; omega)
    rwa [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)] at this
  have e1 : (34 + 20 * UInt64.ofNat j).toNat = 34 + 20 * j := by
    simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.reduceToNat, UInt64.toNat_ofNat']
    omega
  obtain ⟨b1, b2⟩ := hbl' j hj
  constructor
  · exact pos_of_lt (fin' _ (by omega)) (show 0.0 < xs[15 + 20 * j]! by
      have h := b1; unfold rd at h; rwa [e0] at h)
  · exact pos_of_lt (fin' _ (by omega)) (show 0.0 < xs[34 + 20 * j]! by
      have h := b2; unfold rd at h; rwa [e1] at h)

/-- The facts that the search of conjunction `j` of a valid input uses. -/
theorem ready_of {xs : Array Float} {n s : UInt64} (F : Facts xs n s) {j : Nat}
    (hj : j < (count xs).toNat) :
    Ready xs (UInt64.ofNat j) (rd xs 14) s.toNat ∧ (UInt64.ofNat j).toNat = j ∧
      (Finite (rd xs 7).toBits ∧ Finite (rd xs 8).toBits ∧ Finite (rd xs 9).toBits ∧
        Finite (rd xs 10).toBits ∧ Finite (rd xs 11).toBits ∧ Finite (rd xs 12).toBits) := by
  have hk := F.hcount
  have hs := F.size
  have f : ∀ i < 35, Finite (xs[i]!).toBits := fun i hi => F.fin i (by omega)
  have hjn : (UInt64.ofNat j).toNat = j := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  exact ⟨⟨by rw [hjn]; omega, f 13 (by norm_num), F.pad, f 14 (by norm_num), F.budget⟩, hjn,
    f 7 (by norm_num), f 8 (by norm_num), f 9 (by norm_num), f 10 (by norm_num),
    f 11 (by norm_num), f 12 (by norm_num)⟩

/-- An accepted hull of conjunction `j` gives the conditions of the model's theorems and
contains the model's probability for every velocity change of the box and every displacement
within the padding. -/
theorem searchOne_sound {xs : Array Float} {n s : UInt64} (F : Facts xs n s) {j : Nat}
    (hj : j < (count xs).toNat)
    (h : (searchOne Exp.expTable Trig.invPi Trig.halfPi xs n s (UInt64.ofNat j)).bound.status = 0)
    {dv d : V3} (hb : InBox xs dv) (hd : InPad xs d) :
    Good xs j dv d ∧
      Contains (searchOne Exp.expTable Trig.invPi Trig.halfPi xs n s (UInt64.ofNat j)).bound
        (pcAfter xs j dv d) := by
  obtain ⟨R, hjn, fin⟩ := ready_of F hj
  have I := search_inv (n := n) R rfl fin F.box
  have := finish_sound R I h dv d hb hd
  rwa [hjn] at this

/-- A search that showed the probability at or above the threshold has a velocity change of the
box at which, with no displacement, the model's conditions hold and its probability lies at or
above the threshold. -/
theorem searchOne_above {xs : Array Float} {n s : UInt64} (F : Facts xs n s) {j : Nat}
    (hj : j < (count xs).toNat)
    (h : (searchOne Exp.expTable Trig.invPi Trig.halfPi xs n s (UInt64.ofNat j)).above = true) :
    ∃ dv, InBox xs dv ∧ Good xs j dv 0 ∧ val xs 14 ≤ pcAfter xs j dv 0 := by
  obtain ⟨R, hjn, fin⟩ := ready_of F hj
  have I := search_inv (n := n) R rfl fin F.box
  have := I.above h
  rwa [hjn] at this

theorem append_get_left {α : Type} [Inhabited α] (a b : Array α) (k : Nat) (hk : k < a.size) :
    (a ++ b)[k]! = a[k]! := by
  rw [getElem!_pos (a ++ b) k (by simp; omega), getElem!_pos a k hk]
  simp [Array.getElem_append_left hk]

theorem append_get_right {α : Type} [Inhabited α] (a b : Array α) (k : Nat) (hk : k < b.size) :
    (a ++ b)[a.size + k]! = b[k]! := by
  rw [getElem!_pos (a ++ b) (a.size + k) (by simp; omega), getElem!_pos b k hk]
  simp [Array.getElem_append_right]

/-- The results of the conjunctions. -/
theorem results_get {xs : Array Float} {n s : UInt64} (F : Facts xs n s) {j : Nat}
    (hj : j < (count xs).toNat) :
    (LeanExe.build (count xs) fun j => searchOne Exp.expTable Trig.invPi Trig.halfPi xs n s j)[
        (UInt64.ofNat j).toNat]! =
      searchOne Exp.expTable Trig.invPi Trig.halfPi xs n s (UInt64.ofNat j) := by
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by have := F.hcount; have := F.size; omega)]
  exact build_get hj

/-! ### The theorems -/

/-- **A1.**  When `authorize` returns status 0, the input is valid, and for every conjunction,
every velocity change of the box, and every displacement within the padding, the model's
conditions hold and its probability of collision lies below the threshold. -/
theorem authorize_sound {xs : Array Float} {n s : UInt64} (h : (authorize xs n s)[0]! = 0.0) :
    valid xs n s = true ∧ ∀ j < (count xs).toNat, ∀ dv d : V3, InBox xs dv → InPad xs d →
      Good xs j dv d ∧ pcAfter xs j dv d < val xs 14 := by
  unfold authorize authorizeWith at h
  by_cases hv : valid xs n s = true
  · simp only [hv, ite_true] at h
    have F := valid_facts hv
    refine ⟨hv, fun j hj dv d hb hd => ?_⟩
    generalize hrs : (LeanExe.build (count xs) fun j =>
      searchOne Exp.expTable Trig.invPi Trig.halfPi xs n s j) = rs at h
    rw [append_get_left _ _ 0 (by simp),
      show ∀ x y : Float, (#[x, y] : Array Float)[0]! = x from fun _ _ => rfl] at h
    have hall : allBelow rs (rd xs 14) = true := by
      by_contra hc
      simp only [Bool.not_eq_true] at hc
      simp only [hc, Bool.false_eq_true, ite_false] at h
      split_ifs at h <;> exact absurd (congrArg Float.toBits h) (by decide +kernel)
    have hsz : rs.size.toUInt64.toNat = (count xs).toNat := by
      rw [← hrs, build_size]
      simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']
      exact Nat.mod_eq_of_lt (by have := F.hcount; have := F.size; omega)
    obtain ⟨hs, hhi⟩ := allBelow_spec hall j (by rw [hsz]; exact hj)
    rw [← hrs, results_get F hj] at hs hhi
    obtain ⟨G, C⟩ := searchOne_sound F hj hs hb hd
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
`c = 0`, and the ends of its hull for `c = 1` and `c = 2` when it is accepted. -/
theorem output_get {xs : Array Float} {n s : UInt64} (hv : valid xs n s = true) {j c : Nat}
    (hj : j < (count xs).toNat) (hc : c < 3) :
    (authorize xs n s)[2 + 3 * j + c]! =
      if c = 0 then
        verdict (searchOne Exp.expTable Trig.invPi Trig.halfPi xs n s (UInt64.ofNat j)) (rd xs 14)
      else if (searchOne Exp.expTable Trig.invPi Trig.halfPi xs n s (UInt64.ofNat j)).bound.status
          = 0 then
        (if c = 1 then (searchOne Exp.expTable Trig.invPi Trig.halfPi xs n s (UInt64.ofNat j)).bound.lo
          else (searchOne Exp.expTable Trig.invPi Trig.halfPi xs n s (UInt64.ofNat j)).bound.hi)
      else 0.0 := by
  have F := valid_facts hv
  have hk := F.hcount
  have hs := F.size
  unfold authorize authorizeWith
  simp only [hv, ite_true]
  generalize hrs : (LeanExe.build (count xs) fun j =>
    searchOne Exp.expTable Trig.invPi Trig.halfPi xs n s j) = rs
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
  have hr : rs[j]! = searchOne Exp.expTable Trig.invPi Trig.halfPi xs n s (UInt64.ofNat j) := by
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

/-- **A2.**  For a valid input, a conjunction whose verdict is not 2 has an interval that
contains the model's probability for every velocity change of the box and every displacement
within the padding, and verdict 0 places the probability below the threshold. -/
theorem authorize_enclosure {xs : Array Float} {n s : UInt64} (hv : valid xs n s = true) {j : Nat}
    (hj : j < (count xs).toNat) (hs : (authorize xs n s)[2 + 3 * j]! ≠ 2.0) {dv d : V3}
    (hb : InBox xs dv) (hd : InPad xs d) :
    Good xs j dv d ∧ value ((authorize xs n s)[3 + 3 * j]!).toBits ≤ pcAfter xs j dv d ∧
      pcAfter xs j dv d ≤ value ((authorize xs n s)[4 + 3 * j]!).toBits ∧
      ((authorize xs n s)[2 + 3 * j]! = 0.0 → pcAfter xs j dv d < val xs 14) := by
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
  have hsound := fun h0 => searchOne_sound F hj h0 hb hd
  generalize searchOne Exp.expTable Trig.invPi Trig.halfPi xs n s (UInt64.ofNat j) = o at hs hsound ⊢
  have hst : o.bound.status = 0 := by
    by_contra hne
    apply hs
    unfold verdict
    simp only [beq_iff_eq, hne, ite_false]
  have ht : Finite (rd xs 14).toBits := F.fin 14 (by omega)
  obtain ⟨G, C⟩ := hsound hst
  simp only [hst, ite_true]
  refine ⟨G, C.2.2.2.1, C.2.2.2.2, fun h0 => ?_⟩
  have hlt : o.bound.hi < rd xs 14 := by
    by_contra hge
    have hb0 : (o.bound.status == 0) = true := by simp [hst]
    unfold verdict at h0
    simp only [hb0, hge, ↓reduceIte] at h0
    split_ifs at h0 <;> exact absurd (congrArg Float.toBits h0) (by decide +kernel)
  exact lt_of_le_of_lt C.2.2.2.2 ((lt_iff_value C.2.2.1 ht).mp hlt)

/-- **A4.**  For a valid input, a conjunction with verdict 1 has a velocity change of the box at
which, with no displacement, the model's conditions hold and its probability of collision lies
at or above the threshold. -/
theorem authorize_above {xs : Array Float} {n s : UInt64} (hv : valid xs n s = true) {j : Nat}
    (hj : j < (count xs).toNat) (h1 : (authorize xs n s)[2 + 3 * j]! = 1.0) :
    ∃ dv : V3, InBox xs dv ∧ Good xs j dv 0 ∧ val xs 14 ≤ pcAfter xs j dv 0 := by
  have F := valid_facts hv
  have v0 := output_get hv hj (c := 0) (by norm_num)
  rw [show 2 + 3 * j + 0 = 2 + 3 * j by omega] at v0
  simp only [ite_true] at v0
  rw [v0] at h1
  apply searchOne_above F hj
  unfold verdict at h1
  split_ifs at h1 <;> first | assumption | exact absurd (congrArg Float.toBits h1) (by decide +kernel)

/-- **A4 for the status.**  When `authorize` returns status 2, the input is valid, and some
conjunction has a velocity change of the box at which, with no displacement, the model's
conditions hold and its probability of collision lies at or above the threshold. -/
theorem authorize_shown {xs : Array Float} {n s : UInt64} (h : (authorize xs n s)[0]! = 2.0) :
    valid xs n s = true ∧ ∃ j < (count xs).toNat, ∃ dv : V3,
      InBox xs dv ∧ Good xs j dv 0 ∧ val xs 14 ≤ pcAfter xs j dv 0 := by
  unfold authorize authorizeWith at h
  by_cases hv : valid xs n s = true
  · simp only [hv, ite_true] at h
    have F := valid_facts hv
    refine ⟨hv, ?_⟩
    generalize hrs : (LeanExe.build (count xs) fun j =>
      searchOne Exp.expTable Trig.invPi Trig.halfPi xs n s j) = rs at h
    rw [append_get_left _ _ 0 (by simp),
      show ∀ x y : Float, (#[x, y] : Array Float)[0]! = x from fun _ _ => rfl] at h
    have hsh : anyShown rs (rd xs 14) = true := by
      by_contra hc
      simp only [Bool.not_eq_true] at hc
      simp only [hc, Bool.false_eq_true, ite_false] at h
      split_ifs at h <;> exact absurd (congrArg Float.toBits h) (by decide +kernel)
    have hsz : rs.size.toUInt64.toNat = (count xs).toNat := by
      rw [← hrs, build_size]
      simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']
      exact Nat.mod_eq_of_lt (by have := F.hcount; have := F.size; omega)
    obtain ⟨j, hj, ha⟩ := anyShown_spec hsh
    rw [hsz] at hj
    rw [← hrs, results_get F hj] at ha
    exact ⟨j, hj, searchOne_above F hj ha⟩
  · simp only [hv, Bool.false_eq_true, ite_false] at h
    exact absurd (congrArg Float.toBits h) (by decide +kernel)

/-- Status 1 marks exactly the inputs that `valid` rejects. -/
theorem authorize_invalid {xs : Array Float} {n s : UInt64} :
    (authorize xs n s)[0]! = 1.0 ↔ valid xs n s = false := by
  constructor
  · intro h
    by_contra hv
    have hv' : valid xs n s = true := by simpa using hv
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
theorem authorize_model {xs : Array Float} {n s : UInt64} (h : (authorize xs n s)[0]! = 0.0) :
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
#print axioms authorize_above
#print axioms authorize_shown
#print axioms authorize_invalid
#print axioms authorize_model

end Demos.Avoidance
