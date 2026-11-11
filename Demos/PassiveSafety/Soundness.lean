import Demos.PassiveSafety.Program
import Demos.PassiveSafety.Model
import Library.Numerics.Interval.Proof
import LeanExe.Dialect.Lemmas

/-!
Soundness of the passive-safety check.  `check_sound` states that when `check` accepts, every
trajectory of the Hill–Clohessy–Wiltshire model from the box of initial states, with burns at the
plan's times and velocity changes in the plan's boxes, keeps the separation at or above the
threshold and the returned bound over the horizon, and the radial and cross-track distance at or
above its threshold and bound at every time after the scenario's last burn, in every scenario.

The proof follows the program.  `positionI_encloses` gives the enclosure of the position from the
loop over the burns, `Model.path_eq` and `Model.kicks_selectFrom` equate the enclosed sum with the
model's trajectory, `search_covered` states what a finished search covers, `Model.flow_phase`
reduces every time after a scenario's last burn to one period, and `scan_sound` collects the
scenarios.
-/

namespace Demos.PassiveSafety

open LeanExe.ProofKit Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64
open CodeLib.IEEE64 (value Finite)
open Model

set_option exponentiation.threshold 4096

/-! ### Constants -/

theorem lit_zero : Finite (0.0 : Float).toBits ∧ value (0.0 : Float).toBits = 0 := by
  have hb : (0.0 : Float).toBits = 0 := by decide +kernel
  have hs : Wasm.IEEE64.scaledValue 0 = 0 := by decide +kernel
  refine ⟨?_, ?_⟩
  · rw [hb]; unfold CodeLib.IEEE64.Finite; decide +kernel
  · simp only [hb, value, hs]; norm_num

theorem rejected_lo : Finite (rejected.lo).toBits ∧ value (rejected.lo).toBits = 0 :=
  zero_value

theorem maxFloat_finite : Finite maxFloat.toBits := by
  have hb : maxFloat.toBits = 0x7FEFFFFFFFFFFFFF := toBits_ofBits_of_finite (by decide)
  rw [hb]; unfold CodeLib.IEEE64.Finite; decide +kernel

/-- The end of the phases lies at or above `2π`. -/
theorem twoPiHi_bounds : Finite twoPiHi.toBits ∧ 2 * Real.pi ≤ value twoPiHi.toBits := by
  have hb : twoPiHi.toBits = 0x401921FB54442D19 := toBits_ofBits_of_finite (by decide)
  have hs : Wasm.IEEE64.scaledValue 0x401921FB54442D19 = 7074237752028441 * 2 ^ 1024 := by
    decide +kernel
  have hv : value (0x401921FB54442D19 : UInt64) = 7074237752028441 / 2 ^ 50 := by
    simp only [value, hs]; push_cast; norm_num
  have h2 := Real.pi_lt_d20
  refine ⟨?_, ?_⟩
  · rw [hb]; unfold CodeLib.IEEE64.Finite; decide +kernel
  · rw [hb, hv]
    norm_num at h2 ⊢
    linarith

/-! ### Enclosures of the inputs -/

theorem encloses_point (x : Float) : Encloses (point x) (value x.toBits) :=
  fun h => (point_sound h).2

theorem encloses_zero : Encloses (point 0.0) 0 := by
  have h := encloses_point 0.0
  rwa [lit_zero.2] at h

theorem encloses_make {a b : Float} {x : ℝ} (h1 : value a.toBits ≤ x) (h2 : x ≤ value b.toBits) :
    Encloses (make a b) x :=
  fun h => (make_sound h).2.2.2 x h1 h2

theorem encloses_box {xs : Array Float} {i : UInt64} {x : ℝ} (h1 : value (rd xs i).toBits ≤ x)
    (h2 : x ≤ value (rd xs (i + 1)).toBits) : Encloses (box xs i) x :=
  encloses_make h1 h2

theorem encloses_nonneg {v : Interval} {x : ℝ} (hv : Encloses v x) (hx : 0 ≤ x) :
    Encloses (nonneg v) x := fun h => by
  unfold nonneg at h ⊢
  obtain ⟨s, hc⟩ := clamp_sound h
  have c := hv s
  exact hc x c (by rw [lit_zero.2]; exact hx) c.2.2.2.2

/-! ### The real functions of the closed form -/

theorem flowPosition_eq (n t : ℝ) (s : State) :
    flowPosition n t s.x s.y s.z s.vx s.vy s.vz =
      ((flow n t s).x, (flow n t s).y, (flow n t s).z) :=
  rfl

theorem sepSquare_eq (x y z : ℝ) : sepSquare x y z = x ^ 2 + y ^ 2 + z ^ 2 := by
  simp only [sepSquare, abs_mul_abs_self]; ring

theorem rcSquare_eq (x z : ℝ) : rcSquare x z = x ^ 2 + z ^ 2 := by
  simp only [rcSquare, abs_mul_abs_self]; ring

/-! ### The input and the burns -/

/-- The real value of value `i` of the input. -/
noncomputable def val (xs : Array Float) (i : ℕ) : ℝ := value (xs[i]!).toBits

theorem val_rd (xs : Array Float) (i : UInt64) : value (rd xs i).toBits = val xs i.toNat := rfl

/-- The state `s` lies in the box of initial states of the input. -/
def InBox (xs : Array Float) (s : State) : Prop :=
  val xs 4 ≤ s.x ∧ s.x ≤ val xs 5 ∧ val xs 6 ≤ s.y ∧ s.y ≤ val xs 7 ∧
    val xs 8 ≤ s.z ∧ s.z ≤ val xs 9 ∧ val xs 10 ≤ s.vx ∧ s.vx ≤ val xs 11 ∧
    val xs 12 ≤ s.vy ∧ s.vy ≤ val xs 13 ∧ val xs 14 ≤ s.vz ∧ s.vz ≤ val xs 15

/-- The burns `bs` are those of the input's plan: one for each group of seven values after the
first sixteen, at the plan's time, with each velocity change in the plan's interval. -/
def Plan (xs : Array Float) (bs : List Burn) : Prop :=
  xs.size = 16 + 7 * bs.length ∧ ∀ i (h : i < bs.length),
    bs[i].t = val xs (16 + 7 * i) ∧
    val xs (17 + 7 * i) ≤ bs[i].dvx ∧ bs[i].dvx ≤ val xs (18 + 7 * i) ∧
    val xs (19 + 7 * i) ≤ bs[i].dvy ∧ bs[i].dvy ≤ val xs (20 + 7 * i) ∧
    val xs (21 + 7 * i) ≤ bs[i].dvz ∧ bs[i].dvz ≤ val xs (22 + 7 * i)

theorem Plan.getD {xs : Array Float} {bs : List Burn} (h : Plan xs bs) {i : ℕ}
    (hi : i < bs.length) :
    (bs.getD i Burn.none).t = val xs (16 + 7 * i) ∧
    val xs (17 + 7 * i) ≤ (bs.getD i Burn.none).dvx ∧
      (bs.getD i Burn.none).dvx ≤ val xs (18 + 7 * i) ∧
    val xs (19 + 7 * i) ≤ (bs.getD i Burn.none).dvy ∧
      (bs.getD i Burn.none).dvy ≤ val xs (20 + 7 * i) ∧
    val xs (21 + 7 * i) ≤ (bs.getD i Burn.none).dvz ∧
      (bs.getD i Burn.none).dvz ≤ val xs (22 + 7 * i) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact h.2 i hi

theorem burn_idx {k : UInt64} (hk : k.toNat < 16) :
    (burnAt k).toNat = 16 + 7 * k.toNat ∧ (burnAt k + 1).toNat = 17 + 7 * k.toNat ∧
      (burnAt k + 1 + 1).toNat = 18 + 7 * k.toNat ∧ (burnAt k + 3).toNat = 19 + 7 * k.toNat ∧
      (burnAt k + 3 + 1).toNat = 20 + 7 * k.toNat ∧ (burnAt k + 5).toNat = 21 + 7 * k.toNat ∧
      (burnAt k + 5 + 1).toNat = 22 + 7 * k.toNat := by
  simp only [burnAt, UInt64.toNat_add, UInt64.toNat_mul, UInt64.reduceToNat]
  omega

theorem runs_eq {N j k : UInt64} (hN : N.toNat ≤ 16) (hj : j.toNat ≤ 2 * N.toNat)
    (hk : k.toNat < N.toNat) : runs N j k = Model.runs N.toNat j.toNat k.toNat := by
  have hk1 : (k + 1).toNat = k.toNat + 1 := by
    simp only [UInt64.toNat_add, UInt64.reduceToNat]; omega
  have hbeq : (k + 1 == j) = (k.toNat + 1 == j.toNat) := by
    rw [← hk1]
    by_cases e : k + 1 = j
    · rw [e, beq_self_eq_true, beq_self_eq_true]
    · rw [beq_eq_false_iff_ne.mpr e,
        beq_eq_false_iff_ne.mpr fun h => e (UInt64.toNat_inj.mp h)]
  unfold runs Model.runs
  by_cases h0 : j.toNat = 0
  · have : j = 0 := UInt64.toNat_inj.mp (by simpa using h0)
    simp [this]
  · have hj0 : (j == 0) = false := by
      rw [beq_eq_false_iff_ne]
      intro h; subst h; simp at h0
    rw [hj0, ite_eq_right Bool.false_ne_true, ite_eq_right h0]
    by_cases hle : j.toNat ≤ N.toNat
    · rw [ite_eq_left (UInt64.le_iff_toNat_le.mpr hle), ite_eq_left hle, bne, bne, hbeq]
    · have hgt : ¬ j ≤ N := fun h => hle (UInt64.le_iff_toNat_le.mp h)
      have hsub : (j - N).toNat = j.toNat - N.toNat :=
        UInt64.toNat_sub_of_le j N (UInt64.le_iff_toNat_le.mpr (by omega))
      rw [ite_eq_right hgt, ite_eq_right hle]
      exact decide_eq_decide.mpr (by rw [UInt64.lt_iff_toNat_lt, hk1, hsub])

/-! ### Enclosures of positions and states -/

/-- The position component `c` of the term of burn `i` in scenario `j` at time `τ`. -/
noncomputable def posTerm (c : State → ℝ) (n τ : ℝ) (N j : ℕ) (bs : List Burn) (i : ℕ) : ℝ :=
  if Model.runs N j i = true then
    c (flow n (max (τ - (bs.getD i Burn.none).t) 0) (bs.getD i Burn.none).kick)
  else 0

/-- The facts about one burn of the plan that the loops over the burns use. -/
theorem burn_encloses {xs : Array Float} {bs : List Burn} (hplan : Plan xs bs) {k : UInt64}
    (hk : k.toNat < bs.length) (h16 : bs.length ≤ 16) :
    let b := bs.getD k.toNat Burn.none
    Encloses (point (rd xs (burnAt k))) b.t ∧ Encloses (box xs (burnAt k + 1)) b.dvx ∧
      Encloses (box xs (burnAt k + 3)) b.dvy ∧ Encloses (box xs (burnAt k + 5)) b.dvz := by
  intro b
  obtain ⟨i0, i1, i2, i3, i4, i5, i6⟩ := burn_idx (k := k) (by omega)
  obtain ⟨e0, e1, e2, e3, e4, e5, e6⟩ := hplan.getD hk
  refine ⟨?_, encloses_box ?_ ?_, encloses_box ?_ ?_, encloses_box ?_ ?_⟩
  · have h := encloses_point (rd xs (burnAt k))
    rwa [val_rd, i0, ← e0] at h
  · rw [val_rd, i1]; exact e1
  · rw [val_rd, i2]; exact e2
  · rw [val_rd, i3]; exact e3
  · rw [val_rd, i4]; exact e4
  · rw [val_rd, i5]; exact e5
  · rw [val_rd, i6]; exact e6

theorem box_initial {xs : Array Float} {s : State} (h : InBox xs s) :
    Encloses (box xs 4) s.x ∧ Encloses (box xs 6) s.y ∧ Encloses (box xs 8) s.z ∧
      Encloses (box xs 10) s.vx ∧ Encloses (box xs 12) s.vy ∧ Encloses (box xs 14) s.vz := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := h
  exact ⟨encloses_box a0 a1, encloses_box a2 a3, encloses_box a4 a5, encloses_box a6 a7,
    encloses_box a8 a9, encloses_box a10 a11⟩

/-- The enclosures of the position after the first `k` burns of scenario `j` at time `τ`. -/
def PosInv (xs : Array Float) (s : State) (bs : List Burn) (j : ℕ) (τ : ℝ) (k : ℕ)
    (acc : Interval × Interval × Interval) : Prop :=
  Encloses acc.1 ((flow (val xs 0) τ s).x +
      ∑ i ∈ Finset.range k, posTerm State.x (val xs 0) τ bs.length j bs i) ∧
    Encloses acc.2.1 ((flow (val xs 0) τ s).y +
      ∑ i ∈ Finset.range k, posTerm State.y (val xs 0) τ bs.length j bs i) ∧
    Encloses acc.2.2 ((flow (val xs 0) τ s).z +
      ∑ i ∈ Finset.range k, posTerm State.z (val xs 0) τ bs.length j bs i)

theorem positionI_encloses {xs : Array Float} {N j : UInt64} {bs : List Burn} {s : State}
    {tI : Interval} {τ : ℝ} (hN : N.toNat = bs.length) (h16 : bs.length ≤ 16)
    (hj : j.toNat ≤ 2 * bs.length) (hplan : Plan xs bs) (hbox : InBox xs s)
    (hτ : Encloses tI τ) :
    PosInv xs s bs j.toNat τ bs.length (positionI Trig.invPi Trig.halfPi xs N j tI) := by
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := box_initial hbox
  have hn : Encloses (point (rd xs 0)) (val xs 0) := encloses_point _
  have e0 := flowPosition.encloses (powLog := Trig.invPi) (powExp := Trig.halfPi) hn hτ b0 b1 b2
    b3 b4 b5
  rw [flowPosition_eq] at e0
  obtain ⟨p0, p1, p2⟩ := e0
  rw [← hN]
  unfold positionI
  refine LeanExe.Dialect.loop_induction (PosInv xs s bs j.toNat τ) ?_ ?_
  · simp only [PosInv, Finset.range_zero, Finset.sum_empty, add_zero]
    exact ⟨p0, p1, p2⟩
  · intro k acc hk ih
    simp only [PosInv] at ih ⊢
    have hkN : (UInt64.ofNat k).toNat = k := by
      rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
    have hr := runs_eq (N := N) (j := j) (k := UInt64.ofNat k) (by omega) (by omega)
      (by rw [hkN]; exact hk)
    rw [hN, hkN] at hr
    simp only [Finset.sum_range_succ]
    by_cases hrun : Model.runs bs.length j.toNat k = true
    · simp only [hr, hrun, ite_true]
      obtain ⟨et, ex, ey, ez⟩ := burn_encloses hplan (k := UInt64.ofNat k) (by omega) h16
      rw [hkN] at et ex ey ez
      set b := bs.getD k Burn.none
      have hd : Encloses (imax (sub tI (point (rd xs (burnAt (UInt64.ofNat k))))) (point 0.0))
          (max (τ - b.t) 0) := encloses_imax (encloses_sub hτ et) encloses_zero
      have eq := flowPosition.encloses (powLog := Trig.invPi) (powExp := Trig.halfPi)
        (x' := b.kick.x) (y' := b.kick.y) (z' := b.kick.z) (vx' := b.kick.vx)
        (vy' := b.kick.vy) (vz' := b.kick.vz) hn hd encloses_zero encloses_zero encloses_zero
        ex ey ez
      rw [flowPosition_eq] at eq
      obtain ⟨q0, q1, q2⟩ := eq
      dsimp only at q0 q1 q2
      obtain ⟨a0, a1, a2⟩ := ih
      simp only [posTerm, hrun, ite_true]
      refine ⟨?_, ?_, ?_⟩
      · have := encloses_add a0 q0; rwa [add_assoc] at this
      · have := encloses_add a1 q1; rwa [add_assoc] at this
      · have := encloses_add a2 q2; rwa [add_assoc] at this
    · have hf : runs N j (UInt64.ofNat k) = false := by
        rw [hr]; simpa using hrun
      simp only [hf, Bool.false_eq_true, ite_false, posTerm, hrun, add_zero]
      exact ih

/-! ### The model's trajectory as the enclosed sums -/

/-- Burns in nondecreasing order of time. -/
def Sorted (bs : List Burn) : Prop := bs.Pairwise fun a b => a.t ≤ b.t

theorem Sorted.select {bs : List Burn} (h : Sorted bs) (N j : ℕ) : Sorted (select N j bs) :=
  h.sublist (selectFrom_sublist N j 0 bs)

theorem path_position {n : ℝ} (hn : n ≠ 0) {bs : List Burn} (hs : Sorted bs) (N j : ℕ)
    (s : State) (τ : ℝ) :
    let p := path n 0 s (select N j bs) τ
    p.x = (flow n τ s).x + ∑ i ∈ Finset.range bs.length, posTerm State.x n τ N j bs i ∧
      p.y = (flow n τ s).y + ∑ i ∈ Finset.range bs.length, posTerm State.y n τ N j bs i ∧
      p.z = (flow n τ s).z + ∑ i ∈ Finset.range bs.length, posTerm State.z n τ N j bs i := by
  intro p
  have e : p = flow n τ s + kicks n τ (select N j bs) := by
    simp only [p]
    rw [path_eq hn (hs.select N j), sub_zero]
  have hx := kicks_selectFrom State.x (fun _ _ => rfl) rfl n τ N j
    (fun b => (flow n (max (τ - b.t) 0) b.kick).x) 0 bs (fun _ _ _ => kick_term_x n τ _)
  have hy := kicks_selectFrom State.y (fun _ _ => rfl) rfl n τ N j
    (fun b => (flow n (max (τ - b.t) 0) b.kick).y) 0 bs (fun _ _ _ => kick_term_y n τ _)
  have hz := kicks_selectFrom State.z (fun _ _ => rfl) rfl n τ N j
    (fun b => (flow n (max (τ - b.t) 0) b.kick).z) 0 bs (fun _ _ _ => kick_term_z n τ _)
  simp only [Nat.zero_add] at hx hy hz
  rw [e]
  refine ⟨?_, ?_, ?_⟩
  · simp only [State.add_x]; rw [select, hx]; rfl
  · simp only [State.add_y]; rw [select, hy]; rfl
  · simp only [State.add_z]; rw [select, hz]; rfl

/-! ### Searches -/

/-- A property that holds at the start of a `repeatWhile` and that each step under the condition
keeps holds at the end. -/
theorem repeatWhile_invariant {α : Type} (fuel : UInt64) (init : α) (cond : α → Bool)
    (step : α → α) (P : α → Prop) (h0 : P init) (hs : ∀ m, P m → cond m = true → P (step m)) :
    P (LeanExe.repeatWhile fuel init cond step) := by
  unfold LeanExe.repeatWhile
  suffices h : ∀ k m, P m → P (LeanExe.repeatWhile.go cond step k m) from h _ _ h0
  intro k
  induction k with
  | zero => intro m hm; simpa [LeanExe.repeatWhile.go] using hm
  | succ k ih =>
    intro m hm
    rw [LeanExe.repeatWhile.go]
    split_ifs with hc
    · exact ih _ (hs m hm hc)
    · exact hm

/-- The covered part `[0, m.t]` of a search of `g` against `d2`: when it is not empty, `g` is at
least `d2` and the least lower end `m.low` on it. -/
def Covered (g : ℝ → ℝ) (d2 : Float) (m : March) : Prop :=
  Finite m.t.toBits ∧ Finite m.low.toBits ∧
    (0 < value m.t.toBits → ∀ τ, 0 ≤ τ → τ ≤ value m.t.toBits →
      value d2.toBits ≤ g τ ∧ value m.low.toBits ≤ g τ)

theorem panelEnd_finite {t h e : Float} (he : Finite e.toBits) :
    Finite (panelEnd t h e).toBits := by
  unfold panelEnd
  dsimp only
  split_ifs with hc
  · simp only [Bool.and_eq_true, finite_iff] at hc
    exact hc.1
  · exact he

theorem march_covered {g : ℝ → ℝ} {e d2 hmin b : Float} {v : Interval} {m : March}
    (hd : Finite d2.toBits) (hb : Finite b.toBits)
    (hv : ∀ τ, value m.t.toBits ≤ τ → τ ≤ value b.toBits → Encloses v (g τ))
    (hm : Covered g d2 m) : Covered g d2 (march e d2 hmin v b m) := by
  obtain ⟨ft, fl, hc⟩ := hm
  unfold march
  by_cases h1 : (v.status == 0 && m.t ≤ b) = true
  · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
    obtain ⟨hs, htb⟩ := h1
    have htb' := (le_iff_value ft hb).mp htb
    have c0 := hv _ le_rfl htb' hs
    have hlo : Finite v.lo.toBits := c0.2.1
    by_cases h2 : d2 ≤ v.lo
    · have hd2 := (le_iff_value hd hlo).mp h2
      obtain ⟨fm, vm⟩ := fmin_value fl hlo
      simp only [hs, htb, h2, beq_self_eq_true, Bool.and_self, decide_true, ite_true]
      refine ⟨hb, fm, fun _ τ h0 hτ => ?_⟩
      rw [vm]
      by_cases hlt : value m.t.toBits ≤ τ
      · have c := (hv τ hlt hτ hs).2.2.2.1
        exact ⟨hd2.trans c, (min_le_right _ _).trans c⟩
      · have hlt' : τ < value m.t.toBits := not_le.mp hlt
        obtain ⟨c1, c2⟩ := hc (by linarith) τ h0 hlt'.le
        exact ⟨c1, (min_le_left _ _).trans c2⟩
    · simp only [hs, htb, h2, beq_self_eq_true, Bool.and_self, decide_true, ite_true, ite_false]
      split_ifs
      · exact ⟨ft, fl, hc⟩
      · exact ⟨ft, fl, hc⟩
  · simp only [h1, Bool.false_eq_true, ite_false]
    exact ⟨ft, fl, hc⟩

/-- Every search of `[0, e]` covers its part `[0, m.t]` with bounds of `g`, when each panel's
interval encloses `g` on the panel. -/
theorem search_covered {g : ℝ → ℝ} {e d2 hmin : Float} {fuel : UInt64}
    {panel : Float → Float → Interval} (he : Finite e.toBits) (hd : Finite d2.toBits)
    (hp : ∀ a b : Float, ∀ τ, value a.toBits ≤ τ → τ ≤ value b.toBits →
      Encloses (panel a b) (g τ)) :
    Covered g d2 (LeanExe.repeatWhile fuel ⟨0, 0.0, e, maxFloat⟩
      (fun m => m.status == 0 && m.t < e)
      (fun m => march e d2 hmin (panel m.t (panelEnd m.t m.h e)) (panelEnd m.t m.h e) m)) := by
  apply repeatWhile_invariant
  · refine ⟨lit_zero.1, maxFloat_finite, fun h => ?_⟩
    simp only [lit_zero.2, lt_irrefl] at h
  · intro m hm _
    exact march_covered hd (panelEnd_finite he) (fun τ h1 h2 => hp _ _ τ h1 h2) hm

/-- A search that finished with status 0 bounds `g` on `[0, e]`. -/
theorem covered_final {g : ℝ → ℝ} {d2 e : Float} {m : March} (hc : Covered g d2 m)
    (he : Finite e.toBits) (hpos : 0 < value e.toBits) (hs : searchStatus m e 3 5 = 0 ∨
      searchStatus m e 4 6 = 0) :
    Finite m.low.toBits ∧ ∀ τ, 0 ≤ τ → τ ≤ value e.toBits →
      value d2.toBits ≤ g τ ∧ value m.low.toBits ≤ g τ := by
  obtain ⟨ft, fl, hcov⟩ := hc
  have h : m.status = 0 ∧ e ≤ m.t := by
    unfold searchStatus at hs
    by_cases h0 : (m.status == 0) = true
    · by_cases h1 : e ≤ m.t
      · exact ⟨beq_iff_eq.mp h0, h1⟩
      · simp [h0, h1] at hs
    · by_cases h1 : (m.status == 1) = true <;> simp [h0, h1] at hs
  have het := (le_iff_value he ft).mp h.2
  exact ⟨fl, fun τ h0 hτ => hcov (by linarith) τ h0 (hτ.trans het)⟩

/-! ### The time of the last burn -/

/-- The facts about the time `m` after the first `k` burns of scenario `j`. -/
def LastInv (bs : List Burn) (j : ℕ) (k : ℕ) (m : Float) : Prop :=
  Finite m.toBits ∧ 0 ≤ value m.toBits ∧
    (∀ i < k, Model.runs bs.length j i = true → (bs.getD i Burn.none).t ≤ value m.toBits) ∧
    (∀ t, 0 ≤ t → (∀ i < k, Model.runs bs.length j i = true → (bs.getD i Burn.none).t ≤ t) →
      value m.toBits ≤ t)

theorem lastTime_bounds {xs : Array Float} {N j : UInt64} {bs : List Burn}
    (hN : N.toNat = bs.length) (h16 : bs.length ≤ 16) (hj : j.toNat ≤ 2 * bs.length)
    (hplan : Plan xs bs) (hfin : ∀ i < xs.size, Finite (xs[i]!).toBits) :
    LastInv bs j.toNat bs.length (lastTime xs N j) := by
  rw [← hN]
  unfold lastTime
  refine LeanExe.Dialect.loop_induction (LastInv bs j.toNat) ?_ ?_
  · refine ⟨lit_zero.1, by rw [lit_zero.2], fun i hi => absurd hi (Nat.not_lt_zero i),
      fun t ht _ => by rw [lit_zero.2]; exact ht⟩
  · intro k m hk ih
    obtain ⟨fm, m0, mle, mge⟩ := ih
    have hkN : (UInt64.ofNat k).toNat = k := by
      rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
    have hr := runs_eq (N := N) (j := j) (k := UInt64.ofNat k) (by omega) (by omega)
      (by rw [hkN]; exact hk)
    rw [hN, hkN] at hr
    by_cases hrun : Model.runs bs.length j.toNat k = true
    · simp only [hr, hrun, ite_true]
      obtain ⟨i0, -⟩ := burn_idx (k := UInt64.ofNat k) (by omega)
      rw [hkN] at i0
      have ft : Finite (rd xs (burnAt (UInt64.ofNat k))).toBits := by
        unfold rd; rw [i0]; exact hfin _ (by rw [hplan.1]; omega)
      have et : value (rd xs (burnAt (UInt64.ofNat k))).toBits = (bs.getD k Burn.none).t := by
        rw [val_rd, i0, (hplan.getD (by omega)).1]
      obtain ⟨ff, vf⟩ := fmax_value fm ft
      rw [et] at vf
      refine ⟨ff, by rw [vf]; exact m0.trans (le_max_left _ _), fun i hi hri => ?_,
        fun t ht hall => ?_⟩
      · rw [vf]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
        · exact (mle i hi hri).trans (le_max_left _ _)
        · subst hi; exact le_max_right _ _
      · rw [vf]
        exact max_le (mge t ht fun i hi hri => hall i (by omega) hri) (hall k (by omega) hrun)
    · have hf : runs N j (UInt64.ofNat k) = false := by
        rw [hr]; simpa using hrun
      simp only [hf, Bool.false_eq_true, ite_false]
      refine ⟨fm, m0, fun i hi hri => ?_, fun t ht hall =>
        mge t ht fun i hi hri => hall i (by omega) hri⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
      · exact mle i hi hri
      · subst hi; exact absurd hri hrun

/-! ### One scenario -/

/-- The squared separation at `t` of the trajectory of scenario `j` from the state `s` with the
burns `bs`. -/
noncomputable def sepSq (xs : Array Float) (s : State) (bs : List Burn) (j : ℕ) (t : ℝ) : ℝ :=
  (path (val xs 0) 0 s (select bs.length j bs) t).x ^ 2 +
    (path (val xs 0) 0 s (select bs.length j bs) t).y ^ 2 +
    (path (val xs 0) 0 s (select bs.length j bs) t).z ^ 2

/-- The squared radial and cross-track distance at `t` of the same trajectory. -/
noncomputable def rcSqAt (xs : Array Float) (s : State) (bs : List Burn) (j : ℕ) (t : ℝ) : ℝ :=
  (path (val xs 0) 0 s (select bs.length j bs) t).x ^ 2 +
    (path (val xs 0) 0 s (select bs.length j bs) t).z ^ 2

/-- The checks of burn `k`, counted from 0: its time is at least 0 for the first burn and at
least the time of the burn before it otherwise, at most `T`, and each velocity interval is
ordered. -/
def BurnOk (xs : Array Float) (k : ℕ) : Prop :=
  (k = 0 → 0 ≤ val xs 16) ∧ (0 < k → val xs (16 + 7 * (k - 1)) ≤ val xs (16 + 7 * k)) ∧
    val xs (16 + 7 * k) ≤ val xs 1 ∧ val xs (17 + 7 * k) ≤ val xs (18 + 7 * k) ∧
    val xs (19 + 7 * k) ≤ val xs (20 + 7 * k) ∧ val xs (21 + 7 * k) ≤ val xs (22 + 7 * k)

/-- The facts about a valid input that the scenarios use. -/
structure Valid (xs : Array Float) (N : UInt64) : Prop where
  size : xs.size = 16 + 7 * N.toNat
  small : N.toNat ≤ 16
  finite : ∀ i < xs.size, Finite (xs[i]!).toBits
  n_pos : 0 < val xs 0
  horizon_pos : 0 < val xs 1
  box : ∀ i < 6, val xs (4 + 2 * i) ≤ val xs (5 + 2 * i)
  burns : ∀ k < N.toNat, BurnOk xs k

theorem Valid.length {xs : Array Float} {N : UInt64} (hv : Valid xs N) {bs : List Burn}
    (hp : Plan xs bs) : N.toNat = bs.length := by
  have := hp.1; rw [hv.size] at this; omega

theorem Valid.sorted {xs : Array Float} {N : UInt64} (hv : Valid xs N) (bs : List Burn)
    (hp : Plan xs bs) : Sorted bs := by
  have hlen := hv.length hp
  let _ : Trans (fun a b : Burn => a.t ≤ b.t) (fun a b : Burn => a.t ≤ b.t)
    (fun a b : Burn => a.t ≤ b.t) := ⟨fun h1 h2 => le_trans h1 h2⟩
  refine List.isChain_iff_pairwise.mp (List.isChain_iff_getElem.mpr fun i hi => ?_)
  rw [(hp.2 i (by omega)).1, (hp.2 (i + 1) hi).1]
  have := (hv.burns (i + 1) (by omega)).2.1 (by omega)
  simpa using this

/-- Every burn of a valid plan lies in `[0, T]`. -/
theorem Valid.times {xs : Array Float} {N : UInt64} (hv : Valid xs N) {bs : List Burn}
    (hp : Plan xs bs) : ∀ b ∈ bs, 0 ≤ b.t ∧ b.t ≤ val xs 1 := by
  have hlen := hv.length hp
  intro b hb
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hb
  have hs := hv.sorted bs hp
  refine ⟨?_, ?_⟩
  · have h0 : (0 : ℝ) ≤ bs[0].t := by
      rw [(hp.2 0 (by omega)).1]
      simpa using (hv.burns 0 (by omega)).1 rfl
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h; exact h0
    · exact h0.trans (List.pairwise_iff_getElem.mp hs 0 i (by omega) hi h)
  · rw [(hp.2 i hi).1]
    exact (hv.burns i (by omega)).2.2.1

/-- A finished separation search of scenario `j` bounds the squared separation on `[0, T]`. -/
theorem sep_good {xs : Array Float} {N j : UInt64} {d2 : Float} {fuel : UInt64}
    (hv : Valid xs N) (hj : j.toNat ≤ 2 * N.toNat) (hd : Finite d2.toBits)
    (h : searchStatus (sepSearch Trig.invPi Trig.halfPi xs N j (rd xs 1) d2 fuel) (rd xs 1) 3 5
      = 0) {s : State} {bs : List Burn} (hbox : InBox xs s) (hplan : Plan xs bs) :
    let m := sepSearch Trig.invPi Trig.halfPi xs N j (rd xs 1) d2 fuel
    Finite m.low.toBits ∧ ∀ t, 0 ≤ t → t ≤ val xs 1 →
      value d2.toBits ≤ sepSq xs s bs j.toNat t ∧ value m.low.toBits ≤ sepSq xs s bs j.toNat t := by
  intro m
  have hN := hv.length hplan
  have h16 := hv.small
  have he : Finite (rd xs 1).toBits := hv.finite 1 (by rw [hv.size]; omega)
  have hn0 : val xs 0 ≠ 0 := hv.n_pos.ne'
  have hp : ∀ a b : Float, ∀ τ, value a.toBits ≤ τ → τ ≤ value b.toBits →
      Encloses (sepPanel Trig.invPi Trig.halfPi xs N j a b) (sepSq xs s bs j.toNat τ) := by
    intro a b τ h1 h2
    obtain ⟨c0, c1, c2⟩ := positionI_encloses (N := N) (j := j) (tI := make a b) hN
      (by omega) (by omega) hplan hbox (encloses_make h1 h2)
    obtain ⟨e0, e1, e2⟩ := path_position hn0 (hv.sorted bs hplan) bs.length j.toNat s τ
    have hs := sepSquare.encloses (powLog := Trig.invPi) (powExp := Trig.halfPi) c0 c1 c2
    rw [sepSquare_eq, ← e0, ← e1, ← e2] at hs
    exact encloses_nonneg hs (add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _))
  have hc : Covered (sepSq xs s bs j.toNat) d2 m :=
    search_covered (hmin := rd xs 1 * minRatio) (fuel := fuel) he hd hp
  obtain ⟨fl, hb⟩ := covered_final hc he hv.horizon_pos (Or.inl h)
  exact ⟨fl, hb⟩

/-- A finished radial and cross-track search of scenario `j` bounds the squared radial and
cross-track distance at every time after the scenario's burns. -/
theorem rc_good {xs : Array Float} {N j : UInt64} {r2 : Float} {fuel : UInt64}
    (hv : Valid xs N) (hj : j.toNat ≤ 2 * N.toNat) (hd : Finite r2.toBits)
    (h : searchStatus (rcSearch Trig.invPi Trig.halfPi xs N j (lastTime xs N j) twoPiHi r2 fuel)
      twoPiHi 4 6 = 0)
    {s : State} {bs : List Burn} (hbox : InBox xs s) (hplan : Plan xs bs) :
    let m := rcSearch Trig.invPi Trig.halfPi xs N j (lastTime xs N j) twoPiHi r2 fuel
    Finite m.low.toBits ∧ ∀ t, 0 ≤ t → (∀ b ∈ select bs.length j.toNat bs, b.t ≤ t) →
      value r2.toBits ≤ rcSqAt xs s bs j.toNat t ∧
        value m.low.toBits ≤ rcSqAt xs s bs j.toNat t := by
  intro m
  have hN := hv.length hplan
  have h16 := hv.small
  have hn0 : val xs 0 ≠ 0 := hv.n_pos.ne'
  have hsort := hv.sorted bs hplan
  obtain ⟨-, tL0, tLge, tLle⟩ := lastTime_bounds (j := j) hN (by omega) (by omega) hplan
    hv.finite
  set tL := value (lastTime xs N j).toBits
  set n := val xs 0
  have hp : ∀ a b : Float, ∀ φ, value a.toBits ≤ φ → φ ≤ value b.toBits →
      Encloses (rcPanel Trig.invPi Trig.halfPi xs N j (lastTime xs N j) a b)
        (rcSqAt xs s bs j.toNat (tL + φ / n)) := by
    intro a b φ h1 h2
    have ht : Encloses (add (point (lastTime xs N j)) (div (make a b) (point (rd xs 0))))
        (tL + φ / n) := encloses_add (encloses_point _) (encloses_div (encloses_make h1 h2)
          (encloses_point _))
    obtain ⟨c0, -, c2⟩ := positionI_encloses (N := N) (j := j) hN (by omega) (by omega) hplan hbox
      ht
    obtain ⟨e0, -, e2⟩ := path_position hn0 hsort bs.length j.toNat s (tL + φ / n)
    have hs := rcSquare.encloses (powLog := Trig.invPi) (powExp := Trig.halfPi) c0 c2
    rw [rcSquare_eq, ← e0, ← e2] at hs
    exact encloses_nonneg hs (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hc : Covered (fun φ => rcSqAt xs s bs j.toNat (tL + φ / n)) r2 m :=
    search_covered (hmin := twoPiHi * minRatio) (fuel := fuel) twoPiHi_bounds.1 hd hp
  obtain ⟨fl, hb⟩ := covered_final hc twoPiHi_bounds.1
    (lt_of_lt_of_le (by positivity) twoPiHi_bounds.2) (Or.inr h)
  refine ⟨fl, fun t ht hall => ?_⟩
  have hidx : ∀ i < bs.length, Model.runs bs.length j.toNat i = true →
      (bs.getD i Burn.none).t ≤ t := fun i hi hr =>
    hall _ (mem_selectFrom bs.length j.toNat 0 bs i hi (by simpa using hr))
  have hle : tL ≤ t := tLle t ht hidx
  have hafter : ∀ b ∈ select bs.length j.toNat bs, b.t ≤ tL := by
    intro b hb
    obtain ⟨i, hi, hr, e⟩ := exists_of_mem_selectFrom bs.length j.toNat 0 bs b hb
    rw [← e]
    exact tLge i hi (by simpa using hr)
  set P := path n 0 s (select bs.length j.toNat bs) tL
  obtain ⟨φ, hφ, ex, ez⟩ := flow_phase hn0 (t - tL) P
  have hφn : 0 ≤ φ / n := div_nonneg hφ.1 hv.n_pos.le
  have e1 := path_after hn0 (hsort.select bs.length j.toNat) s hafter hle
  have e2 := path_after hn0 (hsort.select bs.length j.toNat) s hafter
    (show tL ≤ tL + φ / n by linarith)
  have hb' := hb φ hφ.1 (hφ.2.le.trans twoPiHi_bounds.2)
  have key : rcSqAt xs s bs j.toNat t = rcSqAt xs s bs j.toNat (tL + φ / n) := by
    unfold rcSqAt
    rw [e1, e2, show tL + φ / n - tL = φ / n by ring, ex, ez]
  rw [key]
  exact hb'

/-! ### The scenarios -/

/-- The bounds of the searches of the scenarios before `k`, for the state `s` and the burns
`bs`. -/
def Bounded (xs : Array Float) (d2 r2 L R : Float) (s : State) (bs : List Burn) (k : ℕ) : Prop :=
  Finite L.toBits ∧ Finite R.toBits ∧ ∀ j < k,
    (∀ t, 0 ≤ t → t ≤ val xs 1 →
      value d2.toBits ≤ sepSq xs s bs j t ∧ value L.toBits ≤ sepSq xs s bs j t) ∧
    (∀ t, 0 ≤ t → (∀ b ∈ select bs.length j bs, b.t ≤ t) →
      value r2.toBits ≤ rcSqAt xs s bs j t ∧ value R.toBits ≤ rcSqAt xs s bs j t)

theorem scan_sound {xs : Array Float} {N fuel : UInt64} {d2 r2 : Float} (hv : Valid xs N)
    (hd : Finite d2.toBits) (hr : Finite r2.toBits)
    (h : (LeanExe.loop (2 * N + 1) (⟨0, 0, 0.0, maxFloat, maxFloat⟩ : Scan)
      fun j s => scanStep Trig.invPi Trig.halfPi xs N fuel d2 r2 j s).status = 0)
    {s : State} {bs : List Burn} (hbox : InBox xs s) (hplan : Plan xs bs) :
    let sc := LeanExe.loop (2 * N + 1) (⟨0, 0, 0.0, maxFloat, maxFloat⟩ : Scan)
      fun j s => scanStep Trig.invPi Trig.halfPi xs N fuel d2 r2 j s
    Bounded xs d2 r2 sc.sepLow sc.rcLow s bs (2 * bs.length + 1) := by
  intro sc
  have hN := hv.length hplan
  have hcount : (2 * N + 1).toNat = 2 * bs.length + 1 := by
    have := hv.small
    simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.reduceToNat]
    omega
  have key := LeanExe.Dialect.loop_induction (n := 2 * N + 1)
    (init := (⟨0, 0, 0.0, maxFloat, maxFloat⟩ : Scan))
    (f := fun j s => scanStep Trig.invPi Trig.halfPi xs N fuel d2 r2 j s)
    (fun k (sc : Scan) => sc.status = 0 → Bounded xs d2 r2 sc.sepLow sc.rcLow s bs k)
    (fun _ => ⟨maxFloat_finite, maxFloat_finite, fun j hj => absurd hj (Nat.not_lt_zero j)⟩)
    (by
      intro k sc hk ih hs
      have hkN : (UInt64.ofNat k).toNat = k := by
        rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by have := hv.small; omega)
      have hj : (UInt64.ofNat k).toNat ≤ 2 * N.toNat := by rw [hkN]; omega
      unfold scanStep at hs ⊢
      by_cases h0 : (sc.status == 0) = true
      · have ih' := ih (beq_iff_eq.mp h0)
        obtain ⟨fL, fR, hprev⟩ := ih'
        simp only [h0, ite_true] at hs ⊢
        by_cases h1 : searchStatus (sepSearch Trig.invPi Trig.halfPi xs N (UInt64.ofNat k)
            (rd xs 1) d2 fuel) (rd xs 1) 3 5 = 0
        · by_cases h2 : searchStatus (rcSearch Trig.invPi Trig.halfPi xs N (UInt64.ofNat k)
              (lastTime xs N (UInt64.ofNat k)) twoPiHi r2 fuel) twoPiHi 4 6 = 0
          · simp only [h1, h2, beq_self_eq_true, ite_true]
            obtain ⟨fm, hm⟩ := sep_good hv hj hd h1 hbox hplan
            obtain ⟨fr, hrc⟩ := rc_good hv hj hr h2 hbox hplan
            rw [hkN] at hm hrc
            obtain ⟨fL', vL⟩ := fmin_value fL fm
            obtain ⟨fR', vR⟩ := fmin_value fR fr
            refine ⟨fL', fR', fun j hjk => ?_⟩
            rw [vL, vR]
            rcases Nat.lt_succ_iff_lt_or_eq.mp hjk with hjk | hjk
            · obtain ⟨a, b⟩ := hprev j hjk
              exact ⟨fun t h1 h2 => ⟨(a t h1 h2).1, (min_le_left _ _).trans (a t h1 h2).2⟩,
                fun t h1 h2 => ⟨(b t h1 h2).1, (min_le_left _ _).trans (b t h1 h2).2⟩⟩
            · subst hjk
              exact ⟨fun t h1 h2 => ⟨(hm t h1 h2).1, (min_le_right _ _).trans (hm t h1 h2).2⟩,
                fun t h1 h2 => ⟨(hrc t h1 h2).1, (min_le_right _ _).trans (hrc t h1 h2).2⟩⟩
          · simp only [h1, h2, beq_self_eq_true, ite_true, beq_iff_eq, ite_false] at hs
        · simp only [h1, beq_iff_eq, ite_false] at hs
      · simp only [h0, Bool.false_eq_true, ite_false] at hs
        exact absurd (beq_iff_eq.mpr hs) h0)
  rw [hcount] at key
  exact key h

/-! ### The checks of the input -/

theorem square_bound {x : Float} (hx : Finite x.toBits) (h0 : 0 ≤ value x.toBits)
    (hs : (square x).status = 0) :
    Finite (square x).hi.toBits ∧ value x.toBits ^ 2 ≤ value (square x).hi.toBits := by
  unfold square at hs ⊢
  by_cases hp : (0.0 : Float) < x
  · simp only [hp, ite_true] at hs ⊢
    have c := encloses_sq (encloses_point x) hs
    exact ⟨c.2.2.1, by rw [pow_two]; exact c.2.2.2.2⟩
  · simp only [hp, ite_false] at hs ⊢
    have c := encloses_zero hs
    have hz : value x.toBits = 0 := by
      have := (lt_iff_value lit_zero.1 hx).not.mp hp
      rw [lit_zero.2] at this
      linarith
    rw [hz]
    exact ⟨c.2.2.1, by simpa using c.2.2.2.2⟩

theorem sqrtDown_le (x : Float) :
    Finite (sqrtDown x).toBits ∧ value (sqrtDown x).toBits ≤ √(value x.toBits) := by
  unfold sqrtDown
  by_cases hs : (sqrt (point x)).status = 0
  · have c := encloses_sqrt (encloses_point x) hs
    obtain ⟨f, v⟩ := fmax_value lit_zero.1 c.2.1
    rw [v, lit_zero.2]
    exact ⟨f, max_le (Real.sqrt_nonneg _) c.2.2.2.1⟩
  · have e : (sqrt (point x)).lo = rejected.lo := by
      unfold Library.Numerics.Interval.sqrt join at hs ⊢
      split_ifs with hc
      · simp [hc] at hs
      · rfl
    rw [e]
    obtain ⟨f, v⟩ := fmax_value lit_zero.1 rejected_lo.1
    rw [v, lit_zero.2, rejected_lo.2, max_self]
    exact ⟨f, Real.sqrt_nonneg _⟩

/-- The returned bound `fmax d (sqrtDown L)` lies between `d` and every quantity whose square is
at least `d²` and `L`. -/
theorem bound_between {d L : Float} {q : ℝ} (hd : Finite d.toBits) (h0 : 0 ≤ value d.toBits)
    (hq : 0 ≤ q) (h1 : value d.toBits ^ 2 ≤ q ^ 2)
    (h2 : value L.toBits ≤ q ^ 2) :
    value d.toBits ≤ value (fmax d (sqrtDown L)).toBits ∧
      value (fmax d (sqrtDown L)).toBits ≤ q := by
  obtain ⟨fs, vs⟩ := sqrtDown_le L
  obtain ⟨-, v⟩ := fmax_value hd fs
  rw [v]
  refine ⟨le_max_left _ _, max_le ?_ ?_⟩
  · exact (pow_le_pow_iff_left₀ h0 hq two_ne_zero).mp h1
  · calc value (sqrtDown L).toBits ≤ √(value L.toBits) := vs
      _ ≤ √(q ^ 2) := Real.sqrt_le_sqrt h2
      _ = q := Real.sqrt_sq hq

theorem finiteAll_sound {xs : Array Float} (hsize : xs.size < 2 ^ 64)
    (h : finiteAll xs = true) : ∀ i < xs.size, Finite (xs[i]!).toBits := by
  have hs : xs.size.toUInt64.toNat = xs.size := by
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt hsize
  have key := LeanExe.Dialect.loop_induction (n := xs.size.toUInt64) (init := true)
    (f := fun i ok => ok && finite (rd xs i))
    (fun k ok => ok = true → ∀ i < k, Finite (xs[i]!).toBits)
    (fun _ i hi => absurd hi (Nat.not_lt_zero i))
    (by
      intro k ok hk ih hok
      simp only [Bool.and_eq_true] at hok
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
      · exact ih hok.1 i hi
      · subst hi
        have e : (UInt64.ofNat i).toNat = i := by
          rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
        have := (finite_iff _).mp hok.2
        unfold rd at this
        rwa [e] at this)
  rw [hs] at key
  exact key h

/-- The facts that `checkWith` establishes before its scenarios. -/
theorem burn_idx' {k : UInt64} (hk : k.toNat < 16) :
    (burnAt k + 2).toNat = 18 + 7 * k.toNat ∧ (burnAt k + 4).toNat = 20 + 7 * k.toNat ∧
      (burnAt k + 6).toNat = 22 + 7 * k.toNat := by
  simp only [burnAt, UInt64.toNat_add, UInt64.toNat_mul, UInt64.reduceToNat]
  omega

theorem valid_of {xs : Array Float} {fuel : UInt64} (hsize : xs.size < 2 ^ 64)
    (hg : (16 ≤ xs.size.toUInt64 && (xs.size.toUInt64 - 16) % 7 == 0 &&
      xs.size.toUInt64 ≤ 128 && 1 ≤ fuel && fuel ≤ 1048576) = true)
    (hval : valuesOk xs ((xs.size.toUInt64 - 16) / 7) = true) :
    Valid xs ((xs.size.toUInt64 - 16) / 7) ∧ 0 ≤ val xs 2 ∧ 0 ≤ val xs 3 := by
  have hs : xs.size.toUInt64.toNat = xs.size := by
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt hsize
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hg
  obtain ⟨⟨⟨⟨g16, g7⟩, g128⟩, -⟩, -⟩ := hg
  have h16 : 16 ≤ xs.size := by
    have := UInt64.le_iff_toNat_le.mp g16; rw [hs] at this; simpa using this
  have h128 : xs.size ≤ 128 := by
    have := UInt64.le_iff_toNat_le.mp g128; rw [hs] at this; simpa using this
  have hsub : (xs.size.toUInt64 - 16).toNat = xs.size - 16 := by
    rw [UInt64.toNat_sub_of_le _ _ g16, hs]; rfl
  have h7 : (xs.size - 16) % 7 = 0 := by
    have := congrArg UInt64.toNat g7
    rw [UInt64.toNat_mod, hsub] at this
    simpa using this
  have hNv : ((xs.size.toUInt64 - 16) / 7).toNat = (xs.size - 16) / 7 := by
    rw [UInt64.toNat_div, hsub]; rfl
  set N := (xs.size.toUInt64 - 16) / 7
  simp only [valuesOk, Bool.and_eq_true, decide_eq_true_eq] at hval
  obtain ⟨⟨⟨⟨⟨⟨hfin, hn⟩, hT⟩, hd⟩, hr⟩, hbox⟩, hburns⟩ := hval
  have fin := finiteAll_sound hsize hfin
  have le_of {a b : UInt64} (ha : a.toNat < xs.size) (hb : b.toNat < xs.size)
      (h : rd xs a ≤ rd xs b) : val xs a.toNat ≤ val xs b.toNat :=
    (le_iff_value (fin _ ha) (fin _ hb)).mp h
  have idx (i : ℕ) (hi : i < 16) : (UInt64.ofNat i).toNat = i := by
    rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  have f (i : ℕ) (hi : i < 16) : Finite (rd xs (UInt64.ofNat i)).toBits := by
    unfold rd; rw [idx i hi]; exact fin i (by omega)
  have pos (i : ℕ) (hi : i < 16) (h : (0.0 : Float) < rd xs (UInt64.ofNat i)) :
      0 < val xs i := by
    have := (lt_iff_value lit_zero.1 (f i hi)).mp h
    rwa [lit_zero.2, val_rd, idx i hi] at this
  have nonneg (i : ℕ) (hi : i < 16) (h : (0.0 : Float) ≤ rd xs (UInt64.ofNat i)) :
      0 ≤ val xs i := by
    have := (le_iff_value lit_zero.1 (f i hi)).mp h
    rwa [lit_zero.2, val_rd, idx i hi] at this
  have hboxes : ∀ i < 6, val xs (4 + 2 * i) ≤ val xs (5 + 2 * i) := by
    have key := LeanExe.Dialect.loop_induction (n := 6) (init := true)
      (f := fun i ok => ok && rd xs (4 + 2 * i) ≤ rd xs (5 + 2 * i))
      (fun k ok => ok = true → ∀ i < k, val xs (4 + 2 * i) ≤ val xs (5 + 2 * i))
      (fun _ i hi => absurd hi (Nat.not_lt_zero i))
      (by
        intro k ok hk ih hok
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
        intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
        · exact ih hok.1 i hi
        · subst hi
          have hk6 : i < 6 := by simpa using hk
          have e4 : (4 + 2 * UInt64.ofNat i).toNat = 4 + 2 * i := by
            simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.reduceToNat, idx i (by omega)]
            omega
          have e5 : (5 + 2 * UInt64.ofNat i).toNat = 5 + 2 * i := by
            simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.reduceToNat, idx i (by omega)]
            omega
          have := le_of (by rw [e4]; omega) (by rw [e5]; omega) hok.2
          rwa [e4, e5] at this)
    simpa using key hbox
  have hburn : ∀ k < N.toNat, BurnOk xs k := by
    have key := LeanExe.Dialect.loop_induction (n := N) (init := true)
      (f := fun k ok =>
        let i := burnAt k
        let prev := if k == 0 then 0.0 else rd xs (i - 7)
        ok && prev ≤ rd xs i && rd xs i ≤ rd xs 1 && rd xs (i + 1) ≤ rd xs (i + 2) &&
          rd xs (i + 3) ≤ rd xs (i + 4) && rd xs (i + 5) ≤ rd xs (i + 6))
      (fun k ok => ok = true → ∀ i < k, BurnOk xs i)
      (fun _ i hi => absurd hi (Nat.not_lt_zero i))
      (by
        intro k ok hk ih hok
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
        obtain ⟨⟨⟨⟨⟨hok', hprev⟩, hlate⟩, hx⟩, hy⟩, hz⟩ := hok
        intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
        · exact ih hok' i hi
        · subst hi
          have hkN := idx i (by omega)
          obtain ⟨i0, i1, -, i3, -, i5, -⟩ := burn_idx (k := UInt64.ofNat i) (by omega)
          obtain ⟨i2, i4, i6⟩ := burn_idx' (k := UInt64.ofNat i) (by omega)
          rw [hkN] at i0 i1 i2 i3 i4 i5 i6
          have h1 : (1 : UInt64).toNat = 1 := rfl
          have small : 22 + 7 * i < xs.size := by omega
          refine ⟨fun h0 => ?_, fun h0 => ?_, ?_, ?_, ?_, ?_⟩
          · subst h0
            have hz0 : (UInt64.ofNat 0 == 0) = true := rfl
            simp only [hz0, ite_true] at hprev
            have := (le_iff_value lit_zero.1 (fin _ (show (burnAt (UInt64.ofNat 0)).toNat <
              xs.size by rw [i0]; omega))).mp hprev
            rw [lit_zero.2, i0] at this
            simpa [val] using this
          · have hne : (UInt64.ofNat i == 0) = false := by
              simp only [beq_eq_false_iff_ne, ne_eq]
              intro e; rw [e] at hkN; simp at hkN; omega
            simp only [hne, Bool.false_eq_true, ite_false] at hprev
            have i7 : (burnAt (UInt64.ofNat i) - 7).toNat = 16 + 7 * (i - 1) := by
              rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
                rw [i0]; simp only [UInt64.reduceToNat]; omega))]
              rw [i0]; simp; omega
            have := le_of (by rw [i7]; omega) (by rw [i0]; omega) hprev
            rwa [i7, i0] at this
          · have := le_of (by rw [i0]; omega) (by rw [h1]; omega) hlate
            rwa [i0, h1] at this
          · have := le_of (by rw [i1]; omega) (by rw [i2]; omega) hx
            rwa [i1, i2] at this
          · have := le_of (by rw [i3]; omega) (by rw [i4]; omega) hy
            rwa [i3, i4] at this
          · have := le_of (by rw [i5]; omega) (by rw [i6]; omega) hz
            rwa [i5, i6] at this)
    exact key hburns
  exact ⟨⟨by omega, by omega, fin, pos 0 (by omega) hn, pos 1 (by omega) hT, hboxes, hburn⟩,
    nonneg 2 (by omega) hd, nonneg 3 (by omega) hr⟩

/-- A valid input has a state in its box and a plan that matches it. -/
theorem Valid.exists {xs : Array Float} {N : UInt64} (hv : Valid xs N) :
    (∃ s, InBox xs s) ∧ ∃ bs, Plan xs bs := by
  refine ⟨⟨⟨val xs 4, val xs 6, val xs 8, val xs 10, val xs 12, val xs 14⟩, ?_⟩, ?_⟩
  · have b := hv.box
    exact ⟨le_rfl, b 0 (by omega), le_rfl, b 1 (by omega), le_rfl, b 2 (by omega), le_rfl,
      b 3 (by omega), le_rfl, b 4 (by omega), le_rfl, b 5 (by omega)⟩
  · refine ⟨List.ofFn fun i : Fin N.toNat =>
      ⟨val xs (16 + 7 * i), val xs (17 + 7 * i), val xs (19 + 7 * i), val xs (21 + 7 * i)⟩,
      by rw [List.length_ofFn, hv.size], fun i hi => ?_⟩
    rw [List.length_ofFn] at hi
    obtain ⟨-, -, -, hx, hy, hz⟩ := hv.burns i hi
    simpa [List.getElem_ofFn] using ⟨hx, hy, hz⟩

theorem bound_lower {d L : Float} (hd : Finite d.toBits) :
    value d.toBits ≤ value (fmax d (sqrtDown L)).toBits := by
  obtain ⟨fs, -⟩ := sqrtDown_le L
  obtain ⟨-, v⟩ := fmax_value hd fs
  rw [v]
  exact le_max_left _ _

/-! ### The theorems -/

/-- The input of an accepted check is valid, with thresholds at least 0. -/
theorem accepted_valid {xs : Array Float} {fuel : UInt64} (hsize : xs.size < 2 ^ 64)
    (h : (check xs fuel).status = 0) :
    Valid xs ((xs.size.toUInt64 - 16) / 7) ∧ 0 ≤ val xs 2 ∧ 0 ≤ val xs 3 := by
  unfold check checkWith at h
  by_cases hg : (16 ≤ xs.size.toUInt64 && (xs.size.toUInt64 - 16) % 7 == 0 &&
      xs.size.toUInt64 ≤ 128 && 1 ≤ fuel && fuel ≤ 1048576) = true
  · simp only [hg, ite_true] at h
    by_cases hval : valuesOk xs ((xs.size.toUInt64 - 16) / 7) = true
    · exact valid_of hsize hg hval
    · simp only [hval, Bool.false_eq_true, ite_false] at h
      exact absurd h (by decide)
  · simp only [hg, Bool.false_eq_true, ite_false] at h
    exact absurd h (by decide)

/-- When `check` accepts, the input holds `16 + 7N` values with `N ≤ 16`, the box of initial
states and the plan's boxes are not empty, and the burns of every list that matches the plan are
in nondecreasing order of time and lie in `[0, T]`. -/
theorem check_input {xs : Array Float} {fuel : UInt64} (hsize : xs.size < 2 ^ 64)
    (h : (check xs fuel).status = 0) :
    (∃ N ≤ 16, xs.size = 16 + 7 * N) ∧ (∃ s, InBox xs s) ∧ (∃ bs, Plan xs bs) ∧
      ∀ bs, Plan xs bs → Sorted bs ∧ ∀ b ∈ bs, 0 ≤ b.t ∧ b.t ≤ val xs 1 := by
  obtain ⟨hv, -, -⟩ := accepted_valid hsize h
  exact ⟨⟨_, hv.small, hv.size⟩, hv.exists.1, hv.exists.2,
    fun bs hp => ⟨hv.sorted bs hp, hv.times hp⟩⟩

/-- When `check` accepts, the real values of the inputs satisfy `n > 0`, `T > 0`, `dmin ≥ 0`, and
`drc ≥ 0`, and `sep` and `rc` are at least `dmin` and `drc`.  For every initial state in the box,
every list of burns at the plan's times with velocity changes in the plan's boxes, and every
scenario `j ≤ 2N`, the separation at every `t` in `[0, T]` is at least `sep`, and the radial and
cross-track distance at every `t ≥ 0` at or after every burn of the scenario is at least `rc`. -/
theorem check_sound {xs : Array Float} {fuel : UInt64} (hsize : xs.size < 2 ^ 64)
    (h : (check xs fuel).status = 0) :
    0 < val xs 0 ∧ 0 < val xs 1 ∧ 0 ≤ val xs 2 ∧ 0 ≤ val xs 3 ∧
      val xs 2 ≤ value (check xs fuel).sep.toBits ∧ val xs 3 ≤ value (check xs fuel).rc.toBits ∧
      ∀ s bs, InBox xs s → Plan xs bs → ∀ j ≤ 2 * bs.length,
        (∀ t, 0 ≤ t → t ≤ val xs 1 →
          value (check xs fuel).sep.toBits ≤
            separation (path (val xs 0) 0 s (select bs.length j bs) t)) ∧
        (∀ t, 0 ≤ t → (∀ b ∈ select bs.length j bs, b.t ≤ t) →
          value (check xs fuel).rc.toBits ≤
            rcDistance (path (val xs 0) 0 s (select bs.length j bs) t)) := by
  unfold check checkWith at h ⊢
  by_cases hg : (16 ≤ xs.size.toUInt64 && (xs.size.toUInt64 - 16) % 7 == 0 &&
      xs.size.toUInt64 ≤ 128 && 1 ≤ fuel && fuel ≤ 1048576) = true
  · simp only [hg, ite_true] at h ⊢
    by_cases hval : valuesOk xs ((xs.size.toUInt64 - 16) / 7) = true
    · simp only [hval, ite_true] at h ⊢
      obtain ⟨hv, hd0, hr0⟩ := valid_of hsize hg hval
      set N := (xs.size.toUInt64 - 16) / 7
      have f2 : Finite (rd xs 2).toBits := hv.finite 2 (by rw [hv.size]; omega)
      have f3 : Finite (rd xs 3).toBits := hv.finite 3 (by rw [hv.size]; omega)
      by_cases hs : ((square (rd xs 2)).status == 0 && (square (rd xs 3)).status == 0) = true
      · simp only [hs, ite_true] at h ⊢
        simp only [Bool.and_eq_true, beq_iff_eq] at hs
        obtain ⟨fd, vd⟩ := square_bound f2 hd0 hs.1
        obtain ⟨fr, vr⟩ := square_bound f3 hr0 hs.2
        set sc := LeanExe.loop (2 * N + 1) (⟨0, 0, 0.0, maxFloat, maxFloat⟩ : Scan)
          fun j s => scanStep Trig.invPi Trig.halfPi xs N fuel (square (rd xs 2)).hi
            (square (rd xs 3)).hi j s
        by_cases h0 : (sc.status == 0) = true
        · simp only [h0, ite_true] at h ⊢
          have d0 : 0 ≤ value (rd xs 2).toBits := hd0
          have r0 : 0 ≤ value (rd xs 3).toBits := hr0
          refine ⟨hv.n_pos, hv.horizon_pos, hd0, hr0, bound_lower f2, bound_lower f3,
            fun s bs hbox hplan j hj => ?_⟩
          obtain ⟨-, -, hb⟩ := scan_sound hv fd fr (beq_iff_eq.mp h0) hbox hplan
          obtain ⟨hsep, hrc⟩ := hb j (by omega)
          refine ⟨fun t h1 h2 => ?_, fun t h1 h2 => ?_⟩
          · obtain ⟨a, b⟩ := hsep t h1 h2
            have hq : 0 ≤ sepSq xs s bs j t := by unfold sepSq; positivity
            have e : √(sepSq xs s bs j t) ^ 2 = sepSq xs s bs j t := Real.sq_sqrt hq
            exact (bound_between (q := √(sepSq xs s bs j t)) f2 d0 (Real.sqrt_nonneg _)
              (by rw [e]; exact vd.trans a) (by rw [e]; exact b)).2
          · obtain ⟨a, b⟩ := hrc t h1 h2
            have hq : 0 ≤ rcSqAt xs s bs j t := by unfold rcSqAt; positivity
            have e : √(rcSqAt xs s bs j t) ^ 2 = rcSqAt xs s bs j t := Real.sq_sqrt hq
            exact (bound_between (q := √(rcSqAt xs s bs j t)) f3 r0 (Real.sqrt_nonneg _)
              (by rw [e]; exact vr.trans a) (by rw [e]; exact b)).2
        · simp only [h0, Bool.false_eq_true, ite_false] at h
          exact absurd (beq_iff_eq.mpr h) h0
      · simp only [hs, Bool.false_eq_true, ite_false] at h
        exact absurd h (by decide)
    · simp only [hval, Bool.false_eq_true, ite_false] at h
      exact absurd h (by decide)
  · simp only [hg, Bool.false_eq_true, ite_false] at h
    exact absurd h (by decide)

/-- Passive safety: when `check` accepts, every trajectory of every scenario from the boxes keeps
a separation of at least `min dmin drc` at every time `t ≥ 0`, since every burn lies in `[0, T]`
and the radial and cross-track distance is at most the separation. -/
theorem check_passive {xs : Array Float} {fuel : UInt64} (hsize : xs.size < 2 ^ 64)
    (h : (check xs fuel).status = 0) :
    ∀ s bs, InBox xs s → Plan xs bs → ∀ j ≤ 2 * bs.length, ∀ t, 0 ≤ t →
      min (val xs 2) (val xs 3) ≤ separation (path (val xs 0) 0 s (select bs.length j bs) t) := by
  obtain ⟨-, -, -, -, hsep, hrc, hall⟩ := check_sound hsize h
  obtain ⟨-, -, -, hburns⟩ := check_input hsize h
  intro s bs hbox hplan j hj t ht
  obtain ⟨hs, hr⟩ := hall s bs hbox hplan j hj
  by_cases hT : t ≤ val xs 1
  · exact (min_le_left _ _).trans (hsep.trans (hs t ht hT))
  · have hb : ∀ b ∈ select bs.length j bs, b.t ≤ t := fun b hb =>
      ((hburns bs hplan).2 b ((selectFrom_sublist _ _ 0 bs).subset hb)).2.trans
        (le_of_lt (not_le.mp hT))
    refine (min_le_right _ _).trans (hrc.trans ((hr t ht hb).trans ?_))
    unfold rcDistance separation
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (path (val xs 0) 0 s
      (select bs.length j bs) t).y])

#print axioms check_sound

end Demos.PassiveSafety
