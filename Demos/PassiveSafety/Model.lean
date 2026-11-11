import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Algebra.Order.ToIntervalMod

/-!
The Hill–Clohessy–Wiltshire model of a deputy's motion relative to a chief in a circular orbit of
mean motion `n`, in the chief's local-vertical, local-horizontal frame: `x` radial, `y` along the
chief's velocity, and `z` along the orbit normal.  The equations are

`ẍ = 3n²x + 2nẏ`,  `ÿ = −2nẋ`,  `z̈ = −n²z`.

`flow n τ s` is their closed-form solution at time `τ` from the state `s` at time 0, the definition
of the model.  `flow_hasDerivAt` states that it solves the equations, `flow_zero` that it starts at
`s`, and `flow_unique` that every solution with the value `s` at 0 equals it.  `path` executes a
list of impulsive burns, `path_eq` writes the result as the closed form from the initial state
plus the closed form of each burn's velocity change, and `select` gives the burns of each
scenario of a plan.
-/

namespace Demos.PassiveSafety.Model

open Real

/-! ### States and the closed form -/

/-- A state of the deputy relative to the chief: the position `x`, `y`, `z` and the velocity
`vx`, `vy`, `vz`. -/
@[ext] structure State where
  x : ℝ
  y : ℝ
  z : ℝ
  vx : ℝ
  vy : ℝ
  vz : ℝ

namespace State

instance : Add State :=
  ⟨fun a b => ⟨a.x + b.x, a.y + b.y, a.z + b.z, a.vx + b.vx, a.vy + b.vy, a.vz + b.vz⟩⟩

instance : Zero State := ⟨⟨0, 0, 0, 0, 0, 0⟩⟩

@[simp] theorem add_x (a b : State) : (a + b).x = a.x + b.x := rfl
@[simp] theorem add_y (a b : State) : (a + b).y = a.y + b.y := rfl
@[simp] theorem add_z (a b : State) : (a + b).z = a.z + b.z := rfl
@[simp] theorem add_vx (a b : State) : (a + b).vx = a.vx + b.vx := rfl
@[simp] theorem add_vy (a b : State) : (a + b).vy = a.vy + b.vy := rfl
@[simp] theorem add_vz (a b : State) : (a + b).vz = a.vz + b.vz := rfl
@[simp] theorem zero_x : (0 : State).x = 0 := rfl
@[simp] theorem zero_y : (0 : State).y = 0 := rfl
@[simp] theorem zero_z : (0 : State).z = 0 := rfl
@[simp] theorem zero_vx : (0 : State).vx = 0 := rfl
@[simp] theorem zero_vy : (0 : State).vy = 0 := rfl
@[simp] theorem zero_vz : (0 : State).vz = 0 := rfl

theorem add_zero (a : State) : a + 0 = a := by ext <;> simp

theorem zero_add (a : State) : 0 + a = a := by ext <;> simp

theorem add_assoc (a b c : State) : a + b + c = a + (b + c) := by ext <;> simp <;> ring

end State

/-- The state at time `τ` of a deputy whose state at time 0 is `s`, the closed-form solution of
the equations. -/
noncomputable def flow (n τ : ℝ) (s : State) : State where
  x := (4 - 3 * cos (n * τ)) * s.x + sin (n * τ) / n * s.vx + 2 / n * (1 - cos (n * τ)) * s.vy
  y := 6 * (sin (n * τ) - n * τ) * s.x + s.y - 2 / n * (1 - cos (n * τ)) * s.vx +
    (4 * sin (n * τ) - 3 * (n * τ)) / n * s.vy
  z := cos (n * τ) * s.z + sin (n * τ) / n * s.vz
  vx := 3 * n * sin (n * τ) * s.x + cos (n * τ) * s.vx + 2 * sin (n * τ) * s.vy
  vy := -(6 * n * (1 - cos (n * τ))) * s.x - 2 * sin (n * τ) * s.vx +
    (4 * cos (n * τ) - 3) * s.vy
  vz := -(n * sin (n * τ)) * s.z + cos (n * τ) * s.vz

/-- The right-hand side of the equations as a first-order system. -/
def field (n : ℝ) (s : State) : State where
  x := s.vx
  y := s.vy
  z := s.vz
  vx := 3 * n ^ 2 * s.x + 2 * n * s.vy
  vy := -(2 * n * s.vx)
  vz := -(n ^ 2 * s.z)

/-- `f` satisfies the equations at `t`: each component of `f` has at `t` the derivative that
`field` gives for the state `f t`. -/
def Solves (n : ℝ) (f : ℝ → State) (t : ℝ) : Prop :=
  HasDerivAt (fun u => (f u).x) (field n (f t)).x t ∧
  HasDerivAt (fun u => (f u).y) (field n (f t)).y t ∧
  HasDerivAt (fun u => (f u).z) (field n (f t)).z t ∧
  HasDerivAt (fun u => (f u).vx) (field n (f t)).vx t ∧
  HasDerivAt (fun u => (f u).vy) (field n (f t)).vy t ∧
  HasDerivAt (fun u => (f u).vz) (field n (f t)).vz t

/-! ### The closed form solves the equations -/

/-- The derivative of a combination of `sin (n u)`, `cos (n u)`, and `n u`. -/
theorem hasDerivAt_trig (n a b c d t : ℝ) :
    HasDerivAt (fun u => a + b * sin (n * u) + c * cos (n * u) + d * (n * u))
      (b * (n * cos (n * t)) - c * (n * sin (n * t)) + d * n) t := by
  have h1 : HasDerivAt (fun u => n * u) n t := by
    simpa using (hasDerivAt_id t).const_mul n
  exact ((((h1.sin.const_mul b).const_add a).add (h1.cos.const_mul c)).add
    (h1.const_mul d)).congr_deriv (by ring)

theorem flow_hasDerivAt {n : ℝ} (hn : n ≠ 0) (s : State) (t : ℝ) :
    Solves n (fun u => flow n u s) t := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e : (fun u => (flow n u s).x) = fun u =>
        (4 * s.x + 2 / n * s.vy) + s.vx / n * sin (n * u) + (-3 * s.x - 2 / n * s.vy) *
          cos (n * u) + 0 * (n * u) := by
      funext u; simp only [flow]; ring
    rw [e]
    refine (hasDerivAt_trig n _ _ _ _ t).congr_deriv ?_
    simp only [field, flow]; field_simp; ring
  · have e : (fun u => (flow n u s).y) = fun u =>
        (s.y - 2 / n * s.vx) + (6 * s.x + 4 / n * s.vy) * sin (n * u) + 2 / n * s.vx *
          cos (n * u) + (-6 * s.x - 3 / n * s.vy) * (n * u) := by
      funext u; simp only [flow]; ring
    rw [e]
    refine (hasDerivAt_trig n _ _ _ _ t).congr_deriv ?_
    simp only [field, flow]; field_simp; ring
  · have e : (fun u => (flow n u s).z) = fun u =>
        0 + s.vz / n * sin (n * u) + s.z * cos (n * u) + 0 * (n * u) := by
      funext u; simp only [flow]; ring
    rw [e]
    refine (hasDerivAt_trig n _ _ _ _ t).congr_deriv ?_
    simp only [field, flow]; field_simp; ring
  · have e : (fun u => (flow n u s).vx) = fun u =>
        0 + (3 * n * s.x + 2 * s.vy) * sin (n * u) + s.vx * cos (n * u) + 0 * (n * u) := by
      funext u; simp only [flow]; ring
    rw [e]
    refine (hasDerivAt_trig n _ _ _ _ t).congr_deriv ?_
    simp only [field, flow]; field_simp; ring
  · have e : (fun u => (flow n u s).vy) = fun u =>
        (-6 * n * s.x - 3 * s.vy) + (-2 * s.vx) * sin (n * u) + (6 * n * s.x + 4 * s.vy) *
          cos (n * u) + 0 * (n * u) := by
      funext u; simp only [flow]; ring
    rw [e]
    refine (hasDerivAt_trig n _ _ _ _ t).congr_deriv ?_
    simp only [field, flow]; field_simp; ring
  · have e : (fun u => (flow n u s).vz) = fun u =>
        0 + (-(n * s.z)) * sin (n * u) + s.vz * cos (n * u) + 0 * (n * u) := by
      funext u; simp only [flow]; ring
    rw [e]
    refine (hasDerivAt_trig n _ _ _ _ t).congr_deriv ?_
    simp only [field, flow]; field_simp; ring

theorem flow_zero (n : ℝ) (s : State) : flow n 0 s = s := by
  ext <;> simp [flow] <;> norm_num

/-! ### Uniqueness -/

/-- The components of a state as a vector. -/
def toVec (s : State) : Fin 6 → ℝ := ![s.x, s.y, s.z, s.vx, s.vy, s.vz]

theorem toVec_injective : Function.Injective toVec := fun a b h => by
  ext
  · simpa [toVec] using congrFun h 0
  · simpa [toVec] using congrFun h 1
  · simpa [toVec] using congrFun h 2
  · simpa [toVec] using congrFun h 3
  · simpa [toVec] using congrFun h 4
  · simpa [toVec] using congrFun h 5

/-- `field` as a linear map on vectors. -/
def fieldVec (n : ℝ) : (Fin 6 → ℝ) →ₗ[ℝ] (Fin 6 → ℝ) where
  toFun v := ![v 3, v 4, v 5, 3 * n ^ 2 * v 0 + 2 * n * v 4, -(2 * n * v 3), -(n ^ 2 * v 2)]
  map_add' a b := by
    ext i; fin_cases i <;> simp <;> ring
  map_smul' c a := by
    ext i; fin_cases i <;> simp <;> ring

theorem toVec_field (n : ℝ) (s : State) : toVec (field n s) = fieldVec n (toVec s) := by
  ext i; fin_cases i <;> simp [toVec, field, fieldVec]

theorem hasDerivAt_toVec {n : ℝ} {f : ℝ → State} {t : ℝ} (h : Solves n f t) :
    HasDerivAt (fun u => toVec (f u)) (fieldVec n (toVec (f t))) t := by
  rw [← toVec_field, hasDerivAt_pi]
  intro i
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
  fin_cases i
  · simpa [toVec] using h0
  · simpa [toVec] using h1
  · simpa [toVec] using h2
  · simpa [toVec] using h3
  · simpa [toVec] using h4
  · simpa [toVec] using h5

/-- Every function that satisfies the equations at every time and has the value `s` at 0 is the
closed form from `s`. -/
theorem flow_unique {n : ℝ} (hn : n ≠ 0) {f : ℝ → State} {s : State} (hf : ∀ t, Solves n f t)
    (h0 : f 0 = s) (t : ℝ) : f t = flow n t s := by
  let L := LinearMap.toContinuousLinearMap (fieldVec n)
  have hL : ∀ v, L v = fieldVec n v := fun _ => rfl
  have key : (fun u => toVec (f u)) = fun u => toVec (flow n u s) :=
    ODE_solution_unique_univ (v := fun _ => L) (s := fun _ => Set.univ) (K := ‖L‖₊) (t₀ := 0)
      (fun _ => L.lipschitzWith.lipschitzOnWith)
      (fun u => ⟨by rw [hL]; exact hasDerivAt_toVec (hf u), trivial⟩)
      (fun u => ⟨by rw [hL]; exact hasDerivAt_toVec (flow_hasDerivAt hn s u), trivial⟩)
      (by simp only [h0, flow_zero])
  exact toVec_injective (congrFun key t)

/-- The closed form over `a + b` is the closed form over `a` after the closed form over `b`. -/
theorem flow_add {n : ℝ} (hn : n ≠ 0) (a b : ℝ) (s : State) :
    flow n (a + b) s = flow n a (flow n b s) := by
  refine flow_unique hn (f := fun u => flow n (u + b) s) (fun t => ?_) (by simp) a
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := flow_hasDerivAt hn s (t + b)
  exact ⟨h0.comp_add_const t b, h1.comp_add_const t b, h2.comp_add_const t b,
    h3.comp_add_const t b, h4.comp_add_const t b, h5.comp_add_const t b⟩

theorem flow_add_state (n τ : ℝ) (s s' : State) :
    flow n τ (s + s') = flow n τ s + flow n τ s' := by
  ext <;> simp [flow] <;> ring

theorem flow_zero_state (n τ : ℝ) : flow n τ 0 = 0 := by
  ext <;> simp [flow]

/-! ### Burns and the trajectory of a plan -/

/-- An impulsive burn: its time and its velocity change. -/
structure Burn where
  t : ℝ
  dvx : ℝ
  dvy : ℝ
  dvz : ℝ

/-- The state with zero position and the burn's velocity change. -/
def Burn.kick (b : Burn) : State := ⟨0, 0, 0, b.dvx, b.dvy, b.dvz⟩

/-- The state at time `t` of a deputy with state `s` at time `t₀` that executes the burns of the
list in order: when the first burn's time is at most `t`, the closed form to that time, the
burn's velocity change, and the rest of the list from that time; otherwise the closed form to
`t`. -/
noncomputable def path (n : ℝ) : ℝ → State → List Burn → ℝ → State
  | t₀, s, [], t => flow n (t - t₀) s
  | t₀, s, b :: bs, t =>
    if b.t ≤ t then path n b.t (flow n (b.t - t₀) s + b.kick) bs t else flow n (t - t₀) s

/-- The sum over the burns at or before `t` of the closed form of each burn's velocity change
from the burn's time to `t`. -/
noncomputable def kicks (n t : ℝ) : List Burn → State
  | [] => 0
  | b :: bs => (if b.t ≤ t then flow n (t - b.t) b.kick else 0) + kicks n t bs

theorem kicks_eq_zero {n t : ℝ} {bs : List Burn} (h : ∀ b ∈ bs, t < b.t) : kicks n t bs = 0 := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [kicks, not_le.mpr (h b List.mem_cons_self), ite_false]
    rw [ih fun c hc => h c (List.mem_cons_of_mem b hc), State.zero_add]

/-- For burns in nondecreasing order of time, the state of `path` is the closed form from the
initial state plus the closed forms of the velocity changes of the burns at or before `t`. -/
theorem path_eq {n : ℝ} (hn : n ≠ 0) {bs : List Burn} (hs : bs.Pairwise fun a b => a.t ≤ b.t)
    (t₀ : ℝ) (s : State) (t : ℝ) : path n t₀ s bs t = flow n (t - t₀) s + kicks n t bs := by
  induction bs generalizing t₀ s with
  | nil => simp only [path, kicks, State.add_zero]
  | cons b bs ih =>
    rw [List.pairwise_cons] at hs
    by_cases hb : b.t ≤ t
    · simp only [path, kicks, hb, ite_true]
      rw [ih hs.2, flow_add_state, ← flow_add hn, State.add_assoc]
      congr 2
      ring
    · simp only [path, kicks, hb, ite_false]
      rw [kicks_eq_zero fun c hc => lt_of_lt_of_le (not_le.mp hb) (hs.1 c hc), State.zero_add,
        State.add_zero]

/-- The position part of a burn's term: the burn adds nothing before its time, since a state with
zero position has zero position at `τ = 0`. -/
theorem kick_term_x (n t : ℝ) (b : Burn) :
    (if b.t ≤ t then flow n (t - b.t) b.kick else 0).x = (flow n (max (t - b.t) 0) b.kick).x := by
  split_ifs with h
  · rw [max_eq_left (by linarith)]
  · rw [max_eq_right (by linarith)]; simp [flow, Burn.kick]

theorem kick_term_y (n t : ℝ) (b : Burn) :
    (if b.t ≤ t then flow n (t - b.t) b.kick else 0).y = (flow n (max (t - b.t) 0) b.kick).y := by
  split_ifs with h
  · rw [max_eq_left (by linarith)]
  · rw [max_eq_right (by linarith)]; simp [flow, Burn.kick]

theorem kick_term_z (n t : ℝ) (b : Burn) :
    (if b.t ≤ t then flow n (t - b.t) b.kick else 0).z = (flow n (max (t - b.t) 0) b.kick).z := by
  split_ifs with h
  · rw [max_eq_left (by linarith)]
  · rw [max_eq_right (by linarith)]; simp [flow, Burn.kick]

/-- After the last burn, the state is the closed form from the state at a time `tL` that follows
every burn. -/
theorem kicks_after {n : ℝ} (hn : n ≠ 0) {bs : List Burn} {tL t : ℝ} (hb : ∀ b ∈ bs, b.t ≤ tL)
    (ht : tL ≤ t) : kicks n t bs = flow n (t - tL) (kicks n tL bs) := by
  induction bs with
  | nil => simp only [kicks, flow_zero_state]
  | cons b bs ih =>
    have h1 := hb b List.mem_cons_self
    simp only [kicks, h1, h1.trans ht, ite_true]
    rw [ih fun c hc => hb c (List.mem_cons_of_mem b hc), flow_add_state, ← flow_add hn]
    congr 3
    ring

/-! ### The radial and cross-track plane -/

/-- The radial and cross-track components of the closed form depend on the time only through the
phase `n τ`, so every time `τ` has a time `φ / n` with `φ` in `[0, 2π)` at which they are the
same.  The along-track component may drift. -/
theorem flow_phase {n : ℝ} (hn : n ≠ 0) (τ : ℝ) (s : State) :
    ∃ φ ∈ Set.Ico 0 (2 * π),
      (flow n τ s).x = (flow n (φ / n) s).x ∧ (flow n τ s).z = (flow n (φ / n) s).z := by
  have hp : (0 : ℝ) < 2 * π := by positivity
  have hm := toIcoMod_mem_Ico hp 0 (n * τ)
  have e := toIcoMod_add_toIcoDiv_zsmul hp 0 (n * τ)
  rw [zsmul_eq_mul] at e
  set φ := toIcoMod hp 0 (n * τ)
  refine ⟨φ, by simpa using hm, ?_⟩
  have hs : sin (n * τ) = sin φ := by rw [← e, sin_add_int_mul_two_pi]
  have hc : cos (n * τ) = cos φ := by rw [← e, cos_add_int_mul_two_pi]
  have hφ : n * (φ / n) = φ := mul_div_cancel₀ φ hn
  simp only [flow, hs, hc, hφ]
  exact ⟨trivial, trivial⟩

/-! ### Scenarios -/

/-- Whether burn `k`, counted from 0, executes in scenario `j` of a plan of `N` burns: every burn
in scenario 0, every burn but burn `j` for `1 ≤ j ≤ N`, and the burns before burn `j − N` for
`N < j`. -/
def runs (N j k : ℕ) : Bool :=
  if j = 0 then true else if j ≤ N then k + 1 != j else decide (k + 1 < j - N)

/-- The burns from position `k` of a plan that execute in scenario `j`. -/
def selectFrom (N j : ℕ) : ℕ → List Burn → List Burn
  | _, [] => []
  | k, b :: bs => if runs N j k then b :: selectFrom N j (k + 1) bs else selectFrom N j (k + 1) bs

/-- The burns of a plan that execute in scenario `j`. -/
def select (N j : ℕ) (bs : List Burn) : List Burn := selectFrom N j 0 bs

theorem selectFrom_sublist (N j k : ℕ) (bs : List Burn) : (selectFrom N j k bs).Sublist bs := by
  induction bs generalizing k with
  | nil => exact List.Sublist.slnil
  | cons b bs ih =>
    simp only [selectFrom]
    split_ifs
    · exact (ih (k + 1)).cons_cons b
    · exact (ih (k + 1)).cons b

/-- The burn at positions past the end of a list. -/
def Burn.none : Burn := ⟨0, 0, 0, 0⟩

/-- A burn of a plan that executes in a scenario is a burn of the scenario's list. -/
theorem mem_selectFrom (N j : ℕ) :
    ∀ (k : ℕ) (bs : List Burn) (i : ℕ), i < bs.length → runs N j (k + i) = true →
      bs.getD i Burn.none ∈ selectFrom N j k bs
  | _, [], _, h, _ => absurd h (Nat.not_lt_zero _)
  | k, b :: bs, 0, _, hr => by
    simp only [Nat.add_zero] at hr
    simp [selectFrom, hr]
  | k, b :: bs, i + 1, hi, hr => by
    have h := mem_selectFrom N j (k + 1) bs i (by simpa using hi)
      (by rwa [show k + 1 + i = k + (i + 1) by omega])
    simp only [List.getD_cons_succ] at h ⊢
    simp only [selectFrom]
    split_ifs
    · exact List.mem_cons_of_mem b h
    · exact h

/-- A burn of a scenario's list executes in the scenario. -/
theorem exists_of_mem_selectFrom (N j : ℕ) :
    ∀ (k : ℕ) (bs : List Burn) (b : Burn), b ∈ selectFrom N j k bs →
      ∃ i < bs.length, runs N j (k + i) = true ∧ bs.getD i Burn.none = b
  | _, [], _, h => by simp [selectFrom] at h
  | k, c :: bs, b, h => by
    simp only [selectFrom] at h
    split_ifs at h with hr
    · rcases List.mem_cons.mp h with e | h
      · exact ⟨0, by simp, by simpa using hr, by simp [e]⟩
      · obtain ⟨i, hi, hr', e⟩ := exists_of_mem_selectFrom N j (k + 1) bs b h
        exact ⟨i + 1, by simpa using hi, by rwa [show k + (i + 1) = k + 1 + i by omega], by simpa⟩
    · obtain ⟨i, hi, hr', e⟩ := exists_of_mem_selectFrom N j (k + 1) bs b h
      exact ⟨i + 1, by simpa using hi, by rwa [show k + (i + 1) = k + 1 + i by omega], by simpa⟩

/-- A component `c` of `kicks` over the burns of scenario `j` from position `k`, for a projection
that adds, is the sum over the positions of the list of `f` of each burn that executes, where
`f` gives the component of each executed burn's term. -/
theorem kicks_selectFrom (c : State → ℝ) (hadd : ∀ a b, c (a + b) = c a + c b) (hzero : c 0 = 0)
    (n τ : ℝ) (N j : ℕ) (f : Burn → ℝ) :
    ∀ (k : ℕ) (bs : List Burn), (∀ i < bs.length, runs N j (k + i) = true →
      c (if (bs.getD i Burn.none).t ≤ τ then
        flow n (τ - (bs.getD i Burn.none).t) (bs.getD i Burn.none).kick else 0) =
        f (bs.getD i Burn.none)) →
      c (kicks n τ (selectFrom N j k bs)) =
        ∑ i ∈ Finset.range bs.length, if runs N j (k + i) = true then f (bs.getD i Burn.none)
          else 0
  | k, [], _ => by simp [selectFrom, kicks, hzero]
  | k, b :: bs, h => by
    have ih := kicks_selectFrom c hadd hzero n τ N j f (k + 1) bs fun i hi hr => by
      have := h (i + 1) (by simpa using hi) (by rwa [show k + (i + 1) = k + 1 + i by omega])
      simpa using this
    have shift : (∑ i ∈ Finset.range bs.length,
        if runs N j (k + (i + 1)) = true then f ((b :: bs).getD (i + 1) Burn.none) else 0) =
        ∑ i ∈ Finset.range bs.length,
          if runs N j (k + 1 + i) = true then f (bs.getD i Burn.none) else 0 :=
      Finset.sum_congr rfl fun i _ => by
        rw [show k + (i + 1) = k + 1 + i by omega, List.getD_cons_succ]
    rw [List.length_cons, Finset.sum_range_succ', shift, ← ih]
    simp only [selectFrom]
    by_cases hr : runs N j k = true
    · have h0 := h 0 (by simp) (by simpa using hr)
      simp only [List.getD_cons_zero] at h0
      simp only [hr, ite_true, kicks, hadd, h0, List.getD_cons_zero, Nat.add_zero]
      ring
    · simp only [hr, Bool.false_eq_true, ite_false, add_zero]

/-- For burns in nondecreasing order of time and a time `tL` at or after every burn, the state at
every later time is the closed form from the state at `tL`. -/
theorem path_after {n : ℝ} (hn : n ≠ 0) {bs : List Burn} (hs : bs.Pairwise fun a b => a.t ≤ b.t)
    (s : State) {tL t : ℝ} (hb : ∀ b ∈ bs, b.t ≤ tL) (ht : tL ≤ t) :
    path n 0 s bs t = flow n (t - tL) (path n 0 s bs tL) := by
  rw [path_eq hn hs, path_eq hn hs, kicks_after hn hb ht, flow_add_state, ← flow_add hn]
  congr 2
  ring

/-- The separation from the chief. -/
noncomputable def separation (s : State) : ℝ := √(s.x ^ 2 + s.y ^ 2 + s.z ^ 2)

/-- The distance from the chief in the radial and cross-track plane. -/
noncomputable def rcDistance (s : State) : ℝ := √(s.x ^ 2 + s.z ^ 2)

end Demos.PassiveSafety.Model
