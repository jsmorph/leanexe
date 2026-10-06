import Examples.Euler.Reference.Interface
import LeanExe.ProofKit.F64AffineUpdate
import LeanExe.ProofKit.RealAffineError

/-! The first-order solver's conservative update against the exact update.  For a positive ratio
`r ≤ 1` of timestep to cell width and three neighboring states that satisfy the state bounds,
each of the four component updates of the center state accepts, and its value is within
`ε M + 1004 ε r M⁵ + 2 μ` of the exact Rusanov update `Rusanov.update` of the three states'
values with the two computed interface speeds, where `ε = 2⁻⁵²` and `μ` is the underflow term of
binary64 multiplication.  When `advanceCell` accepts, its four conserved outputs are those
component updates. -/

namespace Examples.Euler.Reference

open Examples.Euler LeanExe.ProofKit
open CodeLib.IEEE64 (value Finite arithmeticEpsilon multiplicationUnderflowEpsilon)
open LeanExe.ProofKit.F64ArithmeticBounds
open LeanExe.ProofKit.F64Order

set_option exponentiation.threshold 4096

/-- For a positive ratio at most 1, a state at most `M`, and fluxes at most `66 M⁵`, `update`
accepts, and its value is within `ε M + 396 ε r M⁵ + 2 μ` of the exact update of the inputs'
values. -/
theorem update_error (ratio state fluxL fluxR : Float)
    (hr : positive ratio = true) (hs : Finite state.toBits) (hl : Finite fluxL.toBits)
    (hh : Finite fluxR.toBits) (hr1 : real ratio ≤ 1) (M : ℝ) (hM : 1 ≤ M)
    (hMmax : M ≤ (2 : ℝ)^100) (bs : |real state| ≤ M) (bl : |real fluxL| ≤ 66 * M^5)
    (bh : |real fluxR| ≤ 66 * M^5) :
    let result := update ratio state fluxL fluxR
    result.status = 0 ∧ Finite result.value.toBits ∧
      |real result.value - (real state - real ratio * (real fluxR - real fluxL))| ≤
        arithmeticEpsilon * M + 396 * arithmeticEpsilon * real ratio * M^5 +
          2 * multiplicationUnderflowEpsilon := by
  simp only [real] at hr1 bs bl bh ⊢
  rw [positive_eq] at hr
  have hp := positiveBits_spec ratio.toBits hr
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hM5 : 1 ≤ M^5 := one_le_pow₀ hM
  have hM15 : M ≤ M^5 := by
    have h := mul_le_mul_of_nonneg_left (one_le_pow₀ hM : 1 ≤ M^4) hMpos.le
    nlinarith only [h]
  have hmax : M + 132 * M^5 ≤ (2 : ℝ)^1000 := by
    calc
      _ ≤ 133 * M^5 := by linarith only [hM15]
      _ ≤ 133 * ((2 : ℝ)^100)^5 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hMpos.le hMmax 5) (by norm_num)
      _ ≤ (2 : ℝ)^1000 := by norm_num
  have bd : |value fluxR.toBits - value fluxL.toBits| ≤ 132 * M^5 := by
    have h := abs_sub (value fluxR.toBits) (value fluxL.toBits)
    linarith only [h, bh, bl]
  obtain ⟨hd, hi, hv, herr⟩ := F64AffineUpdate.difference_update ratio.toBits state.toBits
    fluxL.toBits fluxR.toBits hp.1 hs hl hh hp.2.le hr1 M (132 * M^5) hM (by linarith only [hM5])
    hmax bs bd
  have hBits : ∀ x : Float, finite x = finiteBits x.toBits := fun _ => rfl
  have hu : update ratio state fluxL fluxR = ⟨0, state - ratio * (fluxR - fluxL)⟩ := by
    unfold update
    dsimp only
    rw [ite_eq_left]
    simp only [hBits, positive_eq, F64Bits.toBits_mul, F64Bits.toBits_sub, hr,
      (finiteBits_iff _).mpr hs, (finiteBits_iff _).mpr hl, (finiteBits_iff _).mpr hh,
      (finiteBits_iff _).mpr hd, (finiteBits_iff _).mpr hi, (finiteBits_iff _).mpr hv,
      Bool.and_self]
  rw [hu]
  simp only [F64Bits.toBits_mul, F64Bits.toBits_sub]
  exact ⟨trivial, hv, herr.trans_eq (by ring)⟩

/-- `update` against the exact update with reference fluxes within `304 ε M⁵` of its input
fluxes. -/
theorem update_reference_error (ratio state fluxL fluxR : Float)
    (hr : positive ratio = true) (hs : Finite state.toBits) (hl : Finite fluxL.toBits)
    (hh : Finite fluxR.toBits) (hr1 : real ratio ≤ 1) (referenceL referenceR M : ℝ)
    (hM : 1 ≤ M) (hMmax : M ≤ (2 : ℝ)^100) (bs : |real state| ≤ M)
    (bl : |real fluxL| ≤ 66 * M^5) (bh : |real fluxR| ≤ 66 * M^5)
    (el : |real fluxL - referenceL| ≤ 304 * arithmeticEpsilon * M^5)
    (eh : |real fluxR - referenceR| ≤ 304 * arithmeticEpsilon * M^5) :
    let result := update ratio state fluxL fluxR
    result.status = 0 ∧ Finite result.value.toBits ∧
      |real result.value - (real state - real ratio * (referenceR - referenceL))| ≤
        arithmeticEpsilon * M + 1004 * arithmeticEpsilon * real ratio * M^5 +
          2 * multiplicationUnderflowEpsilon := by
  obtain ⟨hstatus, hfinite, er⟩ :=
    update_error ratio state fluxL fluxR hr hs hl hh hr1 M hM hMmax bs bl bh
  have ed : |(real fluxR - real fluxL) - (referenceR - referenceL)| ≤
      608 * arithmeticEpsilon * M^5 := by
    obtain ⟨ell, elr⟩ := abs_le.mp el
    obtain ⟨ehl, ehr⟩ := abs_le.mp eh
    apply abs_le.mpr
    constructor <;> linarith only [ell, elr, ehl, ehr]
  have hr0 : 0 ≤ real ratio := (positiveBits_spec ratio.toBits (positive_eq ratio ▸ hr)).2.le
  have hresult := RealAffineError.subtract_product (real ratio) (real state)
    (referenceR - referenceL) (real fluxR - real fluxL) (real ratio * (real fluxR - real fluxL))
    (real (update ratio state fluxL fluxR).value) (608 * arithmeticEpsilon * M^5) 0
    (arithmeticEpsilon * M + 396 * arithmeticEpsilon * real ratio * M^5 +
      2 * multiplicationUnderflowEpsilon)
    hr0 ed (by simp only [sub_self, abs_zero, le_refl]) er
  exact ⟨hstatus, hfinite, hresult.trans_eq (by ring)⟩

/-- Under the state bounds on three neighboring states and a positive ratio at most 1, each
component update of the center state accepts and is within `ε M + 1004 ε r M⁵ + 2 μ` of the
exact Rusanov update. -/
theorem cell_component_error
    (ratio rhoL mxL myL energyL rho mx my energy rhoR mxR myR energyR : Float) (M : ℝ)
    (hM : 1 ≤ M) (hMmax : M ≤ (2 : ℝ)^100) (hr : positive ratio = true) (br : real ratio ≤ 1)
    (hL : StateBounds M rhoL mxL myL energyL) (hC : StateBounds M rho mx my energy)
    (hR : StateBounds M rhoR mxR myR energyR) (i : Fin 4) :
    let left := flux rhoL mxL myL energyL rho mx my energy
    let right := flux rho mx my energy rhoR mxR myR energyR
    let c := update ratio (stateAt ⟨rho, mx, my, energy⟩ i) (fluxAt left i)
      (fluxAt right i)
    c.status = 0 ∧ Finite c.value.toBits ∧
      |real c.value - Equations.Rusanov.update (real ratio) (real left.alpha) (real right.alpha)
        (vec ⟨rhoL, mxL, myL, energyL⟩) (vec ⟨rho, mx, my, energy⟩)
        (vec ⟨rhoR, mxR, myR, energyR⟩) i| ≤
        arithmeticEpsilon * M + 1004 * arithmeticEpsilon * real ratio * M^5 +
          2 * multiplicationUnderflowEpsilon := by
  obtain ⟨-, -, -, bl⟩ :=
    flux_accepted_of_bounds rhoL mxL myL energyL rho mx my energy M hM hMmax hL hC
  obtain ⟨-, -, -, bh⟩ :=
    flux_accepted_of_bounds rho mx my energy rhoR mxR myR energyR M hM hMmax hC hR
  obtain ⟨hl, bl⟩ := bl i
  obtain ⟨hh, bh⟩ := bh i
  obtain ⟨hs, bs⟩ := state_components_bounds rho mx my energy M hM hC i
  have el := interface_reference_error rhoL mxL myL energyL rho mx my energy M hM hMmax hL hC i
  have eh := interface_reference_error rho mx my energy rhoR mxR myR energyR M hM hMmax hC hR i
  dsimp only at el eh
  have er := update_reference_error ratio _ _ _ hr hs hl hh br _ _ M hM hMmax bs bl bh el eh
  simpa only [real_stateAt, Equations.Rusanov.update] using er

/-- When `advanceCell` accepts, its ratio is positive and its four conserved outputs are the
component updates of the center state. -/
theorem advanceCell_accepted
    (ratio rhoL mxL myL energyL rho mx my energy rhoR mxR myR energyR : Float)
    (h : (advanceCell ratio rhoL mxL myL energyL rho mx my energy rhoR mxR myR energyR).status =
      0) :
    positive ratio = true ∧ ∀ i,
      updatedAt
        (advanceCell ratio rhoL mxL myL energyL rho mx my energy rhoR mxR myR energyR) i =
      (update ratio (stateAt ⟨rho, mx, my, energy⟩ i)
        (fluxAt (flux rhoL mxL myL energyL rho mx my energy) i)
        (fluxAt (flux rho mx my energy rhoR mxR myR energyR) i)).value := by
  have hpos : positive ratio = true := by
    cases hp : positive ratio
    · unfold advanceCell at h
      simp [hp] at h
    · rfl
  refine ⟨hpos, fun i => ?_⟩
  unfold advanceCell at h ⊢
  dsimp only at h ⊢
  split_ifs at h ⊢
  all_goals first
    | exact absurd h (by decide)
    | (fin_cases i <;> rfl)

/-- When `advanceCell` accepts three neighboring states that satisfy the state bounds, with a
ratio at most 1, each of its four conserved outputs is within `ε M + 1004 ε r M⁵ + 2 μ` of the
exact Rusanov update of the three states' values with the two computed interface speeds. -/
theorem advanceCell_reference_error
    (ratio rhoL mxL myL energyL rho mx my energy rhoR mxR myR energyR : Float) (M : ℝ)
    (hM : 1 ≤ M) (hMmax : M ≤ (2 : ℝ)^100) (br : real ratio ≤ 1)
    (hL : StateBounds M rhoL mxL myL energyL) (hC : StateBounds M rho mx my energy)
    (hR : StateBounds M rhoR mxR myR energyR)
    (h : (advanceCell ratio rhoL mxL myL energyL rho mx my energy rhoR mxR myR energyR).status =
      0) (i : Fin 4) :
    |real (updatedAt
        (advanceCell ratio rhoL mxL myL energyL rho mx my energy rhoR mxR myR energyR) i) -
      Equations.Rusanov.update (real ratio) (real (flux rhoL mxL myL energyL rho mx my energy).alpha)
        (real (flux rho mx my energy rhoR mxR myR energyR).alpha)
        (vec ⟨rhoL, mxL, myL, energyL⟩) (vec ⟨rho, mx, my, energy⟩)
        (vec ⟨rhoR, mxR, myR, energyR⟩) i| ≤
      arithmeticEpsilon * M + 1004 * arithmeticEpsilon * real ratio * M^5 +
        2 * multiplicationUnderflowEpsilon := by
  obtain ⟨hr, hv⟩ := advanceCell_accepted ratio rhoL mxL myL energyL rho mx my energy rhoR mxR myR
    energyR h
  rw [hv i]
  exact (cell_component_error ratio rhoL mxL myL energyL rho mx my energy rhoR mxR myR energyR M
    hM hMmax hr br hL hC hR i).2.2

end Examples.Euler.Reference
