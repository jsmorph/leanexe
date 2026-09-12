import Project.EulerRiemann.ExecutionSide
import Project.EulerRiemann.Traversal
import Project.EulerDynamicFlux.Helpers

namespace Project.EulerRiemann.Execution
open Wasm

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

private theorem word_max_eq (a b : UInt64) :
    max a b = if a ≤ b then b else a := rfl

theorem scanCell_exact (env : HostEnv Unit) (initial : Store Unit)
    (acc : Traversal.Scan) (cell : Traversal.Cell) :
    TerminatesWith env Project.EulerRiemann.«module» 24 initial
      [.i64 cell.status, .i64 cell.pressure, .i64 cell.state.energy,
        .i64 cell.state.my, .i64 cell.state.mx, .i64 cell.state.density,
        .i64 (UInt64.ofNat cell.index), .i64 acc.alpha, .i64 acc.status]
      (fun final values => final = initial ∧
        values = [.i64 (Traversal.scanCell acc cell).alpha,
          .i64 (Traversal.scanCell acc cell).status]) := by
  let x := Project.Euler2DConservative.Model.sideCheckedBits
    cell.state.density cell.state.mx cell.state.my cell.state.energy
  let y := Project.Euler2DConservative.Model.sideCheckedBits
    cell.state.density cell.state.my cell.state.mx cell.state.energy
  have xCall := side_exact env initial
    cell.state.density cell.state.mx cell.state.my cell.state.energy
  have yCall := side_exact env initial
    cell.state.density cell.state.my cell.state.mx cell.state.energy
  change TerminatesWith env Project.EulerRiemann.«module» 15 initial _
    (fun final values => final = initial ∧
      values = [.i64 x.energyFlux, .i64 x.transverseFlux, .i64 x.momentumFlux,
        .i64 x.massFlux, .i64 x.speed, .i64 x.pressure, .i64 x.velocity, .i64 x.status]) at xCall
  change TerminatesWith env Project.EulerRiemann.«module» 15 initial _
    (fun final values => final = initial ∧
      values = [.i64 y.energyFlux, .i64 y.transverseFlux, .i64 y.momentumFlux,
        .i64 y.massFlux, .i64 y.speed, .i64 y.pressure, .i64 y.velocity, .i64 y.status]) at yCall
  refine TerminatesWith.of_wp_entry_for (f := func24Def) rfl ?_ (by decide)
  change wp Project.EulerRiemann.«module» func24 _ initial
    (func24Def.toLocals [.i64 acc.status, .i64 acc.alpha, .i64 (UInt64.ofNat cell.index),
      .i64 cell.state.density, .i64 cell.state.mx, .i64 cell.state.my,
      .i64 cell.state.energy, .i64 cell.pressure, .i64 cell.status]) env
  unfold func24
  wp_run [func24Def, List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
  refine wp_call_tw xCall ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  dynamic_peel
  refine wp_call_tw yCall ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  by_cases hxy : x.speed ≤ y.speed
  · by_cases ha : acc.alpha ≤ y.speed
    all_goals
      dynamic_peel
      simp only [Traversal.scanCell, word_max_eq]
      simp_all +zetaDelta [-UInt64.not_le]
  · by_cases ha : acc.alpha ≤ x.speed
    all_goals
      dynamic_peel
      simp only [Traversal.scanCell, word_max_eq]
      simp_all +zetaDelta [-UInt64.not_le]

#print axioms scanCell_exact

end Project.EulerRiemann.Execution
