import Project.EulerRiemann.FrozenInitialWeights
import Project.EulerRiemann.FrozenExecutionInitialWeighted
import Project.EulerRiemann.FrozenExecutionSide

namespace Project.EulerRiemann.Frozen.Execution
open Wasm

theorem initialCell_exact (env : HostEnv Unit) (initial : Store Unit)
    (n index : Nat) (hn : n ≤ 800) (hi : index < 1048576) :
    TerminatesWith env Project.EulerRiemann.Frozen.«module» 94 initial
      [.i64 (UInt64.ofNat index), .i64 (UInt64.ofNat n)]
      (fun final values => final = initial ∧ values = cellValues (Traversal.initialCell n index)) := by
  let x : Fin 6 := ⟨initialWeight true n index, by
    have := Nat.min_le_left 5 (4 * n - 5 * coordinateIndex true n index)
    unfold initialWeight
    omega⟩
  let y : Fin 6 := ⟨initialWeight false n index, by
    have := Nat.min_le_left 5 (4 * n - 5 * coordinateIndex false n index)
    unfold initialWeight
    omega⟩
  let q := Initial.weighted x.val y.val
  let out := Numerics.sideCheckedBits q.density q.mx q.my q.energy
  have sideCall := side_exact env initial q.density q.mx q.my q.energy
  change TerminatesWith env Project.EulerRiemann.Frozen.«module» 22 initial _
    (fun final values => final = initial ∧
      values = [.i64 out.energyFlux, .i64 out.transverseFlux, .i64 out.momentumFlux,
        .i64 out.massFlux, .i64 out.speed, .i64 out.pressure, .i64 out.velocity, .i64 out.status]) at sideCall
  refine TerminatesWith.of_wp_entry_for (f := func94Def) rfl ?_ (by decide)
  change wp Project.EulerRiemann.Frozen.«module» func94 _ initial
    (func94Def.toLocals [.i64 (UInt64.ofNat n), .i64 (UInt64.ofNat index)]) env
  rw [← List.take_append_drop 66 func94]
  apply initial_weights_spec env initial _ n index hn hi rfl rfl rfl rfl rfl
  intro frame hParams hLocals hValues hX hY
  unfold func94
  dsimp only
  wp_run [func94Def, List.set, List.length_set, List.getElem?_set,
    reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, *]
  refine wp_call_tw (weighted_exact env initial x y) ?_
  rintro current values ⟨hStore, hResult⟩
  subst current
  subst values
  wp_run [func94Def, stateValues, List.set, List.length_set, List.getElem?_set,
    reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, *]
  refine wp_call_tw sideCall ?_
  rintro current values ⟨hStore, hResult⟩
  subst current
  subst values
  wp_run [func94Def, List.set, List.length_set, List.getElem?_set,
    reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, *]
  simp [cellValues, Traversal.initialCell, q, out, x, y, initialWeight, coordinateIndex]

#print axioms initialCell_exact

end Project.EulerRiemann.Frozen.Execution
