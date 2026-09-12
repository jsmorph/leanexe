import Project.EulerRiemann.ExecutionTimeGuard
import Project.EulerRiemann.InitialModel

namespace Project.EulerRiemann.Execution
open Wasm

theorem fifths_exact (env : HostEnv Unit) (initial : Store Unit) (n : Fin 6) :
    TerminatesWith env Project.EulerRiemann.«module» 79 initial [.i64 (UInt64.ofNat n.val)]
      (fun final values => final = initial ∧ values = [.i64 (Initial.fifths n.val)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func79Def) rfl ?_ (by decide)
  change wp Project.EulerRiemann.«module» func79 _ initial
    (func79Def.toLocals [.i64 (UInt64.ofNat n.val)]) env
  fin_cases n <;> unfold func79
  all_goals
    repeat
      first
      | wp_run [func79Def, Initial.fifths, List.set, List.getElem?_cons_zero,
          List.getElem?_cons_succ, reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
      | refine wp_iff_cons rfl ?_
        simp

theorem weightedWord_exact (env : HostEnv Unit) (initial : Store Unit)
    (x y bl br tl tr : UInt64) :
    TerminatesWith env Project.EulerRiemann.«module» 80 initial
      [.i64 tr, .i64 tl, .i64 br, .i64 bl, .i64 y, .i64 x]
      (fun final values => final = initial ∧
        values = [.i64 (Initial.weightedWord x y bl br tl tr)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func80Def) rfl ?_ (by decide)
  change wp Project.EulerRiemann.«module» func80 _ initial
    (func80Def.toLocals [.i64 x, .i64 y, .i64 bl, .i64 br, .i64 tl, .i64 tr]) env
  wp_run [func80Def, func80, List.set, f64Sub, f64Mul, f64Add,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
  simp [Initial.weightedWord]

theorem conservative_exact (env : HostEnv Unit) (initial : Store Unit)
    (pressure density u v : UInt64) :
    let state := Initial.conservative pressure density u v
    TerminatesWith env Project.EulerRiemann.«module» 81 initial
      [.i64 v, .i64 u, .i64 density, .i64 pressure]
      (fun final values => final = initial ∧
        values = [.i64 state.energy, .i64 state.my, .i64 state.mx, .i64 state.density]) := by
  refine TerminatesWith.of_wp_entry_for (f := func81Def) rfl ?_ (by decide)
  change wp Project.EulerRiemann.«module» func81 _ initial
    (func81Def.toLocals [.i64 pressure, .i64 density, .i64 u, .i64 v]) env
  wp_run [func81Def, func81, List.set, f64Div, f64Mul, f64Add,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
  simp [Initial.conservative]

#print axioms fifths_exact
#print axioms weightedWord_exact
#print axioms conservative_exact

end Project.EulerRiemann.Execution
