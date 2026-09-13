import Project.EulerRiemann.ExecutionTimeGuard
import Project.EulerRiemann.InitialModel

namespace Project.EulerRiemann.Execution
open Wasm

theorem fifths_exact (env : HostEnv Unit) (initial : Store Unit) (n : Fin 6) :
    TerminatesWith env Project.EulerRiemann.«module» 86 initial [.i64 (UInt64.ofNat n.val)]
      (fun final values => final = initial ∧ values = [.i64 (Initial.fifths n.val)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func86Def) rfl ?_ (by decide)
  change wp Project.EulerRiemann.«module» func86 _ initial
    (func86Def.toLocals [.i64 (UInt64.ofNat n.val)]) env
  fin_cases n <;> unfold func86
  all_goals
    repeat
      first
      | wp_run [func86Def, Initial.fifths, List.set, List.getElem?_cons_zero,
          List.getElem?_cons_succ, reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
      | (try simp only [Wasm.wp_iff_control_types])
        refine wp_iff_cons rfl ?_
        simp

theorem weightedWord_exact (env : HostEnv Unit) (initial : Store Unit)
    (x y bl br tl tr : UInt64) :
    TerminatesWith env Project.EulerRiemann.«module» 87 initial
      [.i64 tr, .i64 tl, .i64 br, .i64 bl, .i64 y, .i64 x]
      (fun final values => final = initial ∧
        values = [.i64 (Initial.weightedWord x y bl br tl tr)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func87Def) rfl ?_ (by decide)
  change wp Project.EulerRiemann.«module» func87 _ initial
    (func87Def.toLocals [.i64 x, .i64 y, .i64 bl, .i64 br, .i64 tl, .i64 tr]) env
  wp_run [func87Def, func87, List.set, f64Sub, f64Mul, f64Add,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
  simp [Initial.weightedWord]

theorem conservative_exact (env : HostEnv Unit) (initial : Store Unit)
    (pressure density u v : UInt64) :
    let state := Initial.conservative pressure density u v
    TerminatesWith env Project.EulerRiemann.«module» 88 initial
      [.i64 v, .i64 u, .i64 density, .i64 pressure]
      (fun final values => final = initial ∧
        values = [.i64 state.energy, .i64 state.my, .i64 state.mx, .i64 state.density]) := by
  refine TerminatesWith.of_wp_entry_for (f := func88Def) rfl ?_ (by decide)
  change wp Project.EulerRiemann.«module» func88 _ initial
    (func88Def.toLocals [.i64 pressure, .i64 density, .i64 u, .i64 v]) env
  wp_run [func88Def, func88, List.set, f64Div, f64Mul, f64Add,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
  simp [Initial.conservative]

#print axioms fifths_exact
#print axioms weightedWord_exact
#print axioms conservative_exact

end Project.EulerRiemann.Execution
