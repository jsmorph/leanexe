import Project.Drone.ExecutionRest

namespace Project.Drone.Execution
open Wasm Project.ProofKit LeanExe.Examples.Drone

def edgeStartFrame (r0 r1 z0 z1 u v : UInt64) : Locals :=
  { params := [.i64 r0, .i64 r1, .i64 z0, .i64 z1, .i64 u, .i64 v],
    locals := [.i64 z0, .i64 z1] ++ List.replicate 11 (.i64 0),
    values := [.i64 (distance z0 z1)] }

theorem edgeTicks_entry (env : HostEnv Unit) (initial : Store Unit)
    (r0 r1 z0 z1 u v : UInt64) (P : Store Unit → List Value → Prop)
    (hNext : wp «module» (func9.drop 7)
      (fun c => match c with
        | .Fallthrough store frame => P store (frame.values.take 1)
        | .Return store values => P store (values.take 1)
        | _ => False)
      initial (edgeStartFrame r0 r1 z0 z1 u v) env) :
    TerminatesWith env «module» 9 initial
      [.i64 v, .i64 u, .i64 z1, .i64 z0, .i64 r1, .i64 r0] P := by
  refine TerminatesWith.of_wp_entry_for (f := func9Def) rfl ?_
  change wp «module» func9 _ initial
    { params := [.i64 r0, .i64 r1, .i64 z0, .i64 z1, .i64 u, .i64 v],
      locals := List.replicate 13 (.i64 0) } env
  simp only [func9]
  wp_fixed_frame
  refine wp_call_tw (distance_exact env initial z0 z1) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  simp only [func9Def, Function.numParams, List.length, List.drop, List.take,
    List.append_nil, edgeStartFrame, List.replicate, List.cons_append, List.nil_append, Nat.reduceAdd,
    func9] at hNext ⊢
  convert hNext using 1
  funext continuation
  cases continuation <;> rfl

#print axioms edgeTicks_entry
end Project.Drone.Execution
