import Project.Drone.ExecutionScanFrame

namespace Project.Drone.Execution
open Wasm Project.ProofKit LeanExe.Examples.Drone

theorem scanPredecessors_entry (env : HostEnv Unit) (initial : Store Unit)
    (r0 r1 owner pointer : UInt64) (target count source : Nat) (best : Choice)
    (P : Store Unit → List Value → Prop)
    (hNext : wp «module» (func14.drop 4)
      (fun c => match c with
        | .Fallthrough store frame => P store (frame.values.take 3)
        | .Return store values => P store (values.take 3)
        | _ => False)
      initial (scanFrame r0 r1 owner pointer target count source best ⟨0, 0, 0⟩
        (List.replicate 58 (.i64 0))) env) :
    TerminatesWith env «module» 14 initial
      (choiceValues best ++ [.i64 (UInt64.ofNat target), .i64 pointer, .i64 owner,
        .i64 r1, .i64 r0, .i64 (UInt64.ofNat source), .i64 (UInt64.ofNat count)]) P := by
  refine TerminatesWith.of_wp_entry_for (f := func14Def) rfl ?_
  change wp «module» func14 _ initial
    { params := [.i64 (UInt64.ofNat count), .i64 (UInt64.ofNat source),
        .i64 r0, .i64 r1, .i64 owner, .i64 pointer, .i64 (UInt64.ofNat target),
        .i64 best.time, .i64 best.excess, .i64 best.parent],
      locals := List.replicate 63 (.i64 0) } env
  simp only [func14]
  wp_fixed_frame
  simp only [func14, List.drop, scanFrame, List.replicate, func14Def, choiceValues,
    Function.numParams, List.length, List.take, List.cons_append, List.nil_append,
    List.append_nil, Nat.reduceAdd] at hNext ⊢
  convert hNext using 1
  funext c
  cases c <;> rfl

#print axioms scanPredecessors_entry
end Project.Drone.Execution
