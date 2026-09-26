import Project.Drone.ExecutionPredecessor

namespace Project.Drone.Execution
open Wasm Project.ProofKit LeanExe.Examples.Drone

def scanFrame (r0 r1 owner pointer : UInt64) (target fuel source : Nat)
    (best result : Choice) (scratch : List Value) : Locals :=
  { params := [.i64 (UInt64.ofNat fuel), .i64 (UInt64.ofNat source),
      .i64 r0, .i64 r1, .i64 owner, .i64 pointer, .i64 (UInt64.ofNat target),
      .i64 best.time, .i64 best.excess, .i64 best.parent],
    locals := [.i64 0, .i64 result.time, .i64 result.excess, .i64 result.parent, .i64 0] ++ scratch }

def scanInv (initial : Store Unit) (r0 r1 owner pointer : UInt64)
    (target bound : Nat) (previous : Array UInt64) (expected : Choice)
    (store : Store Unit) (frame : Locals) : Prop :=
  store = initial ∧ ∃ (fuel source : Nat) (best result : Choice) (scratch : List Value),
    frame = scanFrame r0 r1 owner pointer target fuel source best result scratch ∧
    scratch.length = 58 ∧ source + fuel = bound ∧
    scanPredecessors fuel source r0 r1 previous target best = expected

def scanMeasure (_ : Store Unit) (frame : Locals) : Nat :=
  match frame.params with
  | .i64 fuel :: _ => fuel.toNat
  | _ => 0

macro "wp_scan_frame" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| wp_fixed_frame [scanFrame, List.length_append, List.length_cons,
    List.length_nil, List.length_set, List.getElem?_append, List.getElem?_set,
    List.set_append, List.cons_append, List.nil_append, Nat.reduceEqDiff,
    UInt64.lt_irrefl, $ts,*])

theorem scanInv_step {initial : Store Unit} {r0 r1 owner pointer : UInt64}
    {target bound fuel source : Nat} {previous : Array UInt64}
    {expected incumbent chosen result : Choice} {scratch nextScratch : List Value}
    (hScratch : nextScratch.length = 58) (hBound : source + (fuel+1) = bound)
    (hInv : scanPredecessors (fuel+1) source r0 r1 previous target incumbent = expected)
    (hChosen : chosen = choose incumbent (predecessor r0 r1 previous target source))
    (hf : fuel+1 < UInt64.size) :
    scanInv initial r0 r1 owner pointer target bound previous expected initial
      (scanFrame r0 r1 owner pointer target fuel (source+1) chosen result nextScratch) ∧
    scanMeasure initial (scanFrame r0 r1 owner pointer target fuel (source+1) chosen result nextScratch) <
      scanMeasure initial (scanFrame r0 r1 owner pointer target (fuel+1) source incumbent result scratch) := by
  constructor
  · refine ⟨rfl, fuel, source+1, chosen, result, nextScratch, rfl, hScratch, by omega, ?_⟩
    simpa only [scanPredecessors, ← hChosen] using hInv
  · change (UInt64.ofNat fuel).toNat < (UInt64.ofNat (fuel+1)).toNat
    rw [UInt64.toNat_ofNat_of_lt' (show fuel < UInt64.size by omega),
      UInt64.toNat_ofNat_of_lt' hf]
    omega

elab "scan_wp_goal" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainTarget
  unless goal.isAppOf ``Wasm.wp do
    throwError "scan instruction execution reached its postcondition"

macro "scan_calls" call:ident "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  (repeat' ((try wp_scan_frame [$ts,*]) <;> (scan_wp_goal; first
    | (refine wp_call_tw $call ?_;
       rintro final returned ⟨hFinal, hValues⟩; subst final; rw [hValues])
    | (refine wp_constIf rfl ?_)
    | (refine wp_iff_cons rfl ?_;
       simp only [$ts,*, ne_eq, eq_self_iff_true,
         show (1 : UInt32) ≠ 0 by decide,
         show (1 : UInt64) ≠ 0 by decide,
         not_false_eq_true, not_true_eq_false, UInt64.lt_irrefl, ↓reduceIte])))
   try wp_scan_frame [$ts,*]))

#print axioms scanInv_step
end Project.Drone.Execution
