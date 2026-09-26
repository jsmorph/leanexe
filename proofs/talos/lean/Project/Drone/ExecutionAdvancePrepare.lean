import Project.Drone.ExecutionAdvanceFrame
import Project.ProofKit.CheckedNatAdd

namespace Project.Drone.Execution
open Wasm Project.ProofKit WordArrayPush

def advancePreparedAux (aux : List Value) (target : Nat) (r0 r1 : UInt64) (last : Bool)
    (previousOwner previousPointer rowPointer : UInt64) : List Value :=
  (((((((aux.set 16 (.i64 (UInt64.ofNat (target + 1)))).set 17 (.i64 r0)).set 18 (.i64 r1)).set
    19 (.i64 (if last then 1 else 0))).set 20 (.i64 previousOwner)).set 21 (.i64 previousPointer)).set
    22 (.i64 rowPointer))

def advancePreparedScratch (s : Scratch) (target : Nat) (rowPointer value : UInt64) : Scratch :=
  { s with
    source := rowPointer
    length := 1
    count := UInt64.ofNat (target + 1)
    value := value }

set_option maxRecDepth 32768 in
theorem advance_prepare_spec (env : HostEnv Unit) (store : Store Unit)
    (fuel target : Nat) (r0 r1 : UInt64) (last : Bool)
    (previousOwner previousPointer rowOwner rowPointer tracker resultOwner resultPointer value : UInt64)
    (aux : List Value) (s : Scratch) (hAux : aux.length = 38)
    (hValue : aux[13]? = some (.i64 value)) (hNextTarget : target + 1 < UInt64.size)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.Drone.«module» rest Q store
      (advanceFrame fuel target r0 r1 last previousOwner previousPointer rowOwner rowPointer tracker
        resultOwner resultPointer
        (advancePreparedAux aux target r0 r1 last previousOwner previousPointer rowPointer)
        (advancePreparedScratch s target rowPointer value)) env) :
    wp Project.Drone.«module» ((advanceLoopBody.drop 21).take 28 ++ rest) Q store
      (advanceFrame fuel target r0 r1 last previousOwner previousPointer rowOwner rowPointer tracker
        resultOwner resultPointer aux s) env := by
  simp only [advanceLoopBody, func18, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.drop, List.take, List.cons_append, List.nil_append]
  wp_advance_frame [hAux]
  refine CheckedNatAdd.guard_spec 54 _ _ _ _ target 1 [] rfl ?_ hNextTarget _ _ ?_
  · simp [Locals.get, hAux, UInt64.ofNat_add]
  wp_advance_frame [hAux, hValue]
  simpa only [advanceFrame, advancePreparedAux, advancePreparedScratch, Scratch.words,
    List.cons_append, List.nil_append, UInt64.ofNat_add, show UInt64.ofNat 1 = 1 from rfl] using hNext

#print axioms advance_prepare_spec
end Project.Drone.Execution
