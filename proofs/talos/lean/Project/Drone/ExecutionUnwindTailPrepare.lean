import Project.Drone.ExecutionUnwindFrame
import Project.ProofKit.NatSub

namespace Project.Drone.Execution
open Wasm Project.ProofKit WordArrayPush

def unwindTailAux (aux : List Value) (index parent : Nat) (terrain history root : UInt64) : List Value :=
  ((((((aux.set 15 (.i64 (UInt64.ofNat (index - 1)))).set 16 (.i64 (UInt64.ofNat parent))).set
    17 (.i64 0)).set 18 (.i64 terrain)).set 19 (.i64 history)).set 20 (.i64 history)).set
    21 (.i64 root) |>.set 22 (.i64 root)

set_option maxRecDepth 32768 in
theorem unwind_tail_prepare_spec (env : HostEnv Unit) (store : Store Unit)
    (fuel index state parent : Nat) (terrain history row root : UInt64) (tracked : Bool)
    (out0 out1 : UInt64) (aux : List Value) (s : Scratch) (hAux : aux.length = 36)
    (hIndex : index < UInt64.size) (hRoot0 : aux[12]? = some (.i64 root))
    (hRoot1 : aux[13]? = some (.i64 root)) (hParent : aux[14]? = some (.i64 (UInt64.ofNat parent)))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.Drone.«module» rest Q store
      (unwindFrame fuel index state terrain history row tracked out0 out1
        (unwindTailAux aux index parent terrain history root)
        { s with source := UInt64.ofNat index, length := 1 }) env) :
    wp Project.Drone.«module» ((unwindLoopBody.drop 184).take 23 ++ rest) Q store
      (unwindFrame fuel index state terrain history row tracked out0 out1 aux s) env := by
  simp only [unwindLoopBody, func24, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.drop, List.take, List.cons_append, List.nil_append]
  wp_unwind_frame [hAux]
  refine NatSub.guard_spec 51 52 _ _ _ _ index 1 [] rfl ?_ ?_ hIndex (by decide) _ _ ?_
  · simp [Locals.get, hAux]
  · simp [Locals.get, hAux]
  wp_unwind_frame [hAux, hParent, hRoot0, hRoot1]
  simpa only [unwindFrame, unwindParams, unwindTailAux, Scratch.words,
    List.cons_append, List.nil_append] using hNext

#print axioms unwind_tail_prepare_spec
end Project.Drone.Execution
