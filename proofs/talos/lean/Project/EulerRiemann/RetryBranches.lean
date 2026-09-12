import Project.EulerRiemann.RetryTrial

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime

def retryAcceptBody : Wasm.Program :=
  match (retryTrial[42]? : Option Wasm.Instruction) with
  | some (.iff _ _ yes _ _ _) => yes
  | _ => []

def retryRejectBody : Wasm.Program :=
  match (retryTrial[42]? : Option Wasm.Instruction) with
  | some (.iff _ _ _ no _ _) => no
  | _ => []

theorem retry_branches_shape : retryTrial = retryTrial.take 35 ++
    [.localGet 26, .constI64 1, .eqI64,
      .iff 0 1 [.constI64 1] [.constI64 0] [] [.i64],
      .constI64 0, .eqI64, .eqz, .iff 0 0 retryAcceptBody retryRejectBody] := rfl

def retryAcceptedFrame (frame : Locals) (dt root : UInt64) : Locals :=
  let locals := frame.locals.set 1 (.i64 0)
  let locals := locals.set 2 (.i64 dt)
  let locals := locals.set 3 (.i64 root)
  let locals := locals.set 4 (.i64 root)
  let locals := locals.set 5 (.i64 1)
  { frame with locals, values := [] }

def retryRejectedFrame (frame : Locals) (fuel : UInt64) (n : Nat)
    (time dt source frees : UInt64) : Locals :=
  let half := IEEE64.mul 0x3FE0000000000000 dt
  let locals := frame.locals.set 21 (.i64 frees)
  let locals := locals.set 22 (.i64 (UInt64.ofNat n))
  let locals := locals.set 23 (.i64 time)
  let locals := locals.set 24 (.i64 half)
  let locals := locals.set 25 (.i64 source)
  let locals := locals.set 26 (.i64 source)
  let locals := locals.set 27 (.i64 (UInt64.ofNat n))
  let locals := locals.set 28 (.i64 time)
  let locals := locals.set 29 (.i64 half)
  let locals := locals.set 30 (.i64 source)
  let locals := locals.set 31 (.i64 source)
  let locals := locals.set 32 (.i64 0)
  let locals := locals.set 0 (.i64 0)
  { params := [.i64 (fuel - 1), .i64 (UInt64.ofNat n), .i64 time, .i64 half,
      .i64 source, .i64 source]
    locals
    values := [] }

theorem retry_accept_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (n : Nat) (fuel time dt source ratio result : UInt64)
    (hParams : frame.params = [.i64 fuel, .i64 (UInt64.ofNat n), .i64 time,
      .i64 dt, .i64 source, .i64 source])
    (hLocals : frame.locals.length = 51) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.EulerRiemann.«module» rest Q store
      (retryAcceptedFrame (retryTrialFrame frame n ratio source result true) dt result) env) :
    wp Project.EulerRiemann.«module» (retryAcceptBody ++ rest) Q store
      (retryTrialFrame frame n ratio source result true) env := by
  unfold retryAcceptBody retryTrial retryLoop func74
  dsimp only
  wp_run [retryTrialFrame, List.cons_append, List.nil_append, List.length_set,
    List.getElem?_set, List.getElem?_cons_zero, List.getElem?_cons_succ, reduceIte,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, hParams, hLocals]
  simpa [retryAcceptedFrame, retryTrialFrame, hParams] using hNext

theorem retry_reject_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (frame : Locals) (n : Nat) (fuel time dt source ratio : UInt64)
    (result : FreeNode) (grid : Array Traversal.Cell)
    (hParams : frame.params = [.i64 fuel, .i64 (UInt64.ofNat n), .i64 time,
      .i64 dt, .i64 source, .i64 source])
    (hLocals : frame.locals.length = 51) (hTracker : frame.locals[0]? = some (.i64 0))
    (hSource : source ≠ 0) (hHeap : heap.At store) (hOwner : heap.Owns store result grid)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.EulerRiemann.«module» rest Q (heap.releaseStore store result)
      (retryRejectedFrame (retryTrialFrame frame n ratio source result.root false)
        fuel n time dt source (heap.frees + 1)) env) :
    wp Project.EulerRiemann.«module» (retryRejectBody ++ rest) Q store
      (retryTrialFrame frame n ratio source result.root false) env := by
  obtain ⟨hTrackerBound, hTrackerRead⟩ := List.getElem_of_getElem? hTracker
  unfold retryRejectBody retryTrial retryLoop func74
  dsimp only
  wp_run [retryTrialFrame, List.cons_append, List.nil_append, List.length_set,
    List.getElem?_set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub,
    Nat.reduceEqDiff, hParams, hLocals]
  refine wp_call_tw (release_owned env store heap result grid hHeap hOwner) ?_
  rintro final values ⟨rfl, hFinal, hFinalHeap⟩
  subst final
  have hFrees : (heap.releaseStore store result).globals.globals[5]? =
      some (.i64 (heap.frees + 1)) := by rw [hFinalHeap.globals]; rfl
  repeat
    first
    | wp_run [retryTrialFrame, List.cons_append, List.nil_append, List.length_set,
        List.getElem?_set, List.getElem?_cons_zero, List.getElem?_cons_succ, f64Mul,
        reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, *]
    | refine wp_iff_cons rfl ?_
      simp [*, -UInt64.not_le]
  simpa [retryRejectedFrame, retryTrialFrame, hParams, List.set] using hNext

#print axioms retry_branches_shape
#print axioms retry_accept_spec
#print axioms retry_reject_spec

end Project.EulerRiemann.Execution
