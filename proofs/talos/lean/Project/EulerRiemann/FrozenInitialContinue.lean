import Project.EulerRiemann.FrozenInitialLoopFrame
import Project.EulerRiemann.FrozenReleaseOwned

namespace Project.EulerRiemann.Frozen.Execution
open Wasm Project.ProofKit Project.Runtime

def initialContinuedFrame (frame : Locals) (fuel : UInt64) (n size : Nat) (root : UInt64) : Locals :=
  let locals := frame.locals.set 35 (.i64 root)
  let locals := locals.set 36 (.i64 root)
  let locals := locals.set 37 (.i64 (UInt64.ofNat n))
  let locals := locals.set 38 (.i64 (UInt64.ofNat size))
  let locals := locals.set 39 (.i64 root)
  let locals := locals.set 40 (.i64 root)
  let locals := locals.set 41 (.i64 root)
  let locals := locals.set 0 (.i64 root)
  { params := [.i64 (fuel - 1), .i64 (UInt64.ofNat n), .i64 (UInt64.ofNat size), .i64 root, .i64 root]
    locals, values := [] }

theorem initial_continue_shape : initialGrowBody.drop 131 =
    [.localGet 55, .localSet 40, .localGet 40, .localSet 41,
     .localGet 5, .constI64 0, .eqI64, .eqz,
     .iff 0 1 [.localGet 5, .localGet 40, .eqI64, .eqz] [.const 0] [] [.i32],
     .iff 0 0 [.localGet 5, .call 107] [],
     .localGet 37, .localSet 42, .localGet 38, .localSet 43,
     .localGet 40, .localSet 44, .localGet 41, .localSet 45,
     .localGet 40, .localSet 46, .localGet 42, .localSet 1,
     .localGet 43, .localSet 2, .localGet 44, .localSet 3,
     .localGet 45, .localSet 4, .localGet 46, .localSet 5,
     .localGet 0, .constI64 1, .subI64, .localSet 0] := rfl

local macro "initial_continue_peel" : tactic => `(tactic|
  repeat
    first
    | wp_run [List.cons_append, List.nil_append, List.length_set, List.getElem?_set,
        List.getElem?_cons_zero, List.getElem?_cons_succ, reduceIte,
        Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, *]
    | (try simp only [Wasm.wp_iff_control_types])
      refine wp_iff_cons rfl ?_
      simp [*, -UInt64.not_le])

theorem initial_continue_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (frame : Locals) (fuel : UInt64) (n size : Nat) (source : FreeNode)
    (grid : Array Traversal.Cell) (root : UInt64) (tracked : Bool)
    (hParams : frame.params = [.i64 fuel, .i64 (UInt64.ofNat n), .i64 (UInt64.ofNat size),
      .i64 source.root, .i64 source.root])
    (hLocals : frame.locals.length = 61) (hValues : frame.values = [])
    (hTracker : frame.locals[0]? = some (.i64 (if tracked then source.root else 0)))
    (hN : frame.locals[32]? = some (.i64 (UInt64.ofNat n)))
    (hSize : frame.locals[33]? = some (.i64 (UInt64.ofNat size)))
    (hRoot : frame.locals[50]? = some (.i64 root))
    (hSource : source.root ≠ 0) (hDifferent : source.root ≠ root)
    (hHeap : heap.At store) (hOwner : heap.Owns store source grid)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module rest Q (if tracked then heap.releaseStore store source else store)
      (initialContinuedFrame frame fuel n size root) env) :
    wp module (initialGrowBody.drop 131 ++ rest) Q store frame env := by
  obtain ⟨hNBound, hNRead⟩ := List.getElem_of_getElem? hN
  obtain ⟨hSizeBound, hSizeRead⟩ := List.getElem_of_getElem? hSize
  obtain ⟨hRootBound, hRootRead⟩ := List.getElem_of_getElem? hRoot
  rw [initial_continue_shape]
  cases tracked with
  | false =>
    simp only [Bool.false_eq_true, ite_false] at hTracker hNext
    obtain ⟨hTrackerBound, hTrackerRead⟩ := List.getElem_of_getElem? hTracker
    initial_continue_peel
    simpa [initialContinuedFrame, hParams, List.set] using hNext
  | true =>
    simp only [ite_true] at hTracker hNext
    obtain ⟨hTrackerBound, hTrackerRead⟩ := List.getElem_of_getElem? hTracker
    initial_continue_peel
    refine wp_call_tw (release_owned env store heap source grid hHeap hOwner) ?_
    rintro final values ⟨rfl, hFinal, hFinalHeap⟩
    subst final
    initial_continue_peel
    simpa [initialContinuedFrame, hParams, List.set] using hNext

theorem InitialFrameAt.continued {frame : Locals} {fuel : UInt64} {n size : Nat}
    {source tracker output : UInt64} {done : Bool}
    (h : InitialFrameAt frame fuel n size source tracker output done) (root : UInt64) :
    InitialFrameAt (initialContinuedFrame frame fuel n size root)
      (fuel - 1) n size root root output done := by
  cases h
  constructor <;> simp_all [initialContinuedFrame]

#print axioms initial_continue_shape
#print axioms initial_continue_spec
#print axioms InitialFrameAt.continued

end Project.EulerRiemann.Frozen.Execution
