import Project.EulerGridStep.AllocationHeader

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit
open Project.ProofKit.FixedArrayAllocatorWindow
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

def reuseHitBody : Wasm.Program :=
  match ((searchBody 10 1)[23]? : Option Wasm.Instruction) with
  | some (Wasm.Instruction.iff _ _ body _ _ _) => body
  | _ => []

theorem reuse_hit_shape : reuseHitBody =
    [.localGet 20, .constI64 0, .eqI64,
      .iff 0 0 [.localGet 23, .globalSet 1]
        [.localGet 20, .constI64 8, .subI64, .wrapI64, .localGet 23, .store64 0]] ++
    allocationHeaderProgram 21 22 ++ [.localGet 21, .localSet 24] := rfl

def reuseUnlinkedStore (initial : Store Unit) (next : UInt64) : Store Unit :=
  { initial with globals := { globals := initial.globals.globals.set 1 (.i64 next) } }

def reuseChosenFrame (frame : Locals) (root : UInt64) : Locals :=
  { frame with locals := frame.locals.set 19 (.i64 root), values := [] }

/-- The first suitable free block is unlinked, initialized and selected, preserving all other state. -/
theorem reuse_hit_spec (m : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (frame : Locals) (root capacity next : UInt64)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 20)
    (hValues : frame.values = [])
    (hPrevious : frame.get 20 = some (.i64 0))
    (hRoot : frame.get 21 = some (.i64 root))
    (hCapacity : frame.get 22 = some (.i64 capacity))
    (hNextLocal : frame.get 23 = some (.i64 next))
    (hFreeList : initial.globals.globals[1]? = some (.i64 root))
    (hRoot48 : 48 ≤ root.toNat) (hRoot32 : root.toNat < 4294967296)
    (hFit : root.toNat ≤ initial.mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hContinue : wp m rest Q
      (writeAllocationHeader (reuseUnlinkedStore initial next) root capacity)
      (reuseChosenFrame frame root) env) :
    wp m (reuseHitBody ++ rest) Q initial frame env := by
  rw [reuse_hit_shape]
  simp only [List.append_assoc, List.cons_append, List.nil_append,
    wp_localGet_cons, hPrevious, hValues,
    wp_constI64_cons, wp_eqI64_cons]
  apply wp_iff_cons rfl
  rw [ite_eq_left (by simp)]
  simp only [wp_localGet_cons, copyFrame_get_withValues, hNextLocal, wp_globalSet_cons, hFreeList]
  rw [wp_nil]
  simp only [List.take_zero, List.drop_zero, List.nil_append]
  change wp m (allocationHeaderProgram 21 22 ++ ([.localGet 21, .localSet 24] ++ rest)) Q
    (reuseUnlinkedStore initial next) { params := frame.params, locals := frame.locals } env
  rw [copyFrame_ofParts frame hValues]
  apply allocation_header_program_spec 21 22 m env (reuseUnlinkedStore initial next) frame
    root capacity hRoot hCapacity hValues hRoot48 hRoot32 hFit Q _
  simp only [List.cons_append, List.nil_append, wp_localGet_cons, hRoot, wp_localSet_cons, hValues]
  simpa only [Wasm.Locals.set?, hParams, hLocals, List.length, Nat.reduceLT, Nat.reduceAdd,
    Nat.reduceSub, ite_false, ite_true, reuseChosenFrame] using hContinue

#print axioms reuse_hit_shape
#print axioms reuse_hit_spec
end Project.EulerGridStep.Execution
