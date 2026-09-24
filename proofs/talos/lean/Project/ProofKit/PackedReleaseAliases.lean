import Project.ProofKit.PackedReleaseGuard
import Project.ProofKit.AliasGuards

namespace Project.ProofKit.PackedReleaseAliases
open Wasm Project.Runtime Project.EulerRiemann.Execution PackedFloatFrame

/-- Release an owned packed buffer after any number of retained-owner comparisons. -/
def program (owner : Nat) (kept : List Nat) (releaseId : Nat) : Wasm.Program :=
  [.localGet owner, .constI64 0, .eqI64, .eqz] ++ AliasGuards.program owner kept ++
    [.iff 0 0 [.localGet owner, .call releaseId] []]

theorem program_spec (env : HostEnv Unit) (m : Wasm.Module) (id : Nat)
    (initial : Store Unit) (heap : Heap) (frame : Locals) (node : FreeNode)
    (bytes : ByteArray) (owner : Nat) (kept : List Nat) {typeIdx : Option Nat}
    (hFunction : m.funcs[id - m.imports.length]? =
      some { releaseFuncDef id with typeIdx := typeIdx })
    (hImport : m.imports[id]? = none)
    (hHeap : heap.At initial) (hOwner : heap.OwnsPacked initial node bytes)
    (hValues : frame.values = []) (hSource : frame.get owner = some (.i64 node.root))
    (hKept : ∀ slot ∈ kept, ∃ other : UInt64,
      frame.get slot = some (.i64 other) ∧ node.root ≠ other)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : (heap.release node).At (heap.releaseStore initial node) →
      wp m rest Q (heap.releaseStore initial node) frame env) :
    wp m (program owner kept id ++ rest) Q initial frame env := by
  have hNonzero : node.root ≠ 0 := by
    intro hZero
    have := hOwner.buffer.rootBound
    rw [hZero] at this
    contradiction
  simp only [program, List.append_assoc, List.cons_append, List.nil_append]
  simp only [wp_localGet_cons, hSource, wp_constI64_cons, wp_eqI64_cons, wp_eqz_cons,
    hValues, hNonzero, ite_false, ite_true]
  apply AliasGuards.distinct m env initial { frame with values := [.i32 1] } owner kept node.root
    rfl (by simpa using hSource) (by simpa using hKept)
  refine wp_iff_cons rfl ?_
  rw [ite_eq_left (by decide)]
  have hSource' := hSource
  simp only [Locals.get] at hSource'
  wp_packed_frame [hValues, hSource']
  refine wp_call_tw (heap.releasePacked_exact env m id initial node bytes
    hFunction hImport hHeap hOwner) ?_
  rintro final values ⟨rfl, rfl, hFinalHeap⟩
  simpa only [wp_nil, show ({ frame with values := [] } : Locals) = frame from
    Frame.ext _ _ rfl rfl hValues.symm] using hNext hFinalHeap

#print axioms program_spec
end Project.ProofKit.PackedReleaseAliases
