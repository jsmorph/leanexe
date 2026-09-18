import Project.ProofKit.OwnedPacked
import Project.ProofKit.PackedFloatFrame
import Interpreter.Wasm.Wp.Call

namespace Project.ProofKit.PackedReleaseGuard
open Wasm Project.Runtime Project.EulerRiemann.Execution PackedFloatFrame

def program (ownerLocal retainedLocal releaseId : Nat) : Wasm.Program :=
  [.localGet ownerLocal, .constI64 0, .eqI64, .eqz,
   .iff 0 1 [.localGet ownerLocal, .localGet retainedLocal, .eqI64, .eqz]
     [.const 0] [] [.i32],
   .iff 0 0 [.localGet ownerLocal, .call releaseId] []]

theorem program_spec (env : HostEnv Unit) (module_ : Wasm.Module) (id : Nat)
    (initial : Store Unit) (heap : Heap) (frame : Locals) (node : FreeNode)
    (bytes : ByteArray) (retained : UInt64) (ownerLocal retainedLocal : Nat)
    {typeIdx : Option Nat}
    (hFunction : module_.funcs[id - module_.imports.length]? =
      some { releaseFuncDef id with typeIdx := typeIdx })
    (hImport : module_.imports[id]? = none)
    (hHeap : heap.At initial) (hOwner : heap.OwnsPacked initial node bytes)
    (hValues : frame.values = []) (hSource : frame.get ownerLocal = some (.i64 node.root))
    (hRetained : frame.get retainedLocal = some (.i64 retained)) (hNe : node.root ≠ retained)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : (heap.release node).At (heap.releaseStore initial node) →
      wp module_ rest Q (heap.releaseStore initial node) frame env) :
    wp module_ (program ownerLocal retainedLocal id ++ rest) Q initial frame env := by
  have hNonzero : node.root ≠ 0 := by
    intro hZero
    have := hOwner.buffer.rootBound
    rw [hZero] at this
    contradiction
  have hSource' := hSource
  have hRetained' := hRetained
  simp only [Locals.get] at hSource' hRetained'
  simp only [program, List.cons_append, List.nil_append]
  wp_packed_frame [hValues, hSource', hNonzero]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_left (by decide)]
  wp_packed_frame [hValues, hSource', hRetained', hNe]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_left (by decide)]
  wp_packed_frame [hValues, hSource']
  refine wp_call_tw (heap.releasePacked_exact env module_ id initial node bytes
    hFunction hImport hHeap hOwner) ?_
  rintro final values ⟨rfl, rfl, hFinalHeap⟩
  simpa only [wp_nil, show ({ frame with values := [] } : Locals) = frame from
    Frame.ext _ _ rfl rfl hValues.symm] using hNext hFinalHeap

#print axioms program_spec

def programTwo (ownerLocal firstLocal secondLocal releaseId : Nat) : Wasm.Program :=
  [.localGet ownerLocal, .constI64 0, .eqI64, .eqz,
   .iff 0 1 [.localGet ownerLocal, .localGet firstLocal, .eqI64, .eqz]
     [.const 0] [] [.i32],
   .iff 0 1 [.localGet ownerLocal, .localGet secondLocal, .eqI64, .eqz]
     [.const 0] [] [.i32],
   .iff 0 0 [.localGet ownerLocal, .call releaseId] []]

theorem programTwo_spec (env : HostEnv Unit) (module_ : Wasm.Module) (id : Nat)
    (initial : Store Unit) (heap : Heap) (frame : Locals) (node : FreeNode)
    (bytes : ByteArray) (first second : UInt64) (ownerLocal firstLocal secondLocal : Nat)
    {typeIdx : Option Nat}
    (hFunction : module_.funcs[id - module_.imports.length]? =
      some { releaseFuncDef id with typeIdx := typeIdx })
    (hImport : module_.imports[id]? = none)
    (hHeap : heap.At initial) (hOwner : heap.OwnsPacked initial node bytes)
    (hValues : frame.values = []) (hSource : frame.get ownerLocal = some (.i64 node.root))
    (hFirst : frame.get firstLocal = some (.i64 first))
    (hSecond : frame.get secondLocal = some (.i64 second))
    (hFirstNe : node.root ≠ first) (hSecondNe : node.root ≠ second)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : (heap.release node).At (heap.releaseStore initial node) →
      wp module_ rest Q (heap.releaseStore initial node) frame env) :
    wp module_ (programTwo ownerLocal firstLocal secondLocal id ++ rest) Q initial frame env := by
  have hNonzero : node.root ≠ 0 := by
    intro hZero
    have := hOwner.buffer.rootBound
    rw [hZero] at this
    contradiction
  simp only [Locals.get] at hSource hFirst hSecond
  simp only [programTwo, List.cons_append, List.nil_append]
  wp_packed_frame [hValues, hSource, hNonzero]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_left (by decide)]
  wp_packed_frame [hValues, hSource, hFirst, hFirstNe]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_left (by decide)]
  wp_packed_frame [hValues, hSource, hSecond, hSecondNe]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_left (by decide)]
  wp_packed_frame [hValues, hSource]
  refine wp_call_tw (heap.releasePacked_exact env module_ id initial node bytes
    hFunction hImport hHeap hOwner) ?_
  rintro final values ⟨rfl, rfl, hFinalHeap⟩
  simpa only [wp_nil, show ({ frame with values := [] } : Locals) = frame from
    Frame.ext _ _ rfl rfl hValues.symm] using hNext hFinalHeap

#print axioms programTwo_spec

end Project.ProofKit.PackedReleaseGuard
