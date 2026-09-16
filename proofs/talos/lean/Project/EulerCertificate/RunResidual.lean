import Project.EulerCertificate.RunGuard

namespace Project.EulerCertificate.Execution
open Wasm Project.ProofKit
open Project.EulerCertificate.Flux (Vector)
open Project.EulerCertificateFlux.Execution (vectorValues boundsValues)

set_option maxRecDepth 32768
set_option maxHeartbeats 400000
set_option pp.deepTerms false
set_option pp.maxSteps 3000

structure RunResultAt (frame : Locals) (status time root : UInt64) (boundary : Vector) : Prop where
  params : frame.params.length = 2
  locals : frame.locals.length = 256
  status : frame.locals[78]? = some (.i64 status)
  time : frame.locals[79]? = some (.i64 time)
  owner : frame.locals[80]? = some (.i64 root)
  pointer : frame.locals[81]? = some (.i64 root)
  boundary : ∀ i : Fin 12, frame.locals[82 + i.val]? = (vectorValues boundary).reverse[i.val]?

def runReturn : Wasm.Program :=
  [.localGet 226, .localGet 227, .localGet 228, .localGet 229, .localGet 230, .localGet 231,
    .localGet 232, .localGet 233, .localGet 234, .localGet 235, .localGet 236, .localGet 237,
    .localGet 238, .localGet 239, .localGet 240, .localGet 241]

def runResidualBody : Wasm.Program := runBody.drop 301

theorem run_residual_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (status time root : UInt64) (boundary change : Vector)
    (h : RunResultAt frame status time root boundary) (hValues : frame.values = vectorValues change)
    (Q : Assertion Unit)
    (hNext : ∀ finalFrame : Locals,
      finalFrame.values = vectorValues (Vectors.sub change boundary) ++
        [.i64 root, .i64 root, .i64 time, .i64 status] → Q (.Fallthrough store finalFrame)) :
    wp module runResidualBody (FixedArrayEqNode.branchPost module env runReturn Q) store frame env := by
  have hb0 := h.boundary 0
  have hb1 := h.boundary 1
  have hb2 := h.boundary 2
  have hb3 := h.boundary 3
  have hb4 := h.boundary 4
  have hb5 := h.boundary 5
  have hb6 := h.boundary 6
  have hb7 := h.boundary 7
  have hb8 := h.boundary 8
  have hb9 := h.boundary 9
  have hb10 := h.boundary 10
  have hb11 := h.boundary 11
  simp [vectorValues, boundsValues] at hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 hb11
  unfold runResidualBody runBody func189
  dsimp only
  wp_run [h.params, h.locals, h.status, h.time, h.owner, h.pointer, hValues,
    hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11,
    vectorValues, boundsValues, List.cons_append, List.nil_append, List.length_set,
    List.getElem?_set, List.getElem?_cons_zero, List.getElem?_cons_succ, reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff]
  have hSub := vector_sub_exact env store change boundary
  generalize hResidual : Vectors.sub change boundary = residual at hSub
  refine wp_call_tw hSub ?_
  rintro same values ⟨hSame, rfl⟩
  subst same
  wp_run [h.params, h.locals, h.status, h.time, h.owner, h.pointer, hValues,
    hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11,
    vectorValues, boundsValues, runReturn, FixedArrayEqNode.branchPost,
    List.cons_append, List.nil_append, List.length_set, List.getElem?_set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff]
  apply hNext
  simp only [hResidual, vectorValues, boundsValues, List.cons_append, List.nil_append]

#print axioms run_residual_spec
end Project.EulerCertificate.Execution
