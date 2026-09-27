import Project.EulerCertificate.RunResidual

namespace Project.EulerCertificate.Execution
open Wasm Project.ProofKit
open Project.EulerCertificate.Flux (Vector)
open Project.EulerCertificateFlux.Execution (vectorValues boundsValues)

set_option maxRecDepth 32768
set_option maxHeartbeats 400000
set_option pp.deepTerms false
set_option pp.maxSteps 3000

def runChangeBody : Wasm.Program := runBody.drop 192

theorem run_change_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (status time root : UInt64) (boundary initialTotal finalTotal : Vector)
    (h : RunResultAt frame status time root boundary)
    (hInitial : ∀ i : Fin 12, frame.locals[20 + i.val]? = (vectorValues initialTotal).reverse[i.val]?)
    (hValues : frame.values = vectorValues finalTotal) (Q : Assertion Unit)
    (hNext : ∀ finalFrame : Locals,
      finalFrame.values = vectorValues (Vectors.sub (Vectors.sub finalTotal initialTotal) boundary) ++
        [.i64 root, .i64 root, .i64 time, .i64 status] → Q (.Fallthrough store finalFrame)) :
    wp module runChangeBody (FixedArrayEqNode.branchPost module env runReturn Q) store frame env := by
  have hi0 := hInitial 0
  have hi1 := hInitial 1
  have hi2 := hInitial 2
  have hi3 := hInitial 3
  have hi4 := hInitial 4
  have hi5 := hInitial 5
  have hi6 := hInitial 6
  have hi7 := hInitial 7
  have hi8 := hInitial 8
  have hi9 := hInitial 9
  have hi10 := hInitial 10
  have hi11 := hInitial 11
  simp [vectorValues, boundsValues] at hi0 hi1 hi2 hi3 hi4 hi5 hi6 hi7 hi8 hi9 hi10 hi11
  unfold runChangeBody runBody func189
  dsimp only
  wp_run [h.params, h.locals, hValues,
    hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8, hi9, hi10, hi11,
    vectorValues, boundsValues, List.cons_append, List.nil_append, List.length_set,
    List.getElem?_set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff]
  have hSub := vector_sub_exact env store finalTotal initialTotal
  generalize hChange : Vectors.sub finalTotal initialTotal = change at hSub
  refine wp_call_tw hSub ?_
  rintro same values ⟨hSame, rfl⟩
  subst same
  apply run_residual_spec env store _ status time root boundary change
  · constructor
    · exact h.params
    · simpa only [List.length_set] using h.locals
    · simpa [h.locals] using h.status
    · simpa [h.locals] using h.time
    · simpa [h.locals] using h.owner
    · simpa [h.locals] using h.pointer
    · intro i
      have hi := h.boundary i
      fin_cases i <;> simpa [h.locals] using hi
  · rfl
  · simpa only [hChange] using hNext

#print axioms run_change_spec
end Project.EulerCertificate.Execution
