import Project.EulerCertificate.RunChange
import Project.EulerCertificate.TotalsExecution

namespace Project.EulerCertificate.Execution
open Wasm Project.ProofKit
open Project.EulerCertificate.Flux (Vector)
open Project.EulerCertificateFlux.Execution (vectorValues boundsValues)

set_option maxRecDepth 32768
set_option maxHeartbeats 400000
set_option pp.deepTerms false
set_option pp.maxSteps 3000

def runFinishBody : Wasm.Program := runBody.drop 134

theorem run_finish_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (n : Nat) (trials status time root : UInt64) (grid : Array Project.EulerRiemann.Traversal.Cell)
    (boundary initialTotal : Vector) (hn : n ≤ 800)
    (hGrid : Project.EulerRiemann.Memory.GridAt store root grid)
    (hParams : frame.params = [.i64 (UInt64.ofNat n), .i64 trials])
    (hLocals : frame.locals.length = 256)
    (hInitial : ∀ i : Fin 12, frame.locals[20 + i.val]? = (vectorValues initialTotal).reverse[i.val]?)
    (hValues : frame.values = vectorValues boundary ++ [.i64 root, .i64 root, .i64 time, .i64 status])
    (Q : Assertion Unit)
    (hNext : ∀ finalFrame : Locals,
      finalFrame.values = vectorValues (Vectors.sub (Vectors.sub (Totals.physical n grid) initialTotal) boundary) ++
        [.i64 root, .i64 root, .i64 time, .i64 status] → Q (.Fallthrough store finalFrame)) :
    wp module runFinishBody (FixedArrayEqNode.branchPost module env runReturn Q) store frame env := by
  unfold runFinishBody runBody func189
  dsimp only
  wp_run [hParams, hLocals, hValues, vectorValues, boundsValues,
    List.cons_append, List.nil_append, List.length_set, List.getElem?_set,
    List.getElem?_cons_zero, List.getElem?_cons_succ,
    reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff]
  have hTotal := totals_physical_exact env store n root root grid hn hGrid
  generalize hFinal : Totals.physical n grid = finalTotal at hTotal
  refine wp_call_tw hTotal ?_
  rintro same values ⟨hSame, rfl⟩
  subst same
  apply run_change_spec env store _ status time root boundary initialTotal finalTotal
  · constructor
    · rfl
    · simpa only [List.length_set] using hLocals
    · simp [hLocals]
    · simp [hLocals]
    · simp [hLocals]
    · simp [hLocals]
    · intro i
      fin_cases i <;> simp [hLocals, vectorValues, boundsValues]
  · intro i
    have hi := hInitial i
    fin_cases i <;> simpa [hLocals] using hi
  · rfl
  · simpa only [hFinal] using hNext

#print axioms run_finish_spec
end Project.EulerCertificate.Execution
