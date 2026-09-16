import Project.EulerCertificate.RetryFrame

namespace Project.EulerCertificate.Execution
open Wasm Project.ProofKit FixedArrayFold FixedArrayResult
open Project.EulerCertificateFlux.Execution (vectorValues boundsValues)

set_option maxRecDepth 32768

def retryZeroFrame (frame : Locals) (start : Nat) : Locals :=
  let locals := frame.locals.set (start - 8 + 11) (.i64 0)
  let locals := locals.set (start - 8 + 10) (.i64 0)
  let locals := locals.set (start - 8 + 9) (.i64 0)
  let locals := locals.set (start - 8 + 8) (.i64 0)
  let locals := locals.set (start - 8 + 7) (.i64 0)
  let locals := locals.set (start - 8 + 6) (.i64 0)
  let locals := locals.set (start - 8 + 5) (.i64 0)
  let locals := locals.set (start - 8 + 4) (.i64 0)
  let locals := locals.set (start - 8 + 3) (.i64 0)
  let locals := locals.set (start - 8 + 2) (.i64 0)
  let locals := locals.set (start - 8 + 1) (.i64 0)
  let locals := locals.set (start - 8 + 0) (.i64 0)
  let locals := locals.set 5 (.i64 0)
  let locals := locals.set 6 (.i64 0)
  let locals := locals.set 7 (.i64 0)
  let locals := locals.set 8 (.i64 0)
  let locals := locals.set 9 (.i64 0)
  let locals := locals.set 10 (.i64 0)
  let locals := locals.set 11 (.i64 0)
  let locals := locals.set 12 (.i64 0)
  let locals := locals.set 13 (.i64 0)
  let locals := locals.set 14 (.i64 0)
  let locals := locals.set 15 (.i64 0)
  let locals := locals.set 16 (.i64 0)
  { frame with locals, values := [] }

theorem retry_zero_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (start : Nat) (hStart : start = 88 ∨ start = 101)
    (hParams : frame.params.length = 8) (hLocals : frame.locals.length = 121)
    (hValues : frame.values = []) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.EulerCertificate.«module» rest Q store (retryZeroFrame frame start) env) :
    wp Project.EulerCertificate.«module» (retryZeroBoundary start ++ rest) Q store frame env := by
  unfold retryZeroBoundary
  simp only [List.cons_append, List.nil_append]
  have hCall := vector_zero_exact env store
  rw [← hValues] at hCall
  refine wp_call_tw hCall ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  rcases hStart with rfl | rfl <;>
    simp [wp_simp, hParams, hLocals, vectorValues, boundsValues, Vectors.zero,
      List.range_succ, List.reverse_cons] <;>
    simpa [retryZeroFrame, hParams] using hNext

theorem retry_failure_returned (params saved : List Wasm.Value)
    (hParams : params.length = 8) (hSaved : saved.length = 115)
    (hFuel : ∃ value : UInt64, params[0]? = some (.i64 value))
    (status dt previous current capacity next root : UInt64) (start : Nat)
    (hStart : start = 88 ∨ start = 101) :
    RetryReturnedAt (resultFrame (retryZeroFrame
      (retryFailureFrame params saved status dt previous current capacity next root) start) 25 1)
      status dt root Vectors.zero := by
  rcases hStart with rfl | rfl <;>
    constructor <;>
    simp_all [retryZeroFrame, resultFrame, retryFailureFrame, finishFrame,
      FixedArraySearch.frame, retryFailureSaved, vectorValues, boundsValues, Vectors.zero]
  all_goals
    intro i
    fin_cases i <;> simp [hSaved]

#print axioms retry_zero_spec
#print axioms retry_failure_returned
end Project.EulerCertificate.Execution
