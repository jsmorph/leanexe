import Project.EulerCertificate.RetryFrame

namespace Project.EulerCertificate.Execution
open Wasm
open Project.EulerCertificate.Flux (Vector)
open Project.EulerCertificateFlux.Execution (vectorValues boundsValues)

theorem retry_return_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (status dt root : UInt64) (boundary : Vector)
    (h : RetryReturnedAt frame status dt root boundary) (Q : Assertion Unit)
    (hNext : Q (.Fallthrough store { frame with
      values := vectorValues boundary ++ [.i64 root, .i64 root, .i64 dt, .i64 status] })) :
    wp Project.EulerCertificate.«module» retryReturn Q store frame env := by
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
  have hProgram : retryReturn = [.localGet 9, .localGet 10, .localGet 11, .localGet 12,
      .localGet 13, .localGet 14, .localGet 15, .localGet 16, .localGet 17, .localGet 18,
      .localGet 19, .localGet 20, .localGet 21, .localGet 22, .localGet 23, .localGet 24] := rfl
  rw [hProgram]
  wp_run [h.params, h.locals, h.values, h.status, h.outputDt, h.outputOwner, h.outputPointer,
    hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11,
    reduceIte, Nat.reduceLT, Nat.reduceAdd]
  simpa only [vectorValues, boundsValues, List.cons_append, List.nil_append] using hNext

#print axioms retry_return_spec
end Project.EulerCertificate.Execution
