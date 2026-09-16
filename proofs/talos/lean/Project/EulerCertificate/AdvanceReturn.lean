import Project.EulerCertificate.AdvanceTotalFrame

namespace Project.EulerCertificate.Execution
open Wasm
open Project.EulerCertificate.Flux (Vector)
open Project.EulerCertificateFlux.Execution (vectorValues boundsValues)

set_option maxRecDepth 32768

def advanceReturn : Wasm.Program :=
  [.localGet 19, .localGet 20, .localGet 21, .localGet 22, .localGet 23, .localGet 24, .localGet 25, .localGet 26, .localGet 27, .localGet 28, .localGet 29, .localGet 30, .localGet 31, .localGet 32, .localGet 33, .localGet 34]

theorem advance_return_shape : func184.drop 5 = (func184.drop 5).take 4 ++ advanceReturn := rfl

theorem advance_return_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (status time root : UInt64) (boundary : Vector)
    (h : AdvanceReturnedAt frame status time root boundary) (Q : Assertion Unit)
    (hNext : Q (.Fallthrough store { frame with
      values := vectorValues boundary ++ [.i64 root, .i64 root, .i64 time, .i64 status] })) :
    wp Project.EulerCertificate.«module» advanceReturn Q store frame env := by
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
  unfold advanceReturn
  wp_run [h.params, h.locals, h.values, h.status, h.outputTime, h.outputOwner, h.outputPointer,
    hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11,
    reduceIte, Nat.reduceLT, Nat.reduceAdd]
  simpa only [vectorValues, boundsValues, List.cons_append, List.nil_append] using hNext

#print axioms advance_return_shape
#print axioms advance_return_spec
end Project.EulerCertificate.Execution
