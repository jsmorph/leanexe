import Project.Gpt2QuantizedCached.CachedHidden.LayerPrepare
import Project.ProofKit.PackedReleaseFilter

namespace Project.Gpt2QuantizedCached.CachedHidden
open Wasm Project.ProofKit PackedFloatFrame

def statusTestCode (source : Nat) : Program :=
  [.localGet source, .constI64 0, .eqI64,
   .iff 0 1 [.constI64 1] [.constI64 0] [] [.i64],
   .constI64 1, .eqI64,
   .iff 0 1 [.constI64 1] [.constI64 0] [] [.i64],
   .constI64 0, .eqI64, .eqz]

theorem statusTest_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (source : Nat) (status : UInt64) (hValues : frame.values = [])
    (hRead : frame.get source = some (.i64 status))
    (Q : Assertion Unit) (rest : Program)
    (hNext : wp «module» rest Q store
      { frame with values := [.i32 (if status = 0 then 1 else 0)] } env) :
    wp «module» (statusTestCode source ++ rest) Q store frame env := by
  simp only [Locals.get] at hRead
  by_cases h : status = 0
  all_goals
    simp only [statusTestCode, List.cons_append, List.nil_append]
    wp_packed_frame [hValues, hRead, h]
    refine wp_iff_cons rfl ?_
    first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)]
    wp_packed_frame []
    refine wp_iff_cons rfl ?_
    first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)]
    wp_packed_frame []
    simpa only [h, ite_true, ite_false, show (1 : UInt64) ≠ 0 by decide,
      show (1 : UInt32) ≠ 0 by decide, show (0 : UInt32) = 0 from rfl] using hNext

theorem statusGuard_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (source : Nat) (status : UInt64) (hValues : frame.values = [])
    (hRead : frame.get source = some (.i64 status))
    (Q : Assertion Unit) (active inactive rest : Program)
    (hNext : wp «module» (if status = 0 then active else inactive)
      (PackedReleaseFilter.afterAction «module» env rest Q) store frame env) :
    wp «module» (statusTestCode source ++ [.iff 0 0 active inactive] ++ rest) Q store frame env := by
  rw [List.append_assoc]
  apply statusTest_spec env store frame source status hValues hRead
  simp only [List.cons_append, List.nil_append]
  refine wp_iff_cons rfl ?_
  have hEmpty : ({ frame with values := [] } : Locals) = frame := Frame.ext _ _ rfl rfl hValues.symm
  by_cases h : status = 0
  · simp only [h, ite_true] at hNext ⊢
    rw [ite_eq_left (by decide)]
    simp only [List.take_zero, List.drop_zero, List.nil_append, hEmpty]
    apply wp.imp hNext
    intro cont hCont
    cases cont with
    | Break level next result => cases level <;> exact hCont
    | _ => exact hCont
  · simp only [h, ite_false] at hNext ⊢
    rw [ite_eq_right (by decide)]
    simp only [List.take_zero, List.drop_zero, List.nil_append, hEmpty]
    apply wp.imp hNext
    intro cont hCont
    cases cont with
    | Break level next result => cases level <;> exact hCont
    | _ => exact hCont

#print axioms statusTest_spec
#print axioms statusGuard_spec
end Project.Gpt2QuantizedCached.CachedHidden
