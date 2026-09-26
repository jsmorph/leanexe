import Project.LebU32.RecyclingHeader

namespace Project.LebU32.Recycling
open Wasm Project.ProofKit PackedFloatFrame

set_option maxRecDepth 32768
set_option maxHeartbeats 600000

def branchPost (Q : Assertion Unit) : Assertion Unit := fun cont =>
  match cont with
  | .Fallthrough store frame => Q (.Break 0 store { frame with values := [] })
  | .Break 0 store frame => Q (.Break 0 store { frame with values := [] })
  | .Break (k+1) store frame => Q (.Break k store frame)
  | other => Q other

theorem dispatch_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals) (v : UInt64)
    (hValues : frame.values = []) (hRest : frame.get 11 = some (.i64 (v / 128)))
    (Q : Assertion Unit)
    (hPositive : v / 128 = 0 → wp «module» positive (branchPost Q) store frame env)
    (hNegative : v / 128 ≠ 0 → wp «module» negative (branchPost Q) store frame env) :
    wp «module» (loopBody.drop 25) Q store frame env := by
  have hFrame : ({ frame with values := [] } : Locals) = frame := Frame.ext _ _ rfl rfl hValues.symm
  simp only [Locals.get] at hRest
  rw [dispatch_shape]
  simp only [dispatchHead, List.append_assoc, List.cons_append, List.nil_append]
  wp_packed_frame [hValues, hRest]
  by_cases hZero : v / 128 = 0
  · refine wp_iff_cons rfl ?_
    rw [ite_eq_left (by simp [hZero])]
    wp_packed_frame [hValues]
    refine wp_iff_cons rfl ?_
    rw [ite_eq_left (by decide)]
    wp_packed_frame [hValues]
    refine wp_iff_cons rfl ?_
    rw [ite_eq_left (by decide)]
    have hBranch := hPositive hZero
    unfold branchPost at hBranch
    simp only [hFrame, wp_br_cons, List.take_zero, List.drop_zero, List.nil_append]
    convert hBranch using 1
    congr 1
    funext cont
    cases cont <;> try rfl
    case Break k store frame => cases k <;> rfl
  · refine wp_iff_cons rfl ?_
    rw [ite_eq_right (by simp [hZero])]
    wp_packed_frame [hValues]
    refine wp_iff_cons rfl ?_
    rw [ite_eq_right (by decide)]
    wp_packed_frame [hValues]
    refine wp_iff_cons rfl ?_
    rw [ite_eq_right (by decide)]
    have hBranch := hNegative hZero
    unfold branchPost at hBranch
    simp only [hFrame, wp_br_cons, List.take_zero, List.drop_zero, List.nil_append]
    convert hBranch using 1
    congr 1
    funext cont
    cases cont <;> try rfl
    case Break k store frame => cases k <;> rfl

theorem finished_body_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (fuel root : UInt64) (size : Nat) (h : Finished frame fuel root size)
    (Q : Assertion Unit) (hNext : Q (.Break 1 store frame)) : wp «module» loopBody Q store frame env := by
  have hFuel := h.fuel
  have hDone := h.done
  have hValues := h.values
  have hFrame : ({ frame with values := [] } : Locals) = frame := Frame.ext _ _ rfl rfl hValues.symm
  simp only [Locals.get] at hFuel hDone
  rw [active_head_shape]
  simp only [activeHead, List.cons_append, List.nil_append]
  wp_packed_frame [hValues, hFuel]
  by_cases hZero : fuel = 0
  · refine wp_iff_cons rfl ?_
    rw [ite_eq_right (by simp [hZero])]
    wp_packed_frame [hValues]
    simpa [hFrame] using hNext
  · refine wp_iff_cons rfl ?_
    rw [ite_eq_left (by simp [hZero])]
    wp_packed_frame [hValues, hDone]
    simpa [hFrame] using hNext

#print axioms dispatch_spec
#print axioms finished_body_spec
end Project.LebU32.Recycling
