import Project.EulerGridStep.RejectedReuseHit
import Project.EulerGridStep.ReuseSearch

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit
open Project.ProofKit.FixedArrayAllocatorWindow
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

def rejectedReuseSearchFrame (base : Locals) (root : UInt64) : Locals :=
  { base with locals := ((base.locals.set 71 (.i64 0)).set 67 (.i64 0)).set 68 (.i64 root), values := [] }

def rejectedReuseLoadedFrame (base : Locals) (root capacity next : UInt64) : Locals :=
  { rejectedReuseSearchFrame base root with
    locals := ((rejectedReuseSearchFrame base root).locals.set 69 (.i64 capacity)).set 70 (.i64 next) }

def rejectedReuseFoundFrame (base : Locals) (root capacity next : UInt64) : Locals :=
  rejectedReuseChosenFrame (rejectedReuseLoadedFrame base root capacity next) root

def rejectedReuseMeasure (_ : Store Unit) (frame : Locals) : Nat :=
  if frame.get 81 = some (.i64 0) then 1 else 0

theorem rejected_reuse_search_body_shape : searchBody 67 1 =
    (searchBody 67 1).take 23 ++
    [.iff 0 0 rejectedReuseHitBody [.localGet 78, .localSet 77, .localGet 80, .localSet 78], .br 0] := rfl

/-- A sufficient first free block is selected after one successful search iteration. -/
theorem rejected_reuse_search_spec (m : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (base : Locals) (root capacity request next : UInt64)
    (hParams : base.params.length = 10) (hLocals : base.locals.length = 72)
    (hRequest : base.locals[66]? = some (.i64 request))
    (hFreeList : initial.globals.globals[1]? = some (.i64 root))
    (hRoot48 : 48 ≤ root.toNat) (hRoot32 : root.toNat < 4294967296)
    (hFit : root.toNat ≤ initial.mem.pages * 65536)
    (hCapacityRead : initial.mem.read64 (root - 32).toUInt32 = capacity)
    (hNextRead : initial.mem.read64 (root - 8).toUInt32 = next)
    (hEnough : capacity ≥ request)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hContinue : wp m rest Q (reuseStore initial root capacity next)
      (rejectedReuseFoundFrame base root capacity next) env) :
    wp m (search 67 1 ++ rest) Q initial (rejectedReuseSearchFrame base root) env := by
  have hRoot0 : root ≠ 0 := by intro h; subst root; simp at hRoot48
  have hRequestGet : base.locals[66] = .i64 request := by
    have h := hRequest
    rw [List.getElem?_eq_getElem (by omega)] at h
    exact Option.some.inj h
  have hSub32 : (root - 32).toNat = root.toNat - 32 :=
    Memory.toNat_sub_of_le _ _ (by simpa using (show 32 ≤ root.toNat by omega))
  have hSub8 : (root - 8).toNat = root.toNat - 8 :=
    Memory.toNat_sub_of_le _ _ (by simpa using (show 8 ≤ root.toNat by omega))
  have hRead32 : initial.mem.read64 (UInt32.ofNat ((root.toNat - 32) % 4294967296)) = capacity := by
    simpa [Memory.toUInt32_eq_ofNat, hSub32] using hCapacityRead
  have hRead8 : initial.mem.read64 (UInt32.ofNat ((root.toNat - 8) % 4294967296)) = next := by
    simpa [Memory.toUInt32_eq_ofNat, hSub8] using hNextRead
  have hBound32 : (root.toNat - 32) % 4294967296 + 8 ≤ initial.mem.pages * 65536 := by
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hBound8 : (root.toNat - 8) % 4294967296 + 8 ≤ initial.mem.pages * 65536 := by
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  simp only [search, List.cons_append, List.nil_append]
  apply wp_block_cons
  apply wp_loop_cons
    (Inv := fun current frame =>
      (current = initial ∧ frame = rejectedReuseSearchFrame base root) ∨
      (current = reuseStore initial root capacity next ∧ frame = rejectedReuseFoundFrame base root capacity next))
    (μ := rejectedReuseMeasure)
  · exact Or.inl ⟨rfl, rfl⟩
  · rintro current frame (⟨hStore, hFrame⟩ | ⟨hStore, hFrame⟩)
    · subst current
      subst frame
      rw [rejected_reuse_search_body_shape]
      wp_alloc_window_lists [searchBody, rejectedReuseSearchFrame, hParams, hLocals, hRequestGet,
        hRoot0, hSub32, hSub8, hRead32, hRead8, hBound32, hBound8]
      rw [ite_eq_right (Nat.not_lt.mpr hBound32), ite_eq_right (Nat.not_lt.mpr hBound8)]
      apply wp_iff_cons rfl
      rw [ite_eq_left hEnough]
      change wp m (rejectedReuseHitBody ++ []) _ initial (rejectedReuseLoadedFrame base root capacity next) env
      apply rejected_reuse_hit_spec m env initial (rejectedReuseLoadedFrame base root capacity next) root capacity next
        (by simp [rejectedReuseLoadedFrame, rejectedReuseSearchFrame, hParams])
        (by simp [rejectedReuseLoadedFrame, rejectedReuseSearchFrame, hLocals]) rfl
        (by simp [rejectedReuseLoadedFrame, rejectedReuseSearchFrame, Wasm.Locals.get, hParams, hLocals])
        (by simp [rejectedReuseLoadedFrame, rejectedReuseSearchFrame, Wasm.Locals.get, hParams, hLocals])
        (by simp [rejectedReuseLoadedFrame, rejectedReuseSearchFrame, Wasm.Locals.get, hParams, hLocals])
        (by simp [rejectedReuseLoadedFrame, rejectedReuseSearchFrame, Wasm.Locals.get, hParams, hLocals])
        hFreeList hRoot48 hRoot32 hFit _ []
      rw [wp_nil]
      simp only [List.take_zero, List.drop_zero, List.nil_append, wp_br_cons]
      refine ⟨Or.inr ⟨rfl, rfl⟩, ?_⟩
      simp [rejectedReuseMeasure, rejectedReuseChosenFrame, rejectedReuseLoadedFrame, rejectedReuseSearchFrame,
        Wasm.Locals.get, hParams, hLocals, hRoot0]
    · subst current
      subst frame
      wp_alloc_window_lists [searchBody, rejectedReuseChosenFrame, rejectedReuseFoundFrame, rejectedReuseLoadedFrame,
        rejectedReuseSearchFrame, hParams, hLocals, hRoot0]
      simpa [rejectedReuseFoundFrame, rejectedReuseChosenFrame, rejectedReuseLoadedFrame, rejectedReuseSearchFrame] using hContinue

#print axioms rejected_reuse_search_body_shape
#print axioms rejected_reuse_search_spec
end Project.EulerGridStep.Execution
