import Project.EulerGridStep.ReuseHit

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit
open Project.ProofKit.FixedArrayAllocatorWindow
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

def reuseSearchFrame (base : Locals) (root : UInt64) : Locals :=
  { base with locals := ((base.locals.set 19 (.i64 0)).set 15 (.i64 0)).set 16 (.i64 root), values := [] }

def reuseLoadedFrame (base : Locals) (root capacity next : UInt64) : Locals :=
  { reuseSearchFrame base root with
    locals := ((reuseSearchFrame base root).locals.set 17 (.i64 capacity)).set 18 (.i64 next) }

def reuseFoundFrame (base : Locals) (root capacity next : UInt64) : Locals :=
  reuseChosenFrame (reuseLoadedFrame base root capacity next) root

def reuseStore (initial : Store Unit) (root capacity next : UInt64) : Store Unit :=
  writeAllocationHeader (reuseUnlinkedStore initial next) root capacity

def reuseMeasure (_ : Store Unit) (frame : Locals) : Nat :=
  if frame.get 24 = some (.i64 0) then 1 else 0

theorem reuse_search_body_shape : searchBody 10 1 =
    (searchBody 10 1).take 23 ++
    [.iff 0 0 reuseHitBody [.localGet 21, .localSet 20, .localGet 23, .localSet 21], .br 0] := rfl

/-- A sufficient first free block is selected after one successful search iteration. -/
theorem reuse_search_spec (m : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (base : Locals) (root capacity request next : UInt64)
    (hParams : base.params.length = 5) (hLocals : base.locals.length = 20)
    (hRequest : base.locals[14]? = some (.i64 request))
    (hFreeList : initial.globals.globals[1]? = some (.i64 root))
    (hRoot48 : 48 ≤ root.toNat) (hRoot32 : root.toNat < 4294967296)
    (hFit : root.toNat ≤ initial.mem.pages * 65536)
    (hCapacityRead : initial.mem.read64 (root - 32).toUInt32 = capacity)
    (hNextRead : initial.mem.read64 (root - 8).toUInt32 = next)
    (hEnough : capacity ≥ request)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hContinue : wp m rest Q (reuseStore initial root capacity next)
      (reuseFoundFrame base root capacity next) env) :
    wp m (search 10 1 ++ rest) Q initial (reuseSearchFrame base root) env := by
  have hRoot0 : root ≠ 0 := by intro h; subst root; simp at hRoot48
  have hRequestGet : base.locals[14] = .i64 request := by
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
      (current = initial ∧ frame = reuseSearchFrame base root) ∨
      (current = reuseStore initial root capacity next ∧ frame = reuseFoundFrame base root capacity next))
    (μ := reuseMeasure)
  · exact Or.inl ⟨rfl, rfl⟩
  · rintro current frame (⟨hStore, hFrame⟩ | ⟨hStore, hFrame⟩)
    · subst current
      subst frame
      rw [reuse_search_body_shape]
      wp_alloc_window_lists [searchBody, reuseSearchFrame, hParams, hLocals, hRequestGet,
        hRoot0, hSub32, hSub8, hRead32, hRead8, hBound32, hBound8]
      rw [ite_eq_right (Nat.not_lt.mpr hBound32), ite_eq_right (Nat.not_lt.mpr hBound8)]
      apply wp_iff_cons rfl
      rw [ite_eq_left hEnough]
      change wp m (reuseHitBody ++ []) _ initial (reuseLoadedFrame base root capacity next) env
      apply reuse_hit_spec m env initial (reuseLoadedFrame base root capacity next) root capacity next
        (by simp [reuseLoadedFrame, reuseSearchFrame, hParams])
        (by simp [reuseLoadedFrame, reuseSearchFrame, hLocals]) rfl
        (by simp [reuseLoadedFrame, reuseSearchFrame, Wasm.Locals.get, hParams, hLocals])
        (by simp [reuseLoadedFrame, reuseSearchFrame, Wasm.Locals.get, hParams, hLocals])
        (by simp [reuseLoadedFrame, reuseSearchFrame, Wasm.Locals.get, hParams, hLocals])
        (by simp [reuseLoadedFrame, reuseSearchFrame, Wasm.Locals.get, hParams, hLocals])
        hFreeList hRoot48 hRoot32 hFit _ []
      rw [wp_nil]
      simp only [List.take_zero, List.drop_zero, List.nil_append, wp_br_cons]
      refine ⟨Or.inr ⟨rfl, rfl⟩, ?_⟩
      simp [reuseMeasure, reuseChosenFrame, reuseLoadedFrame, reuseSearchFrame,
        Wasm.Locals.get, hParams, hLocals, hRoot0]
    · subst current
      subst frame
      wp_alloc_window_lists [searchBody, reuseChosenFrame, reuseFoundFrame, reuseLoadedFrame,
        reuseSearchFrame, hParams, hLocals, hRoot0]
      simpa [reuseFoundFrame, reuseChosenFrame, reuseLoadedFrame, reuseSearchFrame] using hContinue

#print axioms reuse_search_body_shape
#print axioms reuse_search_spec
end Project.EulerGridStep.Execution
