import Verified.Wasi.SysFlatLoads
import Verified.Wasi.ReadReady
import Verified.Wasi.ReadDiscard
import Verified.Wasi.ReadInvoke
import Verified.Wasi.RuntimeFrame

/-! Parts of the code of a flat call: the local and the capacity of its output, the allocation of
the output buffer, and the buffer and frame that the host call leaves. -/

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

/-- A flat call without an output has no output local and no capacity; a flat call with one
reads its capacity from an argument local. -/
theorem outputLocal_spec {s : Locals} :
    ∀ (params : List Param) (locs : List Nat) (values : List UInt64),
    params.all Param.flatKind = true →
    List.Forall₂ (fun place value => s.get place = some (.i64 value)) locs values →
    values.length = params.countP Param.takesArg →
    (outputLocal params locs = none ∧ flatCapacity params values = none ∧
        params.contains .output = false) ∨
      ∃ place capacity, outputLocal params locs = some place ∧
        flatCapacity params values = some capacity ∧ s.get place = some (.i64 capacity) ∧
        place ∈ locs ∧ params.contains .output = true
  | [], _, _, _, _, _ => Or.inl ⟨rfl, rfl, rfl⟩
  | param :: params, locs, values, kinds, held, count => by
    simp only [List.all_cons, Bool.and_eq_true] at kinds
    cases param with
    | input => simp [Param.flatKind] at kinds
    | reported => simp [Param.flatKind] at kinds
    | result32 | result64 =>
      rcases outputLocal_spec params locs values kinds.2 held
          (by simpa [Param.takesArg, List.countP_cons] using count) with
        ⟨none', capacity, contains⟩ | ⟨place, capacity, found, found', get, member, contains⟩
      · exact Or.inl ⟨by simpa [outputLocal, Param.takesArg] using none',
          by simpa [flatCapacity, Param.takesArg] using capacity, by simpa using contains⟩
      · exact Or.inr ⟨place, capacity, by simpa [outputLocal, Param.takesArg] using found,
          by simpa [flatCapacity, Param.takesArg] using found', get, member,
          by simpa using contains⟩
    | output =>
      cases held with
      | nil => simp [Param.takesArg, List.countP_cons] at count
      | @cons place value locs' values' get held' =>
        exact Or.inr ⟨place, value, rfl, rfl, get, List.mem_cons_self .., by simp⟩
    | word32 | word64 | enum32 =>
      cases held with
      | nil => simp [Param.takesArg, List.countP_cons] at count
      | @cons place value locs' values' get held' =>
        rcases outputLocal_spec params locs' values' kinds.2 held'
            (by simpa [Param.takesArg, List.countP_cons] using count) with
          ⟨none', capacity, contains⟩ | ⟨place', capacity, found, found', get', member, contains⟩
        · exact Or.inl ⟨by simpa [outputLocal, Param.takesArg] using none',
            by simpa [flatCapacity, Param.takesArg] using capacity, by simpa using contains⟩
        · exact Or.inr ⟨place', capacity, by simpa [outputLocal, Param.takesArg] using found,
            by simpa [flatCapacity, Param.takesArg] using found', get',
            List.mem_cons_of_mem _ member, by simpa using contains⟩

/-- An accepted request has an output capacity below `2 ^ 32`. -/
theorem flatCapacity_small :
    ∀ (params : List Param) (values : List UInt64) (capacity : UInt64),
    params.all Param.flatKind = true →
    rejectArgs params (flatArgs params values) = 0 →
    flatCapacity params values = some capacity → capacity.toNat < 4294967296
  | [], _, _, _, _, found => by simp [flatCapacity] at found
  | param :: params, values, capacity, kinds, accepted, found => by
    simp only [List.all_cons, Bool.and_eq_true] at kinds
    cases param with
    | input => simp [Param.flatKind] at kinds
    | reported => simp [Param.flatKind] at kinds
    | result32 | result64 =>
      simp only [rejectArgs, flatArgs, Param.takesArg, Bool.false_eq_true, ite_false] at accepted
      exact flatCapacity_small params values capacity kinds.2 accepted
        (by simpa [flatCapacity, Param.takesArg] using found)
    | output =>
      simp only [flatCapacity, Option.some.injEq] at found
      subst found
      simp only [rejectArgs, flatArgs, Param.takesArg, ite_true, Param.reject,
        Arg.capacity] at accepted
      by_contra large
      simp only [List.headD_eq_head?_getD] at large
      simp [large] at accepted
    | word32 | word64 | enum32 =>
      simp only [rejectArgs, flatArgs, Param.takesArg, ite_true] at accepted
      refine flatCapacity_small params values.tail capacity kinds.2 ?_
        (by simpa [flatCapacity, Param.takesArg] using found)
      split at accepted
      · exact accepted
      · simp_all

/-- The output of a flat reply is the content of the buffer region, of the buffer's capacity. -/
theorem flat_output_at {mem : Mem} {root : UInt32} {sizes : List Nat} {errno : UInt64} :
    ∀ (params : List Param) (values : List UInt64) (outputs : List LeanExe.Bytes) (slot : Nat)
      (capacity : UInt64),
    params.all Param.flatKind = true → params.count .output ≤ 1 →
    ShownAt mem (outputRegions params sizes (flatArgs params values)
      (flatPointers params root slot)) outputs →
    outputs.map (fun output => output.data.size) =
      outputSizesOf params sizes (flatArgs params values) →
    flatCapacity params values = some capacity →
    Bytes.At mem root.toUInt64 (resultBytes params ⟨errno, outputs⟩ 0) ∧
      (resultBytes params ⟨errno, outputs⟩ 0).data.size = capacity.toNat
  | [], _, _, _, _, _, _, _, _, found => by simp [flatCapacity] at found
  | param :: params, values, outputs, slot, capacity, kinds, outputCount, shown, sizes', found => by
    simp only [List.all_cons, Bool.and_eq_true] at kinds
    cases param with
    | input => simp [Param.flatKind] at kinds
    | reported => simp [Param.flatKind] at kinds
    | word32 | word64 | enum32 =>
      simp only [flatArgs, flatPointers, outputRegions, outputSizesOf, List.tail_cons] at shown
      simp only [flatArgs, outputSizesOf, List.tail_cons] at sizes'
      simpa [resultBytes] using flat_output_at params values.tail outputs slot capacity kinds.2
        (by simpa [List.count_cons] using outputCount) shown sizes'
        (by simpa [flatCapacity, Param.takesArg] using found)
    | output =>
      simp only [flatCapacity, Option.some.injEq] at found
      subst found
      simp only [flatArgs, flatPointers, outputRegions, List.tail_cons] at shown
      cases outputs with
      | nil => simp [ShownAt] at shown
      | cons output outputs =>
        simp only [ShownAt, ite_true, List.headD_cons] at shown
        simp only [flatArgs, outputSizesOf, List.map_cons, List.cons.injEq, List.head?_cons,
          Option.map_some, Option.getD_some, Arg.capacity] at sizes'
        refine ⟨?_, ?_⟩
        · simpa [resultBytes, Reply.bytes] using shown.1
        · simpa [resultBytes, Reply.bytes] using sizes'.1
    | result32 | result64 =>
      simp only [flatArgs, flatPointers, outputRegions] at shown
      cases outputs with
      | nil => simp [ShownAt] at shown
      | cons output outputs =>
        simp only [ShownAt, ite_true] at shown
        simp only [flatArgs, outputSizesOf, List.map_cons, List.cons.injEq] at sizes'
        rw [resultBytes, resultBytes_shift]
        exact flat_output_at params values outputs (slot + 8) capacity kinds.2
          (by simpa [List.count_cons] using outputCount) shown.2 sizes'.2
          (by simpa [flatCapacity, Param.takesArg] using found)

/-- The frame of a flat request lies in the scratch area and the output buffer. -/
theorem flat_frame_cover {World : Type} {before after : Store World} {call : LeanExe.Wasi.Call}
    {sizes : List Nat} {values : List UInt64} {root : UInt64} {capacity : Nat}
    (hKinds : call.params.all Param.flatKind = true) (hOutputs : call.params.count .output ≤ 1)
    (hResults : call.params.countP Param.isResult ≤ 2) (hRoot : root.toNat < 4294967296)
    (hCapacity : ∀ value, flatCapacity call.params values = some value → value.toNat = capacity)
    (h : GuestFrame before after ((flatRegions call sizes values root).map Region.span)) :
    GuestFrame before after [ABI.scratch, (root.toNat, capacity)] := by
  refine h.cover fun span member => ?_
  obtain ⟨region, inList, rfl⟩ := List.mem_map.mp member
  rcases flat_region_mem call.params values 0 region hKinds hOutputs (by omega) inList with
    ⟨pointer, _, value, found, size⟩ | ⟨k, hk, pointer, size⟩
  · refine ⟨(root.toNat, capacity), List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_, ?_⟩
    · simp only [Region.span, pointer, UInt64.toNat_toUInt32, Nat.mod_eq_of_lt hRoot]
      omega
    · simp only [Region.span, pointer, size, UInt64.toNat_toUInt32, Nat.mod_eq_of_lt hRoot,
        hCapacity value found]
      omega
  · have hk' : 8 * k + 8 ≤ 16 := by
      have := Nat.mul_le_mul_left 8 (Nat.succ_le_of_lt hk)
      omega
    refine ⟨ABI.scratch, List.mem_cons_self .., ?_, ?_⟩ <;>
      simp only [Region.span, ABI.scratch, pointer] <;> rcases size with ⟨size, _⟩ | ⟨size, _⟩ <;>
      omega

/-- The allocation of the output buffer: none for a capacity of 0, and otherwise one buffer of
the capacity, or a resource trap. -/
theorem wp_sys_allocate_with {calls : List LeanExe.Wasi.Call}
    {World : Type} {source target : Module}
    (runtime : Runtime source) (layout : Relocation.LayoutWith calls source target)
    (profile : Relocation.Profile source) (hImports : target.imports = ABI.importsWith calls)
    (sourceHost : HostEnv Unit) {targetHost : HostEnv World}
    {heap : Heap} {store : Store World} {s : Locals} {capacityLocal rootLocal : Nat}
    {capacity : UInt64} {rest : Program} {Q : Assertion World} {aborts : Bool}
    (hHeap : heap.At (PureTransport.erase store))
    (hCount : capacity.toNat ≤ 4294967296)
    (hCap : (PureTransport.erase store).memoryCap source 0 ≤ 65535)
    (hCapacity : s.get capacityLocal = some (.i64 capacity))
    (hLow : s.params.length ≤ rootLocal) (hHigh : rootLocal < s.params.length + s.locals.length)
    (hRoom : capacity ≠ 0 → aborts = false →
      heap.Room (PureTransport.erase store) source (allocSize capacity))
    (hTrap : aborts = true → ∀ final : Store World,
      final.host = store.host → Q (.Trap final "unreachable"))
    (hZero : capacity = 0 →
      wp target rest Q store (setLocal s rootLocal (.i64 0)) targetHost)
    (hAllocated : capacity ≠ 0 → ∀ final : Store World, heap.Fits (allocSize capacity) →
      PureTransport.erase final =
        heap.allocateStore (PureTransport.erase store) (allocSize capacity) 1 →
      final.host = store.host →
      wp target rest Q final
        (setLocal s rootLocal
          (.i64 (FixedArrayAllocate.root heap.top (allocSize capacity) heap.free))) targetHost) :
    wp target (sysAllocateCodeWith calls capacityLocal rootLocal ++ rest) Q store s targetHost := by
  by_cases hNull : capacity = 0
  · subst capacity
    simp only [sysAllocateCodeWith, List.cons_append, List.nil_append, wp_localGet_cons,
      hCapacity, wp_eqzI64_cons, ite_true, wp_iff_control_types]
    refine wp_iff_cons rfl ?_
    rw [ite_eq_left (by decide : (1 : UInt32) ≠ 0)]
    simp only [wp_constI64_cons, wp_nil, List.take_succ_cons, List.take_zero,
      List.cons_append, List.nil_append, List.drop_zero]
    exact wp_localSet_local hLow hHigh (hZero rfl)
  · simp only [sysAllocateCodeWith, List.cons_append, List.nil_append, wp_localGet_cons,
      hCapacity, wp_eqzI64_cons, ite_eq_right hNull, wp_iff_control_types]
    refine wp_iff_cons rfl ?_
    rw [ite_eq_right (by decide : ¬((0 : UInt32) ≠ 0))]
    simp only [wp_localGet_cons, Locals.get_values, hCapacity]
    refine wp_alloc_frame_with (s := s) (values := s.values)
      runtime layout profile hImports sourceHost hHeap hCount hCap (hRoom hNull) ?_ ?_
    · intro hAbort final hWorld
      exact hTrap hAbort final hWorld
    · intro final hFits hStore hWorld
      simp only [wp_nil, List.take_succ_cons, List.take_zero, List.cons_append,
        List.nil_append, List.drop_zero]
      exact wp_localSet_local hLow hHigh (hAllocated hNull final hFits hStore hWorld)

end Verified.Wasi
