import Verified.Wasi.SysFlatLoads
import Verified.Wasi.ReadReady
import Verified.Wasi.ReadDiscard
import Verified.Wasi.ReadProof
import Verified.Wasi.RuntimeFrame

/-! Parts of a flat call: the capacity of its output, and the output and the frame that the host
call leaves. -/

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

/-! ## Calls with inputs -/

/-- An accepted request with inputs has an output capacity below `2 ^ 32`. -/
theorem flatCapacityWith_small :
    ∀ (params : List Param) (values : List UInt64) (inputs : List LeanExe.Bytes)
      (capacity : UInt64),
    params.all Param.inputKind = true → inputs.length = params.count .input →
    rejectArgs params (flatArgsWith params values inputs) = 0 →
    flatCapacityWith params values inputs = some capacity → capacity.toNat < 4294967296
  | [], _, _, _, _, _, _, found => by simp [flatCapacityWith] at found
  | param :: params, values, inputs, capacity, kinds, count, accepted, found => by
    simp only [List.all_cons, Bool.and_eq_true] at kinds
    cases param with
    | reported | record | iovec | subscriptions => simp [Param.inputKind, Param.flatKind] at kinds
    | input =>
      cases inputs with
      | nil => simp at count
      | cons input inputs =>
        simp only [flatArgsWith, rejectArgs, Param.takesArg, ite_true] at accepted
        refine flatCapacityWith_small params values inputs capacity kinds.2
          (by simpa [List.count_cons] using count) ?_ (by simpa [flatCapacityWith] using found)
        split at accepted
        · exact accepted
        · simp_all
    | result32 | result64 =>
      simp only [rejectArgs, flatArgsWith, Param.takesArg, Bool.false_eq_true, ite_false]
        at accepted
      exact flatCapacityWith_small params values inputs capacity kinds.2
        (by simpa [List.count_cons] using count) accepted
        (by simpa [flatCapacityWith, Param.takesArg] using found)
    | output =>
      simp only [flatCapacityWith, Option.some.injEq] at found
      subst found
      simp only [rejectArgs, flatArgsWith, Param.takesArg, ite_true, Param.reject,
        Arg.capacity] at accepted
      by_contra large
      simp only [List.headD_eq_head?_getD] at large
      simp [large] at accepted
    | word32 | handle | word64 | enum32 | flags32 | flags64 =>
      simp only [rejectArgs, flatArgsWith, Param.takesArg, ite_true] at accepted
      refine flatCapacityWith_small params values.tail inputs capacity kinds.2
        (by simpa [List.count_cons] using count) ?_
        (by simpa [flatCapacityWith, Param.takesArg] using found)
      split at accepted
      · exact accepted
      · simp_all

/-- The output of a flat reply with inputs is the content of the buffer region, of the buffer's
capacity. -/
theorem flat_output_at_inputs {mem : Mem} {root : UInt32} {sizes : List Nat} {errno : UInt64} :
    ∀ (params : List Param) (values : List UInt64) (inputs : List (UInt64 × LeanExe.Bytes))
      (outputs : List LeanExe.Bytes) (slot : Nat) (capacity : UInt64),
    params.all Param.inputKind = true → params.count .output ≤ 1 →
    inputs.length = params.count .input →
    ShownAt mem (outputRegions params sizes (flatArgsWith params values (inputs.map Prod.snd))
      (flatPointersWith params root slot (inputs.map fun input => input.1.toUInt32))) outputs →
    outputs.map (fun output => output.data.size) =
      outputSizesOf params sizes (flatArgsWith params values (inputs.map Prod.snd)) →
    flatCapacityWith params values (inputs.map Prod.snd) = some capacity →
    Bytes.At mem root.toUInt64 (resultBytes params ⟨errno, outputs⟩ 0) ∧
      (resultBytes params ⟨errno, outputs⟩ 0).data.size = capacity.toNat
  | [], _, _, _, _, _, _, _, _, _, _, found => by simp [flatCapacityWith] at found
  | param :: params, values, inputs, outputs, slot, capacity, kinds, outputCount, count, shown,
      sizes', found => by
    simp only [List.all_cons, Bool.and_eq_true] at kinds
    cases param with
    | reported | record | iovec | subscriptions => simp [Param.inputKind, Param.flatKind] at kinds
    | input =>
      cases inputs with
      | nil => simp at count
      | cons input inputs =>
        simp only [List.map_cons, flatArgsWith, flatPointersWith, outputRegions, outputSizesOf,
          List.tail_cons] at shown sizes'
        simpa [resultBytes] using flat_output_at_inputs params values inputs outputs slot capacity
          kinds.2 (by simpa [List.count_cons] using outputCount)
          (by simpa [List.count_cons] using count) shown sizes'
          (by simpa [List.map_cons, flatCapacityWith] using found)
    | word32 | handle | word64 | enum32 | flags32 | flags64 =>
      simp only [flatArgsWith, flatPointersWith, outputRegions, outputSizesOf,
        List.tail_cons] at shown sizes'
      simpa [resultBytes] using flat_output_at_inputs params values.tail inputs outputs slot
        capacity kinds.2 (by simpa [List.count_cons] using outputCount)
        (by simpa [List.count_cons] using count) shown sizes'
        (by simpa [flatCapacityWith, Param.takesArg] using found)
    | output =>
      simp only [flatCapacityWith, Option.some.injEq] at found
      subst found
      simp only [flatArgsWith, flatPointersWith, outputRegions, List.tail_cons] at shown
      cases outputs with
      | nil => simp [ShownAt] at shown
      | cons output outputs =>
        simp only [ShownAt, ite_true, List.headD_cons] at shown
        simp only [flatArgsWith, outputSizesOf, List.map_cons, List.cons.injEq, List.head?_cons,
          Option.map_some, Option.getD_some, Arg.capacity] at sizes'
        refine ⟨?_, ?_⟩
        · simpa [resultBytes, Reply.bytes] using shown.1
        · simpa [resultBytes, Reply.bytes] using sizes'.1
    | result32 | result64 =>
      simp only [flatArgsWith, flatPointersWith, outputRegions] at shown
      cases outputs with
      | nil => simp [ShownAt] at shown
      | cons output outputs =>
        simp only [ShownAt, ite_true] at shown
        simp only [flatArgsWith, outputSizesOf, List.map_cons, List.cons.injEq] at sizes'
        rw [resultBytes, resultBytes_shift]
        exact flat_output_at_inputs params values inputs outputs (slot + 8) capacity kinds.2
          (by simpa [List.count_cons] using outputCount) (by simpa [List.count_cons] using count)
          shown.2 sizes'.2 (by simpa [flatCapacityWith, Param.takesArg] using found)

/-- The frame of a flat request with inputs lies in the scratch area and the output buffer. -/
theorem flat_frame_cover_inputs {World : Type} {before after : Store World}
    {call : LeanExe.Wasi.Call} {sizes : List Nat} {values : List UInt64}
    {inputs : List (UInt64 × LeanExe.Bytes)} {root : UInt64} {capacity : Nat}
    (hKinds : call.params.all Param.inputKind = true) (hOutputs : call.params.count .output ≤ 1)
    (hResults : call.params.countP Param.isResult ≤ 2)
    (hCount : inputs.length = call.params.count .input) (hRoot : root.toNat < 4294967296)
    (hCapacity : ∀ value, flatCapacityWith call.params values (inputs.map Prod.snd) = some value →
      value.toNat = capacity)
    (h : GuestFrame before after
      ((flatRegionsWith call sizes values inputs root).map Region.span)) :
    GuestFrame before after [ABI.scratch, (root.toNat, capacity)] := by
  refine h.cover fun span member => ?_
  obtain ⟨region, inList, rfl⟩ := List.mem_map.mp member
  rcases flat_region_mem_inputs call.params values inputs 0 region hKinds hOutputs (by omega)
      hCount inList with
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

/-! ## Calls without inputs -/

/-- An accepted request has an output capacity below `2 ^ 32`. -/
theorem flatCapacity_small :
    ∀ (params : List Param) (values : List UInt64) (capacity : UInt64),
    params.all Param.flatKind = true →
    rejectArgs params (flatArgs params values) = 0 →
    flatCapacity params values = some capacity → capacity.toNat < 4294967296 := by
  intro params values capacity kinds accepted found
  exact flatCapacityWith_small params values [] capacity (inputKind_of_flat kinds)
    (count_input_of_flat kinds).symm (by rwa [flatArgsWith_nil])
    (by rwa [flatCapacityWith_nil])

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
      (resultBytes params ⟨errno, outputs⟩ 0).data.size = capacity.toNat := by
  intro params values outputs slot capacity kinds outputCount shown sizes' found
  exact flat_output_at_inputs (root := root) (sizes := sizes) params values [] outputs slot
    capacity (inputKind_of_flat kinds) outputCount (by rw [count_input_of_flat kinds]; rfl)
    (by simpa only [List.map_nil, flatArgsWith_nil, flatPointersWith_nil] using shown)
    (by simpa only [List.map_nil, flatArgsWith_nil] using sizes')
    (by simpa only [List.map_nil, flatCapacityWith_nil] using found)

/-- The frame of a flat request lies in the scratch area and the output buffer. -/
theorem flat_frame_cover {World : Type} {before after : Store World} {call : LeanExe.Wasi.Call}
    {sizes : List Nat} {values : List UInt64} {root : UInt64} {capacity : Nat}
    (hKinds : call.params.all Param.flatKind = true) (hOutputs : call.params.count .output ≤ 1)
    (hResults : call.params.countP Param.isResult ≤ 2) (hRoot : root.toNat < 4294967296)
    (hCapacity : ∀ value, flatCapacity call.params values = some value → value.toNat = capacity)
    (h : GuestFrame before after ((flatRegions call sizes values root).map Region.span)) :
    GuestFrame before after [ABI.scratch, (root.toNat, capacity)] := by
  refine flat_frame_cover_inputs (sizes := sizes) (values := values) (inputs := [])
    (inputKind_of_flat hKinds) hOutputs hResults (by rw [count_input_of_flat hKinds]; rfl) hRoot
    (by simpa only [List.map_nil, flatCapacityWith_nil] using hCapacity) ?_
  simpa only [flatRegionsWith, flatRegions, List.map_nil, flatArgsWith_nil,
    flatPointersWith_nil] using h

end Verified.Wasi
