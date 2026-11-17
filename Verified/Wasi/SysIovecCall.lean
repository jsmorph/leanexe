import Verified.Wasi.SysRecord
import Verified.Wasi.NestedBytes

/-! The parts of the code of an iovec call.  Its parameters are those of `iovecParams`: a handle, an
iovec, a 64-bit word for `fd_pread` and `fd_pwrite`, and the result word.  The code tests the
handle and the iovec's capacity or input length, writes the element at scratch address 0, pushes
the handle, the element's address 0 and the count 1, the offset, and the result word's address 8,
and calls the import, whose contract gives the frame of the buffer and the result word. -/

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

/-! ## Parameters -/

theorem iovecParams_cases (isInput offset : Bool) :
    iovecParams isInput offset = [.handle, .iovec isInput, .result32] ∨
      iovecParams isInput offset = [.handle, .iovec isInput, .word64, .result32] := by
  cases offset <;> simp [iovecParams]

theorem iovec_extra {offset : Bool} {extra : List UInt64}
    (hExtra : extra.length = if offset then 1 else 0) :
    (offset = false ∧ extra = []) ∨ ∃ word, offset = true ∧ extra = [word] := by
  cases offset with
  | false => exact .inl ⟨rfl, List.eq_nil_of_length_eq_zero (by simpa using hExtra)⟩
  | true =>
    obtain ⟨word, rfl⟩ := List.length_eq_one_iff.mp (by simpa using hExtra)
    exact .inr ⟨word, rfl, rfl⟩

theorem iovec_wordCount {call : Call} {isInput offset : Bool}
    (hParams : call.params = iovecParams isInput offset) :
    call.wordCount = (if isInput then 1 else 2) + (if offset then 1 else 0) := by
  rw [Call.wordCount, hParams]
  cases isInput <;> cases offset <;> rfl

theorem iovec_inputCount {call : Call} {isInput offset : Bool}
    (hParams : call.params = iovecParams isInput offset) :
    call.inputCount = if isInput then 1 else 0 := by
  rw [Call.inputCount, hParams]
  cases isInput <;> cases offset <;> rfl

/-- The arguments of a read: the handle, the capacity, and the offset of `fd_pread`. -/
theorem iovec_read_args (offset : Bool) (values : List UInt64)
    (hLength : values.length = 2 + if offset then 1 else 0) :
    flatArgsWith (iovecParams false offset) values [] =
      [.word (values.getD 0 0), .space (values.getD 1 0)] ++ (values.drop 2).map .word := by
  cases offset with
  | false =>
    match values, hLength with
    | [a, b], _ => rfl
  | true =>
    match values, hLength with
    | [a, b, c], _ => rfl

/-- The arguments of a write: the handle, the bytes, and the offset of `fd_pwrite`. -/
theorem iovec_write_args (offset : Bool) (values : List UInt64) (bytes : LeanExe.Bytes)
    (hLength : values.length = 1 + if offset then 1 else 0) :
    flatArgsWith (iovecParams true offset) values [bytes] =
      [.word (values.getD 0 0), .bytes bytes] ++ (values.drop 1).map .word := by
  cases offset with
  | false =>
    match values, hLength with
    | [a], _ => rfl
  | true =>
    match values, hLength with
    | [a, b], _ => rfl

theorem iovec_reject (isInput offset : Bool) (handle : UInt64) (arg : Arg) {extra : List UInt64}
    (hExtra : extra.length = if offset then 1 else 0) :
    rejectArgs (iovecParams isInput offset) ([.word handle, arg] ++ extra.map .word) =
      if handle.toNat < 4294967296 then (Param.iovec isInput).reject arg else 61 := by
  have hHandleReject : Param.handle.reject (.word handle) =
      if handle.toNat < 4294967296 then 0 else 61 := rfl
  rcases iovec_extra hExtra with ⟨rfl, rfl⟩ | ⟨word, rfl, rfl⟩
  · simp only [iovecParams, List.nil_append, List.cons_append, List.map_nil,
      List.append_nil, rejectArgs, Param.takesArg, ite_true, hHandleReject]
    by_cases hHandle : handle.toNat < 4294967296 <;> simp only [hHandle, ite_true, ite_false]
    · by_cases hArg : (Param.iovec isInput).reject arg = 0
      · simp [hArg, rejectArgs, Param.takesArg]
      · simp [hArg]
    · simp
  · simp only [iovecParams, ite_true, List.nil_append, List.cons_append, List.map_cons,
      List.map_nil, rejectArgs, Param.takesArg, hHandleReject]
    by_cases hHandle : handle.toNat < 4294967296 <;> simp only [hHandle, ite_true, ite_false]
    · have hWord : ∀ value, Param.word64.reject value = 0 := fun _ => rfl
      by_cases hArg : (Param.iovec isInput).reject arg = 0
      · simp [hArg, hWord]
      · simp [hArg]
    · simp

theorem iovec_fits (isInput offset : Bool) (handle : UInt64) (arg : Arg) {extra : List UInt64}
    (hExtra : extra.length = if offset then 1 else 0) (hHandle : handle.toNat < 2 ^ 32)
    (hArg : argFits (.iovec isInput) arg = true) :
    argsFit (iovecParams isInput offset) ([.word handle, arg] ++ extra.map .word) = true := by
  rcases iovec_extra hExtra with ⟨rfl, rfl⟩ | ⟨word, rfl, rfl⟩ <;>
    simp_all [iovecParams, argsFit, Param.takesArg, argFits]

theorem iovec_lower (isInput offset : Bool) (handle : UInt64) (arg : Arg) {extra : List UInt64}
    (hExtra : extra.length = if offset then 1 else 0) (element buffer result : UInt32) :
    lowerArgs (iovecParams isInput offset) ([.word handle, arg] ++ extra.map .word)
        [element, buffer, result] =
      [.i32 handle.toUInt32, .i32 element, .i32 1] ++ extra.map .i64 ++ [.i32 result] := by
  rcases iovec_extra hExtra with ⟨rfl, rfl⟩ | ⟨word, rfl, rfl⟩ <;>
    simp [iovecParams, lowerArgs, Arg.value]

theorem iovec_read_places (offset : Bool) (handle capacity : UInt64) {extra : List UInt64}
    (hExtra : extra.length = if offset then 1 else 0) (element buffer result : UInt32) :
    inputPlaces (iovecParams false offset)
        ([.word handle, .space capacity] ++ extra.map .word) [element, buffer, result] =
      [(element, elementBytes buffer capacity.toNat)] := by
  rcases iovec_extra hExtra with ⟨rfl, rfl⟩ | ⟨word, rfl, rfl⟩ <;>
    simp [iovecParams, inputPlaces, Arg.capacity]

theorem iovec_write_places (offset : Bool) (handle : UInt64) (bytes : LeanExe.Bytes)
    {extra : List UInt64} (hExtra : extra.length = if offset then 1 else 0)
    (element buffer result : UInt32) :
    inputPlaces (iovecParams true offset) ([.word handle, .bytes bytes] ++ extra.map .word)
        [element, buffer, result] =
      [(element, elementBytes buffer bytes.data.size), (buffer, bytes)] := by
  rcases iovec_extra hExtra with ⟨rfl, rfl⟩ | ⟨word, rfl, rfl⟩ <;>
    simp [iovecParams, inputPlaces, Arg.length]

theorem iovec_read_regions (offset : Bool) (handle capacity : UInt64) {extra : List UInt64}
    (hExtra : extra.length = if offset then 1 else 0) (sizes : List Nat)
    (element buffer result : UInt32) :
    outputRegions (iovecParams false offset)
        sizes ([.word handle, .space capacity] ++ extra.map .word) [element, buffer, result] =
      [⟨buffer, capacity.toNat, 1, true⟩, ⟨result, 4, 4, true⟩] := by
  rcases iovec_extra hExtra with ⟨rfl, rfl⟩ | ⟨word, rfl, rfl⟩ <;>
    simp [iovecParams, outputRegions, Arg.capacity]

theorem iovec_write_regions (offset : Bool) (handle : UInt64) (bytes : LeanExe.Bytes)
    {extra : List UInt64} (hExtra : extra.length = if offset then 1 else 0) (sizes : List Nat)
    (element buffer result : UInt32) :
    outputRegions (iovecParams true offset)
        sizes ([.word handle, .bytes bytes] ++ extra.map .word) [element, buffer, result] =
      [⟨result, 4, 4, true⟩] := by
  rcases iovec_extra hExtra with ⟨rfl, rfl⟩ | ⟨word, rfl, rfl⟩ <;>
    simp [iovecParams, outputRegions]

theorem iovec_read_sizes (offset : Bool) (handle capacity : UInt64) {extra : List UInt64}
    (hExtra : extra.length = if offset then 1 else 0) (sizes : List Nat) :
    outputSizesOf (iovecParams false offset) sizes
        ([.word handle, .space capacity] ++ extra.map .word) = [capacity.toNat, 4] := by
  rcases iovec_extra hExtra with ⟨rfl, rfl⟩ | ⟨word, rfl, rfl⟩ <;>
    simp [iovecParams, outputSizesOf, Arg.capacity]

theorem iovec_write_sizes (offset : Bool) (handle : UInt64) (bytes : LeanExe.Bytes)
    {extra : List UInt64} (hExtra : extra.length = if offset then 1 else 0) (sizes : List Nat) :
    outputSizesOf (iovecParams true offset) sizes
        ([.word handle, .bytes bytes] ++ extra.map .word) = [4] := by
  rcases iovec_extra hExtra with ⟨rfl, rfl⟩ | ⟨word, rfl, rfl⟩ <;>
    simp [iovecParams, outputSizesOf]

/-! ## The bytes that the code stores -/

theorem byteOf_and255 (x : Nat) : byteOf (x &&& 255) 0 = byteOf x 0 := by
  apply UInt8.toNat_inj.mp
  rw [byteOf_toNat, byteOf_toNat, show (255 : Nat) = 2 ^ 8 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  simp

theorem byteOf_and_shift (x shift k : Nat) (h : shift = 8 * k) :
    byteOf (x >>> shift &&& 255) 0 = byteOf x k := by
  apply UInt8.toNat_inj.mp
  rw [byteOf_toNat, byteOf_toNat, show (255 : Nat) = 2 ^ 8 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, h]
  simp

theorem toUInt8_byteOf32 (v : UInt32) : v.toUInt8 = byteOf v.toNat 0 := by
  apply UInt8.toNat_inj.mp
  rw [UInt32.toNat_toUInt8, byteOf_toNat]
  simp

theorem toUInt8_byteOf64 (v : UInt64) : v.toUInt8 = byteOf v.toNat 0 := by
  apply UInt8.toNat_inj.mp
  rw [UInt64.toNat_toUInt8, byteOf_toNat]
  simp

/-- The element of an iovec that two 32-bit stores write at address 0. -/
private theorem element_stores (mem : Mem) (pointer length : UInt32)
    (hMemory : 8 ≤ mem.pages * 65536) :
    Bytes.At ((mem.write32 0 pointer).write32 4 length) 0 (elementBytes pointer length.toNat) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [elementBytes_size]; decide
  · rw [elementBytes_size]
    simpa [Mem.write32] using hMemory
  · intro i hi
    rw [elementBytes_size] at hi
    rw [elementBytes_get]
    have hLength : length.toNat % 2 ^ 32 = length.toNat := Nat.mod_eq_of_lt length.toNat_lt
    rw [hLength]
    interval_cases i <;> simp [Mem.write32, toUInt8_byteOf32, byteOf_and255,
      byteOf_and_shift _ 8 1 rfl, byteOf_and_shift _ 16 2 rfl, byteOf_and_shift _ 24 3 rfl]

/-- The element of an iovec that `metadataCode` writes at scratch address 0. -/
theorem element_written {World : Type} (store : Store World) (pointer length : UInt32)
    (hMemory : 16 ≤ store.mem.pages * 65536) :
    Bytes.At (initializeScratch store pointer length).mem 0 (elementBytes pointer length.toNat) := by
  refine (element_stores store.mem pointer length (by omega)).frame (by
    simp [initializeScratch, Mem.write32]) fun i hi => ?_
  rw [elementBytes_size] at hi
  exact write32_bytes_outside _ 8 0 (by simp only [UInt32.reduceToNat, UInt64.toNat_zero]; omega)

/-! ## The code of the test and the arguments -/

/-- The test of an iovec call leaves 61 when the handle or the length is `2^32` or more, and
otherwise 0. -/
theorem wp_iovec_reject {α : Type} {m : Module} {st : Store α} {env : HostEnv α} {s : Locals}
    {handleLocal lengthLocal : Nat} {handle length : UInt64} {rest : Program} {Q : Assertion α}
    (hHandle : s.get handleLocal = some (.i64 handle))
    (hLength : s.get lengthLocal = some (.i64 length))
    (h : wp m rest Q st { s with values := .i64 (if handle.toNat < 2 ^ 32 then
      (if length.toNat < 2 ^ 32 then 0 else 61) else 61) :: s.values } env) :
    wp m (iovecRejectCode handleLocal lengthLocal ++ rest) Q st s env := by
  simp only [iovecRejectCode, List.cons_append, List.nil_append, wp_localGet_cons, hHandle,
    wp_constI64_cons, wp_geUI64_cons, wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  by_cases hSmall : handle.toNat < 2 ^ 32
  · have hNot : ¬(4294967296 : UInt64) ≤ handle := by
      rw [UInt64.le_iff_toNat_le]; simp only [UInt64.reduceToNat]; omega
    rw [ite_eq_right (by simp [hNot])]
    simp only [wp_localGet_cons, hLength, wp_constI64_cons, wp_geUI64_cons,
      wp_iff_control_types]
    refine wp_iff_cons rfl ?_
    by_cases hShort : length.toNat < 2 ^ 32
    · have hNot' : ¬(4294967296 : UInt64) ≤ length := by
        rw [UInt64.le_iff_toNat_le]; simp only [UInt64.reduceToNat]; omega
      rw [ite_eq_right (by simp [hNot'])]
      simp only [wp_constI64_cons, wp_nil, List.take_succ_cons, List.take_zero, List.cons_append,
        List.nil_append, List.drop_zero, wp_nil]
      simpa only [hSmall, hShort, ite_true] using h
    · have hYes : (4294967296 : UInt64) ≤ length := by
        rw [UInt64.le_iff_toNat_le]; simp only [UInt64.reduceToNat]; omega
      rw [ite_eq_left (by simp [hYes])]
      simp only [wp_constI64_cons, wp_nil, List.take_succ_cons, List.take_zero, List.cons_append,
        List.nil_append, List.drop_zero, wp_nil]
      simpa only [hSmall, hShort, ite_true, ite_false] using h
  · have hYes : (4294967296 : UInt64) ≤ handle := by
      rw [UInt64.le_iff_toNat_le]; simp only [UInt64.reduceToNat]; omega
    rw [ite_eq_left (by simp [hYes])]
    simp only [wp_constI64_cons, wp_nil, List.take_succ_cons, List.take_zero, List.cons_append,
      List.nil_append, List.drop_zero, wp_nil]
    simpa only [hSmall, ite_false] using h

/-- The code pushes the core arguments of an iovec call: the handle, the element's address 0, the
count 1, the offset in `offsetLocal` when there is one, and the result word's address 8. -/
theorem wp_iovec_lower {α : Type} {m : Module} {st : Store α} {env : HostEnv α} {s : Locals}
    {handleLocal : Nat} {offsetLocal : Option Nat} {handle : UInt64} {extra : List UInt64}
    {rest : Program} {Q : Assertion α}
    (hHandle : s.get handleLocal = some (.i64 handle))
    (hOffset : List.Forall₂ (fun place value => s.get place = some (.i64 value))
      offsetLocal.toList extra)
    (h : wp m rest Q st { s with values := ([Value.i32 handle.toUInt32, .i32 0, .i32 1] ++
      extra.map Value.i64 ++ [Value.i32 8]).reverse ++ s.values } env) :
    wp m (iovecLowerCode handleLocal offsetLocal ++ rest) Q st s env := by
  cases offsetLocal with
  | none =>
    cases hOffset
    simp only [iovecLowerCode, List.cons_append, List.nil_append,
      wp_localGet_cons, hHandle, wp_wrapI64_cons, wrap_toUInt32, wp_const_cons]
    simpa only [List.map_nil, List.append_nil, List.cons_append, List.nil_append,
      List.reverse_cons, List.reverse_nil, List.append_assoc, List.singleton_append] using h
  | some place =>
    simp only [Option.toList_some] at hOffset
    obtain ⟨value, rfl⟩ : ∃ value, extra = [value] := by
      cases hOffset with
      | cons _ tail => cases tail; exact ⟨_, rfl⟩
    have hPlace : s.get place = some (.i64 value) := by
      cases hOffset with
      | cons head _ => exact head
    simp only [iovecLowerCode, List.cons_append, List.nil_append,
      wp_localGet_cons, hHandle, wp_wrapI64_cons, wrap_toUInt32, wp_const_cons, Locals.get_values,
      hPlace]
    simpa only [List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.reverse_cons, List.reverse_nil, List.append_assoc, List.singleton_append] using h

/-! ## The host call -/

/-- The stack after the arguments of a host call: the call takes the reversed core arguments and
leaves the values below them. -/
theorem call_stack_take {call : LeanExe.Wasi.Call} {args : List Value} (values : List Value)
    (hLength : args.length = (call.params.flatMap ABI.paramTypes).length) :
    (args.reverse ++ values).take (ABI.callImport call).params.length = args.reverse ∧
      (args.reverse ++ values).drop (ABI.callImport call).params.length = values := by
  constructor
  · apply List.take_left'
    rw [List.length_reverse, hLength]
    rfl
  · apply List.drop_left'
    rw [List.length_reverse, hLength]
    rfl

/-- The host call of a read whose element lies at scratch address 0 and whose buffer lies at
`root`: the code pushes the core arguments and calls the import, and the contract gives the errno,
the frame of the buffer and the result word, and on errno 0 the buffer at `root` and the count at
scratch address 8. -/
theorem wp_iovec_read_call_with {calls : List LeanExe.Wasi.Call} {World : Type} {m : Module}
    {host : Host World} {env : HostEnv (Observed World)} {store : Store (Observed World)}
    {s : Locals} {call : LeanExe.Wasi.Call} {offset : Bool} {handleLocal : Nat}
    {offsetLocal : Option Nat} {handle capacity root : UInt64} {extra : List UInt64}
    {rest : Program} {Q : Assertion (Observed World)}
    (hImports : m.imports = ABI.importsWith calls)
    (hHost : env.Satisfies m (hostSpecWith host calls))
    (hCall : calls[calls.idxOf call]? = some call)
    (hParams : call.params = iovecParams false offset)
    (hExtra : extra.length = if offset then 1 else 0)
    (hHandleSmall : handle.toNat < 4294967296) (hCapacity : capacity.toNat < 4294967296)
    (hHandle : s.get handleLocal = some (.i64 handle))
    (hOffset : List.Forall₂ (fun place value => s.get place = some (.i64 value))
      offsetLocal.toList extra)
    (hElement : Bytes.At store.mem 0 (elementBytes root.toUInt32 capacity.toNat))
    (hMemory : 16 ≤ store.mem.pages * 65536)
    (hBuffer : root.toNat + capacity.toNat ≤ store.mem.pages * 65536)
    (hAddress : root.toNat + capacity.toNat < 2 ^ 32)
    (hSeparate : 16 ≤ root.toNat ∨ (capacity = 0 ∧ root = 0))
    (hNext : ∀ (final : Store (Observed World)) (errno : UInt64) (outputs : List LeanExe.Bytes),
      (observedHost host).sys store.host call ([.word handle, .space capacity] ++ extra.map .word)
        (.returned errno outputs) final.host →
      GuestFrame store final [(root.toNat, capacity.toNat), (8, 4)] →
      (errno = 0 → ∃ buffer count, outputs = [buffer, count] ∧ Bytes.At final.mem root buffer ∧
        Bytes.At final.mem 8 count) →
      wp m rest Q final { s with values := .i32 errno.toUInt32 :: s.values } env)
    (hTrap : ∀ (final : Store (Observed World)) (message : String) (outputs : List LeanExe.Bytes),
      (observedHost host).sys store.host call ([.word handle, .space capacity] ++ extra.map .word)
        (.trapped message outputs) final.host → Q (.Trap final message)) :
    wp m (iovecLowerCode handleLocal offsetLocal ++ .call (3 + calls.idxOf call) :: rest) Q store s
      env := by
  have hRoot32 : root.toUInt32.toNat = root.toNat := by
    rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
  have hRequest : ∀ sizes, SysRequest store
      (lowerArgs call.params ([.word handle, .space capacity] ++ extra.map .word)
        [0, root.toUInt32, 8])
      call ([.word handle, .space capacity] ++ extra.map .word) [0, root.toUInt32, 8] sizes := by
    intro sizes
    have hRegions := iovec_read_regions offset handle capacity hExtra sizes 0 root.toUInt32 8
    have hPlaces := iovec_read_places offset handle capacity hExtra 0 root.toUInt32 8
    rw [← hParams] at hRegions hPlaces
    refine ⟨?_, ?_, rfl, ?_, ?_, ?_, ?_⟩
    · rw [hParams]
      exact iovec_fits false offset handle _ hExtra hHandleSmall
        (by simp [argFits]; omega)
    · change rejectArgs call.params _ = 0
      rw [hParams, iovec_reject false offset handle _ hExtra]
      simp [hHandleSmall, Param.reject, Arg.capacity, hCapacity]
    · rw [hPlaces]
      intro place member
      rw [List.mem_singleton] at member
      subst member
      exact hElement
    · rw [hRegions]
      intro region member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · simp only [hRoot32]
        exact ⟨hBuffer, hAddress, Nat.mod_one _⟩
      · simp only [UInt32.reduceToNat]
        exact ⟨by omega, by decide, by decide⟩
    · rw [hRegions]
      simp only [List.map_cons, List.map_nil, Region.span, hRoot32, UInt32.reduceToNat,
        List.pairwise_cons, List.mem_singleton, forall_eq, List.not_mem_nil,
        IsEmpty.forall_iff, implies_true, List.Pairwise.nil, and_true, regionsDisjoint]
      rcases hSeparate with h | ⟨rfl, rfl⟩
      · omega
      · simp
    · rw [hRegions, hPlaces]
      intro region member place placeMember
      rw [List.mem_singleton] at placeMember
      subst placeMember
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rw [elementBytes_size]
      rcases member with rfl | rfl
      · simp only [Region.span, hRoot32, UInt32.reduceToNat, regionsDisjoint]
        rcases hSeparate with h | ⟨rfl, rfl⟩
        · omega
        · simp
      · simp only [Region.span, UInt32.reduceToNat, regionsDisjoint]
        omega
  have hLower := iovec_lower false offset handle (.space capacity) hExtra 0 root.toUInt32 8
  rw [← hParams] at hLower
  refine wp_iovec_lower hHandle hOffset ?_
  obtain ⟨hTake, hDrop⟩ := call_stack_take (call := call) s.values
    (lowerArgs_length call.params ([.word handle, .space capacity] ++ extra.map .word)
      [0, root.toUInt32, 8])
  rw [← hLower]
  have hIndex : calls.idxOf call < calls.length := (List.getElem?_eq_some_iff.mp hCall).1
  refine wp_call_host_contract (id := 3 + calls.idxOf call) (imp := ABI.callImport call)
    (c := sysContract host call) (by rw [hImports]; exact ABI.importsWith_call hCall) hHost
    (by rw [hImports, ABI.importsWith_length]; omega) (hostSpecWith_sys host hCall) ?_ ?_ ?_
  · intro returned final contract
    rw [hTake, List.reverse_reverse] at contract
    obtain ⟨errno, outputs, rfl, hSys, hFrame, hShown⟩ := contract _ _ (hRequest _)
    have hRegions := iovec_read_regions offset handle capacity hExtra
      (host.reported store.host.world call) 0 root.toUInt32 8
    rw [← hParams] at hRegions
    have hFrame' : GuestFrame store final [(root.toNat, capacity.toNat), (8, 4)] := by
      have h := hFrame
      simp only [hRegions, List.map_cons, List.map_nil, Region.span, hRoot32,
        UInt32.reduceToNat] at h
      exact h
    have hShown' : errno = 0 → ∃ buffer count, outputs = [buffer, count] ∧
        Bytes.At final.mem root buffer ∧ Bytes.At final.mem 8 count := by
      intro hZero
      have h := hShown hZero
      simp only [hRegions] at h
      match outputs, h with
      | [buffer, count], h =>
        simp only [ShownAt, ite_true] at h
        obtain ⟨atBuffer, atCount, _⟩ := h
        refine ⟨buffer, count, rfl, ?_, atCount⟩
        rwa [read_narrow64 root (by omega)] at atBuffer
      | [], h => simp [ShownAt] at h
      | [_], h => simp [ShownAt] at h
      | _ :: _ :: _ :: _, h => simp [ShownAt] at h
    rw [hDrop]
    simpa only [ABI.callImport, ABI.callType, List.length_cons, List.length_nil, Nat.zero_add,
      List.take_succ_cons, List.take_zero, List.cons_append, List.nil_append] using
      hNext final errno outputs hSys hFrame' hShown'
  · intro final message contract
    rw [hTake, List.reverse_reverse] at contract
    obtain ⟨outputs, hSys, _⟩ := contract _ _ (hRequest _)
    exact hTrap final message outputs hSys
  · intro final tag arguments contract
    rw [hTake, List.reverse_reverse] at contract
    exact (contract _ _ (hRequest _)).elim

/-- The host call of a write whose element lies at scratch address 0 and whose bytes lie at
`root`: the code pushes the core arguments and calls the import, and the contract gives the errno,
the frame of the result word, and on errno 0 the count at scratch address 8. -/
theorem wp_iovec_write_call_with {calls : List LeanExe.Wasi.Call} {World : Type} {m : Module}
    {host : Host World} {env : HostEnv (Observed World)} {store : Store (Observed World)}
    {s : Locals} {call : LeanExe.Wasi.Call} {offset : Bool} {handleLocal : Nat}
    {offsetLocal : Option Nat} {handle root : UInt64} {bytes : LeanExe.Bytes}
    {extra : List UInt64} {rest : Program} {Q : Assertion (Observed World)}
    (hImports : m.imports = ABI.importsWith calls)
    (hHost : env.Satisfies m (hostSpecWith host calls))
    (hCall : calls[calls.idxOf call]? = some call)
    (hParams : call.params = iovecParams true offset)
    (hExtra : extra.length = if offset then 1 else 0)
    (hHandleSmall : handle.toNat < 4294967296) (hSize : bytes.data.size < 4294967296)
    (hHandle : s.get handleLocal = some (.i64 handle))
    (hOffset : List.Forall₂ (fun place value => s.get place = some (.i64 value))
      offsetLocal.toList extra)
    (hElement : Bytes.At store.mem 0 (elementBytes root.toUInt32 bytes.data.size))
    (hBytes : Bytes.At store.mem root bytes) (hRootSmall : root.toNat < 4294967296)
    (hApart : regionsDisjoint (root.toNat, bytes.data.size) ABI.scratch)
    (hMemory : 16 ≤ store.mem.pages * 65536)
    (hNext : ∀ (final : Store (Observed World)) (errno : UInt64) (outputs : List LeanExe.Bytes),
      (observedHost host).sys store.host call ([.word handle, .bytes bytes] ++ extra.map .word)
        (.returned errno outputs) final.host →
      GuestFrame store final [(8, 4)] →
      (errno = 0 → ∃ count, outputs = [count] ∧ Bytes.At final.mem 8 count) →
      wp m rest Q final { s with values := .i32 errno.toUInt32 :: s.values } env)
    (hTrap : ∀ (final : Store (Observed World)) (message : String) (outputs : List LeanExe.Bytes),
      (observedHost host).sys store.host call ([.word handle, .bytes bytes] ++ extra.map .word)
        (.trapped message outputs) final.host → Q (.Trap final message)) :
    wp m (iovecLowerCode handleLocal offsetLocal ++ .call (3 + calls.idxOf call) :: rest) Q store s
      env := by
  have hRoot32 : root.toUInt32.toNat = root.toNat := by
    rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt hRootSmall]
  have hRequest : ∀ sizes, SysRequest store
      (lowerArgs call.params ([.word handle, .bytes bytes] ++ extra.map .word)
        [0, root.toUInt32, 8])
      call ([.word handle, .bytes bytes] ++ extra.map .word) [0, root.toUInt32, 8] sizes := by
    intro sizes
    have hRegions := iovec_write_regions offset handle bytes hExtra sizes 0 root.toUInt32 8
    have hPlaces := iovec_write_places offset handle bytes hExtra 0 root.toUInt32 8
    rw [← hParams] at hRegions hPlaces
    refine ⟨?_, ?_, rfl, ?_, ?_, ?_, ?_⟩
    · rw [hParams]
      exact iovec_fits true offset handle _ hExtra hHandleSmall (by simp [argFits]; omega)
    · change rejectArgs call.params _ = 0
      rw [hParams, iovec_reject true offset handle _ hExtra]
      simp [hHandleSmall, Param.reject, Arg.length, hSize]
    · rw [hPlaces]
      intro place member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact hElement
      · simpa only [read_narrow64 root hRootSmall] using hBytes
    · rw [hRegions]
      intro region member
      rw [List.mem_singleton] at member
      subst member
      simp only [UInt32.reduceToNat]
      exact ⟨by omega, by decide, by decide⟩
    · rw [hRegions]
      exact List.pairwise_singleton _ _
    · rw [hRegions, hPlaces]
      intro region member place placeMember
      rw [List.mem_singleton] at member
      subst member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at placeMember
      rcases placeMember with rfl | rfl
      · simp only [Region.span, UInt32.reduceToNat, regionsDisjoint, elementBytes_size]
        omega
      · simp only [Region.span, UInt32.reduceToNat, regionsDisjoint, hRoot32]
        simp only [regionsDisjoint, ABI.scratch] at hApart
        omega
  have hLower := iovec_lower true offset handle (.bytes bytes) hExtra 0 root.toUInt32 8
  rw [← hParams] at hLower
  refine wp_iovec_lower hHandle hOffset ?_
  obtain ⟨hTake, hDrop⟩ := call_stack_take (call := call) s.values
    (lowerArgs_length call.params ([.word handle, .bytes bytes] ++ extra.map .word)
      [0, root.toUInt32, 8])
  rw [← hLower]
  have hIndex : calls.idxOf call < calls.length := (List.getElem?_eq_some_iff.mp hCall).1
  refine wp_call_host_contract (id := 3 + calls.idxOf call) (imp := ABI.callImport call)
    (c := sysContract host call) (by rw [hImports]; exact ABI.importsWith_call hCall) hHost
    (by rw [hImports, ABI.importsWith_length]; omega) (hostSpecWith_sys host hCall) ?_ ?_ ?_
  · intro returned final contract
    rw [hTake, List.reverse_reverse] at contract
    obtain ⟨errno, outputs, rfl, hSys, hFrame, hShown⟩ := contract _ _ (hRequest _)
    have hRegions := iovec_write_regions offset handle bytes hExtra
      (host.reported store.host.world call) 0 root.toUInt32 8
    rw [← hParams] at hRegions
    have hFrame' : GuestFrame store final [(8, 4)] := by
      have h := hFrame
      simp only [hRegions, List.map_cons, List.map_nil, Region.span, UInt32.reduceToNat] at h
      exact h
    have hShown' : errno = 0 → ∃ count, outputs = [count] ∧ Bytes.At final.mem 8 count := by
      intro hZero
      have h := hShown hZero
      simp only [hRegions] at h
      match outputs, h with
      | [count], h =>
        simp only [ShownAt, ite_true] at h
        exact ⟨count, rfl, h.1⟩
      | [], h => simp [ShownAt] at h
      | _ :: _ :: _, h => simp [ShownAt] at h
    rw [hDrop]
    simpa only [ABI.callImport, ABI.callType, List.length_cons, List.length_nil, Nat.zero_add,
      List.take_succ_cons, List.take_zero, List.cons_append, List.nil_append] using
      hNext final errno outputs hSys hFrame' hShown'
  · intro final message contract
    rw [hTake, List.reverse_reverse] at contract
    obtain ⟨outputs, hSys, _⟩ := contract _ _ (hRequest _)
    exact hTrap final message outputs hSys
  · intro final tag arguments contract
    rw [hTake, List.reverse_reverse] at contract
    exact (contract _ _ (hRequest _)).elim

end Verified.Wasi
