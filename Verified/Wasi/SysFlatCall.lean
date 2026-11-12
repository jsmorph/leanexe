import Verified.Wasi.SysLower
import Verified.Wasi.SysCost
import Interpreter.Wasm.Wp.Call

/-! The host call of a flat request.  The output buffer and the result words in the scratch area
are the request's regions; they lie in memory, apart from one another, at aligned pointers, so the
call's premise holds, and its frame is the scratch area and the buffer. -/

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Runtime

theorem ABI.importsWith_call {calls : List LeanExe.Wasi.Call} {index : Nat}
    {call : LeanExe.Wasi.Call} (h : calls[index]? = some call) :
    (ABI.importsWith calls)[3 + index]? = some (ABI.callImport call) := by
  rw [ABI.importsWith_eq, List.getElem?_append_right (by rw [ABI.imports_length]; omega)]
  simp [ABI.imports_length, h]

theorem flatCapacity_none : ∀ (params : List Param) (values : List UInt64),
    params.count .output = 0 → flatCapacity params values = none
  | [], _, _ => rfl
  | param :: params, values, none' => by
    cases param <;> simp_all [flatCapacity, Param.takesArg, flatCapacity_none params]

private theorem slot_toNat {slot : Nat} (h : slot < 4294967296) :
    (UInt32.ofNat slot).toNat = slot :=
  UInt32.toNat_ofNat_of_lt' (by rw [show UInt32.size = 4294967296 from rfl]; exact h)

/-- Each region of a flat request is the output buffer at `root` or a result word at a scratch
address `slot + 8 k` for one of the call's result parameters. -/
theorem flat_region_mem {root : UInt32} {sizes : List Nat} :
    ∀ (params : List Param) (values : List UInt64) (slot : Nat) (region : Region),
    params.all Param.flatKind = true → params.count .output ≤ 1 →
    slot + 8 * params.countP Param.isResult ≤ 16 →
    region ∈ outputRegions params sizes (flatArgs params values) (flatPointers params root slot) →
    (region.pointer = root ∧ region.align = 1 ∧
        ∃ capacity, flatCapacity params values = some capacity ∧ region.size = capacity.toNat) ∨
      ∃ k, k < params.countP Param.isResult ∧ region.pointer.toNat = slot + 8 * k ∧
        ((region.size = 4 ∧ region.align = 4) ∨ (region.size = 8 ∧ region.align = 8))
  | [], _, _, _, _, _, _, member => by simp [outputRegions] at member
  | param :: params, values, slot, region, kinds, outputs, room, member => by
    simp only [List.all_cons, Bool.and_eq_true] at kinds
    cases param with
    | input => simp [Param.flatKind] at kinds
    | reported => simp [Param.flatKind] at kinds
    | word32 | word64 | enum32 =>
      simp only [flatArgs, flatPointers, outputRegions, List.tail_cons] at member
      have tail := flat_region_mem params values.tail slot region kinds.2
        (by simpa [List.count_cons] using outputs)
        (by simpa [Param.isResult, List.countP_cons] using room) member
      simp only [flatCapacity, Param.takesArg, ite_true, Param.isResult, List.countP_cons,
        Bool.false_eq_true, ite_false, Nat.add_zero]
      exact tail
    | output =>
      simp only [flatArgs, flatPointers, outputRegions, List.tail_cons, List.mem_cons] at member
      have none' : params.count .output = 0 := by simp [List.count_cons] at outputs; omega
      rcases member with rfl | member
      · left
        exact ⟨rfl, rfl, values.headD 0, rfl, by simp [Arg.capacity]⟩
      · rcases flat_region_mem params values.tail slot region kinds.2 (by omega)
          (by simpa [Param.isResult, List.countP_cons] using room) member with
          ⟨_, _, capacity, found, _⟩ | result
        · simp [flatCapacity_none params values.tail none'] at found
        · right
          simpa [Param.isResult, List.countP_cons] using result
    | result32 | result64 =>
      simp only [flatArgs, flatPointers, outputRegions, List.mem_cons] at member
      have hSlot : slot + 8 ≤ 16 := by simp [Param.isResult, List.countP_cons] at room; omega
      rcases member with rfl | member
      · right
        exact ⟨0, by simp [Param.isResult, List.countP_cons], by simp [slot_toNat (slot := slot) (by omega)],
          by simp⟩
      · rcases flat_region_mem params values (slot + 8) region kinds.2
          (by simpa [List.count_cons] using outputs)
          (by simp [Param.isResult, List.countP_cons] at room; omega) member with
          output | ⟨k, hk, pointer, size⟩
        · left
          simpa [flatCapacity, Param.takesArg] using output
        · right
          exact ⟨k + 1, by simp [Param.isResult, List.countP_cons]; omega, by omega, size⟩

/-- The regions of a flat request lie apart from one another: the buffer lies above the scratch
area or is empty at 0, and the result words take distinct scratch addresses. -/
theorem flat_regions_apart {root : UInt32} {sizes : List Nat} :
    ∀ (params : List Param) (values : List UInt64) (slot : Nat),
    params.all Param.flatKind = true → params.count .output ≤ 1 →
    slot + 8 * params.countP Param.isResult ≤ 16 →
    (∀ capacity, flatCapacity params values = some capacity →
      16 ≤ root.toNat ∨ (capacity.toNat = 0 ∧ root = 0)) →
    ((outputRegions params sizes (flatArgs params values)
      (flatPointers params root slot)).map Region.span).Pairwise regionsDisjoint
  | [], _, _, _, _, _, _ => by simp [outputRegions]
  | param :: params, values, slot, kinds, outputs, room, separate => by
    have kinds' := kinds
    simp only [List.all_cons, Bool.and_eq_true] at kinds'
    rw [List.pairwise_map]
    cases param with
    | input => simp [Param.flatKind] at kinds'
    | reported => simp [Param.flatKind] at kinds'
    | word32 | word64 | enum32 =>
      simp only [flatArgs, flatPointers, outputRegions, List.tail_cons]
      rw [← List.pairwise_map]
      exact flat_regions_apart params values.tail slot kinds'.2
        (by simpa [List.count_cons] using outputs)
        (by simpa [Param.isResult, List.countP_cons] using room)
        (by simpa [flatCapacity, Param.takesArg] using separate)
    | output =>
      simp only [flatArgs, flatPointers, outputRegions, List.tail_cons, List.pairwise_cons]
      have none' : params.count .output = 0 := by simp [List.count_cons] at outputs; omega
      have hCapacity := separate (values.headD 0) (by simp [flatCapacity])
      have room' : slot + 8 * params.countP Param.isResult ≤ 16 := by
        simpa [Param.isResult, List.countP_cons] using room
      refine ⟨?_, ?_⟩
      · intro region member
        rcases flat_region_mem params values.tail slot region kinds'.2 (by omega) room' member with
          ⟨_, _, capacity, found, _⟩ | ⟨k, hk, pointer, size⟩
        · simp [flatCapacity_none params values.tail none'] at found
        · have hk' : slot + 8 * k + 8 ≤ 16 := by
            have := Nat.mul_le_mul_left 8 (Nat.succ_le_of_lt hk)
            omega
          show regionsDisjoint (root.toNat, (values.headD 0).toNat)
            (region.pointer.toNat, region.size)
          simp only [regionsDisjoint]
          rcases hCapacity with high | ⟨zero, rfl⟩ <;> rcases size with ⟨s4, _⟩ | ⟨s8, _⟩
          all_goals first | omega | (simp only [UInt32.toNat_zero]; omega)
      · rw [← List.pairwise_map]
        exact flat_regions_apart params values.tail slot kinds'.2 (by omega) room'
          (by simp [flatCapacity_none params values.tail none'])
    | result32 | result64 =>
      simp only [flatArgs, flatPointers, outputRegions, List.pairwise_cons]
      have hSlot : slot + 8 ≤ 16 := by simp [Param.isResult, List.countP_cons] at room; omega
      have room' : slot + 8 + 8 * params.countP Param.isResult ≤ 16 := by
        simp [Param.isResult, List.countP_cons] at room; omega
      have outputs' : params.count .output ≤ 1 := by simpa [List.count_cons] using outputs
      refine ⟨?_, ?_⟩
      · intro region member
        rcases flat_region_mem params values (slot + 8) region kinds'.2 outputs' room' member with
          ⟨pointer, _, capacity, found, size⟩ | ⟨k, hk, pointer, size⟩
        · have hCapacity := separate capacity (by simpa [flatCapacity, Param.takesArg] using found)
          simp only [Region.span, List.headD_cons, regionsDisjoint, pointer, size,
            slot_toNat (slot := slot) (by omega)]
          rcases hCapacity with high | ⟨zero, rfl⟩
          · omega
          · simp only [UInt32.toNat_zero]; omega
        · simp only [Region.span, List.headD_cons, regionsDisjoint,
            slot_toNat (slot := slot) (by omega), pointer]
          rcases size with ⟨s4, _⟩ | ⟨s8, _⟩ <;> omega
      · rw [← List.pairwise_map]
        exact flat_regions_apart params values (slot + 8) kinds'.2 outputs' room'
          (by simpa [flatCapacity, Param.takesArg] using separate)


/-- The regions of a flat request with the buffer at `root` and the result words from scratch
address 0. -/
abbrev flatRegions (call : LeanExe.Wasi.Call) (sizes : List Nat) (values : List UInt64)
    (root : UInt64) : List Region :=
  outputRegions call.params sizes (flatArgs call.params values)
    (flatPointers call.params root.toUInt32 0)

/-- The host call of a flat request whose pointers are the buffer's root and the scratch addresses
0 and 8: the argument code pushes the core arguments, the request satisfies the call's premise,
and the contract gives the errno, the frame of the request's regions, and the shown outputs. -/
theorem wp_sys_flat_call_with {calls : List LeanExe.Wasi.Call} {World : Type} {m : Module}
    {host : Host World} {env : HostEnv (Observed World)} {store : Store (Observed World)}
    {s : Locals} {call : LeanExe.Wasi.Call} {locs : List Nat} {values : List UInt64}
    {rootLocal : Nat} {root : UInt64} {rest : Program} {Q : Assertion (Observed World)}
    (hImports : m.imports = ABI.importsWith calls)
    (hHost : env.Satisfies m (hostSpecWith host calls))
    (hCall : calls[calls.idxOf call]? = some call)
    (hKinds : call.params.all Param.flatKind = true) (hOutputs : call.params.count .output ≤ 1)
    (hResults : call.params.countP Param.isResult ≤ 2)
    (hAccepted : call.reject (flatArgs call.params values) = 0)
    (hHeld : List.Forall₂ (fun place value => s.get place = some (.i64 value)) locs values)
    (hCount : values.length = call.argCount)
    (hRoot : s.get rootLocal = some (.i64 root)) (hRootSmall : root.toNat < 4294967296)
    (hMemory : 16 ≤ store.mem.pages * 65536)
    (hBuffer : ∀ capacity, flatCapacity call.params values = some capacity →
      root.toNat + capacity.toNat ≤ store.mem.pages * 65536 ∧
        root.toNat + capacity.toNat ≤ 2 ^ 32 ∧
        (16 ≤ root.toNat ∨ (capacity.toNat = 0 ∧ root = 0)))
    (hNext : ∀ (final : Store (Observed World)) (errno : UInt64) (outputs : List LeanExe.Bytes),
      (observedHost host).sys store.host call (flatArgs call.params values)
        (.returned errno outputs) final.host →
      GuestFrame store final
        ((flatRegions call (host.reported store.host.world call) values root).map Region.span) →
      (errno = 0 → ShownAt final.mem
        (flatRegions call (host.reported store.host.world call) values root) outputs) →
      wp m rest Q final { s with values := .i32 errno.toUInt32 :: s.values } env)
    (hTrap : ∀ (final : Store (Observed World)) (message : String) (outputs : List LeanExe.Bytes),
      (observedHost host).sys store.host call (flatArgs call.params values)
        (.trapped message outputs) final.host →
      GuestFrame store final
        ((flatRegions call (host.reported store.host.world call) values root).map Region.span) →
      Q (.Trap final message)) :
    wp m (sysLowerCode call.params locs rootLocal 0 ++ .call (3 + calls.idxOf call) :: rest) Q
      store s env := by
  have hRoot32 : root.toUInt32.toNat = root.toNat := by
    rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt hRootSmall]
  have hRoom : 0 + 8 * call.params.countP Param.isResult ≤ 16 := by omega
  have hSeparate : ∀ capacity, flatCapacity call.params values = some capacity →
      16 ≤ root.toUInt32.toNat ∨ (capacity.toNat = 0 ∧ root.toUInt32 = 0) := by
    intro capacity found
    rcases (hBuffer capacity found).2.2 with high | ⟨zero, rfl⟩
    · exact Or.inl (by rw [hRoot32]; exact high)
    · exact Or.inr ⟨zero, rfl⟩
  have hIndex : calls.idxOf call < calls.length := (List.getElem?_eq_some_iff.mp hCall).1
  have hRequest : SysRequest store
      (lowerArgs call.params (flatArgs call.params values) (flatPointers call.params root.toUInt32 0))
      call (flatArgs call.params values) (flatPointers call.params root.toUInt32 0)
      (host.reported store.host.world call) := by
    refine ⟨hAccepted, rfl, ?_, ?_, ?_⟩
    · rw [inputPlaces_flat _ _ _ hKinds]
      intro place member
      cases member
    · intro region member
      rcases flat_region_mem call.params values 0 region hKinds hOutputs hRoom member with
        ⟨pointer, align, capacity, found, size⟩ | ⟨k, hk, pointer, size⟩
      · have bound := hBuffer capacity found
        rw [pointer, size, align, hRoot32]
        exact ⟨bound.1, bound.2.1, Nat.mod_one _⟩
      · have hk' : 8 * k + 8 ≤ 16 := by
          have := Nat.mul_le_mul_left 8 (Nat.succ_le_of_lt hk)
          omega
        rw [pointer]
        rcases size with ⟨size, align⟩ | ⟨size, align⟩ <;> rw [size, align] <;>
          refine ⟨by omega, by omega, by omega⟩
    · rw [inputPlaces_flat _ _ _ hKinds, List.map_nil, List.append_nil]
      exact flat_regions_apart call.params values 0 hKinds hOutputs hRoom hSeparate
  have hLength := lowerArgs_length call.params (flatArgs call.params values)
    (flatPointers call.params root.toUInt32 0)
  have hTake : ((lowerArgs call.params (flatArgs call.params values)
      (flatPointers call.params root.toUInt32 0)).reverse ++ s.values).take
      (ABI.callImport call).params.length = (lowerArgs call.params (flatArgs call.params values)
        (flatPointers call.params root.toUInt32 0)).reverse := by
    apply List.take_left'
    rw [List.length_reverse, hLength]
    rfl
  have hDrop : ((lowerArgs call.params (flatArgs call.params values)
      (flatPointers call.params root.toUInt32 0)).reverse ++ s.values).drop
      (ABI.callImport call).params.length = s.values := by
    apply List.drop_left'
    rw [List.length_reverse, hLength]
    rfl
  refine wp_sys_lower call.params locs values 0 s _ Q hKinds hHeld hCount hRoot ?_
  refine wp_call_host_contract (id := 3 + calls.idxOf call) (imp := ABI.callImport call)
    (c := sysContract host call) (by rw [hImports]; exact ABI.importsWith_call hCall) hHost
    (by rw [hImports, ABI.importsWith_length]; omega) (hostSpecWith_sys host hCall) ?_ ?_ ?_
  · intro returned final contract
    rw [hTake, List.reverse_reverse] at contract
    obtain ⟨errno, outputs, rfl, hSys, hFrame, hShown⟩ := contract _ _ hRequest
    rw [hDrop]
    simpa only [ABI.callImport, ABI.callType, List.length_cons, List.length_nil, Nat.zero_add,
      List.take_succ_cons, List.take_zero, List.cons_append, List.nil_append] using
      hNext final errno outputs hSys hFrame hShown
  · intro final message contract
    rw [hTake, List.reverse_reverse] at contract
    obtain ⟨outputs, hSys, hFrame⟩ := contract _ _ hRequest
    exact hTrap final message outputs hSys hFrame
  · intro final tag arguments contract
    rw [hTake, List.reverse_reverse] at contract
    exact (contract _ _ hRequest).elim

end Verified.Wasi
