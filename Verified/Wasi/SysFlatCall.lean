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

theorem rejectArgs_cons_zero {param : Param} {params : List Param} {arg : Arg}
    {rest : List Arg} (takes : param.takesArg = true)
    (zero : rejectArgs (param :: params) (arg :: rest) = 0) :
    param.reject arg = 0 ∧ rejectArgs params rest = 0 := by
  simp only [rejectArgs, takes, ↓reduceIte] at zero
  by_cases head : param.reject arg = 0
  · rw [if_pos head] at zero
    exact ⟨head, zero⟩
  · rw [if_neg head] at zero
    exact absurd zero head

private theorem slot_toNat {slot : Nat} (h : slot < 4294967296) :
    (UInt32.ofNat slot).toNat = slot :=
  UInt32.toNat_ofNat_of_lt' (by rw [show UInt32.size = 4294967296 from rfl]; exact h)

/-- The regions of a flat request with the buffer at `root` and the result words from scratch
address 0. -/
abbrev flatRegions (call : LeanExe.Wasi.Call) (sizes : List Nat) (values : List UInt64)
    (root : UInt64) : List Region :=
  outputRegions call.params sizes (flatArgs call.params values)
    (flatPointers call.params root.toUInt32 0)


/-! ## Calls with inputs -/

theorem flatCapacityWith_none : ∀ (params : List Param) (values : List UInt64)
    (inputs : List LeanExe.Bytes), params.count .output = 0 →
    flatCapacityWith params values inputs = none
  | [], _, _, _ => rfl
  | param :: params, values, inputs, none' => by
    cases param <;> cases inputs <;>
      simp_all [flatCapacityWith, Param.takesArg, flatCapacityWith_none params]

/-- A flat request with inputs that its parameters accept fits them. -/
theorem flatArgsWith_fit : ∀ (params : List Param) (values : List UInt64)
    (inputs : List LeanExe.Bytes),
    params.all Param.inputKind = true → inputs.length = params.count .input →
    rejectArgs params (flatArgsWith params values inputs) = 0 →
    argsFit params (flatArgsWith params values inputs) = true
  | [], _, _, _, _, _ => rfl
  | param :: params, values, inputs, hKinds, hCount, hAccepted => by
    simp only [List.all_cons, Bool.and_eq_true] at hKinds
    cases param with
    | input =>
      cases inputs with
      | nil => simp at hCount
      | cons input inputs =>
        obtain ⟨head, rest⟩ := rejectArgs_cons_zero rfl hAccepted
        simp only [Param.reject, Arg.length] at head
        simp only [flatArgsWith, argsFit, Param.takesArg, ↓reduceIte, argFits, Bool.and_eq_true,
          decide_eq_true_eq]
        refine ⟨?_, flatArgsWith_fit params values inputs hKinds.2
          (by simpa [List.count_cons] using hCount) rest⟩
        by_contra large
        simp only [Nat.reducePow] at large
        simp [large] at head
    | word32 =>
      obtain ⟨head, rest⟩ := rejectArgs_cons_zero rfl hAccepted
      simp only [Param.reject, Arg.value] at head
      simp only [flatArgsWith, argsFit, Param.takesArg, ↓reduceIte, argFits, Bool.and_eq_true,
        decide_eq_true_eq]
      refine ⟨?_, flatArgsWith_fit params values.tail inputs hKinds.2
        (by simpa [List.count_cons] using hCount) rest⟩
      simpa using head
    | enum32 count =>
      obtain ⟨head, rest⟩ := rejectArgs_cons_zero rfl hAccepted
      simp only [Param.reject, Arg.value] at head
      simp only [Param.inputKind, Param.flatKind, decide_eq_true_eq] at hKinds
      simp only [flatArgsWith, argsFit, Param.takesArg, ↓reduceIte, argFits, Bool.and_eq_true,
        decide_eq_true_eq]
      refine ⟨?_, flatArgsWith_fit params values.tail inputs hKinds.2
        (by simpa [List.count_cons] using hCount) rest⟩
      have low : (values.headD 0).toNat < count := by simpa using head
      omega
    | word64 | flags64 =>
      obtain ⟨_, rest⟩ := rejectArgs_cons_zero rfl hAccepted
      simp only [flatArgsWith, argsFit, Param.takesArg, ↓reduceIte, argFits, Bool.true_and]
      exact flatArgsWith_fit params values.tail inputs hKinds.2
        (by simpa [List.count_cons] using hCount) rest
    | flags32 mask =>
      obtain ⟨head, rest⟩ := rejectArgs_cons_zero rfl hAccepted
      simp only [flatArgsWith, argsFit, Param.takesArg, ↓reduceIte, argFits, Bool.and_eq_true,
        decide_eq_true_eq]
      refine ⟨?_, flatArgsWith_fit params values.tail inputs hKinds.2
        (by simpa [List.count_cons] using hCount) rest⟩
      simp only [Param.reject, Arg.value] at head
      by_contra large
      simp only [List.headD_eq_head?_getD, Nat.reducePow] at large
      simp [large] at head
    | output =>
      obtain ⟨head, rest⟩ := rejectArgs_cons_zero rfl hAccepted
      simp only [Param.reject, Arg.capacity] at head
      simp only [flatArgsWith, argsFit, Param.takesArg, ↓reduceIte, argFits, Bool.and_eq_true,
        decide_eq_true_eq]
      refine ⟨?_, flatArgsWith_fit params values.tail inputs hKinds.2
        (by simpa [List.count_cons] using hCount) rest⟩
      simpa using head
    | result32 | result64 =>
      simp only [flatArgsWith, rejectArgs, Param.takesArg, Bool.false_eq_true, ↓reduceIte]
        at hAccepted ⊢
      simp only [argsFit, Param.takesArg, Bool.false_eq_true, ↓reduceIte]
      exact flatArgsWith_fit params values inputs hKinds.2
        (by simpa [List.count_cons] using hCount) hAccepted
    | reported | record => simp [Param.inputKind, Param.flatKind] at hKinds

/-- Each region of a flat request with inputs is the output buffer at `root` or a result word at
a scratch address `slot + 8 k` for one of the call's result parameters. -/
theorem flat_region_mem_inputs {root : UInt32} {sizes : List Nat} :
    ∀ (params : List Param) (values : List UInt64) (inputs : List (UInt64 × LeanExe.Bytes))
      (slot : Nat) (region : Region),
    params.all Param.inputKind = true → params.count .output ≤ 1 →
    slot + 8 * params.countP Param.isResult ≤ 16 → inputs.length = params.count .input →
    region ∈ outputRegions params sizes (flatArgsWith params values (inputs.map Prod.snd))
      (flatPointersWith params root slot (inputs.map fun input => input.1.toUInt32)) →
    (region.pointer = root ∧ region.align = 1 ∧
        ∃ capacity, flatCapacityWith params values (inputs.map Prod.snd) = some capacity ∧
          region.size = capacity.toNat) ∨
      ∃ k, k < params.countP Param.isResult ∧ region.pointer.toNat = slot + 8 * k ∧
        ((region.size = 4 ∧ region.align = 4) ∨ (region.size = 8 ∧ region.align = 8))
  | [], _, _, _, _, _, _, _, _, member => by simp [outputRegions] at member
  | param :: params, values, inputs, slot, region, kinds, outputs, room, count, member => by
    simp only [List.all_cons, Bool.and_eq_true] at kinds
    cases param with
    | reported | record => simp [Param.inputKind, Param.flatKind] at kinds
    | input =>
      cases inputs with
      | nil => simp at count
      | cons input inputs =>
        simp only [List.map_cons, flatArgsWith, flatPointersWith, outputRegions,
          List.tail_cons] at member
        have tail := flat_region_mem_inputs params values inputs slot region kinds.2
          (by simpa [List.count_cons] using outputs)
          (by simpa [Param.isResult, List.countP_cons] using room)
          (by simpa [List.count_cons] using count) member
        simpa [List.map_cons, flatCapacityWith, Param.isResult, List.countP_cons] using tail
    | word32 | word64 | enum32 | flags32 | flags64 =>
      simp only [flatArgsWith, flatPointersWith, outputRegions, List.tail_cons] at member
      have tail := flat_region_mem_inputs params values.tail inputs slot region kinds.2
        (by simpa [List.count_cons] using outputs)
        (by simpa [Param.isResult, List.countP_cons] using room)
        (by simpa [List.count_cons] using count) member
      simp only [flatCapacityWith, Param.takesArg, ite_true, Param.isResult, List.countP_cons,
        Bool.false_eq_true, ite_false, Nat.add_zero]
      exact tail
    | output =>
      simp only [flatArgsWith, flatPointersWith, outputRegions, List.tail_cons,
        List.mem_cons] at member
      have none' : params.count .output = 0 := by simp [List.count_cons] at outputs; omega
      rcases member with rfl | member
      · left
        exact ⟨rfl, rfl, values.headD 0, by simp [flatCapacityWith], by simp [Arg.capacity]⟩
      · rcases flat_region_mem_inputs params values.tail inputs slot region kinds.2 (by omega)
          (by simpa [Param.isResult, List.countP_cons] using room)
          (by simpa [List.count_cons] using count) member with
          ⟨_, _, capacity, found, _⟩ | result
        · simp [flatCapacityWith_none params values.tail _ none'] at found
        · right
          simpa [Param.isResult, List.countP_cons] using result
    | result32 | result64 =>
      simp only [flatArgsWith, flatPointersWith, outputRegions, List.mem_cons] at member
      have hSlot : slot + 8 ≤ 16 := by simp [Param.isResult, List.countP_cons] at room; omega
      rcases member with rfl | member
      · right
        exact ⟨0, by simp [Param.isResult, List.countP_cons],
          by simp [slot_toNat (slot := slot) (by omega)], by simp⟩
      · rcases flat_region_mem_inputs params values inputs (slot + 8) region kinds.2
          (by simpa [List.count_cons] using outputs)
          (by simp [Param.isResult, List.countP_cons] at room; omega)
          (by simpa [List.count_cons] using count) member with
          output | ⟨k, hk, pointer, size⟩
        · left
          simpa [flatCapacityWith, Param.takesArg] using output
        · right
          exact ⟨k + 1, by simp [Param.isResult, List.countP_cons]; omega, by omega, size⟩

/-- The regions of a flat request with inputs lie apart from one another. -/
theorem flat_regions_apart_inputs {root : UInt32} {sizes : List Nat} :
    ∀ (params : List Param) (values : List UInt64) (inputs : List (UInt64 × LeanExe.Bytes))
      (slot : Nat),
    params.all Param.inputKind = true → params.count .output ≤ 1 →
    slot + 8 * params.countP Param.isResult ≤ 16 → inputs.length = params.count .input →
    (∀ capacity, flatCapacityWith params values (inputs.map Prod.snd) = some capacity →
      16 ≤ root.toNat ∨ (capacity.toNat = 0 ∧ root = 0)) →
    ((outputRegions params sizes (flatArgsWith params values (inputs.map Prod.snd))
      (flatPointersWith params root slot (inputs.map fun input => input.1.toUInt32))).map
        Region.span).Pairwise regionsDisjoint
  | [], _, _, _, _, _, _, _, _ => by simp [outputRegions]
  | param :: params, values, inputs, slot, kinds, outputs, room, count, separate => by
    have kinds' := kinds
    simp only [List.all_cons, Bool.and_eq_true] at kinds'
    rw [List.pairwise_map]
    cases param with
    | reported | record => simp [Param.inputKind, Param.flatKind] at kinds'
    | input =>
      cases inputs with
      | nil => simp at count
      | cons input inputs =>
        simp only [List.map_cons, flatArgsWith, flatPointersWith, outputRegions, List.tail_cons]
        rw [← List.pairwise_map]
        exact flat_regions_apart_inputs params values inputs slot kinds'.2
          (by simpa [List.count_cons] using outputs)
          (by simpa [Param.isResult, List.countP_cons] using room)
          (by simpa [List.count_cons] using count)
          (by simpa [List.map_cons, flatCapacityWith] using separate)
    | word32 | word64 | enum32 | flags32 | flags64 =>
      simp only [flatArgsWith, flatPointersWith, outputRegions, List.tail_cons]
      rw [← List.pairwise_map]
      exact flat_regions_apart_inputs params values.tail inputs slot kinds'.2
        (by simpa [List.count_cons] using outputs)
        (by simpa [Param.isResult, List.countP_cons] using room)
        (by simpa [List.count_cons] using count)
        (by simpa [flatCapacityWith, Param.takesArg] using separate)
    | output =>
      simp only [flatArgsWith, flatPointersWith, outputRegions, List.tail_cons, List.pairwise_cons]
      have none' : params.count .output = 0 := by simp [List.count_cons] at outputs; omega
      have hCapacity := separate (values.headD 0) (by simp [flatCapacityWith])
      have room' : slot + 8 * params.countP Param.isResult ≤ 16 := by
        simpa [Param.isResult, List.countP_cons] using room
      have count' : inputs.length = params.count .input := by
        simpa [List.count_cons] using count
      refine ⟨?_, ?_⟩
      · intro region member
        rcases flat_region_mem_inputs params values.tail inputs slot region kinds'.2 (by omega)
            room' count' member with
          ⟨_, _, capacity, found, _⟩ | ⟨k, hk, pointer, size⟩
        · simp [flatCapacityWith_none params values.tail _ none'] at found
        · have hk' : slot + 8 * k + 8 ≤ 16 := by
            have := Nat.mul_le_mul_left 8 (Nat.succ_le_of_lt hk)
            omega
          show regionsDisjoint (root.toNat, (values.headD 0).toNat)
            (region.pointer.toNat, region.size)
          simp only [regionsDisjoint]
          rcases hCapacity with high | ⟨zero, rfl⟩ <;> rcases size with ⟨s4, _⟩ | ⟨s8, _⟩
          all_goals first | omega | (simp only [UInt32.toNat_zero]; omega)
      · rw [← List.pairwise_map]
        exact flat_regions_apart_inputs params values.tail inputs slot kinds'.2 (by omega) room'
          count' (by simp [flatCapacityWith_none params values.tail _ none'])
    | result32 | result64 =>
      simp only [flatArgsWith, flatPointersWith, outputRegions, List.pairwise_cons]
      have hSlot : slot + 8 ≤ 16 := by simp [Param.isResult, List.countP_cons] at room; omega
      have room' : slot + 8 + 8 * params.countP Param.isResult ≤ 16 := by
        simp [Param.isResult, List.countP_cons] at room; omega
      have outputs' : params.count .output ≤ 1 := by simpa [List.count_cons] using outputs
      have count' : inputs.length = params.count .input := by
        simpa [List.count_cons] using count
      refine ⟨?_, ?_⟩
      · intro region member
        rcases flat_region_mem_inputs params values inputs (slot + 8) region kinds'.2 outputs'
            room' count' member with
          ⟨pointer, _, capacity, found, size⟩ | ⟨k, hk, pointer, size⟩
        · have hCapacity := separate capacity
            (by simpa [flatCapacityWith, Param.takesArg] using found)
          simp only [Region.span, List.headD_cons, regionsDisjoint, pointer, size,
            slot_toNat (slot := slot) (by omega)]
          rcases hCapacity with high | ⟨zero, rfl⟩
          · omega
          · simp only [UInt32.toNat_zero]; omega
        · simp only [Region.span, List.headD_cons, regionsDisjoint,
            slot_toNat (slot := slot) (by omega), pointer]
          rcases size with ⟨s4, _⟩ | ⟨s8, _⟩ <;> omega
      · rw [← List.pairwise_map]
        exact flat_regions_apart_inputs params values inputs (slot + 8) kinds'.2 outputs' room'
          count' (by simpa [flatCapacityWith, Param.takesArg] using separate)

/-- The regions of a flat request with inputs, with the buffer at `root` and the result words
from scratch address 0. -/
abbrev flatRegionsWith (call : LeanExe.Wasi.Call) (sizes : List Nat) (values : List UInt64)
    (inputs : List (UInt64 × LeanExe.Bytes)) (root : UInt64) : List Region :=
  outputRegions call.params sizes (flatArgsWith call.params values (inputs.map Prod.snd))
    (flatPointersWith call.params root.toUInt32 0 (inputs.map fun input => input.1.toUInt32))

/-- The host call of a flat request with inputs whose pointers are the inputs' roots, the buffer's
root, and the scratch addresses 0 and 8: the argument code pushes the core arguments, the request
satisfies the call's premise, and the contract gives the errno, the frame of the request's
regions, and the shown outputs. -/
theorem wp_sys_flat_call_inputs_with {calls : List LeanExe.Wasi.Call} {World : Type}
    {m : Module} {host : Host World} {env : HostEnv (Observed World)}
    {store : Store (Observed World)} {s : Locals} {call : LeanExe.Wasi.Call} {locs : List Nat}
    {values : List UInt64} {inputLocs : List Nat} {inputs : List (UInt64 × LeanExe.Bytes)}
    {rootLocal : Nat} {root : UInt64} {rest : Program} {Q : Assertion (Observed World)}
    (hImports : m.imports = ABI.importsWith calls)
    (hHost : env.Satisfies m (hostSpecWith host calls))
    (hCall : calls[calls.idxOf call]? = some call)
    (hKinds : call.params.all Param.inputKind = true) (hOutputs : call.params.count .output ≤ 1)
    (hResults : call.params.countP Param.isResult ≤ 2)
    (hAccepted : call.reject (flatArgsWith call.params values (inputs.map Prod.snd)) = 0)
    (hHeld : List.Forall₂ (fun place value => s.get place = some (.i64 value)) locs values)
    (hCount : values.length = call.wordCount)
    (hInputs : List.Forall₂ (InputHeld s) inputLocs inputs)
    (hInputCount : inputs.length = call.inputCount)
    (hRoot : s.get rootLocal = some (.i64 root)) (hRootSmall : root.toNat < 4294967296)
    (hMemory : 16 ≤ store.mem.pages * 65536)
    (hBuffer : ∀ capacity, flatCapacityWith call.params values (inputs.map Prod.snd) =
        some capacity →
      root.toNat + capacity.toNat ≤ store.mem.pages * 65536 ∧
        root.toNat + capacity.toNat < 2 ^ 32 ∧
        (16 ≤ root.toNat ∨ (capacity.toNat = 0 ∧ root = 0)))
    (hInputAt : ∀ input ∈ inputs,
      Bytes.At store.mem input.1 input.2 ∧ input.1.toNat < 4294967296)
    (hInputApart : ∀ input ∈ inputs,
      regionsDisjoint (input.1.toNat, input.2.data.size) ABI.scratch ∧
        ∀ capacity, flatCapacityWith call.params values (inputs.map Prod.snd) = some capacity →
          regionsDisjoint (input.1.toNat, input.2.data.size) (root.toNat, capacity.toNat))
    (hNext : ∀ (final : Store (Observed World)) (errno : UInt64) (outputs : List LeanExe.Bytes),
      (observedHost host).sys store.host call
        (flatArgsWith call.params values (inputs.map Prod.snd)) (.returned errno outputs)
        final.host →
      GuestFrame store final
        ((flatRegionsWith call (host.reported store.host.world call) values inputs root).map
          Region.span) →
      (errno = 0 → ShownAt final.mem
        (flatRegionsWith call (host.reported store.host.world call) values inputs root)
        outputs) →
      wp m rest Q final { s with values := .i32 errno.toUInt32 :: s.values } env)
    (hTrap : ∀ (final : Store (Observed World)) (message : String) (outputs : List LeanExe.Bytes),
      (observedHost host).sys store.host call
        (flatArgsWith call.params values (inputs.map Prod.snd)) (.trapped message outputs)
        final.host →
      GuestFrame store final
        ((flatRegionsWith call (host.reported store.host.world call) values inputs root).map
          Region.span) →
      Q (.Trap final message)) :
    wp m (sysLowerInputsCode call.params locs inputLocs rootLocal 0 ++
      .call (3 + calls.idxOf call) :: rest) Q store s env := by
  have hRoot32 : root.toUInt32.toNat = root.toNat := by
    rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt hRootSmall]
  have hRoom : 0 + 8 * call.params.countP Param.isResult ≤ 16 := by omega
  have hInputCount' : inputs.length = call.params.count .input := hInputCount
  have hSeparate : ∀ capacity, flatCapacityWith call.params values (inputs.map Prod.snd) =
      some capacity → 16 ≤ root.toUInt32.toNat ∨ (capacity.toNat = 0 ∧ root.toUInt32 = 0) := by
    intro capacity found
    rcases (hBuffer capacity found).2.2 with high | ⟨zero, rfl⟩
    · exact Or.inl (by rw [hRoot32]; exact high)
    · exact Or.inr ⟨zero, rfl⟩
  have hIndex : calls.idxOf call < calls.length := (List.getElem?_eq_some_iff.mp hCall).1
  have hPlaces := inputPlaces_inputs (root := root.toUInt32) call.params values inputs 0 hKinds
    hInputCount'
  have hRequest : SysRequest store
      (lowerArgs call.params (flatArgsWith call.params values (inputs.map Prod.snd))
        (flatPointersWith call.params root.toUInt32 0
          (inputs.map fun input => input.1.toUInt32)))
      call (flatArgsWith call.params values (inputs.map Prod.snd))
      (flatPointersWith call.params root.toUInt32 0 (inputs.map fun input => input.1.toUInt32))
      (host.reported store.host.world call) := by
    refine ⟨flatArgsWith_fit call.params values _ hKinds (by simpa using hInputCount')
      hAccepted, hAccepted, rfl, ?_, ?_,
      flat_regions_apart_inputs call.params values inputs 0 hKinds hOutputs hRoom hInputCount'
        hSeparate, ?_⟩
    · rw [hPlaces]
      intro place member
      obtain ⟨input, inputMember, rfl⟩ := List.mem_map.mp member
      obtain ⟨at_, small⟩ := hInputAt input inputMember
      have narrow : input.1.toUInt32.toUInt64 = input.1 := by
        apply UInt64.toNat_inj.mp
        simp only [UInt32.toNat_toUInt64, UInt64.toNat_toUInt32]
        omega
      simpa only [narrow] using at_
    · intro region member
      rcases flat_region_mem_inputs call.params values inputs 0 region hKinds hOutputs hRoom
          hInputCount' member with
        ⟨pointer, align, capacity, found, size⟩ | ⟨k, hk, pointer, size⟩
      · have bound := hBuffer capacity found
        rw [pointer, size, align, hRoot32]
        exact ⟨bound.1, by omega, Nat.mod_one _⟩
      · have hk' : 8 * k + 8 ≤ 16 := by
          have := Nat.mul_le_mul_left 8 (Nat.succ_le_of_lt hk)
          omega
        rw [pointer]
        rcases size with ⟨size, align⟩ | ⟨size, align⟩ <;> rw [size, align] <;>
          refine ⟨by omega, by omega, by omega⟩
    · intro region member place placeMember
      rw [hPlaces] at placeMember
      obtain ⟨input, inputMember, rfl⟩ := List.mem_map.mp placeMember
      obtain ⟨scratchApart, bufferApart⟩ := hInputApart input inputMember
      have small := (hInputAt input inputMember).2
      have hInput32 : input.1.toUInt32.toNat = input.1.toNat := by
        rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt small]
      rcases flat_region_mem_inputs call.params values inputs 0 region hKinds hOutputs hRoom
          hInputCount' member with
        ⟨pointer, _, capacity, found, size⟩ | ⟨k, hk, pointer, size⟩
      · have apart := bufferApart capacity found
        simp only [Region.span, pointer, size, hRoot32, hInput32, regionsDisjoint] at apart ⊢
        omega
      · have hk' : 8 * k + 8 ≤ 16 := by
          have := Nat.mul_le_mul_left 8 (Nat.succ_le_of_lt hk)
          omega
        simp only [Region.span, pointer, hInput32, regionsDisjoint, ABI.scratch] at scratchApart ⊢
        rcases size with ⟨size, _⟩ | ⟨size, _⟩ <;> rw [size] <;> omega
  have hLength := lowerArgs_length call.params
    (flatArgsWith call.params values (inputs.map Prod.snd))
    (flatPointersWith call.params root.toUInt32 0 (inputs.map fun input => input.1.toUInt32))
  have hTake : ((lowerArgs call.params (flatArgsWith call.params values (inputs.map Prod.snd))
      (flatPointersWith call.params root.toUInt32 0
        (inputs.map fun input => input.1.toUInt32))).reverse ++ s.values).take
      (ABI.callImport call).params.length =
      (lowerArgs call.params (flatArgsWith call.params values (inputs.map Prod.snd))
        (flatPointersWith call.params root.toUInt32 0
          (inputs.map fun input => input.1.toUInt32))).reverse := by
    apply List.take_left'
    rw [List.length_reverse, hLength]
    rfl
  have hDrop : ((lowerArgs call.params (flatArgsWith call.params values (inputs.map Prod.snd))
      (flatPointersWith call.params root.toUInt32 0
        (inputs.map fun input => input.1.toUInt32))).reverse ++ s.values).drop
      (ABI.callImport call).params.length = s.values := by
    apply List.drop_left'
    rw [List.length_reverse, hLength]
    rfl
  refine wp_sys_lower_inputs call.params locs values inputLocs inputs 0 s _ Q hKinds hHeld hCount
    hInputs hInputCount' hRoot ?_
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

/-! ## Calls without inputs -/

/-- A flat request that its parameters accept fits them. -/
theorem flatArgs_fit : ∀ (params : List Param) (values : List UInt64),
    params.all Param.flatKind = true → rejectArgs params (flatArgs params values) = 0 →
    argsFit params (flatArgs params values) = true := by
  intro params values kinds accepted
  have fits := flatArgsWith_fit params values [] (inputKind_of_flat kinds)
    (count_input_of_flat kinds).symm (by rwa [flatArgsWith_nil])
  rwa [flatArgsWith_nil] at fits

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
        ((region.size = 4 ∧ region.align = 4) ∨ (region.size = 8 ∧ region.align = 8)) := by
  intro params values slot region kinds outputs room member
  have found := flat_region_mem_inputs (root := root) (sizes := sizes) params values [] slot
    region (inputKind_of_flat kinds) outputs room (by rw [count_input_of_flat kinds]; rfl)
    (by simpa only [List.map_nil, flatArgsWith_nil, flatPointersWith_nil] using member)
  simpa only [List.map_nil, flatCapacityWith_nil] using found

/-- The regions of a flat request lie apart from one another: the buffer lies above the scratch
area or is empty at 0, and the result words take distinct scratch addresses. -/
theorem flat_regions_apart {root : UInt32} {sizes : List Nat} :
    ∀ (params : List Param) (values : List UInt64) (slot : Nat),
    params.all Param.flatKind = true → params.count .output ≤ 1 →
    slot + 8 * params.countP Param.isResult ≤ 16 →
    (∀ capacity, flatCapacity params values = some capacity →
      16 ≤ root.toNat ∨ (capacity.toNat = 0 ∧ root = 0)) →
    ((outputRegions params sizes (flatArgs params values)
      (flatPointers params root slot)).map Region.span).Pairwise regionsDisjoint := by
  intro params values slot kinds outputs room separate
  have apart := flat_regions_apart_inputs (root := root) (sizes := sizes) params values [] slot
    (inputKind_of_flat kinds) outputs room (by rw [count_input_of_flat kinds]; rfl)
    (by simpa only [List.map_nil, flatCapacityWith_nil] using separate)
  simpa only [List.map_nil, flatArgsWith_nil, flatPointersWith_nil] using apart

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
        root.toNat + capacity.toNat < 2 ^ 32 ∧
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
    refine ⟨flatArgs_fit call.params values hKinds hAccepted, hAccepted, rfl, ?_, ?_,
      flat_regions_apart call.params values 0 hKinds hOutputs hRoom hSeparate, ?_⟩
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
    · rw [inputPlaces_flat _ _ _ hKinds]
      intro _ _ place member
      cases member
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
