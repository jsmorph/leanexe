import Verified.Shim.SysEnv

/-!
The shim's `clock_time_get` and `random_get`.  `clockInvoke` answers clocks 0 and 1 with one
`clock_gettime` into the scratch's timespec, whose event `step_clock` gives for every memory that
holds the cleared timespec, and stores the time at the result's pointer on success; clocks 2 and 3
give errno 8 without a call.  `randomInvoke` fills the buffer with the `getrandom` calls of
`randomLoop`, each asking for the bytes that remain, whose events and memories `step_random`
gives.  `clock_contract` and `random_contract` prove the calls' specifications for the host
`linuxHost F L I replies`.
-/

namespace Verified.Shim

open Wasm LeanExe LeanExe.Wasi Verified.Wasi

variable (F : OpenFlags) (L : ShimLayout) (I : Launch) (replies : Linux.Replies)

/-- `clock_time_get` of the clock `id` with the time's pointer `pointer`. -/
def clockInvoke (before : Store (Observed LinuxWorld)) (args : List Value) :
    HostResult (Observed LinuxWorld) :=
  match args with
  | [.i32 id, .i64 precision, .i32 pointer] =>
    if id.toNat < 4 ∧ pointer.toNat + 8 ≤ before.mem.pages * 65536 ∧
        pointer.toNat + 8 < 2 ^ 32 then
      if id.toNat < 2 then
        let e := clockEvent L id.toUInt64 (replies before.host.world.events.length)
        let reply := clockReply e.ret e.output
        sysAnswer before Call.clockTimeGet [.word id.toUInt64, .word precision]
          (placeReply before.mem (fun outputs => [(pointer, outputs.headD Bytes.empty)]) reply)
          [e] reply
      else
        sysAnswer before Call.clockTimeGet [.word id.toUInt64, .word precision] before.mem []
          (.returned 8 [zeros 8])
    else .Trap before shimTrap
  | _ => .Trap before shimTrap

theorem clock_shape {request : List Arg} (h : argsFit Call.clockTimeGet.params request = true) :
    ∃ id precision, request = [.word id, .word precision] ∧ id.toNat < 2 ^ 32 := by
  obtain ⟨a, request, rfl, ha, h⟩ := argsFit_takes h rfl
  obtain ⟨b, request, rfl, hb, h⟩ := argsFit_takes h rfl
  have empty : request = [] := by simpa [argsFit, Param.takesArg] using h
  subst empty
  cases a <;> cases b <;> simp_all [argFits]

theorem clock_contract (before : Store (Observed LinuxWorld)) (args : List Value) :
    sysContract (linuxHost F L I replies) Call.clockTimeGet before args
      (clockInvoke L replies before args) := by
  apply sys_contract_of
  intro request pointers valid
  obtain ⟨id, precision, rfl, small⟩ := clock_shape valid.fits
  have accepted : id.toNat < 4 := by
    by_contra big
    have h := valid.accepted
    simp [Call.reject, rejectArgs, Param.reject, Call.clockTimeGet, Param.takesArg, Arg.value,
      big] at h
  have regions : outputRegions Call.clockTimeGet.params
      (shimReported I before.host.world.reports Call.clockTimeGet)
      [.word id, .word precision] pointers = [⟨pointers.headD 0, 8, 8, true⟩] := rfl
  have bounds := valid.bounds ⟨pointers.headD 0, 8, 8, true⟩
    (by rw [regions]; exact List.mem_singleton_self _)
  have arguments : args = [.i32 id.toUInt32, .i64 precision, .i32 (pointers.headD 0)] :=
    valid.arguments
  subst arguments
  have narrow : id.toUInt32.toNat = id.toNat := by
    rw [UInt64.toNat_toUInt32]
    omega
  have check : id.toNat < 4 ∧ (pointers.headD 0).toNat + 8 ≤ before.mem.pages * 65536 ∧
      (pointers.headD 0).toNat + 8 < 2 ^ 32 := ⟨accepted, bounds.1, bounds.2.1⟩
  dsimp only
  rw [regions]
  by_cases low : id.toNat < 2
  · have image : SysImage F L I before.host.world.events Call.clockTimeGet
        [.word id, .word precision]
        (clockReply (clockEvent L id (replies before.host.world.events.length)).ret
          (clockEvent L id (replies before.host.world.events.length)).output)
        [clockEvent L id (replies before.host.world.events.length)] := by
      rw [sysImage_clock]
      simp only [ClockImage, low, ↓reduceIte]
      exact ⟨_, _, rfl, rfl⟩
    have answer := placed_one (pointer := pointers.headD 0) (size := 8) (align := 8)
      (clockReply_shape (clockEvent L id (replies before.host.world.events.length)).ret
        (clockEvent L id (replies before.host.world.events.length)).output) bounds.1 bounds.2.1
    refine ⟨_, _, _, ?_, shimStep_one ⟨valid.accepted, image⟩ ⟨rfl, rfl⟩ ?_, answer.1, answer.2⟩
    · simp only [clockInvoke, narrow, check, and_self, ↓reduceIte, low,
        OracleSys.word_roundtrip small]
    · intro g member
      simp only [clockEvent, outputs_clock, List.mem_singleton] at member
      exact Or.inr (Or.inl member)
  · refine ⟨before.mem, [], .returned 8 [zeros 8], ?_, shimStep_none ⟨valid.accepted, ?_⟩,
      MemFrame.refl _ _, fun _ same => absurd (Transfer.returned.inj same).1 (by decide)⟩
    · simp only [clockInvoke, narrow, check, and_self, ↓reduceIte, low,
        OracleSys.word_roundtrip small]
    · rw [sysImage_clock]
      simp [ClockImage, low]

/-! ## Random bytes -/

/-- The `getrandom` calls of `random_get`'s loop, which fills the `length` bytes from the guest's
byte `pointer` and has filled the `done` bytes `filled`, from the memory `mem` with the replies
from call `k` on: the memory after, the events, and the reply.  Each call asks for the bytes that
remain, and a count between 1 and those bytes, exclusive, goes on with the next call. -/
def randomLoop (pointer length : Nat) (done : Nat) (filled : List UInt8) (mem : Mem) (k : Nat) :
    Mem × List Linux.Event × Transfer (List Bytes) :=
  if _more : done < length then
    let e := randomEvent L mem (UInt64.ofNat (pointer + done)) (length - done) (replies k)
    let written := mem.writeBytes (pointer + done)
      ((List.range (length - done)).map (replies k).bytes)
    if going : 0 < (replies k).ret.toNat ∧ (replies k).ret.toNat < length - done then
      let rest := randomLoop pointer length (done + (replies k).ret.toNat)
        (filled ++ e.output.take (replies k).ret.toNat) written (k + 1)
      (rest.1, e :: rest.2.1, rest.2.2)
    else (written, [e], randomLast length (length - done) filled (replies k).ret e.output)
  else (mem, [], .returned 0 [bytesOfList filled])
termination_by length - done
decreasing_by omega

/-- `random_get` into the buffer of `length` bytes at `pointer`. -/
def randomInvoke (before : Store (Observed LinuxWorld)) (args : List Value) :
    HostResult (Observed LinuxWorld) :=
  match args with
  | [.i32 pointer, .i32 length] =>
    if pointer.toNat + length.toNat ≤ before.mem.pages * 65536 ∧
        pointer.toNat + length.toNat < 2 ^ 32 then
      let loop := randomLoop L replies pointer.toNat length.toNat 0 [] before.mem
        before.host.world.events.length
      sysAnswer before Call.randomGet [.space length.toUInt64] loop.1 loop.2.1 loop.2.2
    else .Trap before shimTrap
  | _ => .Trap before shimTrap

theorem random_shape {request : List Arg} (h : argsFit Call.randomGet.params request = true) :
    ∃ length, request = [.space length] ∧ length.toNat < 2 ^ 32 := by
  obtain ⟨a, request, rfl, ha, h⟩ := argsFit_takes h rfl
  have empty : request = [] := by simpa [argsFit, Param.takesArg] using h
  subst empty
  cases a <;> simp_all [argFits]

/-- The bytes `filled` at `pointer` followed by the first `n` bytes of `bytes` written after them. -/
theorem at_append {mem : Mem} {pointer : Nat} {filled bytes : List UInt8} (n : Nat)
    (held : Bytes.At mem (UInt64.ofNat pointer) (bytesOfList filled)) (taken : n ≤ bytes.length)
    (small : pointer < 2 ^ 32) (address : pointer + filled.length + bytes.length ≤ 2 ^ 32)
    (memory : pointer + filled.length + bytes.length ≤ mem.pages * 65536) :
    Bytes.At (mem.writeBytes (pointer + filled.length) bytes) (UInt64.ofNat pointer)
      (bytesOfList (filled ++ bytes.take n)) := by
  have root : (UInt64.ofNat pointer).toNat = pointer :=
    UInt64.toNat_ofNat_of_lt' (show pointer < 2 ^ 64 by omega)
  refine ⟨?_, ?_, ?_⟩
  · simp only [root, bytesOfList_size, List.length_append, List.length_take]
    omega
  · simp only [root, bytesOfList_size, List.length_append, List.length_take, Mem.writeBytes]
    omega
  · intro i bound
    simp only [bytesOfList_size, List.length_append, List.length_take] at bound
    simp only [root, Mem.writeBytes, bytesOfList, ByteArray.getElem_eq_getElem_data,
      List.getElem_toArray]
    by_cases before : i < filled.length
    · rw [dite_eq_right (by omega), List.getElem_append_left before]
      have := held.contents i (by simpa using before)
      rw [root] at this
      simpa [bytesOfList, ByteArray.getElem_eq_getElem_data] using this
    · rw [dite_eq_left (by omega), List.getElem_append_right (by omega), List.getElem_take]
      congr 1
      omega

theorem randomEvent_writesWithin (mem : Mem) {pointer n size : Nat} (r : Linux.Reply)
    (small : pointer + n < 2 ^ 64) (address : pointer + n ≤ size) :
    WritesWithin L size (randomEvent L mem (UInt64.ofNat pointer) n r) := by
  intro g member
  simp only [randomEvent, outputs_getrandom, List.mem_singleton] at member
  subst member
  left
  rw [offset_base, UInt64.toNat_ofNat_of_lt' (show pointer < 2 ^ 64 by omega),
    UInt64.toNat_ofNat_of_lt' (show n < 2 ^ 64 by omega)]
  exact address

/-- The loop's events are those of `RandomCalls` and hold their replies, and its memory changes
only the buffer and holds the reply's bytes on success. -/
theorem randomLoop_spec (pointer length : Nat) (small : pointer + length < 2 ^ 32) :
    ∀ (remaining done : Nat) (filled : List UInt8) (mem : Mem) (k : Nat),
      length - done = remaining → done ≤ length → filled.length = done →
      pointer + length ≤ mem.pages * 65536 →
      Bytes.At mem (UInt64.ofNat pointer) (bytesOfList filled) →
      let loop := randomLoop L replies pointer length done filled mem k
      RandomCalls (L.base + UInt64.ofNat pointer) length done filled loop.2.1 loop.2.2 ∧
        Carried replies k loop.2.1 ∧ (∀ x ∈ loop.2.1, WritesWithin L (2 ^ 32) x) ∧
        MemFrame mem loop.1 [(pointer, length)] ∧
        ∀ outputs, loop.2.2 = .returned 0 outputs →
          ∃ bytes, outputs = [bytes] ∧ Bytes.At loop.1 (UInt64.ofNat pointer) bytes := by
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | _ remaining ih =>
  intro done filled mem k left within sized memory held
  have address : (UInt64.ofNat (pointer + done)).toNat = pointer + done :=
    UInt64.toNat_ofNat_of_lt' (show pointer + done < 2 ^ 64 by omega)
  have shift : L.base + UInt64.ofNat (pointer + done) =
      L.base + UInt64.ofNat pointer + UInt64.ofNat done := by
    rw [UInt64.add_assoc, UInt64.ofNat_add]
  have count : (UInt64.ofNat (length - done)).toNat = length - done :=
    UInt64.toNat_ofNat_of_lt' (show length - done < 2 ^ 64 by omega)
  dsimp only
  rw [randomLoop]
  by_cases more : done < length
  · simp only [more, ↓reduceDIte]
    have frameWrite : MemFrame mem (mem.writeBytes (pointer + done)
        ((List.range (length - done)).map (replies k).bytes)) [(pointer, length)] :=
      MemFrame.writeBytes _ _ _ ⟨_, List.mem_singleton_self _, by omega, by simp; omega⟩
    have carries : Carries (replies k) (randomEvent L mem (UInt64.ofNat (pointer + done))
        (length - done) (replies k)) := by
      refine ⟨rfl, ?_⟩
      simp only [randomEvent, outputs_getrandom, UInt64.toNat_ofNat_of_lt'
        (show length - done < 2 ^ 64 by omega)]
    have within := randomEvent_writesWithin L mem (replies k) (by omega)
      (show pointer + done + (length - done) ≤ 2 ^ 32 by omega)
    have event : randomEvent L mem (UInt64.ofNat (pointer + done)) (length - done) (replies k) =
        ⟨Linux.getrandomCall, [L.base + UInt64.ofNat pointer + UInt64.ofNat done,
          UInt64.ofNat (length - done), 0], [], mem.readBytes (pointer + done) (length - done),
          (replies k).ret, (List.range (length - done)).map (replies k).bytes⟩ := by
      simp only [randomEvent, shift, address]
    split
    · rename_i going
      have next := ih (length - (done + (replies k).ret.toNat)) (by omega)
        (done + (replies k).ret.toNat)
        (filled ++ ((randomEvent L mem (UInt64.ofNat (pointer + done)) (length - done)
          (replies k)).output.take (replies k).ret.toNat))
        (mem.writeBytes (pointer + done) ((List.range (length - done)).map (replies k).bytes))
        (k + 1) rfl (by omega) (by simp [randomEvent, sized]; omega)
        (by simp only [Mem.writeBytes]; exact memory)
        (by
          rw [← sized]
          simp only [randomEvent]
          exact at_append _ held (by simp; omega) (by omega) (by simp; omega)
            (by simp only [List.length_map, List.length_range]; omega))
      obtain ⟨calls, carried, writes, frame, shown⟩ := next
      refine ⟨⟨more, _, _, _, event, ?_⟩, ⟨carries, carried⟩, ?_, frameWrite.trans frame, shown⟩
      · simp only [going]
        simpa [randomEvent] using calls
      · intro x member
        rcases List.mem_cons.mp member with rfl | member
        · exact within
        · exact writes x member
    · rename_i stopping
      refine ⟨⟨more, _, _, _, event, ?_⟩, ⟨carries, ?_⟩, ?_, frameWrite, ?_⟩
      · simp only [stopping, ↓reduceIte]
        simp [randomEvent]
      · trivial
      · intro x member
        obtain rfl := List.mem_singleton.mp member
        exact within
      · intro outputs same
        unfold randomLast at same
        by_cases all : (replies k).ret.toNat = length - done
        · simp only [all, ↓reduceIte] at same
          obtain ⟨_, rfl⟩ := Transfer.returned.inj same
          refine ⟨_, rfl, ?_⟩
          have whole := at_append (bytes := (List.range (length - done)).map (replies k).bytes)
            ((List.range (length - done)).map (replies k).bytes).length held (Nat.le_refl _)
            (by omega) (by simp; omega) (by simp; omega)
          rw [sized, List.take_length] at whole
          simpa [randomEvent] using whole
        · simp only [all, ↓reduceIte] at same
          split at same
          · exact absurd (Transfer.returned.inj same).1 (errnoOf_valid _).2
          · cases same
  · simp only [more, ↓reduceDIte]
    have finished : done = length := by omega
    refine ⟨⟨finished, rfl⟩, ?_, ?_, MemFrame.refl _ _, ?_⟩
    · trivial
    · intro x member
      cases member
    · intro outputs same
      obtain ⟨_, rfl⟩ := Transfer.returned.inj same
      exact ⟨_, rfl, held⟩

theorem random_contract (before : Store (Observed LinuxWorld)) (args : List Value) :
    sysContract (linuxHost F L I replies) Call.randomGet before args
      (randomInvoke L replies before args) := by
  apply sys_contract_of
  intro request pointers valid
  obtain ⟨length, rfl, small⟩ := random_shape valid.fits
  have regions : outputRegions Call.randomGet.params
      (shimReported I before.host.world.reports Call.randomGet)
      [.space length] pointers = [⟨pointers.headD 0, length.toNat, 1, true⟩] := rfl
  have bounds := valid.bounds ⟨pointers.headD 0, length.toNat, 1, true⟩
    (by rw [regions]; exact List.mem_singleton_self _)
  have arguments : args = [.i32 (pointers.headD 0), .i32 (UInt32.ofNat length.toNat)] :=
    valid.arguments
  subst arguments
  have narrow : (UInt32.ofNat length.toNat).toNat = length.toNat := UInt32.toNat_ofNat_of_lt' small
  have wide : (UInt32.ofNat length.toNat).toUInt64 = length := by
    apply UInt64.toNat_inj.mp
    rw [UInt32.toNat_toUInt64, narrow]
  have check : (pointers.headD 0).toNat + length.toNat ≤ before.mem.pages * 65536 ∧
      (pointers.headD 0).toNat + length.toNat < 2 ^ 32 := ⟨bounds.1, bounds.2.1⟩
  have pointerBound := (pointers.headD 0).toNat_lt
  obtain ⟨calls, carried, writes, frame, shown⟩ := randomLoop_spec L replies
    (pointers.headD 0).toNat length.toNat (by omega) _ 0 [] before.mem
    before.host.world.events.length rfl (by omega) rfl bounds.1 (at_nil (by omega) (by omega))
  have root : UInt64.ofNat (pointers.headD 0).toNat = (pointers.headD 0).toUInt64 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_ofNat_of_lt' (show (pointers.headD 0).toNat < 2 ^ 64 by omega),
      UInt32.toNat_toUInt64]
  dsimp only
  rw [regions]
  refine ⟨(randomLoop L replies (pointers.headD 0).toNat length.toNat 0 [] before.mem
      before.host.world.events.length).1,
    (randomLoop L replies (pointers.headD 0).toNat length.toNat 0 [] before.mem
      before.host.world.events.length).2.1,
    (randomLoop L replies (pointers.headD 0).toNat length.toNat 0 [] before.mem
      before.host.world.events.length).2.2,
    ?_, ⟨_, ⟨valid.accepted, ?_⟩, carried, writes, rfl⟩, frame, ?_⟩
  · simp only [randomInvoke, narrow, check, and_self, ↓reduceIte, wide]
  · rw [sysImage_random]
    exact ⟨_, calls⟩
  · intro outputs same
    obtain ⟨bytes, rfl, at_⟩ := shown outputs same
    rw [root] at at_
    exact shownAt_single at_

end Verified.Shim
