import Verified.Shim.SysEnv

/-!
The shim's file functions: `path_open`, `fd_close`, `fd_read` and `fd_write` on a handle,
`fd_filestat_get`, `fd_prestat_get`, and `fd_prestat_dir_name`.  `path_open`, `fd_close`,
`fd_filestat_get`, and the handle forms take the descriptor numbers that they accept,
`openNumbers I events`, from the world's layer events, and refuse every other number with errno 8
(`badf`) and no call.  `openInvoke` makes the checks of `openCheck` and then the `openat2` calls
of `openLoop` with the path and the `open_how` record in the scratch, whose events `step_openat2`
gives, and stores the descriptor on success.  `closeInvoke` makes one `close`.
`handleReadInvoke` and `handleWriteInvoke` read the iovec element at the request's pointer and
make one `read` or `write` of the handle's descriptor through the layer's rule, and store the
count on success.  `filestatInvoke` makes one `statx` of the descriptor with the empty path into
the scratch's `statx` record, whose event `step_statx` gives, and stores the `filestat` record of
`filestatReply` on success.  The prestat functions make no call:
descriptor 3 is the directory `.` while `preopened I events` holds.  Each `*_contract` proves its
call's specification for the host `linuxHost F L I replies`.
-/

namespace Verified.Shim

open Wasm LeanExe LeanExe.Wasi Verified.Wasi

variable (F : OpenFlags) (L : ShimLayout) (I : Launch) (replies : Linux.Replies)

/-! ## `path_open` -/

/-- The `openat2` calls of `path_open` under `dir` from its call `calls`, with the replies from
call `k` on: a call that fails with `EAGAIN` is made again while fewer than four calls were made.
-/
def openLoop (dir : UInt64) (path how : List UInt8) (calls k : Nat) :
    List Linux.Event × Transfer (List Bytes) :=
  if again : (replies k).ret = 0 - 11 ∧ calls < 3 then
    let rest := openLoop dir path how (calls + 1) (k + 1)
    (openEvent L dir path how (replies k) :: rest.1, rest.2)
  else ([openEvent L dir path how (replies k)], openReply (replies k).ret)
termination_by 3 - calls
decreasing_by omega

/-- `path_open` with the path's pointer and length and the descriptor's pointer `result`. -/
def openInvoke (before : Store (Observed LinuxWorld)) (args : List Value) :
    HostResult (Observed LinuxWorld) :=
  match args with
  | [.i32 dir, .i32 dirflags, .i32 pathPointer, .i32 pathLength, .i32 oflags, .i64 rights,
      .i64 inheriting, .i32 fdflags, .i32 result] =>
    if pathPointer.toNat + pathLength.toNat ≤ before.mem.pages * 65536 ∧
        pathPointer.toNat + pathLength.toNat ≤ 2 ^ 32 ∧
        result.toNat + 4 ≤ before.mem.pages * 65536 ∧ result.toNat + 4 < 2 ^ 32 then
      let path := bytesOfList (before.mem.readBytes pathPointer.toNat pathLength.toNat)
      let request := [Arg.word dir.toUInt64, .word dirflags.toUInt64, .bytes path,
        .word oflags.toUInt64, .word rights, .word inheriting, .word fdflags.toUInt64]
      if openCheck (openNumbers I before.host.world.events) dir.toUInt64 oflags.toUInt64 path
          fdflags.toUInt64 = 0 then
        let calls := openLoop L replies dir.toUInt64 path.data.data.toList
          (openHowBytes F dirflags.toUInt64 oflags.toUInt64 rights fdflags.toUInt64) 0
          before.host.world.events.length
        sysAnswer before Call.pathOpen request
          (placeReply before.mem (fun outputs => [(result, outputs.headD Bytes.empty)]) calls.2)
          calls.1 calls.2
      else
        sysAnswer before Call.pathOpen request before.mem []
          (.returned (openCheck (openNumbers I before.host.world.events) dir.toUInt64
            oflags.toUInt64 path fdflags.toUInt64) [zeros 4])
    else .Trap before shimTrap
  | _ => .Trap before shimTrap

theorem openEvent_writesWithin (dir : UInt64) (path how : List UInt8) (r : Linux.Reply)
    (size : Nat) : WritesWithin L size (openEvent L dir path how r) :=
  writesWithin_none rfl

theorem openLoop_spec (dir : UInt64) (path how : List UInt8) :
    ∀ (remaining calls k : Nat), 3 - calls = remaining →
      OpenCalls L dir path how calls (openLoop L replies dir path how calls k).1
          (openLoop L replies dir path how calls k).2 ∧
        Carried replies k (openLoop L replies dir path how calls k).1 ∧
        ∀ x ∈ (openLoop L replies dir path how calls k).1, WritesWithin L (2 ^ 32) x := by
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | _ remaining ih =>
  intro calls k left
  rw [openLoop]
  split
  · rename_i again
    obtain ⟨opens, carried, writes⟩ := ih (3 - (calls + 1)) (by omega) (calls + 1) (k + 1) rfl
    refine ⟨⟨(replies k).ret, rfl, ?_⟩, ⟨⟨rfl, rfl⟩, carried⟩, ?_⟩
    · simp only [again, and_self, ↓reduceIte]
      exact opens
    · intro x member
      rcases List.mem_cons.mp member with rfl | member
      · exact openEvent_writesWithin L _ _ _ _ _
      · exact writes x member
  · rename_i stop
    refine ⟨⟨(replies k).ret, rfl, ?_⟩, ⟨⟨rfl, rfl⟩, ?_⟩, ?_⟩
    · simp only [stop, ↓reduceIte, and_self]
    · trivial
    · intro x member
      obtain rfl := List.mem_singleton.mp member
      exact openEvent_writesWithin L _ _ _ _ _

theorem open_shape {request : List Arg} (h : argsFit Call.pathOpen.params request = true) :
    ∃ dir dirflags path oflags rights inheriting fdflags,
      request = [.word dir, .word dirflags, .bytes path, .word oflags, .word rights,
        .word inheriting, .word fdflags] ∧
      dir.toNat < 2 ^ 32 ∧ dirflags.toNat < 2 ^ 32 ∧ path.data.size < 2 ^ 32 ∧
      oflags.toNat < 2 ^ 32 ∧ fdflags.toNat < 2 ^ 32 := by
  obtain ⟨a0, r, rfl, h0, h⟩ := argsFit_takes h rfl
  obtain ⟨a1, r, rfl, h1, h⟩ := argsFit_takes h rfl
  obtain ⟨a2, r, rfl, h2, h⟩ := argsFit_takes h rfl
  obtain ⟨a3, r, rfl, h3, h⟩ := argsFit_takes h rfl
  obtain ⟨a4, r, rfl, h4, h⟩ := argsFit_takes h rfl
  obtain ⟨a5, r, rfl, h5, h⟩ := argsFit_takes h rfl
  obtain ⟨a6, r, rfl, h6, h⟩ := argsFit_takes h rfl
  have empty : r = [] := by simpa [argsFit, Param.takesArg] using h
  subst empty
  cases a0 <;> simp only [argFits, Bool.false_eq_true, decide_eq_true_eq] at h0
  cases a1 <;> simp only [argFits, Bool.false_eq_true, decide_eq_true_eq] at h1
  cases a2 <;> simp only [argFits, Bool.false_eq_true, decide_eq_true_eq] at h2
  cases a3 <;> simp only [argFits, Bool.false_eq_true, decide_eq_true_eq] at h3
  cases a4 <;> simp only [argFits, Bool.false_eq_true] at h4
  cases a5 <;> simp only [argFits, Bool.false_eq_true] at h5
  cases a6 <;> simp only [argFits, Bool.false_eq_true, decide_eq_true_eq] at h6
  exact ⟨_, _, _, _, _, _, _, rfl, h0, h1, h2, h3, h6⟩

theorem open_contract (before : Store (Observed LinuxWorld)) (args : List Value) :
    sysContract (linuxHost F L I replies) Call.pathOpen before args
      (openInvoke F L I replies before args) := by
  apply sys_contract_of
  intro request pointers valid
  obtain ⟨dir, dirflags, path, oflags, rights, inheriting, fdflags, rfl, sDir, sFlags, sPath,
    sOflags, sFdflags⟩ := open_shape valid.fits
  have regions : outputRegions Call.pathOpen.params
      (shimReported I before.host.world.reports Call.pathOpen)
      [.word dir, .word dirflags, .bytes path, .word oflags, .word rights, .word inheriting,
        .word fdflags] pointers = [⟨pointers.tail.headD 0, 4, 4, true⟩] := rfl
  have bounds := valid.bounds ⟨pointers.tail.headD 0, 4, 4, true⟩
    (by rw [regions]; exact List.mem_singleton_self _)
  have input := valid.inputs (pointers.headD 0, path) (by simp [inputPlaces, Call.pathOpen])
  have arguments : args = [.i32 dir.toUInt32, .i32 dirflags.toUInt32, .i32 (pointers.headD 0),
      .i32 (UInt32.ofNat path.data.size), .i32 oflags.toUInt32, .i64 rights, .i64 inheriting,
      .i32 fdflags.toUInt32, .i32 (pointers.tail.headD 0)] := valid.arguments
  subst arguments
  have length : (UInt32.ofNat path.data.size).toNat = path.data.size :=
    UInt32.toNat_ofNat_of_lt' sPath
  have read : bytesOfList (before.mem.readBytes (pointers.headD 0).toNat path.data.size) = path := by
    have := readBytes_value input
    rwa [UInt32.toNat_toUInt64] at this
  have check : (pointers.headD 0).toNat + path.data.size ≤ before.mem.pages * 65536 ∧
      (pointers.headD 0).toNat + path.data.size ≤ 2 ^ 32 ∧
      (pointers.tail.headD 0).toNat + 4 ≤ before.mem.pages * 65536 ∧
      (pointers.tail.headD 0).toNat + 4 < 2 ^ 32 := by
    have address := input.address
    have memory := input.memory
    simp only [UInt32.toNat_toUInt64] at address memory
    exact ⟨memory, address, bounds.1, bounds.2.1⟩
  dsimp only
  rw [regions]
  by_cases passed : openCheck (openNumbers I before.host.world.events) dir oflags path fdflags = 0
  · have spec := openLoop_spec L replies dir path.data.data.toList
      (openHowBytes F dirflags oflags rights fdflags) _ 0 before.host.world.events.length rfl
    obtain ⟨opens, carried, writes⟩ := spec
    have answer := placed_one (pointer := pointers.tail.headD 0) (size := 4) (align := 4)
      (openCalls_shape opens) bounds.1 bounds.2.1
    refine ⟨_, _, _, ?_, ⟨_, ⟨valid.accepted, ?_⟩, carried, writes, rfl⟩, answer.1, answer.2⟩
    · simp only [openInvoke, length, check, and_self, ↓reduceIte, read,
        OracleSys.word_roundtrip sDir, OracleSys.word_roundtrip sFlags,
        OracleSys.word_roundtrip sOflags, OracleSys.word_roundtrip sFdflags, passed]
    · rw [sysImage_open]
      simp only [OpenImage, passed, ↓reduceIte]
      exact opens
  · refine ⟨before.mem, [],
      .returned (openCheck (openNumbers I before.host.world.events) dir oflags path fdflags)
        [zeros 4], ?_,
      shimStep_none ⟨valid.accepted, ?_⟩, MemFrame.refl _ _, ?_⟩
    · simp only [openInvoke, length, check, and_self, ↓reduceIte, read,
        OracleSys.word_roundtrip sDir, OracleSys.word_roundtrip sFlags,
        OracleSys.word_roundtrip sOflags, OracleSys.word_roundtrip sFdflags, passed]
    · rw [sysImage_open]
      simp [OpenImage, passed]
    · intro outputs same
      exact absurd (Transfer.returned.inj same).1 passed

/-! ## `fd_close` -/

/-- `fd_close` of the descriptor `fd`. -/
def closeInvoke (before : Store (Observed LinuxWorld)) (args : List Value) :
    HostResult (Observed LinuxWorld) :=
  match args with
  | [.i32 fd] =>
    if fd.toUInt64 ∈ openNumbers I before.host.world.events then
      let e := closeEvent fd.toUInt64 (replies before.host.world.events.length)
      sysAnswer before Call.fdClose [.word fd.toUInt64] before.mem [e] (closeReply e.ret)
    else sysAnswer before Call.fdClose [.word fd.toUInt64] before.mem [] (.returned 8 [])
  | _ => .Trap before shimTrap

theorem close_contract (before : Store (Observed LinuxWorld)) (args : List Value) :
    sysContract (linuxHost F L I replies) Call.fdClose before args
      (closeInvoke I replies before args) := by
  apply sys_contract_of
  intro request pointers valid
  obtain ⟨a, r, rfl, h0, h⟩ := argsFit_takes valid.fits rfl
  have empty : r = [] := by simpa [argsFit] using h
  subst empty
  cases a <;> simp only [argFits, Bool.false_eq_true, decide_eq_true_eq] at h0
  rename_i fd
  have arguments : args = [.i32 fd.toUInt32] := valid.arguments
  subst arguments
  dsimp only
  have regions : outputRegions Call.fdClose.params
      (shimReported I before.host.world.reports Call.fdClose) [.word fd] pointers = [] := rfl
  rw [regions]
  by_cases refused : fd ∉ openNumbers I before.host.world.events
  · refine ⟨before.mem, [], .returned 8 [], ?_, shimStep_none ⟨valid.accepted, ?_⟩,
      MemFrame.refl _ _, fun _ same => absurd (Transfer.returned.inj same).1 (by decide)⟩
    · simp only [closeInvoke, OracleSys.word_roundtrip h0, refused, ↓reduceIte]
    · rw [sysImage_close]
      simp [CloseImage, refused]
  have isOpen : fd ∈ openNumbers I before.host.world.events := Decidable.of_not_not refused
  have image : SysImage F L I before.host.world.events Call.fdClose [.word fd]
      (closeReply (closeEvent fd (replies before.host.world.events.length)).ret)
      [closeEvent fd (replies before.host.world.events.length)] := by
    rw [sysImage_close]
    simp only [CloseImage, isOpen, ↓reduceIte]
    exact ⟨_, rfl, rfl⟩
  refine ⟨_, _, _, ?_, shimStep_one ⟨valid.accepted, image⟩ ⟨rfl, rfl⟩ (writesWithin_none rfl),
    MemFrame.refl _ _, ?_⟩
  · simp only [closeInvoke, OracleSys.word_roundtrip h0, isOpen, ↓reduceIte]
  · intro outputs same
    simp only [closeReply, closeEvent] at same
    by_cases zero : (replies before.host.world.events.length).ret = 0
    · simp only [zero, ↓reduceIte] at same
      obtain ⟨_, rfl⟩ := Transfer.returned.inj same
      rfl
    · simp only [zero, ↓reduceIte] at same
      by_cases error : Linux.isError (replies before.host.world.events.length).ret = true
      · simp only [error, ↓reduceIte] at same
        exact absurd (Transfer.returned.inj same).1 (errnoOf_valid _).2
      · simp only [error, Bool.false_eq_true, ↓reduceIte] at same
        cases same

/-! ## `fd_read` and `fd_write` on a handle -/

/-- `fd_read` of the descriptor `fd` into the buffer that the iovec element at `element` names,
with the count's pointer `result`. -/
def handleReadInvoke (before : Store (Observed LinuxWorld)) (args : List Value) :
    HostResult (Observed LinuxWorld) :=
  match args with
  | [.i32 fd, .i32 element, .i32 count, .i32 result] =>
    let buffer := before.mem.read32 element
    let capacity := before.mem.read32 (element + 4)
    if count = 1 ∧ element.toNat + 8 ≤ before.mem.pages * 65536 ∧ element.toNat + 8 ≤ 2 ^ 32 ∧
        buffer.toNat + capacity.toNat ≤ before.mem.pages * 65536 ∧
        buffer.toNat + capacity.toNat ≤ 2 ^ 32 ∧
        result.toNat + 4 ≤ before.mem.pages * 65536 ∧ result.toNat + 4 < 2 ^ 32 then
      if fd.toUInt64 ∈ openNumbers I before.host.world.events then
        let e := readEvent L before.mem fd.toUInt64 buffer capacity
          (replies before.host.world.events.length)
        let reply := handleReadReply capacity.toUInt64 e.ret e.output
        match Linux.step (shimMemory L) before.mem (readRequest L fd.toUInt64 buffer capacity)
            (replies before.host.world.events.length) with
        | some (mem, _) =>
          sysAnswer before Call.fdRead [.word fd.toUInt64, .space capacity.toUInt64]
            (placeReply mem (fun outputs => [(result, outputs.getD 1 Bytes.empty)]) reply) [e]
            reply
        | none => .Trap before shimTrap
      else
        sysAnswer before Call.fdRead [.word fd.toUInt64, .space capacity.toUInt64] before.mem []
          (.returned 8 [zeros capacity.toNat, zeros 4])
    else .Trap before shimTrap
  | _ => .Trap before shimTrap

/-- `fd_write` to the descriptor `fd` of the bytes that the iovec element at `element` names, with
the count's pointer `result`. -/
def handleWriteInvoke (before : Store (Observed LinuxWorld)) (args : List Value) :
    HostResult (Observed LinuxWorld) :=
  match args with
  | [.i32 fd, .i32 element, .i32 count, .i32 result] =>
    let buffer := before.mem.read32 element
    let length := before.mem.read32 (element + 4)
    if count = 1 ∧ element.toNat + 8 ≤ before.mem.pages * 65536 ∧ element.toNat + 8 ≤ 2 ^ 32 ∧
        buffer.toNat + length.toNat ≤ before.mem.pages * 65536 ∧
        buffer.toNat + length.toNat ≤ 2 ^ 32 ∧
        result.toNat + 4 ≤ before.mem.pages * 65536 ∧ result.toNat + 4 < 2 ^ 32 then
      let request := [Arg.word fd.toUInt64,
        .bytes (bytesOfList (before.mem.readBytes buffer.toNat length.toNat))]
      if fd.toUInt64 ∈ openNumbers I before.host.world.events then
        let e := writeEvent L before.mem fd.toUInt64 buffer length
          (replies before.host.world.events.length)
        let reply := handleWriteReply length.toUInt64 e.ret
        sysAnswer before Call.fdWrite request
          (placeReply before.mem (fun outputs => [(result, outputs.headD Bytes.empty)]) reply)
          [e] reply
      else sysAnswer before Call.fdWrite request before.mem [] (.returned 8 [zeros 4])
    else .Trap before shimTrap
  | _ => .Trap before shimTrap

theorem handleRead_shape {request : List Arg} (h : argsFit Call.fdRead.params request = true) :
    ∃ fd capacity, request = [.word fd, .space capacity] ∧ fd.toNat < 2 ^ 32 ∧
      capacity.toNat < 2 ^ 32 := by
  obtain ⟨a, r, rfl, ha, h⟩ := argsFit_takes h rfl
  obtain ⟨b, r, rfl, hb, h⟩ := argsFit_takes h rfl
  have empty : r = [] := by simpa [argsFit, Param.takesArg] using h
  subst empty
  cases a <;> cases b <;> simp_all [argFits]

theorem handleWrite_shape {request : List Arg} (h : argsFit Call.fdWrite.params request = true) :
    ∃ fd data, request = [.word fd, .bytes data] ∧ fd.toNat < 2 ^ 32 ∧ data.data.size < 2 ^ 32 := by
  obtain ⟨a, r, rfl, ha, h⟩ := argsFit_takes h rfl
  obtain ⟨b, r, rfl, hb, h⟩ := argsFit_takes h rfl
  have empty : r = [] := by simpa [argsFit, Param.takesArg] using h
  subst empty
  cases a <;> cases b <;> simp_all [argFits]

/-- An iovec element's buffer: its pointer, below `2^32` with its length, and its length. -/
theorem element_at {mem : Mem} {element buffer : UInt32} {length : Nat}
    (h : Bytes.At mem element.toUInt64 (elementBytes buffer length)) (small : length < 2 ^ 32) :
    mem.read32 element = buffer ∧ (mem.read32 (element + 4)).toNat = length ∧
      element.toNat + 8 ≤ mem.pages * 65536 ∧ element.toNat + 8 ≤ 2 ^ 32 := by
  have read := element_read h
  rw [UInt32.toUInt32_toUInt64] at read
  have address := h.address
  have memory := h.memory
  rw [elementBytes_size, UInt32.toNat_toUInt64] at address memory
  refine ⟨read.1, ?_, memory, address⟩
  rw [read.2, UInt32.toNat_ofNat_of_lt' small]

theorem getD_one (first second : Bytes) (rest : List Bytes) :
    (first :: second :: rest).getD 1 Bytes.empty = second := rfl

theorem handleRead_contract (before : Store (Observed LinuxWorld)) (args : List Value) :
    sysContract (linuxHost F L I replies) Call.fdRead before args
      (handleReadInvoke L I replies before args) := by
  apply sys_contract_of
  intro request pointers valid
  obtain ⟨fd, capacity, rfl, sFd, sCapacity⟩ := handleRead_shape valid.fits
  have regions : outputRegions Call.fdRead.params
      (shimReported I before.host.world.reports Call.fdRead) [.word fd, .space capacity] pointers =
      [⟨pointers.tail.headD 0, capacity.toNat, 1, true⟩,
        ⟨pointers.tail.tail.headD 0, 4, 4, true⟩] := rfl
  have first : (pointers.tail.headD 0).toNat + capacity.toNat ≤ before.mem.pages * 65536 ∧
      (pointers.tail.headD 0).toNat + capacity.toNat < 2 ^ 32 := by
    have b := valid.bounds ⟨pointers.tail.headD 0, capacity.toNat, 1, true⟩
      (by rw [regions]; exact List.mem_cons_self)
    exact ⟨b.1, b.2.1⟩
  have second : (pointers.tail.tail.headD 0).toNat + 4 ≤ before.mem.pages * 65536 ∧
      (pointers.tail.tail.headD 0).toNat + 4 < 2 ^ 32 := by
    have b := valid.bounds ⟨pointers.tail.tail.headD 0, 4, 4, true⟩
      (by rw [regions]; exact List.mem_cons_of_mem _ List.mem_cons_self)
    exact ⟨b.1, b.2.1⟩
  have apart : (pointers.tail.headD 0).toNat + capacity.toNat ≤
      (pointers.tail.tail.headD 0).toNat ∨
      (pointers.tail.tail.headD 0).toNat + 4 ≤ (pointers.tail.headD 0).toNat := by
    have pairs := valid.apart
    rw [regions] at pairs
    simpa [Region.span, LeanExe.Runtime.regionsDisjoint] using pairs
  have element := element_at (valid.inputs (pointers.headD 0,
    elementBytes (pointers.tail.headD 0) capacity.toNat)
    (by simp [inputPlaces, Call.fdRead, Arg.capacity])) sCapacity
  have arguments : args = [.i32 fd.toUInt32, .i32 (pointers.headD 0), .i32 1,
      .i32 (pointers.tail.tail.headD 0)] := valid.arguments
  subst arguments
  dsimp only
  rw [regions]
  generalize pointers.headD 0 = p0 at element ⊢
  generalize pointers.tail.headD 0 = p1 at element first apart ⊢
  generalize pointers.tail.tail.headD 0 = p2 at second apart ⊢
  have narrow : (UInt32.ofNat capacity.toNat).toNat = capacity.toNat :=
    UInt32.toNat_ofNat_of_lt' sCapacity
  have wide : (UInt32.ofNat capacity.toNat).toUInt64 = capacity := by
    apply UInt64.toNat_inj.mp
    rw [UInt32.toNat_toUInt64, narrow]
  have capacityRead : before.mem.read32 (p0 + 4) = UInt32.ofNat capacity.toNat := by
    apply UInt32.toNat_inj.mp
    rw [element.2.1, narrow]
  have check : p0.toNat + 8 ≤ before.mem.pages * 65536 ∧ p0.toNat + 8 ≤ 2 ^ 32 ∧
      p1.toNat + (UInt32.ofNat capacity.toNat).toNat ≤ before.mem.pages * 65536 ∧
      p1.toNat + (UInt32.ofNat capacity.toNat).toNat ≤ 2 ^ 32 ∧
      p2.toNat + 4 ≤ before.mem.pages * 65536 ∧ p2.toNat + 4 < 2 ^ 32 := by
    rw [narrow]
    exact ⟨element.2.2.1, element.2.2.2, first.1, Nat.le_of_lt first.2, second.1, second.2⟩
  by_cases refused : fd ∉ openNumbers I before.host.world.events
  · refine ⟨before.mem, [], .returned 8 [zeros (UInt32.ofNat capacity.toNat).toNat, zeros 4], ?_,
      shimStep_none ⟨valid.accepted, ?_⟩, MemFrame.refl _ _,
      fun _ same => absurd (Transfer.returned.inj same).1 (by decide)⟩
    · simp only [handleReadInvoke, element.1, capacityRead, check, and_self, ↓reduceIte,
        OracleSys.word_roundtrip sFd, wide, refused]
    · rw [sysImage_read]
      simp only [HandleReadImage, refused, narrow, ↓reduceIte, and_self]
  have isOpen : fd ∈ openNumbers I before.host.world.events := Decidable.of_not_not refused
  have stepped := step_read L before.mem fd p1 (UInt32.ofNat capacity.toNat)
    (replies before.host.world.events.length) check.2.2.1
  have shape := handleReadReply_shape capacity
    (readEvent L before.mem fd p1 (UInt32.ofNat capacity.toNat)
      (replies before.host.world.events.length)).ret
    (readEvent L before.mem fd p1 (UInt32.ofNat capacity.toNat)
      (replies before.host.world.events.length)).output
    (by simp only [readEvent, List.length_map, List.length_range, narrow])
  have image : SysImage F L I before.host.world.events Call.fdRead [.word fd, .space capacity]
      (handleReadReply capacity
        (readEvent L before.mem fd p1 (UInt32.ofNat capacity.toNat)
          (replies before.host.world.events.length)).ret
        (readEvent L before.mem fd p1 (UInt32.ofNat capacity.toNat)
          (replies before.host.world.events.length)).output)
      [readEvent L before.mem fd p1 (UInt32.ofNat capacity.toNat)
        (replies before.host.world.events.length)] := by
    rw [sysImage_read]
    simp only [HandleReadImage, isOpen, ↓reduceIte]
    refine ⟨L.base + p1.toUInt64,
      before.mem.readBytes p1.toNat (UInt32.ofNat capacity.toNat).toNat, _, _, ?_, rfl⟩
    simp only [readEvent, wide]
  refine ⟨placeReply (before.mem.writeBytes p1.toNat
      ((List.range (UInt32.ofNat capacity.toNat).toNat).map
        (replies before.host.world.events.length).bytes))
      (fun outputs => [(p2, outputs.getD 1 Bytes.empty)])
      (handleReadReply capacity
        (readEvent L before.mem fd p1 (UInt32.ofNat capacity.toNat)
          (replies before.host.world.events.length)).ret
        (readEvent L before.mem fd p1 (UInt32.ofNat capacity.toNat)
          (replies before.host.world.events.length)).output),
    _, _, ?_, shimStep_one ⟨valid.accepted, image⟩ ⟨rfl, rfl⟩
      (readEvent_writesWithin L before.mem fd _ _ _ check.2.2.2.1), ?_, ?_⟩
  · simp only [handleReadInvoke, element.1, capacityRead, check, and_self, ↓reduceIte,
      OracleSys.word_roundtrip sFd, wide, isOpen, stepped]
  · refine (MemFrame.writeBytes _ _ _ ⟨_, List.mem_cons_self, Nat.le_refl _, ?_⟩).trans
      (MemFrame.placeReply _ _ _ fun outputs same placed member => ?_)
    · simp only [List.length_map, List.length_range, narrow, Region.span]
      exact Nat.le_refl _
    · obtain rfl := List.mem_singleton.mp member
      have sizes := shape.1
      rw [same] at sizes
      rcases outputs with _ | ⟨o0, _ | ⟨o1, _ | ⟨o2, rest⟩⟩⟩
      · simp [Transfer.committed] at sizes
      · simp [Transfer.committed] at sizes
      · simp only [Transfer.committed, List.map_cons, List.map_nil, List.cons.injEq] at sizes
        refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Nat.le_refl _, ?_⟩
        show p2.toNat + o1.data.size ≤ p2.toNat + 4
        omega
      · simp [Transfer.committed] at sizes
  · intro outputs same
    have success := same
    simp only [handleReadReply] at success
    by_cases within : (replies before.host.world.events.length).ret.toNat ≤ capacity.toNat
    · simp only [readEvent, within, ↓reduceIte] at success
      obtain ⟨_, rfl⟩ := Transfer.returned.inj success
      rw [same, placeReply_returned]
      simp only [placeAll, getD_one]
      have written := written_at before.mem p1
        ((List.range (UInt32.ofNat capacity.toNat).toNat).map
        (replies before.host.world.events.length).bytes)
        (by simp only [List.length_map, List.length_range, narrow]; omega)
        (by simp only [List.length_map, List.length_range, narrow]; exact first.1)
      have size4 : (leBytes 4
          (replies before.host.world.events.length).ret.toNat).data.data.toList.length
          = 4 := by
        have size := leBytes_size 4 (replies before.host.world.events.length).ret.toNat
        simp only [ByteArray.size] at size
        simpa only [Array.length_toList] using size
      have count := written_at (before.mem.writeBytes p1.toNat
        ((List.range (UInt32.ofNat capacity.toNat).toNat).map
          (replies before.host.world.events.length).bytes)) p2
        (leBytes 4 (replies before.host.world.events.length).ret.toNat).data.data.toList
        (by rw [size4]; omega) (by rw [size4]; exact second.1)
      rw [bytesOfList_data] at count
      simp only [ShownAt, ↓reduceIte]
      refine ⟨written.frame (Nat.le_refl _) fun i bound => ?_, count, trivial⟩
      simp only [bytesOfList_size, List.length_map, List.length_range, narrow] at bound
      simp only [UInt32.toNat_toUInt64, Mem.writeBytes]
      rw [dite_eq_right (by rw [size4]; omega)]
    · simp only [readEvent, within, ↓reduceIte] at success
      by_cases error : Linux.isError (replies before.host.world.events.length).ret = true
      · simp only [error, ↓reduceIte] at success
        exact absurd (Transfer.returned.inj success).1 (errnoOf_valid _).2
      · simp only [error, Bool.false_eq_true, ↓reduceIte] at success
        cases success

theorem handleWrite_contract (before : Store (Observed LinuxWorld)) (args : List Value) :
    sysContract (linuxHost F L I replies) Call.fdWrite before args
      (handleWriteInvoke L I replies before args) := by
  apply sys_contract_of
  intro request pointers valid
  obtain ⟨fd, data, rfl, sFd, sData⟩ := handleWrite_shape valid.fits
  have regions : outputRegions Call.fdWrite.params
      (shimReported I before.host.world.reports Call.fdWrite) [.word fd, .bytes data] pointers =
      [⟨pointers.tail.tail.headD 0, 4, 4, true⟩] := rfl
  have bounds := valid.bounds ⟨pointers.tail.tail.headD 0, 4, 4, true⟩
    (by rw [regions]; exact List.mem_singleton_self _)
  have result : (pointers.tail.tail.headD 0).toNat + 4 ≤ before.mem.pages * 65536 ∧
      (pointers.tail.tail.headD 0).toNat + 4 < 2 ^ 32 := ⟨bounds.1, bounds.2.1⟩
  have element := element_at (valid.inputs (pointers.headD 0,
    elementBytes (pointers.tail.headD 0) data.data.size)
    (by simp [inputPlaces, Call.fdWrite, Arg.length])) sData
  have held := valid.inputs (pointers.tail.headD 0, data) (by simp [inputPlaces, Call.fdWrite])
  have arguments : args = [.i32 fd.toUInt32, .i32 (pointers.headD 0), .i32 1,
      .i32 (pointers.tail.tail.headD 0)] := valid.arguments
  subst arguments
  dsimp only
  rw [regions]
  generalize pointers.headD 0 = p0 at element ⊢
  generalize pointers.tail.headD 0 = p1 at element held ⊢
  generalize pointers.tail.tail.headD 0 = p2 at result ⊢
  have length : (UInt32.ofNat data.data.size).toNat = data.data.size :=
    UInt32.toNat_ofNat_of_lt' sData
  have lengthRead : before.mem.read32 (p0 + 4) = UInt32.ofNat data.data.size := by
    apply UInt32.toNat_inj.mp
    rw [element.2.1, length]
  have wide : (UInt32.ofNat data.data.size).toUInt64 = UInt64.ofNat data.data.size := by
    apply UInt64.toNat_inj.mp
    rw [UInt32.toNat_toUInt64, length,
      UInt64.toNat_ofNat_of_lt' (show data.data.size < 2 ^ 64 by omega)]
  have read : bytesOfList (before.mem.readBytes p1.toNat data.data.size) = data := by
    have := readBytes_value held
    rwa [UInt32.toNat_toUInt64] at this
  have listed : before.mem.readBytes p1.toNat data.data.size = data.data.data.toList := by
    have := readBytes_eq held
    rwa [UInt32.toNat_toUInt64] at this
  have address := held.address
  have memory := held.memory
  simp only [UInt32.toNat_toUInt64] at address memory
  have check : p0.toNat + 8 ≤ before.mem.pages * 65536 ∧ p0.toNat + 8 ≤ 2 ^ 32 ∧
      p1.toNat + data.data.size ≤ before.mem.pages * 65536 ∧
      p1.toNat + data.data.size ≤ 2 ^ 32 ∧
      p2.toNat + 4 ≤ before.mem.pages * 65536 ∧ p2.toNat + 4 < 2 ^ 32 :=
    ⟨element.2.2.1, element.2.2.2, memory, address, result.1, result.2⟩
  by_cases refused : fd ∉ openNumbers I before.host.world.events
  · refine ⟨before.mem, [], .returned 8 [zeros 4], ?_, shimStep_none ⟨valid.accepted, ?_⟩,
      MemFrame.refl _ _, fun _ same => absurd (Transfer.returned.inj same).1 (by decide)⟩
    · simp only [handleWriteInvoke, element.1, lengthRead, length, check, and_self, ↓reduceIte,
        OracleSys.word_roundtrip sFd, read, refused]
    · rw [sysImage_write]
      simp [HandleWriteImage, refused]
  have isOpen : fd ∈ openNumbers I before.host.world.events := Decidable.of_not_not refused
  have image : SysImage F L I before.host.world.events Call.fdWrite [.word fd, .bytes data]
      (handleWriteReply (UInt64.ofNat data.data.size)
        (writeEvent L before.mem fd p1 (UInt32.ofNat data.data.size)
          (replies before.host.world.events.length)).ret)
      [writeEvent L before.mem fd p1 (UInt32.ofNat data.data.size)
        (replies before.host.world.events.length)] := by
    rw [sysImage_write]
    simp only [HandleWriteImage, isOpen, ↓reduceIte]
    refine ⟨L.base + p1.toUInt64, _, ?_, rfl⟩
    simp only [writeEvent, wide, length, listed]
  have answer := placed_one (pointer := p2) (size := 4) (align := 4)
    (handleWriteReply_shape (UInt64.ofNat data.data.size)
      (writeEvent L before.mem fd p1 (UInt32.ofNat data.data.size)
        (replies before.host.world.events.length)).ret) result.1 result.2
  refine ⟨_, _, _, ?_, shimStep_one ⟨valid.accepted, image⟩ ⟨rfl, rfl⟩
    (writeEvent_writesWithin L _ _ _ _ _ _), answer.1, answer.2⟩
  simp only [handleWriteInvoke, element.1, lengthRead, length, check, and_self, ↓reduceIte,
    OracleSys.word_roundtrip sFd, wide, read, isOpen]

/-! ## The preopened directory -/

/-- `fd_prestat_get` of the descriptor `fd` with the record's pointer `record`. -/
def prestatInvoke (before : Store (Observed LinuxWorld)) (args : List Value) :
    HostResult (Observed LinuxWorld) :=
  match args with
  | [.i32 fd, .i32 record] =>
    if record.toNat + 8 ≤ before.mem.pages * 65536 ∧ record.toNat + 8 < 2 ^ 32 then
      sysAnswer before Call.fdPrestatGet [.word fd.toUInt64]
        (placeReply before.mem (fun outputs => [(record, outputs.headD Bytes.empty)])
          (prestatReply (preopened I before.host.world.events) fd.toUInt64))
        [] (prestatReply (preopened I before.host.world.events) fd.toUInt64)
    else .Trap before shimTrap
  | _ => .Trap before shimTrap

theorem prestat_contract (before : Store (Observed LinuxWorld)) (args : List Value) :
    sysContract (linuxHost F L I replies) Call.fdPrestatGet before args
      (prestatInvoke I before args) := by
  apply sys_contract_of
  intro request pointers valid
  obtain ⟨a, r, rfl, h0, h⟩ := argsFit_takes valid.fits rfl
  have empty : r = [] := by simpa [argsFit, Param.takesArg] using h
  subst empty
  cases a <;> simp only [argFits, Bool.false_eq_true, decide_eq_true_eq] at h0
  rename_i fd
  have regions : outputRegions Call.fdPrestatGet.params
      (shimReported I before.host.world.reports Call.fdPrestatGet) [.word fd] pointers =
      [⟨pointers.headD 0, 8, 4, true⟩] := rfl
  have bounds := valid.bounds ⟨pointers.headD 0, 8, 4, true⟩
    (by rw [regions]; exact List.mem_singleton_self _)
  have arguments : args = [.i32 fd.toUInt32, .i32 (pointers.headD 0)] := valid.arguments
  subst arguments
  have check : (pointers.headD 0).toNat + 8 ≤ before.mem.pages * 65536 ∧
      (pointers.headD 0).toNat + 8 < 2 ^ 32 := ⟨bounds.1, bounds.2.1⟩
  dsimp only
  rw [regions]
  have answer := placed_one (pointer := pointers.headD 0) (size := 8) (align := 4)
    (prestatReply_shape (preopened I before.host.world.events) fd) bounds.1 bounds.2.1
  have image : SysImage F L I before.host.world.events Call.fdPrestatGet [.word fd]
      (prestatReply (preopened I before.host.world.events) fd) [] := by
    rw [sysImage_prestat]
    exact ⟨rfl, rfl⟩
  refine ⟨_, [], _, ?_, shimStep_none ⟨valid.accepted, image⟩, answer.1, answer.2⟩
  simp only [prestatInvoke, check, and_self, ↓reduceIte, OracleSys.word_roundtrip h0]

/-! ## `fd_filestat_get` -/

/-- `fd_filestat_get` of the descriptor `fd` with the record's pointer `record`: a trap when the
record's 64 bytes leave memory, errno 8 (`badf`) with no call for a number that the shim does not
hold, and otherwise one `statx`, whose reply `filestatReply` gives and whose record, on errno 0,
the shim stores at `record`. -/
def filestatInvoke (before : Store (Observed LinuxWorld)) (args : List Value) :
    HostResult (Observed LinuxWorld) :=
  match args with
  | [.i32 fd, .i32 record] =>
    if record.toNat + 64 ≤ before.mem.pages * 65536 ∧ record.toNat + 64 < 2 ^ 32 then
      if fd.toUInt64 ∈ openNumbers I before.host.world.events then
        let e := statxEvent L fd.toUInt64 (replies before.host.world.events.length)
        sysAnswer before Call.fdFilestatGet [.word fd.toUInt64]
          (placeReply before.mem (fun outputs => [(record, outputs.headD Bytes.empty)])
            (filestatReply e.ret e.output))
          [e] (filestatReply e.ret e.output)
      else
        sysAnswer before Call.fdFilestatGet [.word fd.toUInt64] before.mem []
          (.returned 8 [zeros 64])
    else .Trap before shimTrap
  | _ => .Trap before shimTrap

theorem statxEvent_writesWithin (fd : UInt64) (r : Linux.Reply) (size : Nat) :
    WritesWithin L size (statxEvent L fd r) := by
  intro g hg
  change g ∈ Linux.outputRegions [fd, L.path, statxFlags, statxMask, L.statx] 0
    Linux.statxCall.params at hg
  have regions : Linux.outputRegions [fd, L.path, statxFlags, statxMask, L.statx] 0
      Linux.statxCall.params = [(L.statx, 256)] := rfl
  rw [regions, List.mem_singleton] at hg
  exact .inr (.inr hg)

theorem filestat_contract (before : Store (Observed LinuxWorld)) (args : List Value) :
    sysContract (linuxHost F L I replies) Call.fdFilestatGet before args
      (filestatInvoke L I replies before args) := by
  apply sys_contract_of
  intro request pointers valid
  obtain ⟨a, r, rfl, h0, h⟩ := argsFit_takes valid.fits rfl
  have empty : r = [] := by simpa [argsFit, Param.takesArg] using h
  subst empty
  cases a <;> simp only [argFits, Bool.false_eq_true, decide_eq_true_eq] at h0
  rename_i fd
  have regions : outputRegions Call.fdFilestatGet.params
      (shimReported I before.host.world.reports Call.fdFilestatGet) [.word fd] pointers =
      [⟨pointers.headD 0, 64, 8, true⟩] := rfl
  have bounds := valid.bounds ⟨pointers.headD 0, 64, 8, true⟩
    (by rw [regions]; exact List.mem_singleton_self _)
  have arguments : args = [.i32 fd.toUInt32, .i32 (pointers.headD 0)] := valid.arguments
  subst arguments
  have check : (pointers.headD 0).toNat + 64 ≤ before.mem.pages * 65536 ∧
      (pointers.headD 0).toNat + 64 < 2 ^ 32 := ⟨bounds.1, bounds.2.1⟩
  dsimp only
  rw [regions]
  by_cases refused : fd ∉ openNumbers I before.host.world.events
  · have image : SysImage F L I before.host.world.events Call.fdFilestatGet [.word fd]
        (.returned 8 [zeros 64]) [] := by
      rw [sysImage_filestat]
      simp [FilestatImage, refused]
    refine ⟨before.mem, [], .returned 8 [zeros 64], ?_, shimStep_none ⟨valid.accepted, image⟩,
      MemFrame.refl _ _, fun _ same => absurd (Transfer.returned.inj same).1 (by decide)⟩
    simp only [filestatInvoke, check, and_self, ↓reduceIte, OracleSys.word_roundtrip h0,
      refused]
  have isOpen : fd ∈ openNumbers I before.host.world.events := Decidable.of_not_not refused
  have answer := placed_one (pointer := pointers.headD 0) (size := 64) (align := 8)
    (filestatReply_shape (statxEvent L fd (replies before.host.world.events.length)).ret
      (statxEvent L fd (replies before.host.world.events.length)).output) bounds.1 bounds.2.1
  have image : SysImage F L I before.host.world.events Call.fdFilestatGet [.word fd]
      (filestatReply (statxEvent L fd (replies before.host.world.events.length)).ret
        (statxEvent L fd (replies before.host.world.events.length)).output)
      [statxEvent L fd (replies before.host.world.events.length)] := by
    rw [sysImage_filestat]
    simp only [FilestatImage, isOpen, ↓reduceIte]
    exact ⟨_, _, rfl, rfl⟩
  refine ⟨_, _, _, ?_, shimStep_one ⟨valid.accepted, image⟩ ⟨rfl, rfl⟩
    (statxEvent_writesWithin L fd _ _), answer.1, answer.2⟩
  simp only [filestatInvoke, check, and_self, ↓reduceIte, OracleSys.word_roundtrip h0, isOpen]

/-- `fd_prestat_dir_name` of the descriptor `fd` into the buffer of `capacity` bytes at `buffer`. -/
def dirNameInvoke (before : Store (Observed LinuxWorld)) (args : List Value) :
    HostResult (Observed LinuxWorld) :=
  match args with
  | [.i32 fd, .i32 buffer, .i32 capacity] =>
    if buffer.toNat + capacity.toNat ≤ before.mem.pages * 65536 ∧
        buffer.toNat + capacity.toNat < 2 ^ 32 then
      let request := [Arg.word fd.toUInt64, .space capacity.toUInt64]
      if fd.toUInt64 = 3 ∧ preopened I before.host.world.events = true then
        if 1 ≤ capacity.toNat then
          sysAnswer before Call.fdPrestatDirName request (before.mem.writeBytes buffer.toNat [46])
            [] (.returned 0
              [bytesOfList (46 :: before.mem.readBytes (buffer.toNat + 1) (capacity.toNat - 1))])
        else sysAnswer before Call.fdPrestatDirName request before.mem []
          (.returned 37 [zeros capacity.toNat])
      else if fd.toNat < 3 ∨ fd.toUInt64 ∈ openNumbers I before.host.world.events then
        sysAnswer before Call.fdPrestatDirName request before.mem []
          (.returned 54 [zeros capacity.toNat])
      else
        sysAnswer before Call.fdPrestatDirName request before.mem []
          (.returned 8 [zeros capacity.toNat])
    else .Trap before shimTrap
  | _ => .Trap before shimTrap

theorem dirName_contract (before : Store (Observed LinuxWorld)) (args : List Value) :
    sysContract (linuxHost F L I replies) Call.fdPrestatDirName before args
      (dirNameInvoke I before args) := by
  apply sys_contract_of
  intro request pointers valid
  obtain ⟨a, r, rfl, ha, h⟩ := argsFit_takes valid.fits rfl
  obtain ⟨b, r, rfl, hb, h⟩ := argsFit_takes h rfl
  have empty : r = [] := by simpa [argsFit] using h
  subst empty
  cases a <;> cases b <;> simp only [argFits, Bool.false_eq_true, decide_eq_true_eq] at ha hb
  rename_i fd capacity
  have regions : outputRegions Call.fdPrestatDirName.params
      (shimReported I before.host.world.reports Call.fdPrestatDirName) [.word fd, .space capacity]
      pointers = [⟨pointers.headD 0, capacity.toNat, 1, true⟩] := rfl
  have bounds := valid.bounds ⟨pointers.headD 0, capacity.toNat, 1, true⟩
    (by rw [regions]; exact List.mem_singleton_self _)
  have arguments : args = [.i32 fd.toUInt32, .i32 (pointers.headD 0),
      .i32 (UInt32.ofNat capacity.toNat)] := valid.arguments
  subst arguments
  have narrow : (UInt32.ofNat capacity.toNat).toNat = capacity.toNat :=
    UInt32.toNat_ofNat_of_lt' hb
  have wide : (UInt32.ofNat capacity.toNat).toUInt64 = capacity := by
    apply UInt64.toNat_inj.mp
    rw [UInt32.toNat_toUInt64, narrow]
  have fdNarrow : fd.toUInt32.toNat = fd.toNat := by
    rw [UInt64.toNat_toUInt32]
    omega
  have check : (pointers.headD 0).toNat + capacity.toNat ≤ before.mem.pages * 65536 ∧
      (pointers.headD 0).toNat + capacity.toNat < 2 ^ 32 := ⟨bounds.1, bounds.2.1⟩
  dsimp only
  rw [regions]
  have image : ∀ reply,
      DirNameReply (preopened I before.host.world.events) (openNumbers I before.host.world.events)
        fd capacity reply →
      SysImage F L I before.host.world.events Call.fdPrestatDirName [.word fd, .space capacity]
        reply [] := by
    intro reply named
    rw [sysImage_dirName]
    exact ⟨rfl, named⟩
  simp only [dirNameInvoke, narrow, check, and_self, ↓reduceIte, OracleSys.word_roundtrip ha,
    wide, fdNarrow]
  by_cases granted : fd = 3 ∧ preopened I before.host.world.events = true
  · by_cases room : 1 ≤ capacity.toNat
    · simp only [eq_true granted, eq_true room, ↓reduceIte]
      refine ⟨_, [], _, rfl, shimStep_none ⟨valid.accepted, image _ ?_⟩, ?_, ?_⟩
      · simp only [DirNameReply, eq_true granted, eq_true room, ↓reduceIte]
        exact ⟨_, by simp [Mem.readBytes], rfl⟩
      · exact MemFrame.writeBytes _ _ _ ⟨_, List.mem_singleton_self _, Nat.le_refl _,
          by simp [Region.span]; omega⟩
      · intro outputs same
        obtain ⟨_, rfl⟩ := Transfer.returned.inj same
        refine shownAt_single ⟨?_, ?_, ?_⟩
        · simp only [UInt32.toNat_toUInt64, bytesOfList_size, List.length_cons,
            Mem.readBytes, List.length_map, List.length_range]
          omega
        · simp only [UInt32.toNat_toUInt64, bytesOfList_size, List.length_cons,
            Mem.readBytes, List.length_map, List.length_range, Mem.writeBytes]
          omega
        · intro i bound
          simp only [UInt32.toNat_toUInt64, bytesOfList, ByteArray.getElem_eq_getElem_data,
            List.getElem_toArray, Mem.writeBytes]
          rcases i with _ | i
          · simp
          · rw [dite_eq_right (by simp)]
            simp only [List.getElem_cons_succ, Mem.readBytes, List.getElem_map,
              List.getElem_range]
            congr 1
            omega
    · simp only [eq_true granted, eq_false room, ↓reduceIte]
      refine ⟨_, [], _, rfl, shimStep_none ⟨valid.accepted, image _ ?_⟩, MemFrame.refl _ _,
        fun _ same => absurd (Transfer.returned.inj same).1 (by decide)⟩
      simp only [DirNameReply, eq_true granted, eq_false room, ↓reduceIte]
  · simp only [eq_false granted, ↓reduceIte]
    by_cases standard : fd.toNat < 3 ∨ fd ∈ openNumbers I before.host.world.events
    · simp only [eq_true standard, ↓reduceIte]
      refine ⟨_, [], _, rfl, shimStep_none ⟨valid.accepted, image _ ?_⟩, MemFrame.refl _ _,
        fun _ same => absurd (Transfer.returned.inj same).1 (by decide)⟩
      simp only [DirNameReply, eq_false granted, eq_true standard, ↓reduceIte]
    · simp only [eq_false standard, ↓reduceIte]
      refine ⟨_, [], _, rfl, shimStep_none ⟨valid.accepted, image _ ?_⟩, MemFrame.refl _ _,
        fun _ same => absurd (Transfer.returned.inj same).1 (by decide)⟩
      simp only [DirNameReply, eq_false granted, eq_false standard, ↓reduceIte]

end Verified.Shim
