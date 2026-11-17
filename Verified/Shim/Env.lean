import Verified.Shim.Host

/-!
The shim's stream functions as Talos host functions, and their proofs against the WASI contracts.
`readFn`, `writeFn`, and `exitFn` implement `fd_read`, `fd_write`, and `proc_exit` as the shim
does: they check a request as the contract's premise states it, make the request's `read` or
`write` through the layer's rule `Linux.step` on `shimMemory L` with the reply to the call that
the world's events count, append the layer event to the world and the WASI event to the observed
events, and give the WASI reply of the event, storing the count at guest address 8 only on
success.  A request that fails a check traps with `shimTrap` and changes nothing.
`read_contract`, `write_contract`, and `exit_contract` prove the contracts of
`linuxHost F L I replies`.  `readEvent_writesWithin` bounds a read's output region by the
memory's size at the call, the bound that a binding whose store stays within a native cap carries
to the run.
-/

namespace Verified.Shim

open Wasm LeanExe LeanExe.Wasi Verified.Wasi

variable (F : OpenFlags) (L : ShimLayout) (I : Launch) (replies : Linux.Replies)

/-- The store after a call that appended the layer events `l` and the WASI event `event`, with
the memory `mem`. -/
def answered (before : Store (Observed LinuxWorld)) (mem : Mem) (l : List Linux.Event)
    (event : Wasi.Event) : Store (Observed LinuxWorld) :=
  { before with
    mem
    host := ⟨before.host.world.answer l event, before.host.events ++ [event]⟩ }

/-- `fd_read` of descriptor 0 into the buffer whose pointer and length lie at guest address 0,
with the count stored at 8. -/
def readInvoke (before : Store (Observed LinuxWorld)) (args : List Value) :
    HostResult (Observed LinuxWorld) :=
  match args with
  | [.i32 0, .i32 0, .i32 1, .i32 8] =>
    let pointer := before.mem.read32 0
    let capacity := before.mem.read32 4
    if 16 ≤ before.mem.pages * 65536 ∧
        pointer.toNat + capacity.toNat ≤ before.mem.pages * 65536 ∧
        pointer.toNat + capacity.toNat ≤ 2 ^ 32 ∧ (capacity = 0 ∨ 16 ≤ pointer.toNat) then
      match Linux.step (shimMemory L) before.mem (readRequest L 0 pointer capacity)
          (replies before.host.world.events.length) with
      | some (mem, e) =>
        match readReply capacity.toUInt64 e.ret e.output with
        | .returned errno committed =>
          .Return [.i32 errno.toUInt32]
            (answered before
              (if errno = 0 then mem.write32 8 (UInt32.ofNat committed.data.size) else mem) [e]
              (.read capacity.toUInt64 (.returned errno committed)))
        | .trapped message committed =>
          .Trap (answered before mem [e] (.read capacity.toUInt64 (.trapped message committed)))
            message
      | none => .Trap before shimTrap
    else .Trap before shimTrap
  | _ => .Trap before shimTrap

/-- `fd_write` to the stream `output` from the buffer whose pointer and length lie at guest
address 0, with the count stored at 8. -/
def writeOutput (output : Output) (before : Store (Observed LinuxWorld)) :
    HostResult (Observed LinuxWorld) :=
  let pointer := before.mem.read32 0
  let length := before.mem.read32 4
  if 16 ≤ before.mem.pages * 65536 ∧
      pointer.toNat + length.toNat ≤ before.mem.pages * 65536 ∧
      pointer.toNat + length.toNat ≤ 2 ^ 32 then
    match Linux.step (shimMemory L) before.mem (writeRequest L output.fd pointer length)
        (replies before.host.world.events.length) with
    | some (mem, e) =>
      let bytes := bytesOfList (before.mem.readBytes pointer.toNat length.toNat)
      match writeReply length.toUInt64 e.ret with
      | .returned errno committed =>
        .Return [.i32 errno.toUInt32]
          (answered before (if errno = 0 then mem.write32 8 committed.toUInt32 else mem) [e]
            (.write output bytes (.returned errno committed)))
      | .trapped message committed =>
        .Trap (answered before mem [e] (.write output bytes (.trapped message committed))) message
    | none => .Trap before shimTrap
  else .Trap before shimTrap

/-- `fd_write` to descriptor 1 or 2. -/
def writeInvoke (before : Store (Observed LinuxWorld)) (args : List Value) :
    HostResult (Observed LinuxWorld) :=
  match args with
  | [.i32 1, .i32 0, .i32 1, .i32 8] => writeOutput L replies .stdout before
  | [.i32 2, .i32 0, .i32 1, .i32 8] => writeOutput L replies .stderr before
  | _ => .Trap before shimTrap

/-- `proc_exit`: a status below 126 ends the run as an accepted exit, and any other status as a
rejected one. -/
def exitInvoke (before : Store (Observed LinuxWorld)) (args : List Value) :
    HostResult (Observed LinuxWorld) :=
  match args with
  | [.i32 code] =>
    if code.toNat < 126 then
      .Trap { before with
        host := ⟨{ before.host.world with exited := some code.toUInt64 },
          before.host.events ++ [.exit code.toUInt64]⟩ } exitTrap
    else
      .Trap { before with
        host := ⟨before.host.world,
          before.host.events ++ [.exitTrap code.toUInt64 exitRejected]⟩ }
        exitRejected
  | _ => .Trap before shimTrap

def readFn : HostFn (Observed LinuxWorld) where
  params := [.i32, .i32, .i32, .i32]
  results := [.i32]
  invoke := readInvoke L replies

def writeFn : HostFn (Observed LinuxWorld) where
  params := [.i32, .i32, .i32, .i32]
  results := [.i32]
  invoke := writeInvoke L replies

def exitFn : HostFn (Observed LinuxWorld) where
  params := [.i32]
  results := []
  invoke := exitInvoke

theorem bytesOfList_take_at {mem : Mem} {root : UInt64} {bytes : List UInt8}
    (h : Bytes.At mem root (bytesOfList bytes)) (n : Nat) :
    Bytes.At mem root (bytesOfList (bytes.take n)) := by
  have size := h.address
  have memory := h.memory
  simp only [bytesOfList_size] at size memory
  refine ⟨?_, ?_, ?_⟩
  · simp only [bytesOfList_size, List.length_take]
    omega
  · simp only [bytesOfList_size, List.length_take]
    omega
  · intro i hi
    simp only [bytesOfList_size, List.length_take] at hi
    have := h.contents i (by simp only [bytesOfList_size]; omega)
    rw [this]
    simp only [bytesOfList, ByteArray.getElem_eq_getElem_data, List.getElem_toArray,
      List.getElem_take]

theorem readReply_success {count ret : UInt64} {output : List UInt8} {committed : Bytes}
    (h : readReply count ret output = .returned 0 committed) :
    ret.toNat ≤ count.toNat ∧ committed = bytesOfList (output.take ret.toNat) := by
  unfold readReply at h
  split at h
  · cases h
    exact ⟨by assumption, rfl⟩
  · split at h
    · injection h with zero
      exact absurd zero (errnoOf_valid _).2
    · cases h

theorem writeReply_success {count ret committed : UInt64}
    (h : writeReply count ret = .returned 0 committed) : committed = ret := by
  unfold writeReply at h
  split at h
  · cases h
    rfl
  · split at h
    · injection h with zero
      exact absurd zero (errnoOf_valid _).2
    · cases h

/-- A read's output region lies within every size that holds its buffer, the memory's size at the
call among them. -/
theorem readEvent_writesWithin (mem : Mem) (fd : UInt64) (pointer capacity : UInt32)
    (r : Linux.Reply) {size : Nat} (fits : pointer.toNat + capacity.toNat ≤ size) :
    WritesWithin L size (readEvent L mem fd pointer capacity r) := by
  intro g hg
  change g ∈ Linux.outputRegions [fd, L.base + pointer.toUInt64, capacity.toUInt64] 0
    Linux.readCall.params at hg
  rw [outputs_read, List.mem_singleton] at hg
  subst hg
  left
  simp only [offset_base, UInt32.toNat_toUInt64]
  exact fits

/-- A write has no output region. -/
theorem writeEvent_writesWithin (mem : Mem) (fd : UInt64) (pointer length : UInt32)
    (r : Linux.Reply) (size : Nat) :
    WritesWithin L size (writeEvent L mem fd pointer length r) := by
  intro g hg
  have regions := (Linux.regions_write (shimMemory L) mem fd (L.base + pointer.toUInt64)
    length.toUInt64).2
  change g ∈ Linux.outputRegions [fd, L.base + pointer.toUInt64, length.toUInt64] 0
    Linux.writeCall.params at hg
  rw [regions] at hg
  cases hg

/-- The shim's `read` answers an `fd_read` in the host's relation. -/
theorem read_step (w : LinuxWorld) (mem : Mem) (pointer capacity : UInt32)
    (address : pointer.toNat + capacity.toNat ≤ 2 ^ 32) :
    let e := readEvent L mem 0 pointer capacity (replies w.events.length)
    let event := Wasi.Event.read capacity.toUInt64 (readReply capacity.toUInt64 e.ret e.output)
    ShimStep F L I replies w event (w.answer [e] event) := by
  intro e event
  refine ⟨[e], ⟨e, _, rfl, rfl, rfl, rfl, rfl⟩, ⟨⟨rfl, rfl⟩, trivial⟩, ?_, rfl⟩
  intro x hx
  obtain rfl := List.mem_singleton.mp hx
  exact readEvent_writesWithin L mem 0 pointer capacity _ address

/-- The shim's `write` answers an `fd_write` in the host's relation. -/
theorem write_step (w : LinuxWorld) (mem : Mem) (output : Output) (pointer : UInt32)
    (bytes : Bytes) (listed : mem.readBytes pointer.toNat bytes.data.size = bytes.data.data.toList)
    (size : bytes.data.size < 2 ^ 32)
    (wide : (UInt32.ofNat bytes.data.size).toUInt64 = UInt64.ofNat bytes.data.size)
    (length : (UInt32.ofNat bytes.data.size).toNat = bytes.data.size) :
    let e := writeEvent L mem output.fd pointer (UInt32.ofNat bytes.data.size)
      (replies w.events.length)
    let event := Wasi.Event.write output bytes
      (writeReply (UInt32.ofNat bytes.data.size).toUInt64 e.ret)
    ShimStep F L I replies w event (w.answer [e] event) := by
  intro e event
  refine ⟨[e], ⟨e, L.base + pointer.toUInt64, rfl, rfl, ?_, ?_, rfl, size, by rw [wide]⟩,
    ⟨⟨rfl, rfl⟩, trivial⟩, ?_, rfl⟩
  · change [output.fd, L.base + pointer.toUInt64, (UInt32.ofNat bytes.data.size).toUInt64] = _
    rw [wide]
  · change [mem.readBytes pointer.toNat (UInt32.ofNat bytes.data.size).toNat] = _
    rw [length, listed]
  · intro x hx
    obtain rfl := List.mem_singleton.mp hx
    exact writeEvent_writesWithin L mem _ _ _ _ _

theorem read_contract (before : Store (Observed LinuxWorld)) (args : List Value) :
    readContract (linuxHost F L I replies) before args (readInvoke L replies before args) := by
  intro pointer capacity request
  rw [request.arguments]
  simp only [readInvoke, request.pointer_eq, request.length_eq]
  rw [ite_eq_left ⟨request.scratch, request.memory, request.address, request.separate⟩,
    step_read L before.mem 0 pointer capacity _ request.memory]
  dsimp only
  have shim := read_step F L I replies before.host.world before.mem pointer capacity request.address
  dsimp only at shim
  have bound : ((List.range capacity.toNat).map
      (replies before.host.world.events.length).bytes).length ≤ capacity.toNat := by simp
  generalize hreply : readReply capacity.toUInt64
    (readEvent L before.mem 0 pointer capacity (replies before.host.world.events.length)).ret
    (readEvent L before.mem 0 pointer capacity (replies before.host.world.events.length)).output =
    reply at shim
  cases reply with
  | returned errno committed =>
    dsimp only
    refine ⟨errno, committed, rfl, ⟨shim, rfl⟩, ?_, ?_⟩
    · by_cases zero : errno = 0
      · simp only [zero, ↓reduceIte]
        exact (frame_payload before before.host _ _ _ bound).trans
          ((frame_count _ _ _).weaken fun region member => by
            obtain rfl := List.mem_singleton.mp member
            exact List.mem_cons_self)
      · simp only [zero, ↓reduceIte]
        exact frame_payload before _ _ _ _ bound
    · intro zero
      subst zero
      obtain ⟨within, rfl⟩ := readReply_success hreply
      simp only [UInt32.toNat_toUInt64] at within
      simp only [↓reduceIte]
      have written := written_at before.mem pointer
        ((List.range capacity.toNat).map (replies before.host.world.events.length).bytes)
        (by simp only [List.length_map, List.length_range]; exact request.address)
        (by simp only [List.length_map, List.length_range]; exact request.memory)
      refine ⟨at_count (bytesOfList_take_at written _) _ ?_, read32_write32 _ _ _⟩
      rcases request.separate with empty | above
      · left
        simp only [bytesOfList_size, List.length_take]
        have : capacity.toNat = 0 := by rw [empty]; rfl
        omega
      · exact Or.inr above
  | trapped message committed =>
    dsimp only
    exact ⟨committed, ⟨shim, rfl⟩, frame_payload before _ _ _ _ bound⟩

theorem write_contract (before : Store (Observed LinuxWorld)) (args : List Value) :
    writeContract (linuxHost F L I replies) before args (writeInvoke L replies before args) := by
  intro output pointer bytes request
  have invoke : writeInvoke L replies before args = writeOutput L replies output before := by
    rw [request.arguments]
    cases output <;> rfl
  rw [invoke]
  have size := request.size
  have length : (UInt32.ofNat bytes.data.size).toNat = bytes.data.size :=
    UInt32.toNat_ofNat_of_lt' size
  have fits : pointer.toNat + (UInt32.ofNat bytes.data.size).toNat ≤
      before.mem.pages * 65536 := by
    rw [length]
    exact request.data.memory
  have wide : (UInt32.ofNat bytes.data.size).toUInt64 = UInt64.ofNat bytes.data.size := by
    apply UInt64.toNat_inj.mp
    rw [UInt32.toNat_toUInt64, length,
      UInt64.toNat_ofNat_of_lt' (show bytes.data.size < 2 ^ 64 by omega)]
  have listed : before.mem.readBytes pointer.toNat bytes.data.size = bytes.data.data.toList := by
    simpa only [UInt32.toNat_toUInt64] using readBytes_eq request.data
  have decoded : bytesOfList (before.mem.readBytes pointer.toNat
      (UInt32.ofNat bytes.data.size).toNat) = bytes := by
    rw [length, listed, bytesOfList_data]
  simp only [writeOutput, request.pointer_eq, request.length_eq]
  rw [ite_eq_left ⟨request.scratch, fits, by rw [length]; exact request.data.address⟩,
    step_write L before.mem output.fd pointer _ _ fits]
  dsimp only
  rw [decoded]
  have shim := write_step F L I replies before.host.world before.mem output pointer bytes listed size
    wide length
  dsimp only at shim
  generalize hreply : writeReply (UInt32.ofNat bytes.data.size).toUInt64
    (writeEvent L before.mem output.fd pointer (UInt32.ofNat bytes.data.size)
      (replies before.host.world.events.length)).ret = reply at shim
  cases reply with
  | returned errno committed =>
    dsimp only
    refine ⟨errno, committed, rfl, ⟨shim, rfl⟩, ?_, ?_⟩
    · by_cases zero : errno = 0
      · simp only [zero, ↓reduceIte]
        exact frame_count before _ _
      · simp only [zero, ↓reduceIte]
        exact frame_host before _ _
    · intro zero
      subst zero
      simp only [↓reduceIte]
      exact read32_write32 _ _ _
  | trapped message committed =>
    dsimp only
    exact ⟨committed, ⟨shim, rfl⟩, frame_host before _ _⟩

theorem exit_contract (before : Store (Observed LinuxWorld)) (args : List Value) :
    exitContract (linuxHost F L I replies) before args (exitInvoke before args) := by
  intro code arguments
  rw [arguments]
  by_cases accepted : code.toNat < 126
  · dsimp only [exitInvoke]
    rw [ite_eq_left accepted]
    dsimp only
    refine ⟨frame_host _ _ [], Or.inl ⟨rfl, ⟨?_, rfl⟩, rfl⟩⟩
    simpa only [UInt32.toNat_toUInt64]
  · dsimp only [exitInvoke]
    rw [ite_eq_right accepted]
    dsimp only
    refine ⟨frame_host _ _ [], Or.inr ⟨⟨?_, rfl, rfl⟩, rfl⟩⟩
    simp only [UInt32.toNat_toUInt64]
    omega

end Verified.Shim
