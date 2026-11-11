import Demos.Rcv.ProcessCharges

/-! The correctness of the compiled process.  Under StreamFold's host assumptions, a Talos host
that satisfies the three import specifications, and a host that accepts the exit status,
`initial_terminates` states that the module's `_start`, from its initial store, exits with status 0
after writing exactly the bytes of the report of an input of at most `limit` bytes, and
`initial_exits_long` that it exits with status `tooLong` after writing nothing for a longer input.
The memory of a run is a closed number: the buffer of `readAll`, the call of `tabulate` on at most
`limit` bytes, and the copy of a state fit in the 65,535 pages above the literal pool, as
`processMemory_le` states, so neither theorem has a memory premise.  `terminates_of_room` and
`exits_long_of_room` are `Compiled.terminates_of_room` and `Compiled.exits_long_of_room` of
[the runs of a compiled tabulator's process](ProcessRun.lean) for this module, its report, and its
charges. -/

namespace Demos.Rcv.Process

open Wasm _root_.Verified _root_.Verified.Wasi LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime
open Demos.StreamFold (StreamPosition StreamHost observedStreamRep stdoutWords)

theorem memoryCap_pure {α : Type} (store : Store α) :
    store.memoryCap module 0 = store.memoryCap io.pure.module 0 :=
  PureTransport.memoryCap_zero_eq rfl store

/-- The bytes above the literal pool that a run needs: the charge of `begin` and the copy of a
state, which bound the charges of the steps as well. -/
def processMemory : Nat := beginCharge + copyLimit

theorem processMemory_eq : processMemory = 4085008138 := by
  rw [processMemory, beginCharge_eq]
  rfl

/-- From a store with an allocator at `heap`, the literal pool, and room above `heap.top` for
`processMemory` bytes, the module's `_start` exits with status 0 after writing exactly the bytes of
the report of an input of at most `limit` bytes. -/
theorem terminates_of_room {World : Type} (host : Host World)
    (targetHost : HostEnv (Observed World)) (initial : Store (Observed World)) (heap : Heap)
    (rep : StreamPosition → World → Prop) (streams : StreamHost host rep)
    {position : StreamPosition} (represented : rep position initial.host.world)
    (events : initial.host.events = []) (empty : position.output = [])
    (size : position.input.length ≤ limit.toNat)
    (valid : targetHost.Satisfies module (hostSpec host))
    (at_ : heap.At (PureTransport.erase initial)) (free : heap.free = [])
    (static : io.literalPool.Static heap (PureTransport.erase initial))
    (cap : (PureTransport.erase initial).memoryCap module 0 ≤ 65535)
    (room : heap.top.toNat + processMemory ≤
      65536 * (PureTransport.erase initial).memoryCap io.pure.module 0)
    (accepted : ExitAccepted host rep 0) :
    ∃ bound, ∀ fuel ≥ bound, ∃ final,
      run fuel module startIndex initial [] targetHost = .Trap final exitTrap ∧
        stdoutWords final.host.events = expectedOutput position.input ∧
        host.exited final.host.world = some 0 :=
  compiledProcess.terminates_of_room (tab := TabulateProgram.tabulate) (expected := expectedOutput)
    future_report (fun _ sized => (Sized.mk sized).copyCost) (by rw [beginCharge_eq]; decide)
    begin_prefix_bound (fun host _ sized world => step_prefix_bound host ⟨sized⟩ world)
    host targetHost initial heap rep streams represented events empty size valid at_ free static
    cap room accepted

/-- From a store with an allocator at `heap`, the literal pool, and room above `heap.top` for the
charge of `begin`, the module's `_start` exits with status `tooLong` after writing nothing, for an
input of more than `limit` bytes. -/
theorem exits_long_of_room {World : Type} (host : Host World)
    (targetHost : HostEnv (Observed World)) (initial : Store (Observed World)) (heap : Heap)
    (rep : StreamPosition → World → Prop) (streams : StreamHost host rep)
    {position : StreamPosition} (represented : rep position initial.host.world)
    (events : initial.host.events = []) (empty : position.output = [])
    (size : limit.toNat < position.input.length)
    (valid : targetHost.Satisfies module (hostSpec host))
    (at_ : heap.At (PureTransport.erase initial)) (free : heap.free = [])
    (static : io.literalPool.Static heap (PureTransport.erase initial))
    (cap : (PureTransport.erase initial).memoryCap module 0 ≤ 65535)
    (room : heap.top.toNat + processMemory ≤
      65536 * (PureTransport.erase initial).memoryCap io.pure.module 0)
    (accepted : ExitAccepted host rep tooLong) :
    ∃ bound, ∀ fuel ≥ bound, ∃ final,
      run fuel module startIndex initial [] targetHost = .Trap final exitTrap ∧
        stdoutWords final.host.events = [] ∧ host.exited final.host.world = some tooLong :=
  compiledProcess.exits_long_of_room (tab := TabulateProgram.tabulate) begin_prefix_bound
    host targetHost initial heap rep streams represented events empty size valid at_ free static
    cap (Nat.le_trans (Nat.add_le_add_left (Nat.le_add_right beginCharge copyLimit) _) room)
    accepted

set_option maxHeartbeats 2000000 in
theorem initial_memoryCap {World : Type} (world : Observed World) :
    (PureTransport.erase (initialStore world)).memoryCap io.pure.module 0 = 65535 := by
  rw [initialStore, PureTransport.erase_restore]
  decide +kernel

theorem initial_top : (initialStaticHeap io.literalPool).top.toNat = 4096 := by
  decide +kernel

/-- The memory of a run fits above the literal pool, which ends at 4,096 bytes, in the 65,535
pages of the module's memory. -/
theorem processMemory_le : 4096 + processMemory ≤ 65536 * 65535 := by
  rw [processMemory_eq]
  decide

/-- For every input of at most 50,000,000 bytes, under StreamFold's host assumptions, a Talos host
that satisfies the import specifications, and a host that accepts the exit status 0, the compiled
command from its initial store exits with status 0 after writing exactly the bytes of the report
of the input. -/
theorem initial_terminates {World : Type} (host : Host World)
    (targetHost : HostEnv (Observed World)) (world : Observed World)
    (rep : StreamPosition → World → Prop) (streams : StreamHost host rep)
    {position : StreamPosition} (represented : rep position world.world)
    (events : world.events = []) (empty : position.output = [])
    (size : position.input.length ≤ 50000000)
    (valid : targetHost.Satisfies module (hostSpec host)) (accepted : ExitAccepted host rep 0) :
    ∃ bound, ∀ fuel ≥ bound, ∃ final,
      run fuel module startIndex (initialStore world) [] targetHost = .Trap final exitTrap ∧
        stdoutWords final.host.events = expectedOutput position.input ∧
        host.exited final.host.world = some 0 :=
  terminates_of_room host targetHost (initialStore world) (initialStaticHeap io.literalPool)
    rep streams represented events empty (by rw [limit_toNat]; exact size) valid
    (initialState world).1 rfl (initialState world).2.2 (initialState world).2.1
    (by rw [initial_top, initial_memoryCap]; exact processMemory_le) accepted

/-- For every input of more than 50,000,000 bytes, under StreamFold's host assumptions, a Talos
host that satisfies the import specifications, and a host that accepts the exit status
`tooLong`, the compiled command from its initial store exits with status `tooLong`, 22, after
writing nothing. -/
theorem initial_exits_long {World : Type} (host : Host World)
    (targetHost : HostEnv (Observed World)) (world : Observed World)
    (rep : StreamPosition → World → Prop) (streams : StreamHost host rep)
    {position : StreamPosition} (represented : rep position world.world)
    (events : world.events = []) (empty : position.output = [])
    (size : 50000000 < position.input.length)
    (valid : targetHost.Satisfies module (hostSpec host))
    (accepted : ExitAccepted host rep tooLong) :
    ∃ bound, ∀ fuel ≥ bound, ∃ final,
      run fuel module startIndex (initialStore world) [] targetHost = .Trap final exitTrap ∧
        stdoutWords final.host.events = [] ∧ host.exited final.host.world = some tooLong :=
  exits_long_of_room host targetHost (initialStore world) (initialStaticHeap io.literalPool)
    rep streams represented events empty (by rw [limit_toNat]; exact size) valid
    (initialState world).1 rfl (initialState world).2.2 (initialState world).2.1
    (by rw [initial_top, initial_memoryCap]; exact processMemory_le) accepted

/-- One byte sequence encodes the module, decodes to it, and is a valid binary, and the module
satisfies `initial_terminates` and `initial_exits_long`. -/
theorem terminates_bytes : ∃ bytes,
    Encoding.encode module = .ok bytes ∧ Encoding.decode bytes = .ok module ∧
      Encoding.ValidBinary bytes ∧ (type_of% @initial_terminates) ∧
      (type_of% @initial_exits_long) := by
  obtain ⟨bytes, encoded, decoded, valid, _⟩ := command.bytes
  exact ⟨bytes, encoded, decoded, valid, @initial_terminates, @initial_exits_long⟩

end Demos.Rcv.Process
