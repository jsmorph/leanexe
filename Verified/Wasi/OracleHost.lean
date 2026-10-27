import Verified.Wasi.HostMemory
import Interpreter.Wasm.Host.Registry

/-! A Talos host for the three WASI imports from an oracle that answers each request of an
abstract host.  The imports decode the one-iovec arguments from guest memory, as the contracts of
`hostSpec` describe, ask the oracle for the reply and the next world, place the read payload and
the count in guest memory, and append the event.  `env_satisfies` proves that the environment
satisfies `hostSpec host` whenever every reply of the oracle is permitted by `host`. -/

namespace Verified.Wasi.OracleHost

open Wasm LeanExe.Wasi

/-- A reply and a next world for each read, write, and exit request.  An exit reply of `none`
accepts the exit, and `some message` rejects it with that message. -/
structure Oracle (World : Type) where
  read : World → UInt64 → Transfer LeanExe.Bytes × World
  write : World → Output → LeanExe.Bytes → Transfer UInt64 × World
  exit : World → UInt64 → Option String × World

/-- Every reply of `oracle` is one that `host` permits. -/
structure Oracle.Sound {World : Type} (oracle : Oracle World) (host : Host World) : Prop where
  read : ∀ world capacity,
    host.read world capacity (oracle.read world capacity).1 (oracle.read world capacity).2
  write : ∀ world output bytes,
    host.write world output bytes (oracle.write world output bytes).1
      (oracle.write world output bytes).2
  exit : ∀ world code after, oracle.exit world code = (none, after) → host.exit world code after
  exitTrap : ∀ world code message after, oracle.exit world code = (some message, after) →
    host.exitTrap world code message after

variable {World : Type} (oracle : Oracle World)

def replyCount (reply : Transfer α) (count : UInt32) : UInt32 :=
  match reply with
  | .returned errno _ => if errno = 0 then count else 4294967295
  | .trapped _ _ => 4294967295

/-- The bytes of the oracle's read reply. -/
def readData (world : World) (capacity : UInt64) : List UInt8 :=
  (oracle.read world capacity).1.committed.data.data.toList

def readAfter (before : Store (Observed World)) (pointer capacity count : UInt32) :
    Store (Observed World) :=
  let transition := oracle.read before.host.world capacity.toUInt64
  { before with
    mem := (before.mem.writeBytes pointer.toNat
      (readData oracle before.host.world capacity.toUInt64)).write32 8 count
    host := {
      world := transition.2
      events := before.host.events ++ [.read capacity.toUInt64 transition.1] } }

def readInvoke (before : Store (Observed World)) (args : List Value) : HostResult (Observed World) :=
  match args with
  | [.i32 0, .i32 0, .i32 1, .i32 8] =>
      let pointer := before.mem.read32 0
      let capacity := before.mem.read32 4
      if 16 ≤ before.mem.pages * 65536 ∧
          pointer.toNat + capacity.toNat ≤ before.mem.pages * 65536 ∧
          pointer.toNat + capacity.toNat ≤ 2 ^ 32 ∧
          (capacity = 0 ∨ 16 ≤ pointer.toNat) then
        let transition := oracle.read before.host.world capacity.toUInt64
        let count := UInt32.ofNat (readData oracle before.host.world capacity.toUInt64).length
        let after := readAfter oracle before pointer capacity (replyCount transition.1 count)
        match transition.1 with
        | .returned errno _ => .Return [.i32 errno.toUInt32] after
        | .trapped message _ => .Trap after message
      else .Trap before "host: fd_read memory range is invalid"
  | _ => .Trap before "host: fd_read arguments are invalid"

def writeAfter (before : Store (Observed World)) (output : Output)
    (bytes : LeanExe.Bytes) (count : UInt32) : Store (Observed World) :=
  let transition := oracle.write before.host.world output bytes
  { before with
    mem := before.mem.write32 8 count
    host := {
      world := transition.2
      events := before.host.events ++ [.write output bytes transition.1] } }

def writeOutput (before : Store (Observed World)) (output : Output) : HostResult (Observed World) :=
  let pointer := before.mem.read32 0
  let length := before.mem.read32 4
  if 16 ≤ before.mem.pages * 65536 ∧
      pointer.toNat + length.toNat ≤ before.mem.pages * 65536 ∧
      pointer.toNat + length.toNat ≤ 2 ^ 32 then
    let bytes := bytesOfList (before.mem.readBytes pointer.toNat length.toNat)
    let transition := oracle.write before.host.world output bytes
    let after := writeAfter oracle before output bytes
      (replyCount transition.1 transition.1.committed.toUInt32)
    match transition.1 with
    | .returned errno _ => .Return [.i32 errno.toUInt32] after
    | .trapped message _ => .Trap after message
  else .Trap before "host: fd_write memory range is invalid"

def writeInvoke (before : Store (Observed World)) (args : List Value) : HostResult (Observed World) :=
  match args with
  | [.i32 1, .i32 0, .i32 1, .i32 8] => writeOutput oracle before .stdout
  | [.i32 2, .i32 0, .i32 1, .i32 8] => writeOutput oracle before .stderr
  | _ => .Trap before "host: fd_write arguments are invalid"

def exitInvoke (before : Store (Observed World)) (args : List Value) : HostResult (Observed World) :=
  match args with
  | [.i32 code] =>
      match oracle.exit before.host.world code.toUInt64 with
      | (none, world) => .Trap
          { before with host := { world, events := before.host.events ++ [.exit code.toUInt64] } }
          exitTrap
      | (some message, world) => .Trap
          { before with host :=
            { world, events := before.host.events ++ [.exitTrap code.toUInt64 message] } } message
  | _ => .Trap before "host: proc_exit arguments are invalid"

def readFn : HostFn (Observed World) where
  params := [.i32, .i32, .i32, .i32]
  results := [.i32]
  invoke := readInvoke oracle

def writeFn : HostFn (Observed World) where
  params := [.i32, .i32, .i32, .i32]
  results := [.i32]
  invoke := writeInvoke oracle

def exitFn : HostFn (Observed World) where
  params := [.i32]
  results := []
  invoke := exitInvoke oracle

variable {oracle} {host : Host World}

theorem readData_bound (sound : oracle.Sound host) (world : World) (capacity : UInt64) :
    (readData oracle world capacity).length ≤ capacity.toNat := by
  have bound := (host.read_bound (sound.read world capacity)).1
  simpa only [readData, Array.length_toList, ByteArray.size] using bound

theorem readData_bytes (world : World) (capacity : UInt64) :
    bytesOfList (readData oracle world capacity) = (oracle.read world capacity).1.committed := by
  simp only [readData, bytesOfList_data]

theorem readAfter_frame (sound : oracle.Sound host) (before : Store (Observed World))
    (pointer capacity count : UInt32) :
    GuestFrame before (readAfter oracle before pointer capacity count)
      [ABI.scratch, (pointer.toNat, capacity.toNat)] := by
  let transition := oracle.read before.host.world capacity.toUInt64
  let afterHost : Observed World :=
    { world := transition.2
      events := before.host.events ++ [.read capacity.toUInt64 transition.1] }
  let middle : Store (Observed World) :=
    { before with
      mem := before.mem.writeBytes pointer.toNat (readData oracle before.host.world capacity.toUInt64)
      host := afterHost }
  have first := frame_payload before afterHost pointer.toNat capacity.toNat
    (readData oracle before.host.world capacity.toUInt64)
    (by simpa only [UInt32.toNat_toUInt64] using
      readData_bound sound before.host.world capacity.toUInt64)
  have last := (frame_count middle afterHost count).weaken
    (second := [ABI.scratch, (pointer.toNat, capacity.toNat)]) (by
      intro region member
      obtain rfl := List.mem_singleton.mp member
      exact List.mem_cons_self)
  exact first.trans last

theorem readAfter_at (sound : oracle.Sound host) {before : Store (Observed World)}
    {args : List Value} {pointer capacity : UInt32} (request : ReadRequest before args pointer capacity)
    (count : UInt32) :
    Bytes.At (readAfter oracle before pointer capacity count).mem pointer.toUInt64
      (bytesOfList (readData oracle before.host.world capacity.toUInt64)) := by
  have bound := readData_bound sound before.host.world capacity.toUInt64
  simp only [UInt32.toNat_toUInt64] at bound
  have payload := written_at before.mem pointer (readData oracle before.host.world capacity.toUInt64)
    (by have address := request.address; change pointer.toNat + capacity.toNat ≤ 2 ^ 32 at address; omega)
    (by have memory := request.memory; omega)
  apply at_count payload count
  rcases request.separate with zero | above
  · left
    rw [bytesOfList_size]
    have emptyCap : capacity.toNat = 0 := by rw [zero]; rfl
    omega
  · exact Or.inr above

theorem readAfter_source (sound : oracle.Sound host) {before : Store (Observed World)}
    {pointer capacity count : UInt32} {reply : Transfer LeanExe.Bytes}
    (same : (oracle.read before.host.world capacity.toUInt64).1 = reply) :
    (observedHost host).read before.host capacity.toUInt64 reply
      (readAfter oracle before pointer capacity count).host := by
  refine ⟨?_, ?_⟩
  · rw [← same]
    exact sound.read before.host.world capacity.toUInt64
  · simp only [readAfter, same]

theorem writeAfter_source (sound : oracle.Sound host) {before : Store (Observed World)}
    {output : Output} {bytes : LeanExe.Bytes} {count : UInt32} {reply : Transfer UInt64}
    (same : (oracle.write before.host.world output bytes).1 = reply) :
    (observedHost host).write before.host output bytes reply
      (writeAfter oracle before output bytes count).host := by
  refine ⟨?_, ?_⟩
  · rw [← same]
    exact sound.write before.host.world output bytes
  · simp only [writeAfter, same]

theorem read_contract (sound : oracle.Sound host) (before : Store (Observed World))
    (args : List Value) : readContract host before args (readInvoke oracle before args) := by
  intro pointer capacity request
  rw [request.arguments]
  simp only [readInvoke, request.pointer_eq, request.length_eq]
  rw [ite_eq_left ⟨request.scratch, request.memory, request.address, request.separate⟩]
  cases reply : (oracle.read before.host.world capacity.toUInt64).1 with
  | returned errno committed =>
      simp only [replyCount]
      refine ⟨errno, committed, rfl, readAfter_source sound reply, readAfter_frame sound _ _ _ _, ?_⟩
      intro success
      have actual : committed = bytesOfList (readData oracle before.host.world capacity.toUInt64) := by
        rw [readData_bytes, reply]
        rfl
      rw [actual]
      refine ⟨readAfter_at sound request _, ?_⟩
      simp only [readAfter, success, ite_true, bytesOfList_size]
      exact read32_write32 _ _ _
  | trapped message committed =>
      simp only [replyCount]
      exact ⟨committed, readAfter_source sound reply, readAfter_frame sound _ _ _ _⟩

theorem write_contract (sound : oracle.Sound host) (before : Store (Observed World))
    (args : List Value) : writeContract host before args (writeInvoke oracle before args) := by
  intro output pointer bytes request
  have invoke : writeInvoke oracle before args = writeOutput oracle before output := by
    rw [request.arguments]
    cases output <;> rfl
  rw [invoke]
  have length : (UInt32.ofNat bytes.data.size).toNat = bytes.data.size :=
    UInt32.toNat_ofNat_of_lt' request.size
  simp only [writeOutput, request.pointer_eq, request.length_eq, length]
  rw [ite_eq_left ⟨request.scratch, request.data.memory, request.data.address⟩]
  have decoded : bytesOfList (before.mem.readBytes pointer.toNat bytes.data.size) = bytes := by
    simpa only [UInt32.toNat_toUInt64] using readBytes_value request.data
  rw [decoded]
  cases reply : (oracle.write before.host.world output bytes).1 with
  | returned errno committed =>
      simp only [reply, replyCount, Transfer.committed]
      refine ⟨errno, committed, rfl, writeAfter_source sound reply, frame_count _ _ _, ?_⟩
      intro success
      simp only [writeAfter, success, ite_true]
      exact read32_write32 _ _ _
  | trapped message committed =>
      simp only [reply, replyCount, Transfer.committed]
      exact ⟨committed, writeAfter_source sound reply, frame_count _ _ _⟩

theorem exit_contract (sound : oracle.Sound host) (before : Store (Observed World))
    (args : List Value) : exitContract host before args (exitInvoke oracle before args) := by
  intro code arguments
  rw [arguments]
  simp only [exitInvoke]
  cases transition : oracle.exit before.host.world code.toUInt64 with
  | mk reply world =>
      cases reply with
      | none =>
          refine ⟨frame_host _ _ [], Or.inl ⟨rfl, ?_⟩⟩
          exact ⟨sound.exit _ _ _ transition, rfl⟩
      | some message =>
          refine ⟨frame_host _ _ [], Or.inr ?_⟩
          exact ⟨sound.exitTrap _ _ _ _ transition, rfl⟩

variable (oracle host)

/-- The three imports with the contracts of `hostSpec host`. -/
def registry (sound : oracle.Sound host) : HostRegistry (Observed World) :=
  [{ decl := ABI.imports[0]!, fn := readFn oracle, contract := readContract host,
      sound := read_contract sound },
    { decl := ABI.imports[1]!, fn := writeFn oracle, contract := writeContract host,
      sound := write_contract sound },
    { decl := ABI.imports[2]!, fn := exitFn oracle, contract := exitContract host,
      sound := exit_contract sound }]

def env (sound : oracle.Sound host) (target : Wasm.Module) : HostEnv (Observed World) :=
  (registry oracle host sound).envFor target

theorem env_satisfies (sound : oracle.Sound host) (target : Wasm.Module)
    (imports : target.imports = ABI.imports) :
    (env oracle host sound target).Satisfies target (hostSpec host) := by
  have spec : (registry oracle host sound).specFor target = hostSpec host := by
    have i32 : (ValueType.i32 == ValueType.i32) = true := rfl
    simp [HostRegistry.specFor, imports, registry, HostRegistry.entryFor,
      ImportDecl.matches, ABI.imports, ABI.transferType, ABI.exitType, hostSpec, List.find?, i32]
  rw [← spec]
  exact (registry oracle host sound).envFor_satisfies target

end Verified.Wasi.OracleHost
