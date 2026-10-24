import Verified.Wasi.ScriptHostABI

namespace Verified.Wasi.ScriptHost

open Wasm LeanExe.Wasi

theorem readAfter_frame (before : Store (Observed World)) (pointer capacity count : UInt32) :
    GuestFrame before (readAfter before pointer capacity count)
      [ABI.scratch, (pointer.toNat, capacity.toNat)] := by
  let transition := readStep before.host.world capacity.toUInt64
  let afterHost : Observed World :=
    { world := transition.2
      events := before.host.events ++ [.read capacity.toUInt64 transition.1] }
  let middle : Store (Observed World) :=
    { before with
      mem := before.mem.writeBytes pointer.toNat (readData before.host.world capacity.toUInt64)
      host := afterHost }
  have first := frame_payload before afterHost pointer.toNat capacity.toNat
    (readData before.host.world capacity.toUInt64)
    (readData_bound before.host.world capacity.toUInt64)
  have last := (frame_count middle afterHost count).weaken
    (second := [ABI.scratch, (pointer.toNat, capacity.toNat)]) (by
      intro region member
      obtain rfl := List.mem_singleton.mp member
      exact List.mem_cons_self)
  exact first.trans last

theorem readAfter_at {before : Store (Observed World)} {args : List Value}
    {pointer capacity : UInt32} (request : ReadRequest before args pointer capacity) (count : UInt32) :
    Bytes.At (readAfter before pointer capacity count).mem pointer.toUInt64
      (bytesOfList (readData before.host.world capacity.toUInt64)) := by
  have bound := readData_bound before.host.world capacity.toUInt64
  simp only [UInt32.toNat_toUInt64] at bound
  have payload := written_at before.mem pointer (readData before.host.world capacity.toUInt64)
    (by have address := request.address; change pointer.toNat + capacity.toNat ≤ 2 ^ 32 at address; omega)
    (by have memory := request.memory; omega)
  apply at_count payload count
  rcases request.separate with zero | above
  · left
    rw [bytesOfList_size]
    have emptyCap : capacity.toNat = 0 := by rw [zero]; rfl
    omega
  · exact Or.inr above

theorem readAfter_source {before : Store (Observed World)} {pointer capacity count : UInt32}
    {reply : Transfer LeanExe.Bytes}
    (same : (readStep before.host.world capacity.toUInt64).1 = reply) :
    (observedHost sourceHost).read before.host capacity.toUInt64 reply
      (readAfter before pointer capacity count).host := by
  refine ⟨?_, ?_⟩
  · exact Prod.ext same rfl
  · simp only [readAfter, same]

theorem writeAfter_source {before : Store (Observed World)} {output : Output}
    {bytes : LeanExe.Bytes} {count : UInt32} {reply : Transfer UInt64}
    (same : (writeStep before.host.world output bytes).1 = reply) :
    (observedHost sourceHost).write before.host output bytes reply
      (writeAfter before output bytes count).host := by
  refine ⟨?_, ?_⟩
  · exact Prod.ext same rfl
  · simp only [writeAfter, same]

theorem read_contract (before : Store (Observed World)) (args : List Value) :
    readContract sourceHost before args (readInvoke before args) := by
  intro pointer capacity request
  rw [request.arguments]
  simp only [readInvoke, request.pointer_eq, request.length_eq]
  rw [ite_eq_left ⟨request.scratch, request.memory, request.address, request.separate⟩]
  cases reply : (readStep before.host.world capacity.toUInt64).1 with
  | returned errno committed =>
      simp only [replyCount]
      refine ⟨errno, committed, rfl, readAfter_source reply, readAfter_frame _ _ _ _, ?_⟩
      intro success
      have actual : committed = bytesOfList (readData before.host.world capacity.toUInt64) := by
        have same : (readStep before.host.world capacity.toUInt64).1.committed =
            bytesOfList (readData before.host.world capacity.toUInt64) := by
          simp only [readStep, Policy.committed]
        simpa only [reply, Transfer.committed] using same
      rw [actual]
      refine ⟨readAfter_at request _, ?_⟩
      simp only [readAfter, success, ite_true, bytesOfList_size]
      exact read32_write32 _ _ _
  | trapped message committed =>
      simp only [replyCount]
      exact ⟨committed, readAfter_source reply, readAfter_frame _ _ _ _⟩

theorem write_contract (before : Store (Observed World)) (args : List Value) :
    writeContract sourceHost before args (writeInvoke before args) := by
  intro output pointer bytes request
  have invoke : writeInvoke before args = writeOutput before output := by
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
  cases reply : (writeStep before.host.world output bytes).1 with
  | returned errno committed =>
      simp only [reply, replyCount, Transfer.committed]
      refine ⟨errno, committed, rfl, writeAfter_source reply, frame_count _ _ _, ?_⟩
      intro success
      simp only [writeAfter, success, ite_true]
      exact read32_write32 _ _ _
  | trapped message committed =>
      simp only [reply, replyCount, Transfer.committed]
      exact ⟨committed, writeAfter_source reply, frame_count _ _ _⟩

theorem exit_contract (before : Store (Observed World)) (args : List Value) :
    exitContract sourceHost before args (exitInvoke before args) := by
  intro code arguments
  rw [arguments]
  simp only [exitInvoke]
  cases transition : exitStep before.host.world code.toUInt64 with
  | mk reply world =>
      cases reply with
      | none =>
          refine ⟨frame_host _ _ [], Or.inl ⟨rfl, ?_⟩⟩
          exact ⟨transition, rfl⟩
      | some message =>
          refine ⟨frame_host _ _ [], Or.inr ?_⟩
          exact ⟨transition, rfl⟩

def registry : HostRegistry (Observed World) :=
  [{ decl := ABI.imports[0]!, fn := readFn, contract := readContract sourceHost,
      sound := read_contract },
    { decl := ABI.imports[1]!, fn := writeFn, contract := writeContract sourceHost,
      sound := write_contract },
    { decl := ABI.imports[2]!, fn := exitFn, contract := exitContract sourceHost,
      sound := exit_contract }]

def env (target : Wasm.Module) : HostEnv (Observed World) := registry.envFor target

theorem env_satisfies (target : Wasm.Module) (imports : target.imports = ABI.imports) :
    (env target).Satisfies target (hostSpec sourceHost) := by
  have spec : registry.specFor target = hostSpec sourceHost := by
    have i32 : (ValueType.i32 == ValueType.i32) = true := rfl
    simp [HostRegistry.specFor, imports, registry, HostRegistry.entryFor,
      ImportDecl.matches, ABI.imports, ABI.transferType, ABI.exitType, hostSpec, List.find?, i32]
  rw [← spec]
  exact registry.envFor_satisfies target

end Verified.Wasi.ScriptHost
