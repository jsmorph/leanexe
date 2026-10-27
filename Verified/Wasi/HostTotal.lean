import Verified.Wasi.OracleHost

/-! When `hostSpec host` can be satisfied.  `Host.Total` states that `host` permits a reply to every
read and write request and either accepts or rejects every exit.  A total host has a Talos host
environment satisfying `hostSpec host`, built from an oracle that chooses a permitted reply.
Conversely, every host environment satisfying `hostSpec host` answers each request that the
one-iovec ABI can express with a payload buffer at address 16, so `host` must permit a reply to
every read of capacity at most `2^32 - 16`, every write of at most `2^32 - 16` bytes, and every
exit.  A theorem that assumes `targetHost.Satisfies target (hostSpec host)` is vacuous for a host
without those replies. -/

namespace LeanExe.Wasi

open Wasm Verified.Wasi

/-- Every read, write, and exit request has a reply that `host` permits. -/
structure Host.Total {World : Type} (host : Host World) : Prop where
  read : ∀ world capacity, ∃ reply after, host.read world capacity reply after
  write : ∀ world output bytes, ∃ reply after, host.write world output bytes reply after
  exit : ∀ world code,
    (∃ after, host.exit world code after) ∨ ∃ message after, host.exitTrap world code message after

/-- Every request that the one-iovec ABI can express with its payload at address 16 has a reply
that `host` permits: reads of capacity at most `2^32 - 16`, writes of at most `2^32 - 16` bytes,
and exits with a 32-bit status. -/
structure Host.Answers {World : Type} (host : Host World) : Prop where
  read : ∀ world (capacity : UInt32), capacity.toNat + 16 ≤ 2 ^ 32 →
    ∃ reply after, host.read world capacity.toUInt64 reply after
  write : ∀ world output (bytes : LeanExe.Bytes), bytes.data.size + 16 ≤ 2 ^ 32 →
    ∃ reply after, host.write world output bytes reply after
  exit : ∀ world (code : UInt32), (∃ after, host.exit world code.toUInt64 after) ∨
    ∃ message after, host.exitTrap world code.toUInt64 message after

namespace Host.Total

variable {World : Type} {host : Host World}

open Classical in
/-- An oracle that chooses a permitted reply to each request of a total host. -/
noncomputable def oracle (total : host.Total) : OracleHost.Oracle World where
  read world capacity :=
    (Classical.choose (total.read world capacity),
      Classical.choose (Classical.choose_spec (total.read world capacity)))
  write world output bytes :=
    (Classical.choose (total.write world output bytes),
      Classical.choose (Classical.choose_spec (total.write world output bytes)))
  exit world code :=
    if accepted : ∃ after, host.exit world code after then (none, Classical.choose accepted)
    else
      let rejected : ∃ message after, host.exitTrap world code message after :=
        (total.exit world code).resolve_left accepted
      (some (Classical.choose rejected), Classical.choose (Classical.choose_spec rejected))

theorem oracle_sound (total : host.Total) : total.oracle.Sound host where
  read world capacity := Classical.choose_spec (Classical.choose_spec (total.read world capacity))
  write world output bytes :=
    Classical.choose_spec (Classical.choose_spec (total.write world output bytes))
  exit world code after step := by
    simp only [oracle] at step
    split at step
    · next accepted =>
        cases step
        exact Classical.choose_spec accepted
    · cases step
  exitTrap world code message after step := by
    simp only [oracle] at step
    split at step
    · cases step
    · next accepted =>
        cases step
        exact Classical.choose_spec
          (Classical.choose_spec ((total.exit world code).resolve_left accepted))

/-- A total host has a host environment that satisfies `hostSpec host` for every module with the
three WASI imports. -/
theorem satisfiable (total : host.Total) (target : Wasm.Module)
    (imports : target.imports = ABI.imports) :
    ∃ targetHost : HostEnv (Observed World), targetHost.Satisfies target (hostSpec host) :=
  ⟨OracleHost.env total.oracle host total.oracle_sound target,
    OracleHost.env_satisfies total.oracle host total.oracle_sound target imports⟩

theorem answers (total : host.Total) : host.Answers where
  read world capacity _ := total.read world capacity.toUInt64
  write world output bytes _ := total.write world output bytes
  exit world code := total.exit world code.toUInt64

end Host.Total

namespace Host.Answers

variable {World : Type} {host : Host World}

/-- A store with the world `world`, no events, and the memory `mem`. -/
def requestStore (world : World) (mem : Mem) : Store (Observed World) :=
  { globals := {}, mem, host := ⟨world, []⟩ }

/-- A 4 GiB memory whose scratch words name a payload of `capacity` bytes at address 16. -/
def readMemory (capacity : UInt32) : Mem :=
  ((Mem.empty 65536).write32 0 16).write32 4 capacity

def writeMemory (bytes : LeanExe.Bytes) : Mem :=
  (((Mem.empty 65536).writeBytes 16 bytes.data.data.toList).write32 0 16).write32 4
    (UInt32.ofNat bytes.data.size)

theorem read32_first (mem : Mem) (length : UInt32) :
    ((mem.write32 0 16).write32 4 length).read32 0 = 16 := by
  rw [read32_write32_disjoint _ _ _ _ (by decide), read32_write32]

theorem readRequest (world : World) (capacity : UInt32) (fits : capacity.toNat + 16 ≤ 2 ^ 32) :
    ReadRequest (requestStore world (readMemory capacity)) [.i32 0, .i32 0, .i32 1, .i32 8]
      16 capacity where
  arguments := rfl
  scratch := by change 16 ≤ 65536 * 65536; decide
  pointer_eq := read32_first _ _
  length_eq := read32_write32 _ _ _
  memory := by change 16 + capacity.toNat ≤ 65536 * 65536; omega
  address := by change 16 + capacity.toNat ≤ 2 ^ 32; omega
  separate := Or.inr (by decide)

theorem writeRequest (world : World) (output : Output) (bytes : LeanExe.Bytes)
    (fits : bytes.data.size + 16 ≤ 2 ^ 32) :
    WriteRequest (requestStore world (writeMemory bytes))
      [.i32 output.fd.toUInt32, .i32 0, .i32 1, .i32 8] output 16 bytes where
  arguments := rfl
  scratch := by change 16 ≤ 65536 * 65536; decide
  pointer_eq := read32_first _ _
  length_eq := read32_write32 _ _ _
  size := by omega
  data := by
    have length : bytes.data.data.toList.length = bytes.data.size := by
      simp only [Array.length_toList, ByteArray.size]
    have written := written_at (Mem.empty 65536) 16 bytes.data.data.toList
      (by rw [length]; change 16 + bytes.data.size ≤ 2 ^ 32; omega)
      (by rw [length]; change 16 + bytes.data.size ≤ 65536 * 65536; omega)
    rw [bytesOfList_data] at written
    refine written.frame (memory' := (requestStore world (writeMemory bytes)).mem)
      (Nat.le_of_eq rfl) ?_
    intro index _
    simp only [requestStore, writeMemory]
    rw [write32_bytes_outside _ _ _ (Or.inr (by simp; omega)),
      write32_bytes_outside _ _ _ (Or.inr (by simp; omega))]
    rfl

/-- Every host environment that satisfies `hostSpec host` for a module with the three WASI
imports answers each request that the one-iovec ABI expresses with its payload at address 16. -/
theorem of_satisfies {targetHost : HostEnv (Observed World)} {target : Wasm.Module}
    (valid : targetHost.Satisfies target (hostSpec host)) (imports : target.imports = ABI.imports) :
    host.Answers where
  read world capacity fits := by
    obtain ⟨fn, _, call⟩ := valid.lookup_contract (i := 0) (by rw [imports]; decide) (hostSpec_read host)
    have contract := call (requestStore world (readMemory capacity)) [.i32 0, .i32 0, .i32 1, .i32 8]
      16 capacity (readRequest world capacity fits)
    generalize fn.invoke _ _ = result at contract
    cases result with
    | Return values after =>
        obtain ⟨_, _, _, relation, _⟩ := contract
        exact ⟨_, _, relation.1⟩
    | Trap after message =>
        obtain ⟨_, relation, _⟩ := contract
        exact ⟨_, _, relation.1⟩
    | Throw _ _ _ => exact contract.elim
  write world output bytes fits := by
    obtain ⟨fn, _, call⟩ := valid.lookup_contract (i := 1) (by rw [imports]; decide) (hostSpec_write host)
    have contract := call (requestStore world (writeMemory bytes))
      [.i32 output.fd.toUInt32, .i32 0, .i32 1, .i32 8] output 16 bytes
      (writeRequest world output bytes fits)
    generalize fn.invoke _ _ = result at contract
    cases result with
    | Return values after =>
        obtain ⟨_, _, _, relation, _⟩ := contract
        exact ⟨_, _, relation.1⟩
    | Trap after message =>
        obtain ⟨_, relation, _⟩ := contract
        exact ⟨_, _, relation.1⟩
    | Throw _ _ _ => exact contract.elim
  exit world code := by
    obtain ⟨fn, _, call⟩ := valid.lookup_contract (i := 2) (by rw [imports]; decide) (hostSpec_exit host)
    have contract := call (requestStore world (readMemory 0)) [.i32 code] code rfl
    generalize fn.invoke _ _ = result at contract
    cases result with
    | Trap after message =>
        rcases contract.2 with ⟨_, accepted⟩ | rejected
        · exact Or.inl ⟨_, accepted.1⟩
        · exact Or.inr ⟨_, _, rejected.1⟩
    | Return _ _ => exact contract.elim
    | Throw _ _ _ => exact contract.elim

end Host.Answers

end LeanExe.Wasi
