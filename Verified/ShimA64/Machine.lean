import Verified.Shim
import LeanExe.A64.Proof.WithMachine
import LeanExe.A64.Proof.WasiStubs

/-!
The A64 binding of the shim: the process of the Linux call layer's binding as the machine of the
A64 simulation under the shim's stream functions.  The binding covers the stream imports alone, so
its host environment, `streamEnv`, is `linuxEnv F L I replies []` for every open flags `F` and
every launch `I`.  `layoutAt area` places the guest's byte 0 4096 bytes above the area at `area`,
where the A64 back end keeps the memory's bytes, and the scratch's addresses at 0, since the
stream functions use no scratch.  `shimMachine` holds a store as `withMachine` does, with the
relation `TraceRel` between the shim's world and the process's trace: the trace holds the world's
layer events, and each event's output regions lie within the `size` bytes of linear memory from
the guest's byte 0, `WritesLinear`, which excludes the scratch's timespec that `WritesWithin`
admits.  A trap of the shim ends at the trap stub, and an exit, accepted or rejected, at the exit
word `base` with its status in X0, `ShimEnd`.  `errnoOf_lookup` states the shim's `errnoOf` as
the table that the stubs' routine of errnos reads.
-/

namespace Verified.ShimA64

open Wasm LeanExe LeanExe.A64 LeanExe.Wasi Verified.Wasi Verified.Shim

/-- The shim's layout in an executable whose area lies at `area`, with no scratch. -/
def layoutAt (area : UInt64) : ShimLayout := ⟨area + UInt64.ofNat 4096, 0, 0, 0⟩

/-- The shim's stream functions as a host environment. -/
def streamEnv (L : ShimLayout) (replies : Linux.Replies) : HostEnv (Observed LinuxWorld) :=
  { funcs := [readFn L replies, writeFn L replies, exitFn] }

theorem linuxEnv_nil (F : OpenFlags) (L : ShimLayout) (I : Launch) (replies : Linux.Replies) :
    linuxEnv F L I replies [] = streamEnv L replies := rfl

/-- The output regions of the event `e` lie within the `size` bytes from the guest's byte 0. -/
def WritesLinear (L : ShimLayout) (size : Nat) (e : Linux.Event) : Prop :=
  ∀ g ∈ Linux.outputRegions e.args 0 e.call.params, L.offset g.1 + g.2 ≤ size

theorem WritesLinear.writesWithin {L : ShimLayout} {size : Nat} {e : Linux.Event}
    (h : WritesLinear L size e) : WritesWithin L size e := fun g hg => .inl (h g hg)

/-- A read's output region lies within every size that holds its buffer. -/
theorem readEvent_writesLinear (L : ShimLayout) (mem : Mem) (fd : UInt64)
    (pointer capacity : UInt32) (r : Linux.Reply) {size : Nat}
    (fits : pointer.toNat + capacity.toNat ≤ size) :
    WritesLinear L size (readEvent L mem fd pointer capacity r) := by
  intro g hg
  change g ∈ Linux.outputRegions [fd, L.base + pointer.toUInt64, capacity.toUInt64] 0
    Linux.readCall.params at hg
  rw [outputs_read, List.mem_singleton] at hg
  subst hg
  simp only [offset_base, UInt32.toNat_toUInt64]
  exact fits

/-- A write has no output region. -/
theorem writeEvent_writesLinear (L : ShimLayout) (mem : Mem) (fd : UInt64)
    (pointer length : UInt32) (r : Linux.Reply) (size : Nat) :
    WritesLinear L size (writeEvent L mem fd pointer length r) := by
  intro g hg
  have regions := (Linux.regions_write (shimMemory L) mem fd (L.base + pointer.toUInt64)
    length.toUInt64).2
  change g ∈ Linux.outputRegions [fd, L.base + pointer.toUInt64, length.toUInt64] 0
    Linux.writeCall.params at hg
  rw [regions] at hg
  cases hg

/-- The trace `tr` holds the layer events of the world of `h`, the output regions of each of which
lie within the `size` bytes from the guest's byte 0. -/
def TraceRel (L : ShimLayout) (size : Nat) (h : Observed LinuxWorld) (tr : List A64.Event) :
    Prop :=
  tr = h.world.events.map A64.Event.sys ∧ ∀ e ∈ h.world.events, WritesLinear L size e

/-- Where a trap of the shim or an exit ends: an accepted exit at the exit word `base` with the
world's exit status in X0, a rejected exit there with status 1, and a trap of the shim at the trap
stub. -/
def ShimEnd (base : UInt64) (S : Shared) (msg : String) (h : Observed LinuxWorld) (c : State) :
    Prop :=
  (msg = exitTrap ∧ ∃ code, h.world.exited = some code ∧ c.pc = base ∧ c.x 0 = code) ∨
    (msg = exitRejected ∧ c.pc = base ∧ c.x 0 = 1) ∨ (msg = shimTrap ∧ c.pc = S.trapUnreachable)

/-- The process with the calls of `LeanExe.Linux.table` and the replies `R` as a machine of the
shim's stream functions for the area at `area`, the exit word at `base`, and writes within
`size` bytes of linear memory. -/
def shimMachine (R : Linux.Replies) (P : Platform) (code : UInt64 → Option UInt32)
    (hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55)
    (hk : ∀ a w i, code a = some w → decode w = some i → i.keepsX17 = true)
    (area base : UInt64) (size : Nat) : Machine P code (Observed LinuxWorld) :=
  withMachine Linux.table R P code hdom hk area (TraceRel (layoutAt area) size) (ShimEnd base)
    (streamEnv (layoutAt area) R)

/-- The shim's `errnoOf` is the errno that the stubs' table gives. -/
theorem errnoOf_lookup (x : UInt64) : errnoOf x = errnoLookup errnoTable x := by
  unfold errnoOf
  split <;> rename_i h <;>
    simp_all [errnoLookup, errnoTable, ← UInt64.toNat_inj]

end Verified.ShimA64
