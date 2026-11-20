import Verified.Shim
import LeanExe.A64.Proof.WithMachine
import LeanExe.A64.Proof.WasiStubs
import LeanExe.A64.Proof.WasiLaunch

/-!
The A64 binding of the shim: the process of the Linux call layer's binding as the machine of the
A64 simulation under the shim's environment `linuxEnv arm64Flags`.  `shimLayout area G` places the
guest's byte 0 4096 bytes above the area at `area`, where the A64 back end keeps the memory's
bytes, and the scratch's timespec, `open_how` record, path buffer, and `statx` record in the
scratch `G`.

`shimMachine` is `withMachine` with the module's code on `modulePlatform L G`, the data segment
without the scratch, and the process on `wasiPlatform L sp₀ top`, the data segment and the initial
stack from the initial SP `sp₀` to `top`.  Its store relation places the stack's limit in X18 at
least `scratchSize` bytes above the area's end, so that a stub's write of the scratch, which lies
there, changes no byte from SP up, as a stub's return requires.  Its relation `TraceRel` between
the shim's world and the process's trace states that the trace holds the startup's events `l₀`
and then the world's layer events, each of which writes within the `size` bytes of linear memory
from the guest's byte 0 or is a `clock_gettime` into the timespec or a `statx` into the `statx`
record (`WritesNative`).  Its memory relation `ScratchHolds` states that the scratch's first word
holds `sp₀`, that the initial stack holds the launch's arguments and environment, and that the
preopen flag and the byte of each descriptor number below 1,024 follow `preopened` and
`openNumbers` of the world's events.  `ScratchHolds` reads only the scratch and bytes from `2^32`
up, which `modulePlatform` leaves out, so the module's code cannot change it
(`ScratchHolds.frame`).  A trap of the shim ends at the trap stub, and an exit, accepted or
rejected, at the exit word `base` with its status in X0, `ShimEnd`.  `errnoOf_lookup` states the
shim's `errnoOf` as the table that the stubs' routine of errnos reads.
-/

namespace Verified.ShimA64

open Wasm LeanExe LeanExe.A64 LeanExe.Wasi Verified.Wasi Verified.Shim

/-- The shim's layout in an executable whose area lies at `area` and whose scratch is `G`. -/
def shimLayout (area : UInt64) (G : Scratch) : ShimLayout :=
  ⟨area + UInt64.ofNat 4096, G.timespec, G.openHow, G.path, G.statx⟩

/-- The output regions of the event `e` lie within the `size` bytes from the guest's byte 0. -/
def WritesLinear (L : ShimLayout) (size : Nat) (e : Linux.Event) : Prop :=
  ∀ g ∈ Linux.outputRegions e.args 0 e.call.params, L.offset g.1 + g.2 ≤ size

theorem WritesLinear.writesWithin {L : ShimLayout} {size : Nat} {e : Linux.Event}
    (h : WritesLinear L size e) : WritesWithin L size e := fun g hg => .inl (h g hg)

/-- The event `e` writes within the `size` bytes from the guest's byte 0, or it is a
`clock_gettime` whose output region is the timespec, or a `statx` whose output region is the
`statx` record. -/
def WritesNative (L : ShimLayout) (size : Nat) (e : Linux.Event) : Prop :=
  WritesLinear L size e ∨ (e.call = Linux.clockGettimeCall ∧
    Linux.outputRegions e.args 0 e.call.params = [(L.timespec, 16)]) ∨
    (e.call = Linux.statxCall ∧ Linux.outputRegions e.args 0 e.call.params = [(L.statx, 256)])

theorem WritesNative.writesWithin {L : ShimLayout} {size : Nat} {e : Linux.Event}
    (h : WritesNative L size e) : WritesWithin L size e := by
  rcases h with h | ⟨-, h⟩ | ⟨-, h⟩
  · exact h.writesWithin
  · intro g hg
    rw [h, List.mem_singleton] at hg
    exact .inr (.inl hg)
  · intro g hg
    rw [h, List.mem_singleton] at hg
    exact .inr (.inr hg)

/-- An event of a call other than `clock_gettime` and `statx` that writes as `WritesNative` admits
writes within the `size` bytes from the guest's byte 0. -/
theorem WritesNative.linear {L : ShimLayout} {size : Nat} {e : Linux.Event}
    (h : WritesNative L size e) (hc : e.call ≠ Linux.clockGettimeCall)
    (hs : e.call ≠ Linux.statxCall) : WritesLinear L size e := by
  rcases h with h | ⟨h, -⟩ | ⟨h, -⟩
  · exact h
  · exact absurd h hc
  · exact absurd h hs

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

/-- The trace `tr` holds the startup's events `l₀` and then the layer events of the world of `h`,
each of which writes within the `size` bytes from the guest's byte 0 or is a `clock_gettime` into
the timespec. -/
def TraceRel (l₀ : List Linux.Event) (L : ShimLayout) (size : Nat) (h : Observed LinuxWorld)
    (tr : List A64.Event) : Prop :=
  tr = (l₀ ++ h.world.events).map A64.Event.sys ∧ ∀ e ∈ h.world.events, WritesNative L size e

/-- The scratch `G` and the initial stack in the memory `mem` after the layer events `events` of
a process that Linux started with the initial SP `sp₀` and the launch `I`: the scratch's first word
holds `sp₀`, the initial stack from `sp₀` to `top` holds `I`'s arguments and environment, the
preopen flag is 1 exactly while descriptor 3 is the preopened directory, and the byte of each
number below `descriptorLimit` is 1 exactly while the shim holds the number. -/
structure ScratchHolds (G : Scratch) (I : Launch) (sp₀ top : UInt64)
    (events : List Linux.Event) (mem : UInt64 → UInt8) : Prop where
  saved : load64 mem G.savedSp = sp₀
  stack : InitialStack I.args I.environ sp₀ top mem
  preopen : mem G.preopen = if preopened I events then 1 else 0
  held : ∀ d < descriptorLimit,
    mem (G.held d) = if UInt64.ofNat d ∈ openNumbers I events then 1 else 0

/-- Two memories that agree outside the Normal memory of `modulePlatform L G` meet `ScratchHolds`
together, when the data segment ends below `2^32` and the scratch below `2^64`. -/
theorem ScratchHolds.frame {L : ElfLayout} {G : Scratch} {I : Launch} {sp₀ top : UInt64}
    {events : List Linux.Event} {m m' : UInt64 → UInt8} (hL : L.area.toNat + L.dataMem ≤ 2 ^ 32)
    (hG : G.base.toNat + scratchSize < 2 ^ 64) (h : ScratchHolds G I sp₀ top events m)
    (hm : ∀ a, (modulePlatform L G).normal a = false → m' a = m a) :
    ScratchHolds G I sp₀ top events m' := by
  have scr : ∀ j < scratchSize, m' (G.base + UInt64.ofNat j) = m (G.base + UInt64.ofNat j) :=
    fun j hj => hm _ (modulePlatform_scratch hj hG)
  refine ⟨?_, h.stack.congr fun a ha => hm a (modulePlatform_high hL ha), ?_, fun d hd => ?_⟩
  · rw [← h.saved]
    exact load64_congr fun k hk => scr k (by unfold scratchSize; omega)
  · rw [← h.preopen]
    exact scr 8 (by decide)
  · rw [← h.held d hd]
    exact scr (16 + d) (by unfold scratchSize; unfold descriptorLimit at hd; omega)

/-- Where a trap of the shim or an exit ends: an accepted exit at the exit word `base` with the
world's exit status in X0, a rejected exit there with status 1, and a trap of the shim at the trap
stub. -/
def ShimEnd (base : UInt64) (S : Shared) (msg : String) (h : Observed LinuxWorld) (c : State) :
    Prop :=
  (msg = exitTrap ∧ ∃ code, h.world.exited = some code ∧ c.pc = base ∧ c.x 0 = code) ∨
    (msg = exitRejected ∧ c.pc = base ∧ c.x 0 = 1) ∨ (msg = shimTrap ∧ c.pc = S.trapUnreachable)

/-- The process with the calls of `LeanExe.Linux.table` and the replies `R` as a machine of the
shim's environment `linuxEnv arm64Flags` with the flat calls `calls`, for an executable with layout
`L` and scratch `G`, the launch `I`, a process that Linux started with the initial SP `sp₀` and the
initial stack below `top`, the startup's events `l₀`, the exit word at `base`, and writes within
`size` bytes of linear memory.  The replies of the world's calls are those of `R` from call
`l₀.length` on. -/
def shimMachine (R : Linux.Replies) (L : ElfLayout) (G : Scratch) (I : Launch) (sp₀ top : UInt64)
    (l₀ : List Linux.Event) (calls : List LeanExe.Wasi.Call) (code : UInt64 → Option UInt32)
    (hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55)
    (hk : ∀ a w i, code a = some w → decode w = some i → i.keepsX17 = true)
    (hk18 : ∀ a w i, code a = some w → decode w = some i → i.keepsX18 = true)
    (hL : L.area.toNat + L.dataMem ≤ 2 ^ 32) (hG : G.base.toNat + scratchSize < 2 ^ 64)
    (base : UInt64) (size : Nat) : Machine (modulePlatform L G) code (Observed LinuxWorld) :=
  withMachine Linux.table R (modulePlatform L G) (wasiPlatform L sp₀ top)
    (modulePlatform_le_wasi L G sp₀ top) code hdom hk hk18 L.area scratchSize
    (TraceRel l₀ (shimLayout L.area G) size)
    (fun h mem => ScratchHolds G I sp₀ top h.world.events mem)
    (fun _ _ _ h hm => h.frame hL hG hm) (ShimEnd base)
    (linuxEnv arm64Flags (shimLayout L.area G) I (fun j => R (l₀.length + j)) calls)

/-- The shim's `errnoOf` is the errno that the stubs' table gives. -/
theorem errnoOf_lookup (x : UInt64) : errnoOf x = errnoLookup errnoTable x := by
  unfold errnoOf
  split <;> rename_i h <;>
    simp_all [errnoLookup, errnoTable, ← UInt64.toNat_inj]

end Verified.ShimA64
