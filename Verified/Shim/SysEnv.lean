import Verified.Shim.Env
import Verified.Wasi.OracleSys

/-!
What the shim's flat calls share.  A flat call's function checks the request, makes its layer
calls, and gives `sysAnswer`: the store with the memory after the calls, the layer events and the
WASI event appended, and the reply's errno or trap.  `sys_contract_of` reduces the contract of
`sysContract` for such an answer to three facts about the call: the shim's step in the host's
relation, a memory that differs from the store's only in the request's output regions, and on
errno 0 the outputs in their regions.  `placeReply` writes the result words of a successful reply,
`MemFrame` states which bytes a memory keeps, and `argsFit_takes` reads a request's arguments off
its description.
-/

namespace Verified.Shim

open Wasm LeanExe LeanExe.Wasi Verified.Wasi

/-- The result of a flat call: the errno of a returned reply with the store `after`, or a trap of
the reply's message with it. -/
def sysResult (after : Store (Observed LinuxWorld)) :
    Transfer (List Bytes) → HostResult (Observed LinuxWorld)
  | .returned errno _ => .Return [.i32 errno.toUInt32] after
  | .trapped message _ => .Trap after message

/-- The result of the flat call `call` with the arguments `request` that the shim answered with
the memory `mem`, the layer events `l`, and the reply `reply`. -/
def sysAnswer (before : Store (Observed LinuxWorld)) (call : Call) (request : List Arg)
    (mem : Mem) (l : List Linux.Event) (reply : Transfer (List Bytes)) :
    HostResult (Observed LinuxWorld) :=
  sysResult (answered before mem l (.sys call request reply)) reply

/-- `mem` with the outputs that `place` gives for a reply of errno 0 written at their pointers,
and `mem` for any other reply. -/
def placeReply (mem : Mem) (place : List Bytes → List (UInt32 × Bytes)) :
    Transfer (List Bytes) → Mem
  | .returned errno outputs => if errno = 0 then placeAll mem (place outputs) else mem
  | .trapped _ _ => mem

/-- `mem` has the pages of `before` and its bytes outside the regions `writable`. -/
def MemFrame (before mem : Mem) (writable : List (Nat × Nat)) : Prop :=
  mem.pages = before.pages ∧
    ∀ address, (∀ region ∈ writable, ¬InRange address region) → mem.bytes address = before.bytes address

theorem MemFrame.refl (mem : Mem) (writable : List (Nat × Nat)) : MemFrame mem mem writable :=
  ⟨rfl, fun _ _ => rfl⟩

theorem MemFrame.trans {first second third : Mem} {writable : List (Nat × Nat)}
    (h : MemFrame first second writable) (h' : MemFrame second third writable) :
    MemFrame first third writable :=
  ⟨h'.1.trans h.1, fun address outside => (h'.2 address outside).trans (h.2 address outside)⟩

/-- A region inside one of `writable`. -/
def Inside (writable : List (Nat × Nat)) (pointer size : Nat) : Prop :=
  ∃ region ∈ writable, region.1 ≤ pointer ∧ pointer + size ≤ region.1 + region.2

theorem MemFrame.writeBytes (mem : Mem) (pointer : Nat) (bytes : List UInt8)
    {writable : List (Nat × Nat)} (inside : Inside writable pointer bytes.length) :
    MemFrame mem (mem.writeBytes pointer bytes) writable := by
  obtain ⟨region, member, low, high⟩ := inside
  refine ⟨rfl, fun address outside => ?_⟩
  have apart := outside region member
  simp only [InRange] at apart
  simp only [Mem.writeBytes]
  rw [dite_eq_right (by omega)]

theorem MemFrame.placeAll (mem : Mem) {places : List (UInt32 × Bytes)} {writable : List (Nat × Nat)}
    (inside : ∀ place ∈ places, Inside writable place.1.toNat place.2.data.size) :
    MemFrame mem (placeAll mem places) writable := by
  refine ⟨placeAll_pages _ _, fun address outside => placeAll_outside _ _ _ fun place member => ?_⟩
  obtain ⟨region, regionMember, low, high⟩ := inside place member
  have apart := outside region regionMember
  simp only [InRange, placeSpan] at apart ⊢
  omega

theorem MemFrame.placeReply (mem : Mem) (place : List Bytes → List (UInt32 × Bytes))
    {writable : List (Nat × Nat)} (reply : Transfer (List Bytes))
    (inside : ∀ outputs, reply = .returned 0 outputs →
      ∀ placed ∈ place outputs, Inside writable placed.1.toNat placed.2.data.size) :
    MemFrame mem (placeReply mem place reply) writable := by
  cases reply with
  | returned errno outputs =>
    by_cases zero : errno = 0
    · subst zero
      simp only [Verified.Shim.placeReply, ↓reduceIte]
      exact MemFrame.placeAll mem (inside outputs rfl)
    · simp only [Verified.Shim.placeReply, zero, ↓reduceIte]
      exact MemFrame.refl mem writable
  | trapped => exact MemFrame.refl mem writable

theorem placeReply_returned (mem : Mem) (place : List Bytes → List (UInt32 × Bytes))
    (outputs : List Bytes) : placeReply mem place (.returned 0 outputs) = placeAll mem (place outputs) :=
  rfl

/-- The contract of a flat call for a function whose result for every request that the contract
admits is an answer of the shim, from the shim's step in the host's relation, the memory's frame,
and the outputs in their regions on errno 0. -/
theorem sys_contract_of {F : OpenFlags} {L : ShimLayout} {I : Launch} {replies : Linux.Replies}
    {call : Call} {before : Store (Observed LinuxWorld)} {args : List Value}
    {result : HostResult (Observed LinuxWorld)}
    (answer : ∀ request pointers,
      SysRequest before args call request pointers (shimReported I before.host.world.reports call) →
      let regions := outputRegions call.params (shimReported I before.host.world.reports call)
        request pointers
      ∃ mem l reply, result = sysAnswer before call request mem l reply ∧
        ShimStep F L I replies before.host.world (.sys call request reply)
          (before.host.world.answer l (.sys call request reply)) ∧
        MemFrame before.mem mem (regions.map Region.span) ∧
        ∀ outputs, reply = .returned 0 outputs → ShownAt mem regions outputs) :
    sysContract (linuxHost F L I replies) call before args result := by
  intro request pointers valid
  obtain ⟨mem, l, reply, rfl, step, frame, shown⟩ := answer request pointers valid
  have guest : GuestFrame before (answered before mem l (.sys call request reply))
      ((outputRegions call.params (shimReported I before.host.world.reports call) request
        pointers).map Region.span) := ⟨rfl, frame.1, frame.2⟩
  cases reply with
  | returned errno outputs =>
    dsimp only [sysAnswer, sysResult]
    refine ⟨errno, outputs, rfl, ⟨step, rfl⟩, guest, fun zero => ?_⟩
    subst zero
    exact shown outputs rfl
  | trapped message outputs =>
    dsimp only [sysAnswer, sysResult]
    exact ⟨outputs, ⟨step, rfl⟩, guest⟩

/-- A step that makes no layer call. -/
theorem shimStep_none {F : OpenFlags} {L : ShimLayout} {I : Launch} {replies : Linux.Replies}
    {w : LinuxWorld} {e : Wasi.Event} (image : Image F L I w.events e []) :
    ShimStep F L I replies w e (w.answer [] e) :=
  by
  refine ⟨[], image, ?_, ?_, rfl⟩
  · trivial
  · intro x member
    cases member

/-- A step that makes one layer call. -/
theorem shimStep_one {F : OpenFlags} {L : ShimLayout} {I : Launch} {replies : Linux.Replies}
    {w : LinuxWorld} {e : Wasi.Event} {x : Linux.Event} (image : Image F L I w.events e [x])
    (carries : Carries (replies w.events.length) x) (within : WritesWithin L (2 ^ 32) x) :
    ShimStep F L I replies w e (w.answer [x] e) := by
  refine ⟨[x], image, ⟨carries, trivial⟩, fun y member => ?_, rfl⟩
  obtain rfl := List.mem_singleton.mp member
  exact within

/-- A call event without an output region writes within every bound. -/
theorem writesWithin_none {L : ShimLayout} {size : Nat} {x : Linux.Event}
    (none : Linux.outputRegions x.args 0 x.call.params = []) : WritesWithin L size x := by
  intro g member
  rw [none] at member
  cases member

theorem argsFit_takes {p : Param} {ps : List Param} {args : List Arg}
    (h : argsFit (p :: ps) args = true) (takes : p.takesArg = true) :
    ∃ a rest, args = a :: rest ∧ argFits p a = true ∧ argsFit ps rest = true := by
  cases args with
  | nil => simp [argsFit, takes] at h
  | cons a rest =>
    simp only [argsFit, takes, ↓reduceIte, Bool.and_eq_true] at h
    exact ⟨a, rest, rfl, h⟩

theorem argsFit_nil {args : List Arg} (h : argsFit [] args = true) : args = [] := by
  simpa [argsFit] using h

/-- A reply whose outputs on errno 0 the shim writes at the request's shown regions, which lie in
memory below `2^32` and apart from one another, changes only those regions and leaves each output
in its region.  `place` gives the outputs' pointers as `OracleSys.shownPlaces` does. -/
theorem placed {mem : Mem} {regions : List Region} {reply : Transfer (List Bytes)}
    {place : List Bytes → List (UInt32 × Bytes)}
    (shape : ReplyShape ((regions.filter (·.shown)).map (·.size)) reply)
    (agree : ∀ outputs, outputs.map (·.data.size) = (regions.filter (·.shown)).map (·.size) →
      place outputs = OracleSys.shownPlaces regions outputs)
    (bounds : ∀ region ∈ regions, region.pointer.toNat + region.size ≤ mem.pages * 65536 ∧
      region.pointer.toNat + region.size < 2 ^ 32)
    (apart : (regions.map Region.span).Pairwise LeanExe.Runtime.regionsDisjoint) :
    MemFrame mem (placeReply mem place reply) (regions.map Region.span) ∧
      ∀ outputs, reply = .returned 0 outputs →
        ShownAt (placeReply mem place reply) regions outputs := by
  have covered : ∀ outputs, reply = .returned 0 outputs →
      ∀ placed ∈ place outputs, ∃ region ∈ regions, region.span = placeSpan placed := by
    intro outputs same placed member
    subst same
    rw [agree outputs shape.1] at member
    have inSpans : placeSpan placed ∈ (regions.filter (·.shown)).map Region.span := by
      rw [← OracleSys.shownPlaces_spans regions outputs shape.1]
      exact List.mem_map.mpr ⟨placed, member, rfl⟩
    obtain ⟨region, inFilter, eq⟩ := List.mem_map.mp inSpans
    exact ⟨region, List.mem_of_mem_filter inFilter, eq⟩
  constructor
  · apply MemFrame.placeReply
    intro outputs same placed member
    obtain ⟨region, regionMember, eq⟩ := covered outputs same placed member
    refine ⟨region.span, List.mem_map.mpr ⟨region, regionMember, rfl⟩, ?_⟩
    simp only [Region.span, placeSpan, Prod.mk.injEq] at eq ⊢
    omega
  · intro outputs same
    have sizes := shape.1
    rw [same] at sizes
    subst same
    rw [placeReply_returned, agree outputs sizes]
    have spans := OracleSys.shownPlaces_spans regions outputs sizes
    apply OracleSys.shownAt_of
    · simpa [Transfer.committed] using congrArg List.length sizes
    · apply placeAll_at
      · rw [spans]
        exact apart.sublist (List.filter_sublist.map _)
      · intro placed member
        obtain ⟨region, regionMember, eq⟩ := covered outputs rfl placed
          (by rw [agree outputs sizes]; exact member)
        have bound := bounds region regionMember
        simp only [placeSpan, Region.span, Prod.mk.injEq] at eq
        rw [← eq.1, ← eq.2]
        exact ⟨Nat.le_of_lt bound.2, bound.1⟩

/-- One output written at a single shown region. -/
theorem placed_one {mem : Mem} {pointer : UInt32} {size align : Nat}
    {reply : Transfer (List Bytes)} (shape : ReplyShape [size] reply)
    (memory : pointer.toNat + size ≤ mem.pages * 65536) (address : pointer.toNat + size < 2 ^ 32) :
    MemFrame mem (placeReply mem (fun outputs => [(pointer, outputs.headD Bytes.empty)]) reply)
        (([⟨pointer, size, align, true⟩] : List Region).map Region.span) ∧
      ∀ outputs, reply = .returned 0 outputs →
        ShownAt (placeReply mem (fun outputs => [(pointer, outputs.headD Bytes.empty)]) reply)
          [⟨pointer, size, align, true⟩] outputs := by
  refine placed shape (fun outputs sizes => ?_) ?_ (List.pairwise_singleton _ _)
  · rcases outputs with _ | ⟨output, _ | ⟨other, rest⟩⟩
    · simp at sizes
    · rfl
    · simp at sizes
  · intro region member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨memory, address⟩

theorem shownAt_single {mem : Mem} {pointer : UInt32} {size align : Nat} {output : Bytes}
    (h : Bytes.At mem pointer.toUInt64 output) :
    ShownAt mem [⟨pointer, size, align, true⟩] [output] := by
  show Bytes.At mem pointer.toUInt64 output ∧ ShownAt mem [] []
  exact ⟨h, rfl⟩

theorem at_nil {mem : Mem} {pointer : Nat} (address : pointer ≤ 2 ^ 32)
    (memory : pointer ≤ mem.pages * 65536) : Bytes.At mem (UInt64.ofNat pointer) (bytesOfList []) := by
  have root : (UInt64.ofNat pointer).toNat = pointer :=
    UInt64.toNat_ofNat_of_lt' (show pointer < 2 ^ 64 by omega)
  refine ⟨?_, ?_, fun i bound => by simp at bound⟩
  · simp only [root, bytesOfList_size, List.length_nil, Nat.add_zero]
    omega
  · simp only [root, bytesOfList_size, List.length_nil, Nat.add_zero]
    exact memory

end Verified.Shim
