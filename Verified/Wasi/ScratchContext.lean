import Verified.Wasi.After
import Verified.Wasi.GuestFrame

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime

namespace Holds

variable {context : List Ty} {env : Env context} {slots : List Slot}
  {live sel : Nat → Bool} {base : Nat} {heap heap' : Heap}
  {store store' : Store Unit} {locals locals' : Locals} {fresh : List (Nat × Nat)}

theorem ApartFrom.agree (h : Holds env slots live base heap store locals)
    {region : Nat × Nat} (apart : ApartFrom env slots sel store locals region)
    (frame : Frame base locals locals') (selected : ∀ i, sel i = true → live i = true) :
    ApartFrom env slots sel store locals' region := by
  intro type x hSelected words held width block member
  exact apart type x hSelected words
    ((h.hold_agree frame (selected _ hSelected) width).mp held) width block member

theorem ApartFrom.transfer (h : Holds env slots live base heap store locals)
    {region : Nat × Nat} {keep : Nat × Nat → Prop}
    (apart : ApartFrom env slots sel store locals region)
    (step : Step heap store keep heap' store' fresh) (frame : Frame base locals locals')
    (selected : ∀ i, sel i = true → live i = true)
    (kept : ∀ (type : Ty) (x : Var context type), sel x.index = true →
      ∀ words, LocalsHold locals (slots.getD x.index default).loc type.types words →
      words.length = type.width →
      ∀ block ∈ type.regions (slots.getD x.index default).mode
        store words (env.get x), keep block) :
    ApartFrom env slots sel store' locals' region := by
  intro type x hSelected words held width block member
  have original := (h.hold_agree frame (selected _ hSelected) width).mp held
  have same := (h.regions_after step (selected _ hSelected) original width
    (kept type x hSelected words original width)).1
  rw [same] at member
  exact apart type x hSelected words original width block member

theorem ApartFrom.push {type : Ty} {value : type.denote} {slot : Slot}
    {selected : Nat → Bool} {words : List Value} {region : Nat × Nat}
    (apart : ApartFrom env slots (fun i => selected (i + 1)) store locals region)
    (held : LocalsHold locals slot.loc type.types words) (width : words.length = type.width)
    (head : selected 0 = true →
      ∀ block ∈ type.regions slot.mode store words value, regionsDisjoint region block) :
    ApartFrom (.cons value env) (slot :: slots) selected store locals region := by
  intro other x hSelected values hValues hWidth block member
  cases x with
  | here =>
      change LocalsHold locals slot.loc type.types values at hValues
      obtain rfl := LocalsHold.unique hValues held (hWidth.trans width.symm)
      exact head hSelected block member
  | there x =>
      exact apart other x hSelected values hValues hWidth block member

theorem ApartFrom.pop {type : Ty} {value : type.denote} {slot : Slot}
    {selected : Nat → Bool} {region : Nat × Nat}
    (apart : ApartFrom (.cons value env) (slot :: slots) selected store locals region) :
    ApartFrom env slots (fun i => selected (i + 1)) store locals region :=
  fun type x hSelected => apart type (.there x) hSelected

theorem KeepDying.transfer_kept (h : Holds env slots live base heap store locals)
    {liveIn liveOut : Nat → Bool} {region : Nat × Nat} {keep : Nat × Nat → Prop}
    (step : Step heap store keep heap' store' fresh) (frame : Frame base locals locals')
    (selected : ∀ i, liveIn i = true → liveOut i = false → live i = true)
    (kept : ∀ (type : Ty) (x : Var context type),
      liveIn x.index = true → liveOut x.index = false → ∀ words,
      LocalsHold locals (slots.getD x.index default).loc type.types words →
      words.length = type.width →
      ∀ block ∈ type.regions (slots.getD x.index default).mode
        store words (env.get x), keep block)
    (apart : KeepDying env slots liveIn liveOut store locals region) :
    KeepDying env slots liveIn liveOut store' locals' region := by
  intro type x hIn hOut owned words held width block member
  have original := (h.hold_agree frame (selected _ hIn hOut) width).mp held
  have same := (h.regions_after step (selected _ hIn hOut) original width
    (kept type x hIn hOut words original width)).1
  simp only [Ty.regions, owned] at same
  rw [same] at member
  exact apart type x hIn hOut owned words original width block member

theorem step_scratch (h : Holds env slots live base heap store locals)
    (apart : ApartFrom env slots live store locals Wasi.ABI.scratch)
    (step : Step heap store (fun region => regionsDisjoint region Wasi.ABI.scratch)
      heap' store' fresh) (frame : Frame base locals locals') :
    Holds env slots live base heap' store' locals' :=
  (h.step step fun type x hLive words held width block member =>
    regionsDisjoint_symm (apart type x hLive words held width block member)).agree frame

theorem step_scratch_dying {liveIn : Nat → Bool}
    (h : Holds env slots liveIn base heap store locals)
    (apart : ApartFrom env slots live store locals Wasi.ABI.scratch)
    (selected : ∀ i, live i = true → liveIn i = true)
    (step : Step heap store
      (fun region => KeepDying env slots liveIn live store locals region ∧
        regionsDisjoint region Wasi.ABI.scratch) heap' store' fresh)
    (frame : Frame base locals locals') :
    Holds env slots live base heap' store' locals' :=
  ((h.live_mono selected).step step fun type x hLive words held width block member =>
    ⟨h.keepDying selected hLive held width block member,
      regionsDisjoint_symm (apart type x hLive words held width block member)⟩).agree frame

end Holds

namespace Wasi

theorem GuestFrame.scratchHolds {World : Type} {context : List Ty} {env : Env context}
    {slots : List Slot} {live : Nat → Bool} {base : Nat} {heap : Heap}
    {before after : Store World} {locals locals' : Locals}
    (frame : GuestFrame before after [ABI.scratch])
    (at_ : heap.At (PureTransport.erase before))
    (vars : Holds env slots live base heap (PureTransport.erase before) locals)
    (apart : Holds.ApartFrom env slots live (PureTransport.erase before) locals ABI.scratch)
    (localsFrame : Frame base locals locals') :
    Holds env slots live base heap (PureTransport.erase after) locals' :=
  vars.step_scratch apart (frame.scratchStep at_) localsFrame

theorem bytes_scratch {heap : Heap} {store : Store Unit} {root length : UInt64}
    {bytes : LeanExe.Bytes} (rep : Bytes.Rep heap store root length bytes) :
    ∀ region ∈ Bytes.regions store root, regionsDisjoint ABI.scratch region := by
  intro region member
  rcases rep.buffer with ⟨rfl, _⟩ | buffer
  · simp [Bytes.regions] at member
  · simp only [Bytes.regions, ite_eq_right buffer.nonzero, List.mem_singleton] at member
    subst region
    have := buffer.object.base
    left
    dsimp only [ABI.scratch, block]
    omega

end Wasi
end Verified
