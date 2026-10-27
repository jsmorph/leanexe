import Verified.Bytes.LiteralFrame
import Verified.After

namespace Verified.Bytes.LiteralPool

open Wasm LeanExe.Pipeline LeanExe.Runtime

structure Safe (pool : LiteralPool) {Γ : List Ty} (env : Env Γ) (slots : List Slot)
    (live : Nat → Bool) (heap : Heap) (store : Store Unit) (s : Locals) : Prop where
  static : pool.Static heap store
  apart : ∀ region ∈ pool.regions,
    Holds.KeepDying env slots live (fun _ => false) store s region

namespace Safe

theorem empty (address : Nat) {Γ : List Ty} (env : Env Γ) (slots : List Slot)
    (live : Nat → Bool) (heap : Heap) (store : Store Unit) (s : Locals) :
    Safe ⟨address, []⟩ env slots live heap store s :=
  ⟨Static.empty _ _ _, by simp [regions, payload]⟩

theorem mono {pool : LiteralPool} {Γ : List Ty} {env : Env Γ} {slots : List Slot}
    {live live' : Nat → Bool} {heap : Heap} {store : Store Unit} {s : Locals}
    (h : Safe pool env slots live heap store s)
    (hLive : ∀ i, live' i = true → live i = true) :
    Safe pool env slots live' heap store s :=
  ⟨h.static, fun region hRegion => (h.apart region hRegion).mono
    fun i hi _ => ⟨hLive i hi, rfl⟩⟩

theorem values {pool : LiteralPool} {Γ : List Ty} {env : Env Γ} {slots : List Slot}
    {live : Nat → Bool} {heap : Heap} {store : Store Unit} {s : Locals}
    (h : Safe pool env slots live heap store s) (values : List Value) :
    Safe pool env slots live heap store { s with values } := by
  refine ⟨h.static, ?_⟩
  intro region hRegion t x hx hFalse hm wx hWords hLength block hBlock
  exact h.apart region hRegion t x hx hFalse hm wx
    (by simpa only [LocalsHold, Locals.positions_values, Locals.get_values] using hWords)
    hLength block hBlock

theorem frame {pool : LiteralPool} {Γ : List Ty} {env : Env Γ} {slots : List Slot}
    {live : Nat → Bool} {base : Nat} {heap : Heap} {store : Store Unit} {s s' : Locals}
    (h : Safe pool env slots live heap store s)
    (hVars : Holds env slots live base heap store s) (hFrame : Frame base s s') :
    Safe pool env slots live heap store s' := by
  refine ⟨h.static, ?_⟩
  intro region hRegion t x hx hFalse hm words hWords hLength block hBlock
  exact h.apart region hRegion t x hx hFalse hm words
    ((hVars.hold_agree hFrame hx hLength).mp hWords) hLength block hBlock

theorem push {pool : LiteralPool} {Γ : List Ty} {env : Env Γ} {slots : List Slot}
    {live : Nat → Bool} {heap : Heap} {store : Store Unit} {s : Locals}
    {t : Ty} {value : t.denote} {slot : Slot} {words : List Value}
    (h : Safe pool env slots (fun i => live (i + 1)) heap store s)
    (hWords : LocalsHold s slot.loc t.types words)
    (hRep : t.Rep slot.mode heap store words value)
    (hFresh : ∀ region ∈ pool.regions,
      ∀ block ∈ slot.mode.fresh store t words value, regionsDisjoint region block) :
    Safe pool (.cons value env) (slot :: slots) live heap store s := by
  refine ⟨h.static, ?_⟩
  intro region hRegion u x hx hFalse hm values hValues hLength block hBlock
  cases x with
  | here =>
    change slot.mode = .owned at hm
    change LocalsHold s slot.loc t.types values at hValues
    obtain rfl := LocalsHold.unique hValues hWords (hLength.trans hRep.length.symm)
    exact hFresh region hRegion block (by simpa only [Mode.fresh, hm, Env.get] using hBlock)
  | there x =>
    exact h.apart region hRegion u x hx hFalse hm values hValues hLength block hBlock

theorem pop {pool : LiteralPool} {Γ : List Ty} {env : Env Γ} {slots : List Slot}
    {live : Nat → Bool} {heap : Heap} {store : Store Unit} {s : Locals}
    {t : Ty} {value : t.denote} {slot : Slot}
    (h : Safe pool (.cons value env) (slot :: slots) live heap store s) :
    Safe pool env slots (fun i => live (i + 1)) heap store s := by
  refine ⟨h.static, ?_⟩
  intro region hRegion u x hx hFalse hm words hWords hLength block hBlock
  exact h.apart region hRegion u (.there x) hx hFalse hm words hWords hLength block hBlock

theorem after {pool : LiteralPool} {Γ : List Ty} {env : Env Γ} {slots : List Slot}
    {liveIn live : Nat → Bool} {base : Nat} {heap heap' : Heap}
    {store store' : Store Unit} {s s' : Locals} {t : Ty} {mode : Mode}
    {value : t.denote} {words : List Value}
    (h : Safe pool env slots liveIn heap store s)
    (hVars : Holds env slots liveIn base heap store s)
    (a : After env slots liveIn live base heap store s t mode value heap' store' s' words)
    (hLive : ∀ i, live i = true → liveIn i = true) :
    Safe pool env slots live heap' store' s' ∧
      ∀ region ∈ pool.regions, ∀ block ∈ mode.fresh store' t words value,
        regionsDisjoint region block := by
  have hKeep : ∀ region ∈ pool.regions,
      Holds.KeepDying env slots liveIn live store s region :=
    fun region hRegion => (h.apart region hRegion).mono fun i hi _ => ⟨hi, rfl⟩
  obtain ⟨hStatic, hFresh⟩ := h.static.step a.step hKeep
  refine ⟨⟨hStatic, ?_⟩, hFresh⟩
  intro region hRegion
  exact Holds.KeepDying.transfer hVars a.step a.frame hLive (fun _ hi _ => hi)
    ((h.apart region hRegion).mono fun i hi _ => ⟨hLive i hi, rfl⟩)

theorem evolves {pool : LiteralPool} {Γ : List Ty} {env : Env Γ} {slots : List Slot}
    {liveIn live : Nat → Bool} {base : Nat} {heap heap' : Heap}
    {store store' : Store Unit} {s s' : Locals}
    (h : Safe pool env slots liveIn heap store s)
    (hVars : Holds env slots liveIn base heap store s)
    (e : Evolves env slots liveIn live base heap store s heap' store' s')
    (hLive : ∀ i, live i = true → liveIn i = true) :
    Safe pool env slots live heap' store' s' := by
  have a := After.ofScalar (t := .word) (mode := .borrowed) (v := (0 : UInt64))
    (ws := [.i64 0]) rfl e.step rfl e.frame e.holds rfl
  exact (h.after hVars a hLive).1

theorem step {pool : LiteralPool} {Γ : List Ty} {env : Env Γ} {slots : List Slot}
    {live : Nat → Bool} {base : Nat} {heap heap' : Heap}
    {store store' : Store Unit} {s s' : Locals} {fresh : List (Nat × Nat)}
    (h : Safe pool env slots live heap store s)
    (hVars : Holds env slots live base heap store s)
    (hStep : Step heap store (fun _ => True) heap' store' fresh)
    (hFrame : Frame base s s') (hHolds : Holds env slots live base heap' store' s') :
    Safe pool env slots live heap' store' s' :=
  h.evolves hVars
    ⟨hStep.mono (fun _ _ => trivial) (fun _ hMem => nomatch hMem), hFrame, hHolds⟩
    (fun _ hLive => hLive)

theorem bind {pool : LiteralPool} {Γ : List Ty} {env : Env Γ} {slots : List Slot}
    {liveIn live bodyLive : Nat → Bool} {base : Nat} {heap heap' : Heap}
    {store store' : Store Unit} {s s1 s2 : Locals} {t : Ty} {mode : Mode}
    {value : t.denote} {words : List Value}
    (h : Safe pool env slots liveIn heap store s)
    (hVars : Holds env slots liveIn base heap store s)
    (a : After env slots liveIn live base heap store s t mode value heap' store' s1 words)
    (hLive : ∀ i, live i = true → liveIn i = true)
    (hBody : ∀ i, bodyLive (i + 1) = true → live i = true)
    (hFrame : Frame base s1 s2) (hWords : LocalsHold s2 base t.types words) :
    Safe pool (.cons value env) (⟨base, mode⟩ :: slots) bodyLive heap' store' s2 := by
  obtain ⟨hAfter, hFresh⟩ := h.after hVars a hLive
  exact ((hAfter.frame a.holds hFrame).mono hBody).push hWords a.rep hFresh

theorem bind2 {pool : LiteralPool} {Γ : List Ty} {env : Env Γ} {slots : List Slot}
    {liveIn live bodyLive : Nat → Bool} {base : Nat} {heap heap' : Heap}
    {store store' : Store Unit} {s s1 s2 : Locals} {first second : Ty} {mode : Mode}
    {value : (Ty.pair first second).denote} {wf ws : List Value}
    (h : Safe pool env slots liveIn heap store s)
    (hVars : Holds env slots liveIn base heap store s)
    (a : After env slots liveIn live base heap store s (.pair first second) mode value
      heap' store' s1 (wf ++ ws))
    (hLive : ∀ i, live i = true → liveIn i = true)
    (hBody : ∀ i, bodyLive (i + 2) = true → live i = true)
    (hFrame : Frame base s1 s2)
    (hFirst : first.Rep mode heap' store' wf value.1)
    (hSecond : second.Rep mode heap' store' ws value.2)
    (hWF : LocalsHold s2 base first.types wf)
    (hWS : LocalsHold s2 (base + first.width) second.types ws) :
    Safe pool (.cons value.2 (.cons value.1 env))
      (⟨base + first.width, mode⟩ :: ⟨base, mode⟩ :: slots) bodyLive heap' store' s2 := by
  obtain ⟨hAfter, hFresh⟩ := h.after hVars a hLive
  have hParts : ∀ region ∈ pool.regions,
      (∀ block ∈ mode.fresh store' first wf value.1, regionsDisjoint region block) ∧
      (∀ block ∈ mode.fresh store' second ws value.2, regionsDisjoint region block) := by
    intro region hRegion
    have hBoth := hFresh region hRegion
    rw [Mode.fresh_pair hFirst.length] at hBoth
    exact ⟨fun block hb => hBoth block (List.mem_append_left _ hb),
      fun block hb => hBoth block (List.mem_append_right _ hb)⟩
  have hTail := (hAfter.frame a.holds hFrame).mono hBody
  have hFirstSafe : Safe pool (.cons value.1 env) (⟨base, mode⟩ :: slots)
      (fun i => bodyLive (i + 1)) heap' store' s2 :=
    hTail.push hWF hFirst (fun region hr => (hParts region hr).1)
  exact hFirstSafe.push hWS hSecond (fun region hr => (hParts region hr).2)

theorem params {pool : LiteralPool} {Γ : List Ty} {env : Env Γ} {modes : List Mode}
    {heap : Heap} {store : Store Unit} {s : Locals} {words : List Value} {base : Nat}
    (hStatic : pool.Static heap store)
    (hRep : Env.Rep (paramMode Γ modes) heap store words env)
    (hApart : ∀ region ∈ pool.regions,
      Apart store (Env.moves store (paramMode Γ modes) words env) region)
    (hWords : ∀ {t : Ty} (x : Var Γ t),
      LocalsHold s (base + x.offset) t.types ((words.drop x.offset).take t.width)) :
    Safe pool env (paramSlots Γ modes base) (fun _ => true) heap store s := by
  refine ⟨hStatic, ?_⟩
  intro region hRegion t x _ _ hm values hValues hLength block hBlock
  rw [paramSlots_getD x] at hValues hm
  obtain rfl := LocalsHold.unique hValues (hWords x) (hLength.trans (hRep.var x).length.symm)
  rw [Ty.blocks_pointers] at hBlock
  obtain ⟨pointer, hPointer, rfl⟩ := List.mem_map.mp hBlock
  exact hApart region hRegion pointer (Env.moves_var x hRep hm pointer hPointer)

end Safe
end Verified.Bytes.LiteralPool
