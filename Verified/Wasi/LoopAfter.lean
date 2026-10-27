import Verified.Wasi.AfterScratch
import Verified.Wasi.OwnedScratch

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime

namespace Wasi

def loopCaptured (slots : List Slot) : List Slot :=
  slots.map fun slot => { slot with mode := .borrowed }

@[simp] theorem loopCaptured_getD (slots : List Slot) (index : Nat) :
    (loopCaptured slots).getD index default = { slots.getD index default with mode := .borrowed } := by
  induction slots generalizing index with
  | nil => rfl
  | cons slot rest ih =>
      cases index with
      | zero => rfl
      | succ index => simpa only [loopCaptured, List.map_cons, List.getD_cons_succ] using ih index

end Wasi

namespace Holds

theorem loopBorrow {context : List Ty} {env : Env context} {slots : List Slot}
    {live : Nat → Bool} {base : Nat} {heap : Heap} {store : Store Unit} {locals : Locals}
    (vars : Holds env slots live base heap store locals) :
    Holds env (Wasi.loopCaptured slots) live base heap store locals := by
  refine ⟨?_, ?_⟩
  · intro type x selected
    obtain ⟨below, words, held, rep⟩ := vars.get x selected
    simpa only [Wasi.loopCaptured_getD] using
      (show (slots.getD x.index default).loc + type.width ≤ base ∧
        ∃ words, LocalsHold locals (slots.getD x.index default).loc type.types words ∧
          type.Rep .borrowed heap store words (env.get x) from ⟨below, words, held, rep.borrow⟩)
  · intro first second x y hx hy different owned
    simp only [Wasi.loopCaptured_getD] at owned
    exact nomatch owned

theorem Apart.loopBorrow {context : List Ty} {env : Env context} {slots : List Slot}
    {live : Nat → Bool} {base : Nat} {heap : Heap} {store : Store Unit} {locals : Locals}
    {type : Ty} {words : List Value} {value : type.denote}
    (vars : Holds env slots live base heap store locals)
    (apart : Holds.Apart env slots live store locals type .owned words value) :
    Holds.Apart env (Wasi.loopCaptured slots) live store locals type .owned words value := by
  intro other x selected _ values held width block member region inRegion
  simp only [Wasi.loopCaptured_getD] at held inRegion
  obtain ⟨_, actual, actualHeld, actualRep⟩ := vars.get x selected
  have same : values = actual := LocalsHold.unique held actualHeld (width.trans actualRep.length.symm)
  subst values
  exact actualRep.reads_apart block
    (fun region member' => apart other x selected (Or.inl rfl) actual actualHeld
      actualRep.length block member region member') region inRegion

theorem ApartFrom.loopBorrow {context : List Ty} {env : Env context} {slots : List Slot}
    {live : Nat → Bool} {base : Nat} {heap : Heap} {store : Store Unit} {locals : Locals}
    {region : Nat × Nat} (vars : Holds env slots live base heap store locals)
    (apart : Holds.ApartFrom env slots live store locals region) :
    Holds.ApartFrom env (Wasi.loopCaptured slots) live store locals region := by
  intro other x selected values held width block member
  simp only [Wasi.loopCaptured_getD] at held member
  obtain ⟨_, actual, actualHeld, actualRep⟩ := vars.get x selected
  have same : values = actual := LocalsHold.unique held actualHeld (width.trans actualRep.length.symm)
  subst values
  exact actualRep.reads_apart region
    (apart other x selected actual actualHeld actualRep.length) block member

end Holds

namespace Wasi

theorem loopCaptured_safe {pool : Bytes.LiteralPool} {context : List Ty} {env : Env context}
    {slots : List Slot} {live : Nat → Bool} {heap : Heap} {store : Store Unit} {locals : Locals}
    (static : pool.Static heap store) :
    pool.Safe env (loopCaptured slots) live heap store locals := by
  refine ⟨static, ?_⟩
  intro region member type x selected discarded owned
  simp only [loopCaptured_getD] at owned
  exact nomatch owned

theorem After.reframe {World : Type} {context : List Ty} {env : Env context}
    {slots : List Slot} {liveIn live : Nat → Bool} {base : Nat}
    {heap finalHeap : Heap} {initial final : Store World}
    {locals finalLocals adjusted : Locals} {result : ResultTy} {value : result.denote}
    {words : List Value}
    (after : After env slots liveIn live base heap initial locals result value
      finalHeap final finalLocals words) (frame : Frame base finalLocals adjusted) :
    After env slots liveIn live base heap initial locals result value
      finalHeap final adjusted words := by
  refine ⟨after.step, after.frame.trans frame, after.holds.agree frame, after.rep, ?_⟩
  cases result with
  | unit => trivial
  | value type => exact Holds.Apart.agree after.holds after.apart frame

def LoopStateKeep (type : Ty) (store : Store Unit) (words : List Value)
    (value : type.denote) (region : Nat × Nat) : Prop :=
  (∀ block ∈ type.blocks store words value, regionsDisjoint region block) ∧
    regionsDisjoint region ABI.scratch

theorem After.loopAdvance {World : Type} {context : List Ty} {env : Env context}
    {slots : List Slot} {liveIn live : Nat → Bool} {base : Nat}
    {heap middleHeap finalHeap : Heap} {initial middle final : Store World}
    {locals middleLocals finalLocals : Locals} {type : Ty} {state value : type.denote}
    {stateWords words : List Value}
    (after : After env slots liveIn live base heap initial locals (.value type) state
      middleHeap middle middleLocals stateWords)
    (scratch : Holds.ApartFrom env slots live (PureTransport.erase middle) middleLocals ABI.scratch)
    (step : Step middleHeap (PureTransport.erase middle)
      (LoopStateKeep type (PureTransport.erase middle) stateWords state)
      finalHeap (PureTransport.erase final) (type.blocks (PureTransport.erase final) words value))
    (frame : Frame base middleLocals finalLocals)
    (rep : type.Rep .owned finalHeap (PureTransport.erase final) words value) :
    After env slots liveIn live base heap initial locals (.value type) value
      finalHeap final finalLocals words := by
  have keep : ∀ (other : Ty) (x : Var context other), live x.index = true →
      ∀ values, LocalsHold middleLocals (slots.getD x.index default).loc other.types values →
      values.length = other.width → ∀ region ∈ other.regions
        (slots.getD x.index default).mode (PureTransport.erase middle) values (env.get x),
        LoopStateKeep type (PureTransport.erase middle) stateWords state region := by
    intro other x selected values held width region member
    exact ⟨fun block inState => regionsDisjoint_symm
      (after.apart other x selected (Or.inl rfl) values held width block inState region member),
      regionsDisjoint_symm (scratch other x selected values held width region member)⟩
  refine ⟨after.step.trans step (fun region kept => ⟨kept, fun fresh => ⟨fresh, kept.2⟩⟩),
    after.frame.trans frame, (after.holds.step step keep).agree frame, rep, ?_⟩
  intro other x selected _ values held width block member region inRegion
  have original := (after.holds.hold_agree frame selected width).mp held
  have regions := after.holds.regions_after step selected original width
    (keep other x selected values original width)
  rw [regions.1] at inRegion
  exact regionsDisjoint_symm (regions.2 region inRegion block member)

theorem After.loopTest {World : Type} {context : List Ty} {env : Env context}
    {slots : List Slot} {liveIn live : Nat → Bool} {base : Nat}
    {heap middleHeap finalHeap : Heap} {initial middle final : Store World}
    {locals middleLocals finalLocals : Locals} {type : Ty} {state : type.denote}
    {words : List Value}
    (after : After env slots liveIn live base heap initial locals (.value type) state
      middleHeap middle middleLocals words)
    (scratch : Holds.ApartFrom env slots live (PureTransport.erase middle) middleLocals ABI.scratch)
    (step : Step middleHeap (PureTransport.erase middle)
      (fun region => regionsDisjoint region ABI.scratch) finalHeap (PureTransport.erase final) [])
    (frame : Frame base middleLocals finalLocals) :
    After env slots liveIn live base heap initial locals (.value type) state
      finalHeap final finalLocals words := by
  have rep : type.Rep .owned middleHeap (PureTransport.erase middle) words state := after.rep
  obtain ⟨rep', same, _⟩ := rep.step step
    (fun region member => regionsDisjoint_symm (owned_scratch rep region member))
  have sameBlocks : type.blocks (PureTransport.erase final) words state =
      type.blocks (PureTransport.erase middle) words state := same
  have combined := after.step.transBoth step (fun region kept => ⟨kept, fun _ => kept.2⟩)
  have keep : ∀ (other : Ty) (x : Var context other), live x.index = true →
      ∀ values, LocalsHold middleLocals (slots.getD x.index default).loc other.types values →
      values.length = other.width → ∀ region ∈ other.regions
        (slots.getD x.index default).mode (PureTransport.erase middle) values (env.get x),
        regionsDisjoint region ABI.scratch :=
    fun other x selected values held width region member =>
      regionsDisjoint_symm (scratch other x selected values held width region member)
  refine ⟨?_, after.frame.trans frame, (after.holds.step step keep).agree frame, rep', ?_⟩
  · simpa only [ResultTy.fresh, Mode.fresh, List.append_nil, sameBlocks] using combined
  · exact Holds.Apart.transfer after.holds after.apart step frame keep same

end Wasi

end Verified
