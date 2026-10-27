import Verified.Wasi.ScratchContext
import Verified.Bytes.StaticEnv

namespace Verified.Wasi

open Wasm LeanExe.Pipeline LeanExe.Runtime

theorem After.values {World : Type} {context : List Ty} {env : Env context}
    {slots : List Slot} {liveIn live : Nat → Bool} {base : Nat}
    {heap finalHeap : Heap} {store finalStore : Store World} {locals finalLocals : Locals}
    {result : ResultTy} {value : result.denote} {words : List Value}
    (after : After env slots liveIn live base heap store locals result value
      finalHeap finalStore finalLocals words) (initialValues finalValues : List Value) :
    After env slots liveIn live base heap store { locals with values := initialValues }
      result value finalHeap finalStore { finalLocals with values := finalValues } words :=
  ⟨after.step, ⟨after.frame.params, after.frame.length, after.frame.below, after.frame.below32⟩,
    after.holds, after.rep, after.apart⟩

theorem After.ofValues {World : Type} {context : List Ty} {env : Env context}
    {slots : List Slot} {liveIn live : Nat → Bool} {base : Nat}
    {heap finalHeap : Heap} {store finalStore : Store World} {locals finalLocals : Locals}
    {result : ResultTy} {value : result.denote} {words values : List Value}
    (after : After env slots liveIn live base heap store { locals with values }
      result value finalHeap finalStore finalLocals words) :
    After env slots liveIn live base heap store locals result value
      finalHeap finalStore finalLocals words :=
  ⟨after.step, after.frame.values, after.holds, after.rep, after.apart⟩

theorem After.scratch {World : Type} {context : List Ty} {env : Env context}
    {slots : List Slot} {liveIn live : Nat → Bool} {base : Nat}
    {heap finalHeap : Heap} {store finalStore : Store World} {locals finalLocals : Locals}
    {result : ResultTy} {value : result.denote} {words : List Value}
    (after : After env slots liveIn live base heap store locals result value
      finalHeap finalStore finalLocals words)
    (vars : Holds env slots liveIn base heap (PureTransport.erase store) locals)
    (apart : Holds.ApartFrom env slots liveIn (PureTransport.erase store) locals ABI.scratch)
    (selected : ∀ i, live i = true → liveIn i = true) :
    Holds.ApartFrom env slots live (PureTransport.erase finalStore) finalLocals ABI.scratch := by
  refine Holds.ApartFrom.transfer vars (apart.mono selected) after.step after.frame selected ?_
  intro type x hLive values held width region member
  exact ⟨vars.keepDying selected hLive held width region member,
    regionsDisjoint_symm (apart type x (selected _ hLive) values held width region member)⟩

theorem After.keepDying {World : Type} {context : List Ty} {env : Env context}
    {slots : List Slot} {liveIn live selectedIn selectedOut : Nat → Bool} {base : Nat}
    {heap finalHeap : Heap} {store finalStore : Store World} {locals finalLocals : Locals}
    {result : ResultTy} {value : result.denote} {words : List Value} {region : Nat × Nat}
    (after : After env slots liveIn live base heap store locals result value
      finalHeap finalStore finalLocals words)
    (vars : Holds env slots liveIn base heap (PureTransport.erase store) locals)
    (apart : Holds.ApartFrom env slots liveIn (PureTransport.erase store) locals ABI.scratch)
    (selected : ∀ i, live i = true → liveIn i = true)
    (used : ∀ i, selectedIn i = true → selectedOut i = false → live i = true)
    (kept : Holds.KeepDying env slots selectedIn selectedOut
      (PureTransport.erase store) locals region) :
    Holds.KeepDying env slots selectedIn selectedOut
      (PureTransport.erase finalStore) finalLocals region := by
  refine Holds.KeepDying.transfer_kept vars after.step after.frame
    (fun i hIn hOut => selected i (used i hIn hOut)) ?_ kept
  intro type x hIn hOut values held width block member
  have hLive := used _ hIn hOut
  exact ⟨vars.keepDying selected hLive held width block member,
    regionsDisjoint_symm (apart type x (selected _ hLive) values held width block member)⟩

theorem After.pool_safe {World : Type} {context : List Ty} {env : Env context}
    {slots : List Slot} {liveIn live : Nat → Bool} {base : Nat}
    {heap finalHeap : Heap} {store finalStore : Store World} {locals finalLocals : Locals}
    {result : ResultTy} {value : result.denote} {words : List Value} {pool : Bytes.LiteralPool}
    (after : After env slots liveIn live base heap store locals result value
      finalHeap finalStore finalLocals words)
    (safe : pool.Safe env slots liveIn heap (PureTransport.erase store) locals)
    (vars : Holds env slots liveIn base heap (PureTransport.erase store) locals)
    (apart : Holds.ApartFrom env slots liveIn (PureTransport.erase store) locals ABI.scratch)
    (selected : ∀ i, live i = true → liveIn i = true)
    (poolApart : ∀ region ∈ pool.regions, regionsDisjoint region ABI.scratch) :
    pool.Safe env slots live finalHeap (PureTransport.erase finalStore) finalLocals ∧
      ∀ region ∈ pool.regions,
        ∀ block ∈ result.fresh (PureTransport.erase finalStore) words value,
          regionsDisjoint region block := by
  have kept : ∀ region ∈ pool.regions,
      Holds.KeepDying env slots liveIn live (PureTransport.erase store) locals region ∧
        regionsDisjoint region ABI.scratch :=
    fun region member =>
      ⟨(safe.apart region member).mono (fun i hIn _ => ⟨hIn, rfl⟩), poolApart region member⟩
  obtain ⟨static, fresh⟩ := safe.static.step after.step kept
  refine ⟨⟨static, ?_⟩, fresh⟩
  intro region member
  exact after.keepDying vars apart selected (fun _ hLive _ => hLive)
    ((safe.apart region member).mono (fun i hLive _ => ⟨selected i hLive, rfl⟩))

theorem After.thenUnit {World : Type} {context : List Ty} {env : Env context}
    {slots : List Slot} {liveIn liveMid live : Nat → Bool} {base : Nat}
    {heap middleHeap finalHeap : Heap} {store middleStore finalStore : Store World}
    {locals middleLocals finalLocals : Locals} {result : ResultTy}
    {value : result.denote} {words : List Value}
    (vars : Holds env slots liveIn base heap (PureTransport.erase store) locals)
    (apart : Holds.ApartFrom env slots liveIn (PureTransport.erase store) locals ABI.scratch)
    (first : After env slots liveIn liveMid base heap store locals .unit ()
      middleHeap middleStore middleLocals [])
    (second : After env slots liveMid live base middleHeap middleStore middleLocals
      result value finalHeap finalStore finalLocals words)
    (midSelected : ∀ i, liveMid i = true → liveIn i = true)
    (selected : ∀ i, live i = true → liveMid i = true) :
    After env slots liveIn live base heap store locals result value
      finalHeap finalStore finalLocals words := by
  refine ⟨first.step.trans second.step ?_, first.frame.trans second.frame,
    second.holds, second.rep, second.apart⟩
  intro region kept
  have before : Holds.KeepDying env slots liveIn liveMid
      (PureTransport.erase store) locals region := kept.1.mono fun i hIn hMid =>
    ⟨hIn, by
      cases hLive : live i with
      | false => rfl
      | true => rw [selected i hLive] at hMid; exact nomatch hMid⟩
  refine ⟨⟨before, kept.2⟩, fun _ => ⟨?_, kept.2⟩⟩
  exact first.keepDying vars apart midSelected (fun _ hMid _ => hMid)
    (kept.1.mono fun i hMid hLive => ⟨midSelected i hMid, hLive⟩)

theorem After.thenWord {World : Type} {context : List Ty} {env : Env context}
    {slots : List Slot} {liveIn liveMid live : Nat → Bool} {base : Nat}
    {heap middleHeap finalHeap : Heap} {store middleStore finalStore : Store World}
    {locals middleLocals finalLocals : Locals} {result : ResultTy}
    {word : UInt64} {value : result.denote} {firstWords words : List Value}
    (vars : Holds env slots liveIn base heap (PureTransport.erase store) locals)
    (apart : Holds.ApartFrom env slots liveIn (PureTransport.erase store) locals ABI.scratch)
    (first : After env slots liveIn liveMid base heap store locals (.value .word) word
      middleHeap middleStore middleLocals firstWords)
    (second : After env slots liveMid live base middleHeap middleStore middleLocals
      result value finalHeap finalStore finalLocals words)
    (midSelected : ∀ i, liveMid i = true → liveIn i = true)
    (selected : ∀ i, live i = true → liveMid i = true) :
    After env slots liveIn live base heap store locals result value
      finalHeap finalStore finalLocals words := by
  have unit : After env slots liveIn liveMid base heap store locals .unit ()
      middleHeap middleStore middleLocals [] :=
    ⟨first.step, first.frame, first.holds, rfl, trivial⟩
  exact After.thenUnit vars apart unit second midSelected selected

theorem After.bind_value {World : Type} {context : List Ty} {env : Env context}
    {slots : List Slot} {liveIn liveMid bodyIn live : Nat → Bool} {base : Nat}
    {heap middleHeap finalHeap : Heap} {store middleStore finalStore : Store World}
    {locals middleLocals boundLocals finalLocals : Locals} {type : Ty} {intermediate : type.denote}
    {result : ResultTy} {value : result.denote} {firstWords words : List Value}
    (vars : Holds env slots liveIn base heap (PureTransport.erase store) locals)
    (apart : Holds.ApartFrom env slots liveIn (PureTransport.erase store) locals ABI.scratch)
    (first : After env slots liveIn liveMid base heap store locals (.value type) intermediate
      middleHeap middleStore middleLocals firstWords)
    (frame : Frame base middleLocals boundLocals)
    (held : LocalsHold boundLocals base type.types firstWords)
    (body : After (.cons intermediate env) (⟨base, .owned⟩ :: slots)
      bodyIn (shift 1 live) (base + type.width) middleHeap middleStore boundLocals
      result value finalHeap finalStore finalLocals words)
    (bodySelected : ∀ i, bodyIn (i + 1) = true → liveMid i = true)
    (midSelected : ∀ i, liveMid i = true → liveIn i = true)
    (selected : ∀ i, live i = true → liveMid i = true) :
    After env slots liveIn live base heap store locals result value
      finalHeap finalStore finalLocals words := by
  have firstRep : type.Rep .owned middleHeap (PureTransport.erase middleStore)
      firstWords intermediate := first.rep
  refine ⟨first.step.trans body.step ?_,
    first.frame.trans (frame.trans (body.frame.mono (Nat.le_add_right _ _))), ?_, body.rep, ?_⟩
  · intro region kept
    have before : Holds.KeepDying env slots liveIn liveMid
        (PureTransport.erase store) locals region := kept.1.mono fun i hIn hMid =>
      ⟨hIn, by
        cases hLive : live i with
        | false => rfl
        | true => rw [selected i hLive] at hMid; exact nomatch hMid⟩
    refine ⟨⟨before, kept.2⟩, fun fresh => ⟨?_, kept.2⟩⟩
    have middle : Holds.KeepDying env slots liveMid live
        (PureTransport.erase middleStore) middleLocals region :=
      first.keepDying vars apart midSelected (fun _ hMid _ => hMid)
        (kept.1.mono fun i hMid hLive => ⟨midSelected i hMid, hLive⟩)
    intro other x hIn hOut owned values hValues width block member
    cases x with
    | here =>
        change LocalsHold boundLocals base type.types values at hValues
        obtain rfl := LocalsHold.unique hValues held (width.trans firstRep.length.symm)
        exact fresh block member
    | there x =>
        change (slots.getD x.index default).mode = .owned at owned
        change LocalsHold boundLocals (slots.getD x.index default).loc other.types values at hValues
        have hMid := bodySelected _ hIn
        have hNotLive : live x.index = false := by simpa only [Var.index, shift_add] using hOut
        exact middle other x hMid hNotLive owned values
          ((first.holds.hold_agree frame hMid width).mp hValues) width block member
  · exact (body.holds.pop.live_mono fun i h => by simpa only [shift_add] using h).lower vars
      fun i h => midSelected i (selected i h)
  · cases result with
    | unit => trivial
    | value type =>
        exact body.apart.pop.live_mono fun i h => by simpa only [shift_add] using h

end Verified.Wasi
