import Verified.Wasi.LoopAfter

namespace Verified.Wasi

open Wasm LeanExe.Pipeline LeanExe.Runtime

@[simp] theorem loopCaptured_cons (slot : Slot) (slots : List Slot) :
    loopCaptured (slot :: slots) = { slot with mode := .borrowed } :: loopCaptured slots := rfl

@[simp] theorem loopCaptured_idempotent (slots : List Slot) :
    loopCaptured (loopCaptured slots) = loopCaptured slots := by
  induction slots with
  | nil => rfl
  | cons slot slots ih => simp only [loopCaptured_cons, ih]

theorem loop_index_hold {locals : Locals} {base : Nat} {index : UInt64}
    (value : locals.get (base + 1) = some (.i64 index)) :
    LocalsHold locals (base + 1) Ty.word.types [.i64 index] := by
  intro k bound
  obtain rfl : k = 0 := by simpa using bound
  simpa [Ty.types, slotIndex] using value

theorem loop_context_holds {context : List Ty} {env : Env context} {slots : List Slot}
    {type : Ty} {state : type.denote} {index : UInt64} {live : Nat → Bool} {base : Nat}
    {heap : Heap} {store : Store Unit} {locals : Locals} {words : List Value}
    (vars : Holds env slots (fun i => live (i + 2)) base heap store locals)
    (held : LocalsHold locals (base + 2) type.types words)
    (rep : type.Rep .owned heap store words state)
    (apart : Holds.Apart env slots (fun i => live (i + 2)) store locals type .owned words state)
    (counter : locals.get (base + 1) = some (.i64 index)) :
    Holds (.cons state (.cons (t := .word) index env))
      (⟨base + 2, .owned⟩ :: ⟨base + 1, .borrowed⟩ :: loopCaptured slots)
      live (base + 2 + type.width) heap store locals := by
  have indexed : Holds (.cons (t := .word) index env)
      (⟨base + 1, .borrowed⟩ :: loopCaptured slots)
      (fun i => live (i + 1)) (base + 2) heap store locals := by
    simpa only [Ty.width, Elem.width, Nat.add_assoc] using
      (vars.loopBorrow.mono (Nat.le_succ base)).push
        (live' := fun i => live (i + 1)) (loop_index_hold counter) rfl
        (Holds.Apart.ofScalar (t := .word) rfl)
  have stateApart := (Holds.Apart.loopBorrow vars apart).push
    (u := .word) (v := index) (mv := .borrowed)
    (live' := fun i => live (i + 1)) (loop_index_hold counter) rfl
    (fun _ _ _ _ member => nomatch member)
  exact indexed.push held rep stateApart

theorem loop_context_scratch {context : List Ty} {env : Env context} {slots : List Slot}
    {type : Ty} {state : type.denote} {index : UInt64} {live : Nat → Bool} {base : Nat}
    {heap : Heap} {store : Store Unit} {locals : Locals} {words : List Value}
    (vars : Holds env slots (fun i => live (i + 2)) base heap store locals)
    (scratch : Holds.ApartFrom env slots (fun i => live (i + 2)) store locals ABI.scratch)
    (held : LocalsHold locals (base + 2) type.types words)
    (rep : type.Rep .owned heap store words state)
    (counter : locals.get (base + 1) = some (.i64 index)) :
    Holds.ApartFrom (.cons state (.cons (t := .word) index env))
      (⟨base + 2, .owned⟩ :: ⟨base + 1, .borrowed⟩ :: loopCaptured slots)
      live store locals ABI.scratch := by
  have indexed : Holds.ApartFrom (.cons (t := .word) index env)
      (⟨base + 1, .borrowed⟩ :: loopCaptured slots) (fun i => live (i + 1))
      store locals ABI.scratch :=
    (Holds.ApartFrom.loopBorrow vars scratch).push
      (loop_index_hold counter) rfl (fun _ _ member => nomatch member)
  exact indexed.push held rep.length (fun _ => owned_scratch rep)

theorem loop_context_safe {pool : Bytes.LiteralPool} {context : List Ty} {env : Env context}
    {slots : List Slot} {type : Ty} {state : type.denote} {index : UInt64}
    {live : Nat → Bool} {base : Nat} {heap : Heap} {store : Store Unit} {locals : Locals}
    {words : List Value} (static : pool.Static heap store)
    (held : LocalsHold locals (base + 2) type.types words)
    (rep : type.Rep .owned heap store words state)
    (fresh : ∀ region ∈ pool.regions,
      ∀ block ∈ type.blocks store words state, regionsDisjoint region block)
    (counter : locals.get (base + 1) = some (.i64 index)) :
    pool.Safe (.cons state (.cons (t := .word) index env))
      (⟨base + 2, .owned⟩ :: ⟨base + 1, .borrowed⟩ :: loopCaptured slots)
      live heap store locals := by
  have captured : pool.Safe env (loopCaptured slots) (fun i => live (i + 2)) heap store locals :=
    loopCaptured_safe static
  have indexed : pool.Safe (.cons (t := .word) index env)
      (⟨base + 1, .borrowed⟩ :: loopCaptured slots) (fun i => live (i + 1)) heap store locals :=
    captured.push (loop_index_hold counter) rfl (fun _ _ _ member => nomatch member)
  exact indexed.push held rep fresh

theorem loop_test_holds {context : List Ty} {env : Env context} {slots : List Slot}
    {type : Ty} {state : type.denote} {index : UInt64} {live : Nat → Bool} {base : Nat}
    {heap : Heap} {store : Store Unit} {locals : Locals} {words : List Value}
    (vars : Holds env slots (fun i => live (i + 2)) base heap store locals)
    (held : LocalsHold locals (base + 2) type.types words)
    (rep : type.Rep .owned heap store words state)
    (apart : Holds.Apart env slots (fun i => live (i + 2)) store locals type .owned words state)
    (counter : locals.get (base + 1) = some (.i64 index)) :
    Holds (.cons state (.cons (t := .word) index env))
      (⟨base + 2, .borrowed⟩ :: ⟨base + 1, .borrowed⟩ :: loopCaptured slots)
      live (base + 2 + type.width) heap store locals := by
  simpa only [loopCaptured_cons, loopCaptured_idempotent] using
    (loop_context_holds vars held rep apart counter).loopBorrow

theorem loop_test_scratch {context : List Ty} {env : Env context} {slots : List Slot}
    {type : Ty} {state : type.denote} {index : UInt64} {live : Nat → Bool} {base : Nat}
    {heap : Heap} {store : Store Unit} {locals : Locals} {words : List Value}
    (vars : Holds env slots (fun i => live (i + 2)) base heap store locals)
    (scratch : Holds.ApartFrom env slots (fun i => live (i + 2)) store locals ABI.scratch)
    (held : LocalsHold locals (base + 2) type.types words)
    (rep : type.Rep .owned heap store words state)
    (apart : Holds.Apart env slots (fun i => live (i + 2)) store locals type .owned words state)
    (counter : locals.get (base + 1) = some (.i64 index)) :
    Holds.ApartFrom (.cons state (.cons (t := .word) index env))
      (⟨base + 2, .borrowed⟩ :: ⟨base + 1, .borrowed⟩ :: loopCaptured slots)
      live store locals ABI.scratch := by
  simpa only [loopCaptured_cons, loopCaptured_idempotent] using
    Holds.ApartFrom.loopBorrow (loop_context_holds vars held rep apart counter)
      (loop_context_scratch vars scratch held rep counter)

theorem loop_test_safe {pool : Bytes.LiteralPool} {context : List Ty} {env : Env context}
    {slots : List Slot} {type : Ty} {state : type.denote} {index : UInt64}
    {live : Nat → Bool} {base : Nat} {heap : Heap} {store : Store Unit} {locals : Locals}
    (static : pool.Static heap store) :
    pool.Safe (.cons state (.cons (t := .word) index env))
      (⟨base + 2, .borrowed⟩ :: ⟨base + 1, .borrowed⟩ :: loopCaptured slots)
      live heap store locals :=
  loopCaptured_safe (slots := ⟨base + 2, .owned⟩ :: ⟨base + 1, .borrowed⟩ :: slots) static

theorem loop_test_step {World : Type} {context : List Ty} {env : Env context} {slots : List Slot}
    {type : Ty} {state : type.denote} {index : UInt64} {liveIn live : Nat → Bool}
    {base scratch : Nat} {heap finalHeap : Heap} {initial final : Store World}
    {locals finalLocals : Locals} {decision : Bool} {words : List Value}
    (after : After (.cons state (.cons (t := .word) index env))
      (⟨base + 2, .borrowed⟩ :: ⟨base + 1, .borrowed⟩ :: loopCaptured slots)
      liveIn live scratch heap initial locals (.value .bool) decision
      finalHeap final finalLocals words) :
    Step heap (PureTransport.erase initial) (fun region => regionsDisjoint region ABI.scratch)
      finalHeap (PureTransport.erase final) [] := by
  refine after.step.mono (fun region kept => ⟨?_, kept⟩) (fun _ member => nomatch member)
  intro other x selected discarded owned
  cases x with
  | here => exact nomatch owned
  | there x =>
      cases x with
      | here => exact nomatch owned
      | there x =>
          simp only [Var.index, List.getD_cons_succ, loopCaptured_getD] at owned
          exact nomatch owned

end Verified.Wasi
