import Verified.OwnedValues
import Verified.WordCode

namespace Verified

open Wasm LeanExe.Pipeline

/-- The words of word fields, elements of one word each, and the rest of a context. -/
theorem Env.Rep.wordFields {heap : Heap} {store : Store Unit} {ps : List Ty}
    (tail : Env ps) : (n : Nat) → (es : Fin n → Elem) → (∀ i, (es i).width = 1) →
    (words : (i : Fin n) → (es i).denote) →
    ∀ (modes : Nat → Mode) (ws : List Value),
      Env.Rep modes heap store ws (Env.prependFn n (fun i => .elem (es i)) words tail) →
      ∃ rest, ws = (List.ofFn fun i =>
          typedValue (es i).slotType ((es i).slotWord (words i))) ++ rest ∧
        Env.Rep (fun i => modes (i + n)) heap store rest tail ∧
        (Env.prependFn n (fun i => .elem (es i)) words tail).blocks store ws =
          tail.blocks store rest
  | 0, _, _, _, _, ws, hRep => ⟨ws, rfl, hRep, rfl⟩
  | n + 1, es, hWidth, words, modes, ws, hRep => by
    obtain ⟨first, middle, rfl, hFirst, hMiddle⟩ := hRep
    have hFirst' : first = [typedValue (es 0).slotType ((es 0).slotWord (words 0))] :=
      hFirst.trans (Elem.values_one (es 0) (hWidth 0) (words 0))
    subst hFirst'
    obtain ⟨rest, hWords, hRep, hBlocks⟩ := Env.Rep.wordFields tail n (fun i => es i.succ)
      (fun i => hWidth i.succ) (fun i => words i.succ) (fun i => modes (i + 1)) middle hMiddle
    refine ⟨rest, ?_, ?_, ?_⟩
    · rw [List.ofFn_succ]
      simpa only [List.singleton_append, List.cons_append, List.nil_append] using congrArg
        (List.cons (typedValue (es 0).slotType ((es 0).slotWord (words 0)))) hWords
    · simpa only [Nat.add_assoc] using hRep
    · change (Env.cons (t := .elem (es 0)) (words 0)
        (Env.prependFn n (fun i => .elem (es i.succ)) (fun i => words i.succ) tail)).blocks
          store _ = _
      rw [Env.blocks_cons (t := .elem (es 0))
        (by simp only [List.length_singleton, Ty.width, hWidth 0])]
      exact hBlocks

theorem Env.Rep.treeFields {heap : Heap} {store : Store Unit} {ps : List Ty}
    {shape : TreeShape} (tail : Env ps) :
    (n : Nat) → (values : Fin n → Tree shape) →
    ∀ (modes : Nat → Mode) (ws : List Value),
      Env.Rep modes heap store ws (Env.prependRepeat (.tree shape) n values tail) →
      ∃ pointers : Fin n → UInt64, ∃ rest,
        ws = (List.ofFn fun i => Value.i64 (pointers i)) ++ rest ∧
        (∀ i, Mode.node (modes i.val) heap store (pointers i) (values i).toNode) ∧
        Env.Rep (fun i => modes (i + n)) heap store rest tail ∧
        (Env.prependRepeat (.tree shape) n values tail).blocks store ws =
          (List.ofFn fun i => (values i).toNode.blocks store (pointers i)).flatten ++
            tail.blocks store rest
  | 0, _, modes, ws, hRep =>
    ⟨Fin.elim0, ws, rfl, (fun i => Fin.elim0 i), by
      simpa only [Env.prependRepeat, List.replicate_zero, List.nil_append, Nat.add_zero]
        using hRep, rfl⟩
  | n + 1, values, modes, ws, hRep => by
    obtain ⟨first, middle, rfl, hFirst, hMiddle⟩ := hRep
    obtain ⟨ptr, rfl, hNode⟩ := hFirst
    obtain ⟨pointers, rest, hWords, hNodes, hRep, hBlocks⟩ := Env.Rep.treeFields tail n
      (fun i => values i.succ) (fun i => modes (i + 1)) middle hMiddle
    refine ⟨Fin.cases ptr pointers, rest, ?_, ?_, ?_, ?_⟩
    · rw [List.ofFn_succ]
      simpa only [Fin.cases_zero, Fin.cases_succ, List.singleton_append, List.cons_append,
        List.nil_append] using
        congrArg (List.cons (.i64 ptr)) hWords
    · intro i
      cases i using Fin.cases with
      | zero => exact hNode
      | succ i => exact hNodes i
    · simpa only [Nat.add_assoc] using hRep
    · change (Env.cons (t := .tree shape) (values 0)
        (Env.prependRepeat (.tree shape) n (fun i => values i.succ) tail)).blocks store _ = _
      rw [Env.blocks_cons (t := .tree shape) rfl, hBlocks, List.ofFn_succ]
      simp only [Ty.blocks, Fin.cases_zero, Fin.cases_succ, List.flatten_cons, List.append_assoc]

end Verified
