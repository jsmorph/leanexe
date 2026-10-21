import Verified.WGSL.Cell

namespace Verified.WGSL

variable {t : Ty} {ctx : Context Γ} {base : Nat}
  {value : Funs S → Verified.Env Γ → t.denote}

def put (locals : Locals) (j : Nat) (value : Wasm.Value) : Locals :=
  fun i => if i = j then some value else locals i

def Code.save (a : Code ctx base value) {type : LeanExe.IR.ScalarType}
    (input : Rep t → LeanExe.IR.Expr type) (output : Nat → Rep t)
    (encode : t.denote → type.denote)
    (outputBound : ∀ j, (output j).locals ≤ j + 1)
    (inputHolds : ∀ rep locals arrays x, rep.Holds locals arrays x →
      (input rep).denote locals arrays = some (encode x))
    (outputHolds : ∀ locals arrays j x,
      (output j).Holds (put locals j (type.value (encode x))) arrays x) :
    Code ctx base value where
  next := a.next + 1
  body := .seq a.body (.assign a.next (input a.result))
  result := output a.next
  vars := a.vars ++ [(a.next, type)]
  grows := Nat.le_trans a.grows (Nat.le_succ _)
  writes := by
    intro j hj
    simp only [LeanExe.IR.Stmt.writes, List.mem_append, List.mem_singleton] at hj
    rcases hj with hj | rfl
    · have := a.writes j hj
      exact ⟨this.1, Nat.lt_succ_of_lt this.2⟩
    · exact ⟨a.grows, Nat.lt_succ_self _⟩
  resultBound := outputBound a.next
  correct := by
    intro ctxBound funs env locals arrays agree unused
    obtain ⟨middle, ha, hva⟩ := a.correct ctxBound funs env locals arrays agree unused
    refine ⟨put middle a.next (type.value (encode (value funs env))), ?_,
      outputHolds middle arrays a.next (value funs env)⟩
    simp only [LeanExe.IR.Stmt.denote, ha, Option.bind_some, unused a.next a.grows,
      ↓reduceIte, inputHolds a.result middle arrays _ hva, Option.map_some]
    rfl

def Code.saveCell (a : Code ctx base value) (cell : Cell t) : Code ctx base value :=
  a.save cell.input cell.read cell.encode cell.readBound cell.inputHolds
    (fun locals arrays j x => cell.readHolds _ arrays j x (by simp [put]))

def Code.cache (a : Code ctx base value) : Code ctx base value :=
  match t with
  | .word => a.saveCell .word
  | .bool => a.saveCell .bool
  | .float32 => a.saveCell .float32
  | _ => a

end Verified.WGSL
