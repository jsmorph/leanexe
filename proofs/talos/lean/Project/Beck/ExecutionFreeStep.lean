import Project.Beck.ExecutionContains
import Project.Beck.FreeColumn

namespace Project.Beck.Execution

open Wasm Project.ProofKit LeanExe.Examples.Beck

abbrev FreeScratch := Fin 32 → Value

def freeFrame (input : Input) (point : Point) (inputOwner inputPointer pointOwner pointPointer
    columnsOwner columnsPointer : UInt64) (index : Nat) (found : Bool) (scratch : FreeScratch) : Locals :=
  { params := (inputValues input inputOwner inputPointer).reverse ++
      (pointValues point pointOwner pointPointer).reverse ++ [.i64 columnsOwner, .i64 columnsPointer]
    locals := [.i64 (boolWord found), .i64 (if found then index.toUInt64 else 0), .i64 0,
      scratch 0, scratch 1, scratch 2, scratch 3, scratch 4, scratch 5, scratch 6,
      scratch 7, scratch 8, scratch 9, scratch 10, scratch 11, scratch 12, scratch 13,
      scratch 14, scratch 15, scratch 16, scratch 17, scratch 18, scratch 19, scratch 20,
      scratch 21, scratch 22, scratch 23, scratch 24,
      .i64 index.toUInt64, .i64 input.jobs.toUInt64, .i64 1,
      scratch 25, scratch 26, scratch 27, scratch 28, scratch 29, scratch 30, scratch 31] }

def eligible (point : Point) (columns : Array UInt64) (index : Nat) : Bool :=
  !frozen point index && !contains columns index.toUInt64

def freeScratch (point : Point) (pointOwner pointPointer columnsOwner columnsPointer : UInt64)
    (index : Nat) (isFrozen found : Bool) (scratch : FreeScratch) : FreeScratch := fun k =>
  match k.val with
  | 0 | 4 | 14 => .i64 index.toUInt64
  | 1 | 11 => .i64 point.denominator
  | 2 | 12 => .i64 pointOwner
  | 3 | 13 => .i64 pointPointer
  | 5 | 15 => if isFrozen then scratch k else .i64 columnsOwner
  | 6 | 16 => if isFrozen then scratch k else .i64 columnsPointer
  | 7 | 17 => if isFrozen then scratch k else .i64 index.toUInt64
  | 8 => .i64 (boolWord found)
  | 9 => .i64 (if found then index.toUInt64 else 0)
  | 10 | 28 => .i64 0
  | 25 => .i64 (if found then 1 else index.toUInt64)
  | 26 => .i64 1
  | 27 => .i64 (if found then index.toUInt64 else (index + 1).toUInt64)
  | _ => scratch k

def freeBody : Wasm.Program :=
  match (func28[12]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

set_option maxHeartbeats 1000000 in
theorem freeStep_exact (env : HostEnv Unit) (initial : Store Unit) (input : Input) (point : Point)
    (columns : Array UInt64) (inputOwner inputPointer pointOwner pointPointer columnsOwner columnsPointer : UInt64)
    (index : Nat) (scratch : FreeScratch)
    (pointArray : UInt64Array.At initial pointPointer point.numerators)
    (columnsArray : UInt64Array.At initial columnsPointer columns)
    (bounded : index < point.numerators.size) (Q : Assertion Unit)
    (next : eligible point columns index = false →
      Q (.Break 0 initial (freeFrame input point inputOwner inputPointer pointOwner pointPointer
        columnsOwner columnsPointer (index + 1) false
        (freeScratch point pointOwner pointPointer columnsOwner columnsPointer index (frozen point index) false scratch))))
    (done : eligible point columns index = true →
      Q (.Break 1 initial (freeFrame input point inputOwner inputPointer pointOwner pointPointer
        columnsOwner columnsPointer index true
        (freeScratch point pointOwner pointPointer columnsOwner columnsPointer index (frozen point index) true scratch)))) :
    wp «module» (freeBody.drop 4) Q initial
      (freeFrame input point inputOwner inputPointer pointOwner pointPointer columnsOwner columnsPointer
        index false scratch) env := by
  have fit : index + 1 < UInt64.size := by have := pointArray.size_lt; omega
  have noOverflow : ¬UInt64.ofNat index + 1 < UInt64.ofNat index :=
    CheckedNatAdd.guard_of_fits index 1 fit
  have hFrozen := frozen_exact env initial point pointOwner pointPointer index pointArray bounded
  have hContains := contains_exact env initial columns columnsOwner columnsPointer index.toUInt64 columnsArray
  cases hf : frozen point index <;> cases hc : contains columns index.toUInt64
  all_goals
    simp only [freeBody, func28, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.drop, freeFrame, inputValues, pointValues, List.reverse_cons, List.reverse_nil,
      List.cons_append, List.nil_append, boolWord, Bool.false_eq_true, ↓reduceIte]
    repeat' ((try wp_fixed_frame [boolWord, hf, hc, noOverflow]) <;>
      first
      | (refine wp_call_tw hFrozen ?_; rintro final values ⟨rfl, rfl⟩)
      | (refine wp_call_tw hContains ?_; rintro final values ⟨rfl, rfl⟩)
      | (refine wp_iff_cons rfl ?_; simp [noOverflow]))
  · simpa [freeFrame, freeScratch, inputValues, pointValues, boolWord, hf] using
      done (by simp [eligible, hf, hc])
  all_goals
    simpa [freeFrame, freeScratch, inputValues, pointValues, boolWord, hf] using
      next (by simp [eligible, hf, hc])

end Project.Beck.Execution
