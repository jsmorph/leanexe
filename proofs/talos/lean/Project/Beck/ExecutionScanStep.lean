import Project.Beck.ExecutionRead
import Project.ProofKit.CheckedNatAddArithmetic

namespace Project.Beck.Execution

open Wasm Project.ProofKit LeanExe.Examples.Beck

abbrev ScanScratch := Fin 26 → Value

def frozenFrame (point : Point) (owner pointer : UInt64) (index : Nat) (found : Bool)
    (scratch : ScanScratch) : Locals :=
  { params := [.i64 point.denominator, .i64 owner, .i64 pointer]
    locals := [.i64 (boolWord found), .i64 0, .i64 0,
      scratch 0, scratch 1, scratch 2, scratch 3, scratch 4, scratch 5, scratch 6,
      scratch 7, scratch 8, scratch 9, scratch 10, scratch 11, scratch 12,
      scratch 13, scratch 14, scratch 15, scratch 16, scratch 17, scratch 18,
      .i64 index.toUInt64, .i64 point.numerators.size.toUInt64, .i64 1,
      scratch 19, scratch 20, scratch 21, scratch 22, scratch 23, scratch 24, scratch 25] }

def frozenScratch (point : Point) (owner pointer : UInt64) (index : Nat) (live : Bool)
    (scratch : ScanScratch) : ScanScratch := fun k =>
  match k.val with
  | 0 | 4 | 11 => .i64 index.toUInt64
  | 1 | 8 => .i64 point.denominator
  | 2 | 9 => .i64 owner
  | 3 | 10 => .i64 pointer
  | 5 => .i64 (boolWord live)
  | 6 | 7 | 22 => .i64 0
  | 19 => .i64 (if live then 1 else index.toUInt64)
  | 20 => .i64 1
  | 21 => .i64 (if live then 0 else (index + 1).toUInt64)
  | _ => scratch k

def frozenBody : Wasm.Program :=
  match (func13[16]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

set_option maxHeartbeats 600000 in
theorem frozenStep_exact (env : HostEnv Unit) (initial : Store Unit) (point : Point)
    (owner pointer : UInt64) (index : Nat) (scratch : ScanScratch)
    (array : UInt64Array.At initial pointer point.numerators) (bounded : index < point.numerators.size)
    (Q : Assertion Unit)
    (next : frozen point index = true → Q (.Break 0 initial (frozenFrame point owner pointer (index + 1) false
      (frozenScratch point owner pointer index false scratch))))
    (done : frozen point index = false → Q (.Break 1 initial (frozenFrame point owner pointer index true
      (frozenScratch point owner pointer index true scratch)))) :
    wp «module» (frozenBody.drop 4) Q initial (frozenFrame point owner pointer index false scratch) env := by
  have fit : index + 1 < UInt64.size := by have := array.size_lt; omega
  have noOverflow : ¬UInt64.ofNat index + 1 < UInt64.ofNat index :=
    CheckedNatAdd.guard_of_fits index 1 fit
  have addition : index.toUInt64 + 1 = (index + 1).toUInt64 := (UInt64.ofNat_add _ _).symm
  have call := frozen_exact env initial point owner pointer index array bounded
  by_cases frozen : LeanExe.Examples.Beck.frozen point index = true
  all_goals
    simp only [frozenBody, func13, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.drop, frozenFrame, boolWord, Bool.false_eq_true, ↓reduceIte]
    repeat' ((try wp_fixed_frame [boolWord, frozen, noOverflow, addition]) <;>
      first
      | (refine wp_call_tw call ?_; rintro final values ⟨rfl, rfl⟩)
      | (refine wp_iff_cons rfl ?_; simp [noOverflow]))
  · simpa [frozenFrame, frozenScratch, boolWord] using next frozen
  · have live : LeanExe.Examples.Beck.frozen point index = false := Bool.eq_false_iff.mpr frozen
    simpa [frozenFrame, frozenScratch, boolWord] using done live

end Project.Beck.Execution
