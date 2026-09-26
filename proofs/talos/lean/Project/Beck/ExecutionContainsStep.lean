import Project.Beck.ExecutionRead
import Project.ProofKit.CheckedNatAddArithmetic

namespace Project.Beck.Execution

open Wasm Project.ProofKit LeanExe.Examples.Beck

abbrev ContainsScratch := Fin 20 → Value

def containsFrame (xs : Array UInt64) (owner pointer value : UInt64) (index : Nat) (found : Bool)
    (scratch : ContainsScratch) : Locals :=
  { params := [.i64 owner, .i64 pointer, .i64 value]
    locals := [.i64 (boolWord found), .i64 (boolWord found), .i64 0,
      scratch 0, scratch 1, scratch 2, scratch 3, scratch 4, scratch 5, scratch 6,
      scratch 7, scratch 8, scratch 9, scratch 10,
      .i64 index.toUInt64, .i64 xs.size.toUInt64, .i64 1,
      scratch 11, scratch 12, scratch 13, scratch 14, scratch 15, scratch 16,
      scratch 17, scratch 18, scratch 19] }

def containsScratch (pointer : UInt64) (index : Nat) (found : Bool)
    (scratch : ContainsScratch) : ContainsScratch := fun k =>
  match k.val with
  | 0 => .i64 index.toUInt64
  | 1 | 2 | 14 | 15 => .i64 (boolWord found)
  | 3 | 16 => .i64 0
  | 11 => .i64 (if found then pointer else index.toUInt64)
  | 12 => .i64 (if found then index.toUInt64 else 1)
  | 13 => .i64 (if found then 1 else (index + 1).toUInt64)
  | _ => scratch k

def containsBody : Wasm.Program :=
  match (func20[16]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

set_option maxHeartbeats 600000 in
theorem containsStep_exact (env : HostEnv Unit) (initial : Store Unit) (xs : Array UInt64)
    (owner pointer value : UInt64) (index : Nat) (scratch : ContainsScratch)
    (array : UInt64Array.At initial pointer xs) (bounded : index < xs.size)
    (Q : Assertion Unit)
    (next : xs[index] ≠ value → Q (.Break 0 initial (containsFrame xs owner pointer value (index + 1) false
      (containsScratch pointer index false scratch))))
    (done : xs[index] = value → Q (.Break 1 initial (containsFrame xs owner pointer value index true
      (containsScratch pointer index true scratch)))) :
    wp «module» (containsBody.drop 4) Q initial (containsFrame xs owner pointer value index false scratch) env := by
  have fit : index + 1 < UInt64.size := by have := array.size_lt; omega
  have noOverflow : ¬UInt64.ofNat index + 1 < UInt64.ofNat index :=
    CheckedNatAdd.guard_of_fits index 1 fit
  by_cases found : xs[index] = value
  all_goals
    simp only [containsBody, func20, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.drop, containsFrame, boolWord, Bool.false_eq_true, ↓reduceIte]
    repeat' (first
      | (refine CheckedArrayGet.checkedGetCore_spec 20 21 «module» env initial _ pointer xs index []
          rfl rfl rfl array bounded _ _ ?_)
      | wp_fixed_frame_step
      | ((first
          | rw [wp_eqI64_cons]
          | rw [wp_eqz_cons]
          | rw [wp_neI64_cons]
          | rw [wp_ltUI64_cons]
          | rw [wp_addI64_cons]
          | rw [wp_nil]
          | rw [wp_localTee_cons]
          | rw [wp_br_if_cons]
          | rw [wp_br_cons]) <;>
        simp only [List.take, List.drop, List.append_nil, Nat.toUInt64, found, ↓reduceIte])
      | (try simp only [wp_iff_control_types]
         refine wp_iff_cons rfl ?_
         first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)]))
  · simpa [containsFrame, containsScratch, boolWord] using done found
  · wp_fixed_frame [noOverflow]
    refine wp_iff_cons rfl ?_
    simp
    simpa [containsFrame, containsScratch, boolWord] using next found

end Project.Beck.Execution
