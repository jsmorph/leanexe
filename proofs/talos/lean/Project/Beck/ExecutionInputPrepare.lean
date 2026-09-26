import Project.Beck.ExecutionInputEmpty

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def inputPreparedSaved (saved : InputSaved) (pointer : UInt64) (jobs categories : Nat) (index : Fin 50) : Value :=
  match index.val with
  | 14 | 16 => .i64 jobs.toUInt64
  | 15 | 19 => .i64 categories.toUInt64
  | 17 | 18 => .i64 pointer
  | 21 => .i64 2
  | 22 => .i64 0
  | _ => saved index

def inputPreparedTail (tail : InputTail) (pointer : UInt64) (index : Fin 10) : UInt64 :=
  match index.val with
  | 0 => pointer
  | 1 => 1
  | _ => tail index

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1500000 in
theorem inputPrepare_exact (env : HostEnv Unit) (initial : Store Unit)
    (pointer : UInt64) (saved : InputSaved) (tail : InputTail) (words : Array UInt64)
    (represented : UInt64Array.At initial pointer words) (lengthBound : 2 ≤ words.size)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (next : wp Project.Beck.«module» rest Q initial
      (inputFrame pointer (inputPreparedSaved saved pointer words[0]!.toNat words[1]!.toNat)
        (inputPreparedTail tail pointer)) env) :
    wp Project.Beck.«module» (inputEligible.take 34 ++ rest) Q initial (inputFrame pointer saved tail) env := by
  simp only [inputEligible, inputInBounds, func6, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.take, List.cons_append, List.nil_append, inputFrame, inputPrefix]
  wp_fixed_frame_step
  wp_fixed_frame_step
  wp_fixed_frame_step
  wp_fixed_frame_step
  refine CheckedArrayGet.checkedGetCore_spec 52 53 Project.Beck.«module» env initial _ pointer words 0 []
    rfl rfl rfl represented (by omega) _ _ ?_
  wp_fixed_frame_step
  wp_fixed_frame_step
  wp_fixed_frame_step
  wp_fixed_frame_step
  wp_fixed_frame_step
  refine CheckedArrayGet.checkedGetCore_spec 52 53 Project.Beck.«module» env initial _ pointer words 1 []
    rfl rfl rfl represented (by omega) _ _ ?_
  wp_fixed_frame
  simpa only [inputFrame, inputPrefix, inputPreparedSaved, inputPreparedTail, Nat.toUInt64, UInt64.ofNat_toNat,
    getElem!_pos words 0 (by omega), getElem!_pos words 1 (by omega),
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, List.cons_append, List.nil_append] using next

#print axioms inputPrepare_exact

end Project.Beck.Execution
