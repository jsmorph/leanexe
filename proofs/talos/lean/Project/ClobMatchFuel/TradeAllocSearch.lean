import Project.ClobMatchFuel.Allocation
import Project.Runtime.FreeList
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop

namespace Project.ClobMatchFuel.TradeAllocSearch

open Wasm Project.Common Project.Runtime Project.ClobMatchFuel

set_option maxHeartbeats 8000000
set_option maxRecDepth 1048576

macro "wp_run_big" "(" hParams:term "," hLocals:term "," hValues:term ")" : tactic => `(tactic|
  simp (config := { maxSteps := 10000000 }) [wp_simp,
    Locals.get, Locals.set?, Locals.validIndex,
    Function.toLocals, Function.numParams, Function.numLocals,
    List.take, List.drop, List.replicate, List.length, List.map,
    List.length_set, List.getElem?_set,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceSub,
    ValueType.zero, List.headD, ($hParams), ($hLocals), ($hValues)])

def tradeAllocSearchFrame (base : Locals)
    (need previous current capacity next result : UInt64) : Locals :=
  { base with
    locals := ((((((base.locals.set 69 (.i64 need)).set 70 (.i64 previous)).set
      71 (.i64 current)).set 72 (.i64 capacity)).set 73 (.i64 next)).set
      74 (.i64 result)) }

def tradeAllocSearchBodyProg : Wasm.Program :=
  [
  .localGet 80,
  .constI64 (0 : UInt64),
  .eqI64,
  .br_if 1,
  .localGet 83,
  .constI64 (0 : UInt64),
  .neI64,
  .br_if 1,
  .localGet 80,
  .constI64 (32 : UInt64),
  .subI64,
  .wrapI64,
  .load64 (0 : UInt32),
  .localSet 81,
  .localGet 80,
  .constI64 (8 : UInt64),
  .subI64,
  .wrapI64,
  .load64 (0 : UInt32),
  .localSet 82,
  .localGet 81,
  .localGet 78,
  .geUI64,
  .iff 0 0 [
    .localGet 79,
    .constI64 (0 : UInt64),
    .eqI64,
    .iff 0 0 [
      .localGet 82,
      .globalSet 1
    ] [
      .localGet 79,
      .constI64 (8 : UInt64),
      .subI64,
      .wrapI64,
      .localGet 82,
      .store64 (0 : UInt32)
    ],
    .localGet 80,
    .constI64 (48 : UInt64),
    .subI64,
    .wrapI64,
    .constI64 (5501223100278326855 : UInt64),
    .store64 (0 : UInt32),
    .localGet 80,
    .constI64 (40 : UInt64),
    .subI64,
    .wrapI64,
    .constI64 (1 : UInt64),
    .store64 (0 : UInt32),
    .localGet 80,
    .constI64 (32 : UInt64),
    .subI64,
    .wrapI64,
    .localGet 81,
    .store64 (0 : UInt32),
    .localGet 80,
    .constI64 (24 : UInt64),
    .subI64,
    .wrapI64,
    .constI64 (2 : UInt64),
    .store64 (0 : UInt32),
    .localGet 80,
    .constI64 (16 : UInt64),
    .subI64,
    .wrapI64,
    .constI64 (4 : UInt64),
    .store64 (0 : UInt32),
    .localGet 80,
    .constI64 (8 : UInt64),
    .subI64,
    .wrapI64,
    .constI64 (0 : UInt64),
    .store64 (0 : UInt32),
    .localGet 80,
    .localSet 83
  ] [
    .localGet 80,
    .localSet 79,
    .localGet 82,
    .localSet 80
  ],
  .br 0
]

def tradeAllocSearchProg : Wasm.Program :=
  [.block 0 0 [.loop 0 0 tradeAllocSearchBodyProg]]

private def noFitInv (st0 : Store Unit) (base : Locals) (need : UInt64)
    (original : List FreeNode) :
    AssertionF Unit :=
  fun st s =>
    ∃ previous capacity next : UInt64,
      ∃ visited remaining : List FreeNode,
      st = st0 ∧
      original = visited ++ remaining ∧
      FreeListAt st0.mem remaining ∧
      (∀ node ∈ remaining, node.capacity < need) ∧
      s = tradeAllocSearchFrame base need previous (freeHead remaining)
        capacity next 0

private def noFitMeasure (original : List FreeNode) (_ : Store Unit)
    (s : Locals) : Nat :=
  match s.get 80 with
  | some (.i64 current) => scanRemaining original current
  | _ => 0

theorem tradeAllocSearchProg_no_fit
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (need capacity next : UInt64) (nodes : List FreeNode)
    (hParams : base.params.length = 9)
    (hLocals : base.locals.length = 76)
    (hValues : base.values = [])
    (hList : FreeListAt st.mem nodes)
    (hNoFit : takeFirstFit need nodes = none)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ previous capacity next : UInt64,
      wp «module» rest Q st
        (tradeAllocSearchFrame base need previous 0 capacity next 0) env) :
    wp «module» (tradeAllocSearchProg ++ rest) Q st
      (tradeAllocSearchFrame base need 0 (freeHead nodes) capacity next 0) env := by
  simp only [tradeAllocSearchProg, List.cons_append, List.nil_append]
  apply wp_block_cons
  apply wp_loop_cons (Inv := noFitInv st base need nodes)
    (μ := noFitMeasure nodes)
  · exact ⟨0, capacity, next, [], nodes, rfl, by simp, hList,
      (takeFirstFit_none_iff need nodes).mp hNoFit, rfl⟩
  · rintro st1 s1
      ⟨previous, currentCapacity, currentNext, visited, remaining, rfl,
        hSplit, hRemaining, hSmall, rfl⟩
    cases remaining with
    | nil =>
        simp only [tradeAllocSearchBodyProg, tradeAllocSearchFrame, freeHead]
        wp_run_big (hParams, hLocals, hValues)
        simpa only [tradeAllocSearchFrame, hValues] using
          hNext previous currentCapacity currentNext
    | cons node tail =>
        cases hRemaining with
        | cons hp h32 hfit hrc hcapacity hnext hsep htail =>
            have hroot : node.root ≠ 0 := by
              intro hzero
              have := congrArg UInt64.toNat hzero
              simp at this
              omega
            have hcapSmall : node.capacity < need :=
              hSmall node List.mem_cons_self
            have hsub32 : (node.root - 32).toNat = node.root.toNat - 32 :=
              toNat_sub_le _ _ (by
                rw [show (32 : UInt64).toNat = 32 from rfl]
                omega)
            have hsub8 : (node.root - 8).toNat = node.root.toNat - 8 :=
              toNat_sub_le _ _ (by
                rw [show (8 : UInt64).toNat = 8 from rfl]
                omega)
            have hcapBound : (node.root - 32).toNat % 4294967296 + 8 ≤
                st1.mem.pages * 65536 := by
              rw [hsub32, Nat.mod_eq_of_lt (by omega)]
              omega
            have hnextBound : (node.root - 8).toNat % 4294967296 + 8 ≤
                st1.mem.pages * 65536 := by
              rw [hsub8, Nat.mod_eq_of_lt (by omega)]
              omega
            have hcapacity' : st1.mem.read64
                (UInt32.ofNat ((node.root - 32).toNat % 4294967296)) =
                node.capacity := by
              rw [← toUInt32_eq_ofNat]
              exact hcapacity
            have hnext' : st1.mem.read64
                (UInt32.ofNat ((node.root - 8).toNat % 4294967296)) =
                freeHead tail := by
              rw [← toUInt32_eq_ofNat]
              exact hnext
            simp only [tradeAllocSearchBodyProg, tradeAllocSearchFrame, freeHead]
            wp_run_big (hParams, hLocals, hValues)
            simp only [if_neg hroot]
            rw [if_neg (by omega)]
            rw [if_neg (by omega)]
            simp only [hcapacity', hnext']
            have hnotFit : ¬ need ≤ node.capacity := by
              rw [UInt64.le_iff_toNat_le]
              rw [UInt64.lt_iff_toNat_lt] at hcapSmall
              omega
            simp only [if_neg hnotFit]
            refine wp_iff_cons rfl ?_
            rw [if_neg (by simp)]
            wp_run_big (hParams, hLocals, hValues)
            have hSplitNext :
                nodes = (visited ++ [node]) ++ tail := by
              simpa [List.append_assoc] using hSplit
            refine ⟨⟨node.root, node.capacity, freeHead tail,
              visited ++ [node], tail, rfl, hSplitNext, htail, ?_, ?_⟩, ?_⟩
            · intro other hother
              exact hSmall other (List.mem_cons_of_mem _ hother)
            · unfold tradeAllocSearchFrame
              rw [hValues]
              congr 1
              apply List.ext_getElem?
              intro i
              by_cases h70 : 70 = i
              · subst i
                simp [List.getElem?_set]
              by_cases h71 : 71 = i
              · subst i
                simp [List.getElem?_set]
              by_cases h72 : 72 = i
              · subst i
                simp [List.getElem?_set]
              by_cases h73 : 73 = i
              · subst i
                simp [List.getElem?_set]
              · simp [List.getElem?_set, h70, h71, h72, h73]
            · have hBefore := hList.scanRemaining_suffix hSplit
              have hAfter := hList.scanRemaining_suffix hSplitNext
              unfold noFitMeasure
              simp [Locals.get, hParams, hLocals]
              rw [hAfter]
              have hBefore' :
                  scanRemaining nodes node.root = tail.length + 1 := by
                simpa [freeHead] using hBefore
              rw [hBefore']
              simp

end Project.ClobMatchFuel.TradeAllocSearch
