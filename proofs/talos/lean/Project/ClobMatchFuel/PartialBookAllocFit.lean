import Project.ClobMatchFuel.PartialBookAllocSearch
import Project.ClobMatchFuel.BookAllocFit

namespace Project.ClobMatchFuel.PartialBookAllocFit

open Wasm Project.Common Project.Runtime Project.Clob Project.ClobMatchFuel

set_option maxHeartbeats 8000000
set_option maxRecDepth 1048576

macro "wp_run_fit" "(" hParams:term "," hLocals:term "," hValues:term ")" : tactic => `(tactic|
  simp (config := { maxSteps := 10000000 }) [wp_simp,
    Locals.get, Locals.set?, Locals.validIndex,
    Function.toLocals, Function.numParams, Function.numLocals,
    List.take, List.drop, List.replicate, List.length, List.map,
    List.length_set, List.getElem?_set,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceSub,
    ValueType.zero, List.headD, ($hParams), ($hLocals), ($hValues)])

abbrev fixedArrayAllocFitMem := BookAllocFit.fixedArrayAllocFitMem
abbrev fixedArrayAllocFitStore := BookAllocFit.fixedArrayAllocFitStore
abbrev bookAllocFitMem := BookAllocFit.bookAllocFitMem
abbrev bookAllocFitStore := BookAllocFit.bookAllocFitStore

private def fitInv (st0 : Store Unit) (base : Locals) (need : UInt64)
    (skipped tail : List FreeNode) (choice : FreeChoice) :
    AssertionF Unit :=
  fun st s =>
    (∃ capacity next : UInt64, ∃ visited remaining : List FreeNode,
      st = st0 ∧
      skipped = visited ++ remaining ∧
      FreeListAt st0.mem (remaining ++ choice.node :: tail) ∧
      (∀ node ∈ remaining, node.capacity < need) ∧
      s = PartialBookAllocSearch.bookAllocSearchFrame base need
        (previousRoot 0 visited)
        (freeHead (remaining ++ choice.node :: tail)) capacity next 0) ∨
    (st = bookAllocFitStore st0 choice ∧
      s = PartialBookAllocSearch.bookAllocSearchFrame base need choice.previous
        choice.node.root choice.node.capacity choice.next choice.node.root)

private def fitMeasure (nodes : List FreeNode) (_ : Store Unit)
    (s : Locals) : Nat :=
  match s.get 84 with
  | some (.i64 result) =>
      if result = 0 then
        match s.get 81 with
        | some (.i64 current) => scanRemaining nodes current
        | _ => 0
      else
        0
  | _ => 0

set_option Elab.async false in
theorem bookAllocSearchProg_fit
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (need capacity next : UInt64) (nodes : List FreeNode)
    (choice : FreeChoice)
    (hParams : base.params.length = 9)
    (hLocals : base.locals.length = 76)
    (hValues : base.values = [])
    (hGlobal1 : st.globals.globals[1]? =
      some (.i64 (freeHead nodes)))
    (hList : FreeListAt st.mem nodes)
    (hTake : takeFirstFitFrom 0 need nodes = some choice)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q (bookAllocFitStore st choice)
      (PartialBookAllocSearch.bookAllocSearchFrame base need choice.previous
        choice.node.root choice.node.capacity choice.next choice.node.root) env) :
    wp «module» (PartialBookAllocSearch.bookAllocSearchProg ++ rest) Q st
      (PartialBookAllocSearch.bookAllocSearchFrame base need 0 (freeHead nodes)
        capacity next 0) env := by
  obtain ⟨skipped, tail, hnodes, hprevious, hnext, _, hsmall⟩ :=
    takeFirstFitFrom_some_decompose hTake
  subst nodes
  have hChoiceFit : need ≤ choice.node.capacity :=
    takeFirstFitFrom_some_capacity hTake
  have hChoiceRoot : choice.node.root ≠ 0 :=
    hList.roots_ne_zero choice.node
      (List.mem_append_right skipped List.mem_cons_self)
  simp only [PartialBookAllocSearch.bookAllocSearchProg, List.cons_append,
    List.nil_append]
  apply wp_block_cons
  apply wp_loop_cons
    (Inv := fitInv st base need skipped tail choice)
    (μ := fitMeasure (skipped ++ choice.node :: tail))
  · left
    exact ⟨capacity, next, [], skipped, rfl, by simp, hList, hsmall, rfl⟩
  · rintro st1 s1 hInv
    rcases hInv with hSearch | hDone
    · obtain ⟨currentCapacity, currentNext, visited, remaining, rfl,
          hSplit, hRemaining, hRemainingSmall, rfl⟩ := hSearch
      cases remaining with
      | cons node remaining =>
          simp only [List.cons_append] at hRemaining
          cases hRemaining with
          | cons hp h32 hfit hrc hcapacity hnodeNext hsep htailRep =>
              have hroot : node.root ≠ 0 := by
                intro hzero
                have := congrArg UInt64.toNat hzero
                simp at this
                omega
              have hcapSmall : node.capacity < need :=
                hRemainingSmall node List.mem_cons_self
              have hsub32 : (node.root - 32).toNat =
                  node.root.toNat - 32 :=
                toNat_sub_le _ _ (by
                  rw [show (32 : UInt64).toNat = 32 from rfl]
                  omega)
              have hsub8 : (node.root - 8).toNat =
                  node.root.toNat - 8 :=
                toNat_sub_le _ _ (by
                  rw [show (8 : UInt64).toNat = 8 from rfl]
                  omega)
              have hcapBound :
                  (node.root - 32).toNat % 4294967296 + 8 ≤
                    st1.mem.pages * 65536 := by
                rw [hsub32, Nat.mod_eq_of_lt (by omega)]
                omega
              have hnextBound :
                  (node.root - 8).toNat % 4294967296 + 8 ≤
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
                    freeHead (remaining ++ choice.node :: tail) := by
                rw [← toUInt32_eq_ofNat]
                exact hnodeNext
              simp only [PartialBookAllocSearch.bookAllocSearchBodyProg,
                PartialBookAllocSearch.bookAllocSearchFrame, freeHead]
              wp_run_fit (hParams, hLocals, hValues)
              simp only [if_neg hroot]
              rw [if_neg (Nat.not_lt.mpr hcapBound),
                if_neg (Nat.not_lt.mpr hnextBound)]
              simp only [hcapacity', hnext']
              have hnotFit : ¬ need ≤ node.capacity := by
                rw [UInt64.le_iff_toNat_le]
                rw [UInt64.lt_iff_toNat_lt] at hcapSmall
                omega
              simp only [if_neg hnotFit]
              refine wp_iff_cons rfl ?_
              rw [if_neg (by simp)]
              wp_run_fit (hParams, hLocals, hValues)
              have hSplitNext :
                  skipped = (visited ++ [node]) ++ remaining := by
                simpa [List.append_assoc] using hSplit
              have hOriginalBefore :
                  skipped ++ choice.node :: tail =
                    visited ++ (node :: remaining ++ choice.node :: tail) := by
                rw [hSplit]
                simp [List.append_assoc]
              have hOriginalAfter :
                  skipped ++ choice.node :: tail =
                    (visited ++ [node]) ++
                      (remaining ++ choice.node :: tail) := by
                rw [hSplit]
                simp [List.append_assoc]
              refine ⟨Or.inl ⟨node.capacity, freeHead
                (remaining ++ choice.node :: tail), visited ++ [node],
                remaining, rfl, hSplitNext, htailRep, ?_, ?_⟩, ?_⟩
              · intro other hother
                exact hRemainingSmall other
                  (List.mem_cons_of_mem node hother)
              · unfold PartialBookAllocSearch.bookAllocSearchFrame
                rw [hValues]
                congr 1
                apply List.ext_getElem?
                intro i
                by_cases h71 : 71 = i
                · subst i
                  simp [List.getElem?_set,
                    previousRoot_append_singleton]
                by_cases h72 : 72 = i
                · subst i
                  simp [List.getElem?_set]
                by_cases h73 : 73 = i
                · subst i
                  simp [List.getElem?_set]
                by_cases h74 : 74 = i
                · subst i
                  simp [List.getElem?_set]
                · simp [List.getElem?_set, h71, h72, h73, h74]
              · have hBefore := hList.scanRemaining_suffix hOriginalBefore
                have hAfter := hList.scanRemaining_suffix hOriginalAfter
                unfold fitMeasure
                simp [Locals.get, hParams, hLocals]
                rw [hAfter]
                have hBefore' :
                    scanRemaining (skipped ++ choice.node :: tail) node.root =
                      (remaining ++ choice.node :: tail).length + 1 := by
                  simpa [freeHead] using hBefore
                rw [hBefore']
                simp
      | nil =>
          simp only [List.nil_append] at hRemaining
          cases hRemaining with
          | cons hp h32 hfit hrc hcapacity hnodeNext hsep htailRep =>
              have hsub (offset : UInt64)
                  (hLow : 8 ≤ offset.toNat)
                  (hHigh : offset.toNat ≤ 48) :
                  (choice.node.root - offset).toNat =
                    choice.node.root.toNat - offset.toNat :=
                toNat_sub_le _ _ (by omega)
              have hbound (offset : UInt64)
                  (hLow : 8 ≤ offset.toNat)
                  (hHigh : offset.toNat ≤ 48) :
                  (choice.node.root - offset).toNat % 4294967296 + 8 ≤
                    st1.mem.pages * 65536 := by
                rw [hsub offset hLow hHigh,
                  Nat.mod_eq_of_lt (by omega)]
                omega
              have hcapacity' : st1.mem.read64
                  (UInt32.ofNat
                    ((choice.node.root - 32).toNat % 4294967296)) =
                    choice.node.capacity := by
                rw [← toUInt32_eq_ofNat]
                exact hcapacity
              have hnext' : st1.mem.read64
                  (UInt32.ofNat
                    ((choice.node.root - 8).toNat % 4294967296)) =
                    freeHead tail := by
                rw [← toUInt32_eq_ofNat]
                exact hnodeNext
              have hRuntimePrevious :
                  previousRoot 0 visited = choice.previous := by
                rw [hSplit] at hprevious
                simpa using hprevious.symm
              have hScanPositive :
                  0 < scanRemaining (skipped ++ choice.node :: tail)
                    choice.node.root := by
                have hScan := hList.scanRemaining_suffix
                  (visited := skipped) (remaining := choice.node :: tail) rfl
                have hScan' :
                    scanRemaining (skipped ++ choice.node :: tail)
                      choice.node.root = tail.length + 1 := by
                  simpa [freeHead] using hScan
                rw [hScan']
                simp
              have hFinalFrame :
                  { params := base.params,
                    locals := (((PartialBookAllocSearch.bookAllocSearchFrame base
                      need (previousRoot 0 visited) choice.node.root
                      currentCapacity currentNext 0).locals.set 73
                        (.i64 choice.node.capacity)).set 74
                        (.i64 (freeHead tail))).set 75
                        (.i64 choice.node.root) } =
                    PartialBookAllocSearch.bookAllocSearchFrame base need
                      choice.previous choice.node.root choice.node.capacity
                      choice.next choice.node.root := by
                unfold PartialBookAllocSearch.bookAllocSearchFrame
                rw [hValues]
                congr 1
                apply List.ext_getElem?
                intro i
                by_cases h75 : 75 = i
                · subst i
                  simp [List.getElem?_set]
                by_cases h74 : 74 = i
                · subst i
                  simp [List.getElem?_set, h75, hnext]
                by_cases h73 : 73 = i
                · subst i
                  simp [List.getElem?_set, h75, h74]
                · simp [List.getElem?_set, h75, h74, h73,
                    hRuntimePrevious, hnext]
              simp only [PartialBookAllocSearch.bookAllocSearchBodyProg,
                PartialBookAllocSearch.bookAllocSearchFrame, freeHead]
              wp_run_fit (hParams, hLocals, hValues)
              simp only [if_neg hChoiceRoot]
              rw [if_neg (Nat.not_lt.mpr
                  (hbound 32 (by decide) (by decide))),
                if_neg (Nat.not_lt.mpr
                  (hbound 8 (by decide) (by decide)))]
              simp only [hcapacity', hnext', if_pos hChoiceFit]
              refine wp_iff_cons rfl ?_
              wp_run_fit (hParams, hLocals, hValues)
              by_cases hPreviousZero : choice.previous = 0
              · refine wp_iff_cons (c := 1) (vs := [])
                  (by simp [hRuntimePrevious, hPreviousZero]) ?_
                wp_run_fit (hParams, hLocals, hValues)
                simp only [hGlobal1]
                rw [if_neg (Nat.not_lt.mpr
                    (hbound 48 (by decide) (by decide))),
                  if_neg (Nat.not_lt.mpr
                    (hbound 40 (by decide) (by decide))),
                  if_neg (Nat.not_lt.mpr
                    (hbound 32 (by decide) (by decide))),
                  if_neg (Nat.not_lt.mpr
                    (hbound 24 (by decide) (by decide))),
                  if_neg (Nat.not_lt.mpr
                    (hbound 16 (by decide) (by decide))),
                  if_neg (Nat.not_lt.mpr
                    (hbound 8 (by decide) (by decide)))]
                refine ⟨Or.inr ⟨?_, ?_⟩, ?_⟩
                · simp only [bookAllocFitStore,
                    BookAllocFit.bookAllocFitStore,
                    BookAllocFit.fixedArrayAllocFitStore,
                    BookAllocFit.fixedArrayAllocFitMem, unlinkFreeChoice,
                    if_pos hPreviousZero, hnext, ← toUInt32_eq_ofNat]
                · simpa only [PartialBookAllocSearch.bookAllocSearchFrame] using
                    hFinalFrame
                · unfold fitMeasure
                  simp [Locals.get, hParams, hLocals, hChoiceRoot,
                    hScanPositive]
              · refine wp_iff_cons (c := 0) (vs := [])
                  (by simp [hRuntimePrevious, hPreviousZero]) ?_
                wp_run_fit (hParams, hLocals, hValues)
                have hSkippedNonempty : skipped ≠ [] := by
                  intro hEmpty
                  rw [hEmpty] at hSplit
                  have hVisitedEmpty : visited = [] := by
                    simp only [List.append_nil] at hSplit
                    exact Eq.symm hSplit
                  subst visited
                  simp only [previousRoot] at hRuntimePrevious
                  exact hPreviousZero hRuntimePrevious.symm
                let predecessor := skipped.getLast hSkippedNonempty
                have hsplitLast :
                    skipped.dropLast ++ [predecessor] = skipped :=
                  List.dropLast_append_getLast hSkippedNonempty
                have hPrevious : choice.previous = predecessor.root := by
                  rw [hprevious, ← hsplitLast,
                    previousRoot_append_singleton]
                have hPredecessorMem :
                    predecessor ∈ skipped ++ choice.node :: tail := by
                  rw [← hsplitLast]
                  simp
                obtain ⟨hPrevious48, hPrevious32, hPreviousFit⟩ :=
                  hList.mem_bounds hPredecessorMem
                have hPreviousBound :
                    (choice.previous - 8).toNat % 4294967296 + 8 ≤
                      st1.mem.pages * 65536 := by
                  rw [hPrevious, toNat_sub_le _ _ (by
                    rw [show (8 : UInt64).toNat = 8 from rfl]
                    omega)]
                  rw [show (8 : UInt64).toNat = 8 from rfl,
                    Nat.mod_eq_of_lt (by omega)]
                  omega
                rw [hRuntimePrevious,
                  if_neg (Nat.not_lt.mpr hPreviousBound),
                  if_neg (Nat.not_lt.mpr
                    (hbound 48 (by decide) (by decide))),
                  if_neg (Nat.not_lt.mpr
                    (hbound 40 (by decide) (by decide))),
                  if_neg (Nat.not_lt.mpr
                    (hbound 32 (by decide) (by decide))),
                  if_neg (Nat.not_lt.mpr
                    (hbound 24 (by decide) (by decide))),
                  if_neg (Nat.not_lt.mpr
                    (hbound 16 (by decide) (by decide))),
                  if_neg (Nat.not_lt.mpr
                    (hbound 8 (by decide) (by decide)))]
                refine ⟨Or.inr ⟨?_, ?_⟩, ?_⟩
                · simp only [bookAllocFitStore,
                    BookAllocFit.bookAllocFitStore,
                    BookAllocFit.fixedArrayAllocFitStore,
                    BookAllocFit.fixedArrayAllocFitMem, unlinkFreeChoice,
                    if_neg hPreviousZero, hnext, ← toUInt32_eq_ofNat]
                · simpa only [PartialBookAllocSearch.bookAllocSearchFrame,
                    hRuntimePrevious] using hFinalFrame
                · unfold fitMeasure
                  simp [Locals.get, hParams, hLocals, hChoiceRoot,
                    hScanPositive]
    · rcases hDone with ⟨rfl, rfl⟩
      simp only [PartialBookAllocSearch.bookAllocSearchBodyProg,
        PartialBookAllocSearch.bookAllocSearchFrame]
      wp_run_fit (hParams, hLocals, hValues)
      simp only [if_neg hChoiceRoot]
      simpa [PartialBookAllocSearch.bookAllocSearchFrame, hValues] using hNext

end Project.ClobMatchFuel.PartialBookAllocFit
