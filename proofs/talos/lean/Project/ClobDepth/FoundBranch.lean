import Project.ClobDepth.FoundAllocPrepare
import Project.ClobDepth.FoundBranchFacts

/-!
# Found-price branch

This theorem composes the generated found-price phases from the scan outcome
through the owned replaced level array.  The branch enters the guarded
allocation with the matched flag, uses bump allocation under the stated
empty-free-list premise, and assigns the returned pointer to the result
locals.
-/

namespace Project.ClobDepth.FoundBranch

open Wasm Project.Common Project.Clob Project.ClobDepth
  Project.ClobDepth.Model Project.ClobDepth.Properties
  Project.ClobDepth.Representation
  Project.ClobDepth.FoundBranchFacts

set_option maxRecDepth 1048576
set_option maxHeartbeats 8000000

structure ResultLocalsAt (final : Locals) (target : UInt64) : Prop where
  params : final.params.length = 4
  locals : final.locals.length = 26
  values : final.values = []
  result : final.locals[7]? = some (.i64 target)
  owner : final.locals[8]? = some (.i64 target)
  pointer : final.locals[9]? = some (.i64 target)

set_option Elab.async false in
theorem foundProg_spec
    (env : HostEnv Unit) (st : Store Unit)
    (owner source price qty sourceCapacity g0 g2 : UInt64)
    (levels : List LevelL) (i : Nat)
    (hLength : levels.length < 4294967296)
    (hIndex : priceIdx levels price = some i)
    (hSource32 :
      source.toNat + fixedArrayBytes levels.length 2 < 4294967296)
    (hSource48 : 48 ≤ source.toNat)
    (hSourceCapacity :
      fixedArrayBytes levels.length 2 ≤ sourceCapacity.toNat)
    (hSourceBelow : source.toNat + sourceCapacity.toNat ≤ g0.toNat)
    (hOwned : OwnedLevelArrayAt st source sourceCapacity levels)
    (hGlobal0 : st.globals.globals[0]? = some (.i64 g0))
    (hGlobal1 : st.globals.globals[1]? = some (.i64 0))
    (hGlobal2 : st.globals.globals[2]? = some (.i64 g2))
    (hPages : st.mem.pages ≤ 65536)
    (hFit32 : g0.toNat + 48 + (capacity levels).toNat < 4294967296)
    (hFit : g0.toNat + 48 + (capacity levels).toNat ≤
      st.mem.pages * 65536)
    (hsep : flatWordsDisjoint
      (flatWordsRegion (target g0) (levels.length * 2))
      (flatWordsRegion source (levels.length * 2)))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ st1,
      ResultState st st1 g0 g2 source sourceCapacity levels i
        { lprice := price, lqty := levels[i]!.lqty + qty } →
      ∀ final, ResultLocalsAt final (target g0) →
      wp «module» rest Q st1 final env) :
    wp «module» (Entry.foundProg ++ rest) Q st
      (FoundPrepare.branchFrame owner source price qty levels i) env := by
  have hi : i < levels.length := priceIdx_some_lt hIndex
  have hNeedNat : (capacity levels).toNat =
      fixedArrayBytes levels.length 2 := by
    apply fixedArrayBytesU_toNat
    · rw [size_eq]
      omega
    · decide
    · unfold fixedArrayBytes
      rw [size_eq]
      omega
  have hNeed8 : 8 ≤ (capacity levels).toNat := by
    rw [hNeedNat]
    unfold fixedArrayBytes
    omega
  have hRoot : (target g0).toNat = g0.toNat + 48 := by
    unfold target
    apply fixedArrayBumpRoot_toNat
    rw [size_eq]
    omega
  have hTop : (g0 + 48 + capacity levels).toNat =
      g0.toNat + 48 + (capacity levels).toNat := by
    rw [UInt64.toNat_add, show (g0 + 48).toNat = g0.toNat + 48 by
      simpa [target] using hRoot]
    exact Nat.mod_eq_of_lt (by omega)
  have hTarget32 :
      (target g0).toNat + (levels.length * 2 + 1) * 8 < 4294967296 := by
    rw [hRoot]
    unfold fixedArrayBytes at hNeedNat
    omega
  have hTargetFit :
      (target g0).toNat + (levels.length * 2 + 1) * 8 ≤
        (allocatedStore st g0 g2 levels).mem.pages * 65536 := by
    rw [allocatedStore_pages, hRoot]
    unfold fixedArrayBytes at hNeedNat
    omega
  have hCopySource32 :
      source.toNat + (levels.length * 2 + 1) * 8 < 4294967296 := by
    unfold fixedArrayBytes at hSource32
    omega
  have hTotal64 : levels.length * 2 < UInt64.size := by
    rw [size_eq]
    omega
  have hLengthU : (UInt64.ofNat levels.length).toNat = levels.length := by u64_omega
  have hTotalU : (UInt64.ofNat levels.length * 2).toNat =
      levels.length * 2 := by
    rw [UInt64.toNat_mul, hLengthU]
    exact Nat.mod_eq_of_lt hTotal64
  let prepared := FoundAllocPrepare.allocFrame owner source price qty
    levels i
  let bumped := MissingBump.bumpFrame prepared g0 (capacity levels)
  let copyBase := MissingFinish.finishFrame bumped (target g0)
  have hPreparedParams : prepared.params.length = 4 := by
    simp [prepared, FoundAllocPrepare.allocFrame]
  have hPreparedLocals : prepared.locals.length = 26 := by
    simp [prepared, FoundAllocPrepare.allocFrame]
  have hPreparedValues : prepared.values = [] := by
    simp [prepared, FoundAllocPrepare.allocFrame]
  have hPreparedNeed : prepared.locals[20]? =
      some (.i64 (capacity levels)) := by
    simp [prepared, FoundAllocPrepare.allocFrame, capacity]
  have hPreparedResult : prepared.locals[25]? = some (.i64 0) := by
    simp [prepared, FoundAllocPrepare.allocFrame]
  have hPreparedCurrent : prepared.locals[22]? = some (.i64 0) := by
    simp [prepared, FoundAllocPrepare.allocFrame]
  have hBumpedParams : bumped.params.length = 4 := by
    simp [bumped, MissingBump.bumpFrame, hPreparedParams]
  have hBumpedLocals : bumped.locals.length = 26 := by
    simp [bumped, MissingBump.bumpFrame, hPreparedLocals]
  have hBumpedValues : bumped.values = [] := by
    simp [bumped, MissingBump.bumpFrame]
  have hBumpedTarget : bumped.locals[25]? = some (.i64 (target g0)) := by
    simp [bumped, MissingBump.bumpFrame, prepared,
      FoundAllocPrepare.allocFrame, target]
  have hBumpedCount : bumped.locals[12]? =
      some (.i64 (UInt64.ofNat levels.length)) := by
    simp [bumped, MissingBump.bumpFrame, prepared,
      FoundAllocPrepare.allocFrame]
  have hBumpGlobal2 :
      (fixedArrayAllocBumpStore st g0 (capacity levels) 2).globals.globals[2]? =
        some (.i64 g2) :=
    fixedArrayAllocBumpStore_global_of_ne_zero st g0 (capacity levels) 2 2
      (.i64 g2) (by decide) hGlobal2
  have hFinishBound :
      (target g0).toNat % 4294967296 + 8 ≤
        (fixedArrayAllocBumpStore st g0 (capacity levels) 2).mem.pages *
          65536 := by
    rw [Nat.mod_eq_of_lt (by omega), hRoot,
      fixedArrayAllocBumpStore_pages]
    omega
  have hCopyParams : copyBase.params.length = 4 := by
    simp [copyBase, MissingFinish.finishFrame, hBumpedParams]
  have hCopyLocals : copyBase.locals.length = 26 := by
    simp [copyBase, MissingFinish.finishFrame, hBumpedLocals]
  have hCopyValues : copyBase.values = [] := by
    simp [copyBase, MissingFinish.finishFrame]
  have hCopySource : copyBase.locals[10]? = some (.i64 source) := by
    simp [copyBase, MissingFinish.finishFrame, bumped,
      MissingBump.bumpFrame, prepared, FoundAllocPrepare.allocFrame]
  have hCopyTotal : copyBase.locals[13]? =
      some (.i64 (UInt64.ofNat levels.length * 2)) := by
    simp [copyBase, MissingFinish.finishFrame, bumped,
      MissingBump.bumpFrame, prepared, FoundAllocPrepare.allocFrame]
  have hCopyTarget : copyBase.locals[14]? = some (.i64 (target g0)) := by
    simp [copyBase, MissingFinish.finishFrame, hBumpedLocals]
  have hCopyCounter : copyBase.locals[15]? = some (.i64 0) := by
    simp [copyBase, MissingFinish.finishFrame, hBumpedLocals]
  have hCopyIndex : copyBase.locals[11]? =
      some (.i64 (UInt64.ofNat i)) := by
    simp [copyBase, MissingFinish.finishFrame, bumped,
      MissingBump.bumpFrame, prepared, FoundAllocPrepare.allocFrame]
  have hCopyPrice : copyBase.locals[16]? = some (.i64 price) := by
    simp [copyBase, MissingFinish.finishFrame, bumped,
      MissingBump.bumpFrame, prepared, FoundAllocPrepare.allocFrame]
  have hCopyQty : copyBase.locals[17]? =
      some (.i64 (levels[i]!.lqty + qty)) := by
    simp [copyBase, MissingFinish.finishFrame, bumped,
      MissingBump.bumpFrame, prepared, FoundAllocPrepare.allocFrame]
  have hInit := copyInvariant_initial st copyBase g0 g2 source
    sourceCapacity levels hCopyLocals hCopyValues hCopyCounter hNeed8 hFit32
    hRoot hSource32 hSource48 hSourceCapacity hSourceBelow hOwned
  rw [Entry.foundProg_decomposition]
  simp only [List.append_assoc]
  apply FoundPrepare.foundPrepareProg_spec env st owner source price qty
    levels i hLength hIndex hOwned.2
  simp only [FoundPrepare.prepareFrame, List.cons_append, List.nil_append]
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp)]
  rw [Entry.foundAllocProg_decomposition]
  simp only [Entry.foundSearchProg, Entry.foundBumpProg,
    List.append_assoc]
  apply FoundAllocPrepare.foundAllocPrepareProg_spec env st owner source
    price qty levels i hLength hGlobal1
  apply MissingSearch.missingSearchProg_empty env st prepared
    hPreparedParams hPreparedLocals hPreparedValues hPreparedCurrent
  apply MissingBump.missingBumpProg_spec env st prepared g0 (capacity levels)
    hPreparedParams hPreparedLocals hPreparedValues hPreparedNeed
    hPreparedResult hNeed8 hTop hFit32 hFit hPages hGlobal0
  apply FoundFinish.foundAllocFinishProg_spec env
    (fixedArrayAllocBumpStore st g0 (capacity levels) 2) bumped
    (target g0) (UInt64.ofNat levels.length) g2 hBumpedParams
    hBumpedLocals hBumpedValues hBumpedTarget hBumpedCount hBumpGlobal2
    hFinishBound
  apply FoundCopy.foundCopyProg_spec env
    (allocatedStore st g0 g2 levels) copyBase (target g0) source
    (capacity levels) levels hCopyParams hCopyLocals hCopyValues hCopySource
    hCopyTotal hCopyTarget hTotalU hTotal64 (by rw [hRoot]; omega)
    hCopySource32 hTarget32 hTargetFit hsep
  · exact hInit
  · intro st1 hInvariant
    apply FoundStore.foundStoreProg_spec env
      (allocatedStore st g0 g2 levels) st1 copyBase (target g0) source
      (capacity levels) price (levels[i]!.lqty + qty) levels i hCopyParams
      hCopyLocals hCopyValues hCopyIndex hCopyTarget hCopyPrice hCopyQty
      hInvariant hi hTotalU hTotal64 (by rw [hRoot]; omega)
      hCopySource32 hTarget32 hTargetFit hsep
    intro st2 hFinish
    have hResult := ResultState.of_finish hFinish hSource32 hSource48
      hSourceCapacity hSourceBelow hRoot (by omega) hOwned
    simp (config := { maxSteps := 10000000 }) [wp_simp,
      Entry.foundResultProg, List.cons_append, List.nil_append,
      FoundStore.storeResultFrame, MissingCopyInvariant.copyLoopFrame,
      copyBase, MissingFinish.finishFrame, bumped, MissingBump.bumpFrame,
      prepared, FoundAllocPrepare.allocFrame,
      Locals.get, Locals.set?,
      List.take, List.drop, List.length,
      Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
    refine hNext st2 hResult _ ?_
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp

end Project.ClobDepth.FoundBranch
