import Project.ClobDepth.MissingBranch
import Project.ClobDepth.FoundBranch

/-!
# Level-update function

Function 3 scans the represented level array for the incoming price and
either appends a missing level or replaces the matched quantity.  The
composition returns one semantic result: the returned array represents
`addLevelL levels price qty` with a capacity derived from the result length,
beside allocator globals, page equality, and the below-heap memory frame.
-/

namespace Project.ClobDepth.Func3

open Wasm Project.Common Project.Clob Project.ClobDepth
  Project.ClobDepth.Model Project.ClobDepth.Properties
  Project.ClobDepth.Representation

set_option maxRecDepth 1048576
set_option maxHeartbeats 8000000

def target (g0 : UInt64) : UInt64 :=
  g0 + 48

def capacity (levels : List LevelL) (price qty : UInt64) : UInt64 :=
  fixedArrayBytesU (addLevelL levels price qty).length 2

structure UpdateResult (st0 st : Store Unit)
    (g0 g2 source sourceCapacity price qty : UInt64)
    (levels : List LevelL) : Prop where
  pages : st.mem.pages = st0.mem.pages
  globals : st.globals.globals =
    (st0.globals.globals.set 0
      (.i64 (g0 + 48 + capacity levels price qty))).set 2 (.i64 (g2 + 1))
  resultOwned : OwnedLevelArrayAt st (target g0)
    (capacity levels price qty) (addLevelL levels price qty)
  sourceOwned : OwnedLevelArrayAt st source sourceCapacity levels
  bytesBefore : ∀ a : Nat, a < g0.toNat →
    st.mem.bytes a = st0.mem.bytes a

theorem UpdateResult.of_missing
    {st0 st : Store Unit} {g0 g2 source sourceCapacity price qty : UInt64}
    {levels : List LevelL}
    (hIndex : priceIdx levels price = none)
    (hResult : MissingBranchFacts.ResultState st0 st g0 g2 source
      sourceCapacity levels { lprice := price, lqty := qty }) :
    UpdateResult st0 st g0 g2 source sourceCapacity price qty levels := by
  have hAdd := addLevelL_of_priceIdx_none levels price qty hIndex
  have hCap : capacity levels price qty =
      MissingBranchFacts.capacity levels := by
    unfold capacity MissingBranchFacts.capacity
    rw [hAdd]
    simp
  refine {
    pages := hResult.pages
    globals := ?_
    resultOwned := ?_
    sourceOwned := hResult.sourceOwned
    bytesBefore := hResult.bytesBefore }
  · rw [hCap]
    exact hResult.globals
  · rw [hCap, hAdd]
    exact hResult.resultOwned

theorem UpdateResult.of_found
    {st0 st : Store Unit} {g0 g2 source sourceCapacity price qty : UInt64}
    {levels : List LevelL} {i : Nat}
    (hIndex : priceIdx levels price = some i)
    (hResult : FoundBranchFacts.ResultState st0 st g0 g2 source
      sourceCapacity levels i
      { lprice := price, lqty := levels[i]!.lqty + qty }) :
    UpdateResult st0 st g0 g2 source sourceCapacity price qty levels := by
  have hAdd := addLevelL_of_priceIdx_some levels price qty i hIndex
  have hCap : capacity levels price qty =
      FoundBranchFacts.capacity levels := by
    unfold capacity FoundBranchFacts.capacity
    rw [hAdd]
    simp
  refine {
    pages := hResult.pages
    globals := ?_
    resultOwned := ?_
    sourceOwned := hResult.sourceOwned
    bytesBefore := hResult.bytesBefore }
  · rw [hCap]
    exact hResult.globals
  · rw [hCap, hAdd]
    exact hResult.resultOwned

structure ResultAt (final : Locals) (target : UInt64) : Prop where
  params : final.params.length = 4
  locals : final.locals.length = 26
  values : final.values = [.i64 target, .i64 target]

set_option Elab.async false in
theorem func3_spec
    (env : HostEnv Unit) (st : Store Unit)
    (owner source price qty sourceCapacity g0 g2 : UInt64)
    (levels : List LevelL)
    (hLength : levels.length < 4294967296)
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
    (hFit32 : g0.toNat + 48 +
      (MissingBranchFacts.capacity levels).toNat < 4294967296)
    (hFit : g0.toNat + 48 + (MissingBranchFacts.capacity levels).toNat ≤
      st.mem.pages * 65536)
    (hFoundFit32 : g0.toNat + 48 +
      (FoundBranchFacts.capacity levels).toNat < 4294967296)
    (hFoundFit : g0.toNat + 48 +
      (FoundBranchFacts.capacity levels).toNat ≤ st.mem.pages * 65536)
    (hsepMissing : flatWordsDisjoint
      (flatWordsRegion (target g0) ((levels.length + 1) * 2))
      (flatWordsRegion source (levels.length * 2)))
    (hsepFound : flatWordsDisjoint
      (flatWordsRegion (target g0) (levels.length * 2))
      (flatWordsRegion source (levels.length * 2)))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ st1,
      UpdateResult st st1 g0 g2 source sourceCapacity price qty levels →
      ∀ final, ResultAt final (target g0) →
      wp «module» rest Q st1 final env) :
    wp «module» (Project.ClobDepth.func3 ++ rest) Q st
      (Scan.entryFrame owner source price qty) env := by
  have hResultProg : Entry.resultProg = [.localGet 12, .localGet 13] := by
    unfold Entry.resultProg Project.ClobDepth.func3
    rfl
  rw [Entry.func3_decomposition, hResultProg]
  simp only [List.append_assoc]
  apply Scan.scanProg_spec levels hLength hOwned.2
  · intro hIndex f4 f5
    simp only [Scan.outcomeFrame, List.cons_append, List.nil_append]
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp)]
    rw [show Entry.missingProg = Entry.missingProg ++ ([] : Wasm.Program)
      from (List.append_nil _).symm]
    apply MissingBranch.missingProg_spec env st owner source price qty
      sourceCapacity g0 g2 levels f4 f5 hLength hSource32 hSource48
      hSourceCapacity hSourceBelow hOwned hGlobal0 hGlobal1 hGlobal2
      hPages hFit32 hFit hsepMissing
    intro st1 hResult final hLocals
    have hFinalLen : final.locals.length = 26 := hLocals.locals
    have hOwner' : final.locals[8] =
        .i64 (MissingBranchFacts.target g0) := by
      apply Option.some.inj
      calc
        some final.locals[8] = final.locals[8]? :=
          (List.getElem?_eq_getElem (by omega)).symm
        _ = some (.i64 (MissingBranchFacts.target g0)) := hLocals.owner
    have hPointer' : final.locals[9] =
        .i64 (MissingBranchFacts.target g0) := by
      apply Option.some.inj
      calc
        some final.locals[9] = final.locals[9]? :=
          (List.getElem?_eq_getElem (by omega)).symm
        _ = some (.i64 (MissingBranchFacts.target g0)) := hLocals.pointer
    simp (config := { maxSteps := 10000000 }) [wp_simp,
      hLocals.params, hLocals.locals, hOwner', hPointer',
      Locals.get, List.take, List.drop]
    refine hNext st1 (UpdateResult.of_missing hIndex hResult) _ ?_
    exact ⟨hLocals.params, hLocals.locals, rfl⟩
  · intro i hIndex
    simp only [Scan.outcomeFrame, List.cons_append, List.nil_append]
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    rw [show Entry.foundProg = Entry.foundProg ++ ([] : Wasm.Program)
      from (List.append_nil _).symm]
    apply FoundBranch.foundProg_spec env st owner source price qty
      sourceCapacity g0 g2 levels i hLength hIndex hSource32 hSource48
      hSourceCapacity hSourceBelow hOwned hGlobal0 hGlobal1 hGlobal2
      hPages hFoundFit32 hFoundFit hsepFound
    intro st1 hResult final hLocals
    have hFinalLen : final.locals.length = 26 := hLocals.locals
    have hOwner' : final.locals[8] =
        .i64 (FoundBranchFacts.target g0) := by
      apply Option.some.inj
      calc
        some final.locals[8] = final.locals[8]? :=
          (List.getElem?_eq_getElem (by omega)).symm
        _ = some (.i64 (FoundBranchFacts.target g0)) := hLocals.owner
    have hPointer' : final.locals[9] =
        .i64 (FoundBranchFacts.target g0) := by
      apply Option.some.inj
      calc
        some final.locals[9] = final.locals[9]? :=
          (List.getElem?_eq_getElem (by omega)).symm
        _ = some (.i64 (FoundBranchFacts.target g0)) := hLocals.pointer
    simp (config := { maxSteps := 10000000 }) [wp_simp,
      hLocals.params, hLocals.locals, hOwner', hPointer',
      Locals.get, List.take, List.drop]
    refine hNext st1 (UpdateResult.of_found hIndex hResult) _ ?_
    exact ⟨hLocals.params, hLocals.locals, rfl⟩

set_option Elab.async false in
theorem func3_terminates
    (env : HostEnv Unit) (st : Store Unit)
    (owner source price qty sourceCapacity g0 g2 : UInt64)
    (levels : List LevelL)
    (hLength : levels.length < 4294967296)
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
    (hFit32 : g0.toNat + 48 +
      (MissingBranchFacts.capacity levels).toNat < 4294967296)
    (hFit : g0.toNat + 48 + (MissingBranchFacts.capacity levels).toNat ≤
      st.mem.pages * 65536)
    (hFoundFit32 : g0.toNat + 48 +
      (FoundBranchFacts.capacity levels).toNat < 4294967296)
    (hFoundFit : g0.toNat + 48 +
      (FoundBranchFacts.capacity levels).toNat ≤ st.mem.pages * 65536)
    (hsepMissing : flatWordsDisjoint
      (flatWordsRegion (target g0) ((levels.length + 1) * 2))
      (flatWordsRegion source (levels.length * 2)))
    (hsepFound : flatWordsDisjoint
      (flatWordsRegion (target g0) (levels.length * 2))
      (flatWordsRegion source (levels.length * 2))) :
    TerminatesWith (m := «module») (id := 3) (initial := st) (env := env)
      [.i64 qty, .i64 price, .i64 source, .i64 owner]
      (fun st1 vs =>
        UpdateResult st st1 g0 g2 source sourceCapacity price qty levels ∧
        vs = [.i64 (target g0), .i64 (target g0)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func3Def) ?_ ?_
  · simp [«module»]
  · change wp «module» Project.ClobDepth.func3 _ st
      (Scan.entryFrame owner source price qty) env
    rw [show Project.ClobDepth.func3 =
      Project.ClobDepth.func3 ++ ([] : Wasm.Program)
      from (List.append_nil _).symm]
    apply func3_spec env st owner source price qty sourceCapacity g0 g2
      levels hLength hSource32 hSource48 hSourceCapacity hSourceBelow
      hOwned hGlobal0 hGlobal1 hGlobal2 hPages hFit32 hFit hFoundFit32
      hFoundFit hsepMissing hsepFound
    intro st1 hResult final hFinal
    simp (config := { maxSteps := 10000000 }) [wp_simp, func3Def,
      Function.numParams, hFinal.values]
    exact hResult

end Project.ClobDepth.Func3
