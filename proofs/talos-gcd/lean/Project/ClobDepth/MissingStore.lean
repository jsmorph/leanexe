import Project.ClobDepth.MissingStoreFacts

/-!
# Missing-price final stores

The missing-price branch writes the appended level and assigns the internal
result locals.  The continuation receives the represented extended array and
the exact result frame.
-/

namespace Project.ClobDepth.MissingStore

open Wasm Project.Common Project.Clob Project.ClobDepth
  Project.ClobDepth.Model Project.ClobDepth.Representation
  Project.ClobDepth.MissingCopyInvariant
  Project.ClobDepth.MissingStoreFacts

set_option maxRecDepth 1048576

macro "wp_run_missing_store" "(" hParams:term "," hLocals:term ","
    hValues:term "," hLength:term "," hTarget:term ","
    hPrice:term "," hQty:term ")" : tactic => `(tactic|
  simp (config := { maxSteps := 10000000 }) [wp_simp,
    Locals.get, Locals.set?, Locals.validIndex,
    Function.toLocals, Function.numParams, Function.numLocals,
    List.take, List.drop, List.replicate, List.length, List.map,
    List.length_set, List.getElem?_set,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceSub,
    ValueType.zero, List.headD, ($hParams), ($hLocals), ($hValues),
    ($hLength), ($hTarget), ($hPrice), ($hQty)])

structure ResultLocalsAt (final : Locals) (target : UInt64) : Prop where
  params : final.params.length = 4
  locals : final.locals.length = 26
  values : final.values = []
  working : final.locals[4]? = some (.i64 target)
  owner : final.locals[8]? = some (.i64 target)
  pointer : final.locals[9]? = some (.i64 target)

def resultFrame (base : Locals) (word : Nat) (target : UInt64) : Locals :=
  let copied := copyLoopFrame base word
  { copied with
    locals := ((copied.locals.set 4 (.i64 target)).set 8
      (.i64 target)).set 9 (.i64 target)
    values := [] }

theorem resultFrame_resultLocals
    (base : Locals) (word : Nat) (target : UInt64)
    (hParams : base.params.length = 4)
    (hLocals : base.locals.length = 26) :
    ResultLocalsAt (resultFrame base word target) target := by
  refine {
    params := by simpa [resultFrame, copyLoopFrame] using hParams
    locals := by simpa [resultFrame, copyLoopFrame] using hLocals
    values := by simp [resultFrame, copyLoopFrame]
    working := by simp [resultFrame, copyLoopFrame, hLocals]
    owner := by simp [resultFrame, copyLoopFrame, hLocals]
    pointer := by simp [resultFrame, copyLoopFrame, hLocals] }

set_option Elab.async false in
theorem missingStoreProg_spec
    (env : HostEnv Unit) (st0 st1 : Store Unit) (base : Locals)
    (target source capacity price qty : UInt64) (levels : List LevelL)
    (hParams : base.params.length = 4)
    (hLocals : base.locals.length = 26)
    (hValues : base.values = [])
    (hLength : base.locals[11]? =
      some (.i64 (UInt64.ofNat levels.length)))
    (hTarget : base.locals[14]? = some (.i64 target))
    (hPrice : base.locals[16]? = some (.i64 price))
    (hQty : base.locals[17]? = some (.i64 qty))
    (hInvariant : CopyInvariant st0 base target source capacity levels st1
      (copyLoopFrame base (levels.length * 2)))
    (hTotalU : (UInt64.ofNat levels.length * 2).toNat =
      levels.length * 2)
    (hTotal64 : levels.length * 2 < UInt64.size)
    (hTarget48 : 48 ≤ target.toNat)
    (hSource32 :
      source.toNat + (levels.length * 2 + 1) * 8 < 4294967296)
    (hTarget32 : target.toNat + ((levels.length + 1) * 2 + 1) * 8 <
      4294967296)
    (hTargetFit : target.toNat + ((levels.length + 1) * 2 + 1) * 8 ≤
      st0.mem.pages * 65536)
    (hsep : flatWordsDisjoint
      (flatWordsRegion target ((levels.length + 1) * 2))
      (flatWordsRegion source (levels.length * 2)))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ st2,
      FinishState st0 st2 target source capacity levels
        { lprice := price, lqty := qty } →
      ∀ final, ResultLocalsAt final target →
      wp «module» rest Q st2 final env) :
    wp «module» (Entry.missingStoreProg ++ rest) Q st1
      (copyLoopFrame base (levels.length * 2)) env := by
  have hState := hInvariant.at_end hLocals hTotalU hTotal64
  have hValues' : base.values = [] := by
    exact hValues
  have hLength' : base.locals[11] =
      .i64 (UInt64.ofNat levels.length) := by
    apply Option.some.inj
    calc
      some base.locals[11] = base.locals[11]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 (UInt64.ofNat levels.length)) := hLength
  have hTarget' : base.locals[14] = .i64 target := by
    apply Option.some.inj
    calc
      some base.locals[14] = base.locals[14]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 target) := hTarget
  have hPrice' : base.locals[16] = .i64 price := by
    apply Option.some.inj
    calc
      some base.locals[16] = base.locals[16]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 price) := hPrice
  have hQty' : base.locals[17] = .i64 qty := by
    apply Option.some.inj
    calc
      some base.locals[17] = base.locals[17]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 qty) := hQty
  have hLengthNat : (UInt64.ofNat levels.length).toNat = levels.length :=
    toNat_ofNat_lt (by omega)
  simp only [Entry.missingStoreProg, copyLoopFrame, List.cons_append,
    List.nil_append]
  wp_run_missing_store
    (hParams, hLocals, hValues', hLength', hTarget', hPrice', hQty')
  try simp [hLengthNat, hTotalU]
  have hWriteBound (field : Nat) (hField1 : 1 ≤ field)
      (hField2 : field ≤ 2) :
      (target.toNat + (levels.length * 2 + field) * 8) % 4294967296 + 8 ≤
        st1.mem.pages * 65536 := by
    rw [Nat.mod_eq_of_lt (by omega), hState.pages]
    omega
  rw [if_neg (Nat.not_lt.mpr (hWriteBound 1 (by omega) (by omega))),
    if_neg (Nat.not_lt.mpr (hWriteBound 2 (by omega) (by omega)))]
  have hFinish := MissingStoreFacts.finish
    (level := { lprice := price, lqty := qty }) hState hTarget48 hSource32
    hTarget32 hTargetFit hsep
  have hResult := resultFrame_resultLocals base (levels.length * 2) target
    hParams hLocals
  have hContinue := hNext
    (appendLevelStore st1 target levels.length
      { lprice := price, lqty := qty }) hFinish
    (resultFrame base (levels.length * 2) target) hResult
  simpa [appendLevelStore, resultFrame, copyLoopFrame, hLengthNat, hTotalU]
    using hContinue

end Project.ClobDepth.MissingStore
