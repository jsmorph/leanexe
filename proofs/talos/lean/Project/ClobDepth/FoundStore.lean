import Project.ClobDepth.FoundStoreFacts

/-!
# Found-price final stores

The found branch overwrites the matched level's price and quantity words and
leaves the target pointer on the stack as the allocation-branch result.  The
continuation receives the represented replaced array and the copy frame with
that pointer.
-/

namespace Project.ClobDepth.FoundStore

open Wasm Project.Common Project.Clob Project.ClobDepth
  Project.ClobDepth.Model Project.ClobDepth.Representation
  Project.ClobDepth.MissingCopyInvariant
  Project.ClobDepth.FoundCopyInvariant
  Project.ClobDepth.FoundStoreFacts
  Project.ClobDepth.MissingStoreFacts

set_option maxRecDepth 1048576


def storeResultFrame (base : Locals) (word : Nat)
    (target : UInt64) : Locals :=
  { copyLoopFrame base word with values := [.i64 target] }

set_option Elab.async false in
theorem foundStoreProg_spec
    (env : HostEnv Unit) (st0 st1 : Store Unit) (base : Locals)
    (target source capacity price newQty : UInt64) (levels : List LevelL)
    (i : Nat)
    (hParams : base.params.length = 4)
    (hLocals : base.locals.length = 26)
    (hValues : base.values = [])
    (hIndex : base.locals[11]? = some (.i64 (UInt64.ofNat i)))
    (hTarget : base.locals[14]? = some (.i64 target))
    (hPrice : base.locals[16]? = some (.i64 price))
    (hQty : base.locals[17]? = some (.i64 newQty))
    (hInvariant : FoundCopyInvariant.CopyInvariant st0 base target source capacity levels st1
      (copyLoopFrame base (levels.length * 2)))
    (hi : i < levels.length)
    (hTotalU : (UInt64.ofNat levels.length * 2).toNat =
      levels.length * 2)
    (hTotal64 : levels.length * 2 < UInt64.size)
    (hTarget48 : 48 ≤ target.toNat)
    (hSource32 :
      source.toNat + (levels.length * 2 + 1) * 8 < 4294967296)
    (hTarget32 : target.toNat + (levels.length * 2 + 1) * 8 <
      4294967296)
    (hTargetFit : target.toNat + (levels.length * 2 + 1) * 8 ≤
      st0.mem.pages * 65536)
    (hsep : flatWordsDisjoint
      (flatWordsRegion target (levels.length * 2))
      (flatWordsRegion source (levels.length * 2)))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ st2,
      ReplaceState st0 st2 target source capacity levels i
        { lprice := price, lqty := newQty } →
      wp «module» rest Q st2
        (storeResultFrame base (levels.length * 2) target) env) :
    wp «module» (Entry.foundStoreProg ++ rest) Q st1
      (copyLoopFrame base (levels.length * 2)) env := by
  have hState := hInvariant.at_end hLocals hTotalU hTotal64
  have hValues' : base.values = [] := by
    exact hValues
  have hIndex' : base.locals[11] = .i64 (UInt64.ofNat i) := getElem_of_some hIndex
  have hTarget' : base.locals[14] = .i64 target := getElem_of_some hTarget
  have hPrice' : base.locals[16] = .i64 price := getElem_of_some hPrice
  have hQty' : base.locals[17] = .i64 newQty := getElem_of_some hQty
  have hIndexNat : (UInt64.ofNat i).toNat = i :=
    toNat_ofNat_lt (by omega)
  simp only [Entry.foundStoreProg, copyLoopFrame, List.cons_append,
    List.nil_append]
  wp_run_with [hParams, hLocals, hValues', hIndex', hTarget', hPrice', hQty']
  try simp [hIndexNat, hTotalU]
  have hWriteBound (field : Nat) (hField1 : 1 ≤ field)
      (hField2 : field ≤ 2) :
      (target.toNat + (i * 2 + field) * 8) % 4294967296 + 8 ≤
        st1.mem.pages * 65536 := by
    rw [Nat.mod_eq_of_lt (by omega), hState.pages]
    omega
  rw [if_neg (Nat.not_lt.mpr (hWriteBound 1 (by omega) (by omega))),
    if_neg (Nat.not_lt.mpr (hWriteBound 2 (by omega) (by omega)))]
  have hFinish := FoundStoreFacts.finish
    (level := { lprice := price, lqty := newQty }) hState hi hTarget48
    hSource32 hTarget32 hTargetFit hsep
  have hContinue := hNext
    (appendLevelStore st1 target i { lprice := price, lqty := newQty })
    hFinish
  simpa [appendLevelStore, storeResultFrame, copyLoopFrame, hIndexNat,
    hTotalU] using hContinue

end Project.ClobDepth.FoundStore
