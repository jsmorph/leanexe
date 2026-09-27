import Project.ClobMatchFuel.IterationPrepare

namespace Project.ClobMatchFuel.Iteration

open Wasm Project.Common Project.Clob Project.ClobFindBest.Model
  Project.ClobMatchFuel

set_option maxHeartbeats 8000000
set_option maxRecDepth 1048576

def searchLocals (base : Locals) (bookOwner book : UInt64)
    (taker : OrderL) (result : Option Nat) : List Value :=
  let locals := base.locals.set 16 (.i64 bookOwner)
  let locals := locals.set 17 (.i64 book)
  let locals := locals.set 18 (.i64 taker.oid)
  let locals := locals.set 19 (.i64 taker.otrader)
  let locals := locals.set 20 (.i64 taker.oside)
  let locals := locals.set 21 (.i64 taker.oprice)
  let locals := locals.set 22 (.i64 taker.oqty)
  let locals := locals.set 24 (.i64 (optionPayload result))
  locals.set 23 (.i64 (optionTag result))

def searchFrame (base : Locals) (bookOwner book : UInt64) (taker : OrderL)
    (result : Option Nat) : Locals :=
  { base with
    locals := searchLocals base bookOwner book taker result
    values := [] }

def quantityFrame (base : Locals) (bookOwner book : UInt64)
    (taker : OrderL) (os : List OrderL) (i : Nat) : Locals :=
  SelectedOrder.loadFrame (searchFrame base bookOwner book taker (some i))
    book i os[i]!

def zeroIffPost (env : HostEnv Unit) (rest : Wasm.Program)
    (Q : Assertion Unit) : Assertion Unit :=
  fun cont =>
    match cont with
    | .Fallthrough st' s' =>
        wp «module» rest Q st' { s' with values := [] } env
    | .Break 0 st' s' =>
        wp «module» rest Q st' { s' with values := [] } env
    | .Break (k + 1) st' s' => Q (.Break k st' s')
    | other => Q other

def dispatchBranchPost (env : HostEnv Unit) (rest : Wasm.Program)
    (Q : Assertion Unit) : Assertion Unit :=
  zeroIffPost env [] (zeroIffPost env [] (zeroIffPost env rest Q))

def quantityProg : Wasm.Program :=
  [.localGet 38, .localGet 18, .leUI64,
    .iff 0 0 fullBranchProg PartialBranch.partialBranchProg]

set_option Elab.async false in
theorem quantityProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (makerQty remaining : UInt64)
    (hParams : base.params.length = 9)
    (hLocals : base.locals.length = 86)
    (hValues : base.values = [])
    (hQty : base.get 38 = some (.i64 makerQty))
    (hRemaining : base.get 18 = some (.i64 remaining))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hFull : makerQty ≤ remaining →
      wp «module» fullBranchProg (zeroIffPost env rest Q) st base env)
    (hPartial : ¬makerQty ≤ remaining →
      wp «module» PartialBranch.partialBranchProg (zeroIffPost env rest Q) st base env) :
    wp «module» (quantityProg ++ rest) Q st base env := by
  have hQtyElem : base.locals[29] = .i64 makerQty := by
    simpa [Locals.get, hParams, hLocals] using hQty
  have hRemainingElem : base.locals[9] = .i64 remaining := by
    simpa [Locals.get, hParams, hLocals] using hRemaining
  rcases base with ⟨params, locals, values⟩
  dsimp only at hValues
  subst values
  simp only [quantityProg, List.cons_append, List.nil_append]
  wp_run_with [hParams, hLocals, hQtyElem, hRemainingElem]
  refine wp_iff_cons rfl ?_
  by_cases hLe : makerQty ≤ remaining
  · rw [if_pos hLe, if_pos (by decide)]
    refine wp.imp (hFull hLe) ?_
    intro c hc
    unfold zeroIffPost at hc
    cases c <;> try exact hc
    case Break k _ _ => cases k <;> exact hc
  · rw [if_neg hLe, if_neg (by decide)]
    refine wp.imp (hPartial hLe) ?_
    intro c hc
    unfold zeroIffPost at hc
    cases c <;> try exact hc
    case Break k _ _ => cases k <;> exact hc

end Project.ClobMatchFuel.Iteration
