import Project.ClobLimit.HeapAppendFacts
import Project.ClobLimit.HeapAppendProgram

namespace Project.ClobLimit.HeapAppendFinish
open Wasm Project.Common Project.Clob Project.ClobLimit
open Project.ClobLimit.HeapAppendFacts Project.ClobPostOnly.AppendStore

structure StoreLocalsAt (frame : Locals) (target : UInt64) (n : Nat) (order : OrderL) : Prop where
  params : frame.params.length = 6
  locals : frame.locals.length = 55
  values : frame.values = []
  length : frame.locals[37]? = some (.i64 (UInt64.ofNat n))
  target : frame.locals[40]? = some (.i64 target)
  oid : frame.locals[42]? = some (.i64 order.oid)
  trader : frame.locals[43]? = some (.i64 order.otrader)
  side : frame.locals[44]? = some (.i64 order.oside)
  price : frame.locals[45]? = some (.i64 order.oprice)
  quantity : frame.locals[46]? = some (.i64 order.oqty)

set_option maxRecDepth 1048576
set_option maxHeartbeats 2000000 in
set_option Elab.async false in
theorem store_spec (env : HostEnv Unit) (st0 st1 : Store Unit) (frame : Locals)
    (base capacity source : UInt64) (os : List OrderL) (order : OrderL)
    (hLocals : StoreLocalsAt frame (base + 48) os.length order)
    (hState : CopyState st0 st1 (base + 48) source capacity os (os.length * 5))
    (hRoot : (base + 48).toNat = base.toNat + 48)
    (hTarget48 : 48 ≤ (base + 48).toNat)
    (hTarget32 : (base + 48).toNat + ((os.length + 1) * 5 + 1) * 8 < 4294967296)
    (hTargetFit : (base + 48).toNat + ((os.length + 1) * 5 + 1) * 8 ≤ st0.mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final, FinishState st0 final base capacity source os order →
      wp «module» rest Q final frame env) :
    wp «module» (LimitEntry.residualStoreProg ++ rest) Q st1 frame env := by
  have hp := hLocals.params
  have hl := hLocals.locals
  have hv := hLocals.values
  have hLength := getElem_of_some hLocals.length
  have hTarget := getElem_of_some hLocals.target
  have hOid := getElem_of_some hLocals.oid
  have hTrader := getElem_of_some hLocals.trader
  have hSide := getElem_of_some hLocals.side
  have hPrice := getElem_of_some hLocals.price
  have hQuantity := getElem_of_some hLocals.quantity
  have hLengthNat : (UInt64.ofNat os.length).toNat = os.length :=
    toNat_ofNat_lt (by rw [size_eq]; omega)
  have hTotalU : (UInt64.ofNat os.length * 5).toNat = os.length * 5 := by
    rw [UInt64.toNat_mul, hLengthNat]
    change os.length * 5 % 18446744073709551616 = os.length * 5
    omega
  simp only [LimitEntry.residualStoreProg, List.cons_append, List.nil_append]
  wp_run_with [hp, hl, hv, hLength, hTarget, hOid, hTrader, hSide, hPrice, hQuantity]
  try simp [hRoot, hLengthNat, hTotalU]
  have hWriteBound (field : Nat) (hField1 : 1 ≤ field) (hField5 : field ≤ 5) :
      (base.toNat + 48 + (os.length * 5 + field) * 8) % 4294967296 + 8 ≤
        st1.mem.pages * 65536 := by
    rw [Nat.mod_eq_of_lt (by rw [← hRoot]; omega), hState.pages]
    omega
  rw [if_neg (Nat.not_lt.mpr (hWriteBound 1 (by omega) (by omega))),
    if_neg (Nat.not_lt.mpr (hWriteBound 2 (by omega) (by omega))),
    if_neg (Nat.not_lt.mpr (hWriteBound 3 (by omega) (by omega))),
    if_neg (Nat.not_lt.mpr (hWriteBound 4 (by omega) (by omega))),
    if_neg (Nat.not_lt.mpr (hWriteBound 5 (by omega) (by omega)))]
  have hContinue := hNext (finishStore st1 base os.length order)
    (finish hState hRoot hTarget48 hTarget32 hTargetFit)
  have hEmpty : { frame with values := [] } = frame := by cases frame; simp_all
  simpa [finishStore, appendOrderStore, hRoot, hEmpty] using hContinue

#print axioms store_spec
end Project.ClobLimit.HeapAppendFinish
