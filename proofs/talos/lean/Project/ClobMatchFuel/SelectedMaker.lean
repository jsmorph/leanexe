import Project.ClobMatchFuel.Helpers

/-! The generated matcher reads the selected maker once and reuses its fields. -/
namespace Project.ClobMatchFuel.SelectedMaker
open Wasm Project.Common Project.Clob Project.ClobMatchFuel
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def At (base : Locals) (maker : OrderL) : Prop :=
  base.locals[25]? = some (.i64 maker.oid) ∧
  base.locals[26]? = some (.i64 maker.otrader) ∧
  base.locals[27]? = some (.i64 maker.oside) ∧
  base.locals[28]? = some (.i64 maker.oprice) ∧
  base.locals[29]? = some (.i64 maker.oqty)

def readProg : Program := [
.localGet 15,
.localSet 76,
.localGet 33,
.localSet 77,
.localGet 77,
.localGet 76,
.wrapI64,
.load64 0,
.ltUI64,
.iff 0 1 [
      .localGet 76,
      .localGet 77,
      .constI64 5,
      .mulI64,
      .constI64 1,
      .addI64,
      .constI64 8,
      .mulI64,
      .addI64,
      .wrapI64,
      .load64 0
     ] [
      .unreachable
     ] [] [.i64],
.localSet 34,
.localGet 15,
.localSet 76,
.localGet 33,
.localSet 77,
.localGet 77,
.localGet 76,
.wrapI64,
.load64 0,
.ltUI64,
.iff 0 1 [
      .localGet 76,
      .localGet 77,
      .constI64 5,
      .mulI64,
      .constI64 2,
      .addI64,
      .constI64 8,
      .mulI64,
      .addI64,
      .wrapI64,
      .load64 0
     ] [
      .unreachable
     ] [] [.i64],
.localSet 35,
.localGet 15,
.localSet 76,
.localGet 33,
.localSet 77,
.localGet 77,
.localGet 76,
.wrapI64,
.load64 0,
.ltUI64,
.iff 0 1 [
      .localGet 76,
      .localGet 77,
      .constI64 5,
      .mulI64,
      .constI64 3,
      .addI64,
      .constI64 8,
      .mulI64,
      .addI64,
      .wrapI64,
      .load64 0
     ] [
      .unreachable
     ] [] [.i64],
.localSet 36,
.localGet 15,
.localSet 76,
.localGet 33,
.localSet 77,
.localGet 77,
.localGet 76,
.wrapI64,
.load64 0,
.ltUI64,
.iff 0 1 [
      .localGet 76,
      .localGet 77,
      .constI64 5,
      .mulI64,
      .constI64 4,
      .addI64,
      .constI64 8,
      .mulI64,
      .addI64,
      .wrapI64,
      .load64 0
     ] [
      .unreachable
     ] [] [.i64],
.localSet 37,
.localGet 15,
.localSet 76,
.localGet 33,
.localSet 77,
.localGet 77,
.localGet 76,
.wrapI64,
.load64 0,
.ltUI64,
.iff 0 1 [
      .localGet 76,
      .localGet 77,
      .constI64 5,
      .mulI64,
      .constI64 5,
      .addI64,
      .constI64 8,
      .mulI64,
      .addI64,
      .wrapI64,
      .load64 0
     ] [
      .unreachable
     ] [] [.i64],
.localSet 38
]

def cacheLocals (base : Locals) (book : UInt64) (i : Nat) (maker : OrderL) : List Value :=
  let locals := base.locals.set 67 (.i64 book)
  let locals := locals.set 68 (.i64 (UInt64.ofNat i))
  let locals := locals.set 25 (.i64 maker.oid)
  let locals := locals.set 67 (.i64 book)
  let locals := locals.set 68 (.i64 (UInt64.ofNat i))
  let locals := locals.set 26 (.i64 maker.otrader)
  let locals := locals.set 67 (.i64 book)
  let locals := locals.set 68 (.i64 (UInt64.ofNat i))
  let locals := locals.set 27 (.i64 maker.oside)
  let locals := locals.set 67 (.i64 book)
  let locals := locals.set 68 (.i64 (UInt64.ofNat i))
  let locals := locals.set 28 (.i64 maker.oprice)
  let locals := locals.set 67 (.i64 book)
  let locals := locals.set 68 (.i64 (UInt64.ofNat i))
  let locals := locals.set 29 (.i64 maker.oqty)
  locals

def cacheFrame (base : Locals) (book : UInt64) (i : Nat) (maker : OrderL) : Locals :=
  { base with locals := cacheLocals base book i maker, values := [] }

@[simp] theorem cacheFrame_at (base : Locals) (book : UInt64) (i : Nat)
    (maker : OrderL) (hLocals : base.locals.length = 86) :
    At (cacheFrame base book i maker) maker := by
  simp [At, cacheFrame, cacheLocals, hLocals]

theorem cacheLocals_kept (base : Locals) (book : UInt64) (i : Nat)
    (maker : OrderL) (j : Nat) (hLow : j < 25 ∨ 30 ≤ j)
    (hBook : j ≠ 67) (hIndex : j ≠ 68) :
    (cacheLocals base book i maker)[j]? = base.locals[j]? := by
  simp (discharger := omega) [cacheLocals, List.getElem?_set]


theorem read_spec (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (book : UInt64) (os : List OrderL) (i : Nat)
    (hParams : base.params.length = 9) (hLocals : base.locals.length = 86)
    (hValues : base.values = [])
    (hBook : base.locals[6]? = some (.i64 book))
    (hIndex : base.locals[24]? = some (.i64 (UInt64.ofNat i)))
    (hLength : os.length < 4294967296) (hi : i < os.length)
    (hInput : OrdersAt st book os) (Q : Assertion Unit) (rest : Program)
    (hNext : wp «module» rest Q st (cacheFrame base book i os[i]!) env) :
    wp «module» (readProg ++ rest) Q st base env := by
  have hBook' := getElem_of_some hBook
  have hIndex' := getElem_of_some hIndex
  have hkU : (UInt64.ofNat i).toNat = i := by u64_omega
  have hlt : UInt64.ofNat i < UInt64.ofNat os.length := by
    rw [UInt64.lt_iff_toNat_lt, hkU, toNat_ofNat_lt (by rw [size_eq]; omega)]
    exact hi
  obtain ⟨⟨hHead, hHeadB⟩, hElems⟩ := hInput
  obtain ⟨⟨hr1, hb1⟩, ⟨hr2, hb2⟩, ⟨hr3, hb3⟩, ⟨hr4, hb4⟩, ⟨hr5, hb5⟩⟩ := hElems i hi
  have hSafeHead := Nat.not_lt.mpr hHeadB
  have hSafe1 := Nat.not_lt.mpr hb1
  have hSafe2 := Nat.not_lt.mpr hb2
  have hSafe3 := Nat.not_lt.mpr hb3
  have hSafe4 := Nat.not_lt.mpr hb4
  have hSafe5 := Nat.not_lt.mpr hb5
  simp only [readProg, List.cons_append, List.nil_append]
  wp_run_with [hParams, hLocals, hValues, hBook', hIndex', hkU, hHead, hr1, hr2, hr3, hr4, hr5, hSafeHead, hSafe1, hSafe2, hSafe3, hSafe4, hSafe5]
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp [hlt])]
  wp_run_with [hParams, hLocals, hValues, hBook', hIndex', hkU, hHead, hr1, hr2, hr3, hr4, hr5, hSafeHead, hSafe1, hSafe2, hSafe3, hSafe4, hSafe5]
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp [hlt])]
  wp_run_with [hParams, hLocals, hValues, hBook', hIndex', hkU, hHead, hr1, hr2, hr3, hr4, hr5, hSafeHead, hSafe1, hSafe2, hSafe3, hSafe4, hSafe5]
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp [hlt])]
  wp_run_with [hParams, hLocals, hValues, hBook', hIndex', hkU, hHead, hr1, hr2, hr3, hr4, hr5, hSafeHead, hSafe1, hSafe2, hSafe3, hSafe4, hSafe5]
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp [hlt])]
  wp_run_with [hParams, hLocals, hValues, hBook', hIndex', hkU, hHead, hr1, hr2, hr3, hr4, hr5, hSafeHead, hSafe1, hSafe2, hSafe3, hSafe4, hSafe5]
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp [hlt])]
  wp_run_with [hParams, hLocals, hValues, hBook', hIndex', hkU, hHead, hr1, hr2, hr3, hr4, hr5, hSafeHead, hSafe1, hSafe2, hSafe3, hSafe4, hSafe5]
  simpa only [cacheFrame, cacheLocals, List.getElem!_eq_getElem?_getD] using hNext

#print axioms read_spec
end Project.ClobMatchFuel.SelectedMaker
