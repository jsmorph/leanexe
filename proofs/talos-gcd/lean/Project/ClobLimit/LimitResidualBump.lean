import Project.ClobLimit.LimitResidualAllocPrepare
import Project.FixedArrayAllocation
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop

/-!
# Residual `limit` bump allocation

The residual allocator starts with an empty free-list head.  Its generated
search loop exits on the first check, and the bump fallback writes a
stride-five fixed-array header.  The counter and array-length stores remain in
the following phase.
-/

namespace Project.ClobLimit.LimitResidualBump

open Wasm Project.Common Project.Clob Project.ClobLimit
  Project.ClobLimit.InternalLoopInvariant
  Project.ClobMatchFuel.Allocation

set_option maxRecDepth 1048576

macro "wp_run_bump" "(" hParams:term "," hLocals:term ","
    hValues:term "," hNeed:term "," hResult:term ")" : tactic => `(tactic|
  simp (config := { maxSteps := 10000000 }) [wp_simp,
    Locals.get, Locals.set?, Locals.validIndex,
    Function.toLocals, Function.numParams, Function.numLocals,
    List.take, List.drop, List.replicate, List.length, List.map,
    List.length_set, List.getElem?_set,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceSub,
    ValueType.zero, List.headD, ($hParams), ($hLocals), ($hValues),
    ($hNeed), ($hResult)])

def bumpFrame (base : Locals) (g0 need : UInt64) : Locals :=
  { base with
    locals := ((base.locals.set 50 (.i64 (g0 + 48 + need))).set 51
      (.i64 ((g0 + 48 + need - 1) / 65536 + 1))).set 52
      (.i64 (g0 + 48))
    values := [] }

set_option Elab.async false in
theorem residualAllocSearchProg_empty
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (order : OrderL) (ctx : Context)
    (data : InternalLoopResult.OutputData)
    (hAlloc : LimitResidualAllocPrepare.AllocLocalsAt base order ctx data)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q st base env) :
    wp «module» (LimitEntry.residualAllocSearchProg ++ rest) Q st
      base env := by
  have hParams := hAlloc.orderLocals.fields.params
  have hLocals := hAlloc.orderLocals.fields.locals
  have hValues := hAlloc.orderLocals.fields.values
  have hCurrent : base.locals[49] = .i64 0 := by
    apply Option.some.inj
    calc
      some base.locals[49] = base.locals[49]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 0) := hAlloc.current
  simp only [LimitEntry.residualAllocSearchProg, List.cons_append,
    List.nil_append]
  apply wp_block_cons
  apply wp_loop_cons
    (Inv := fun st' s => st' = st ∧ s = base)
    (μ := fun _ _ => 0)
  · exact ⟨rfl, rfl⟩
  · rintro st' s ⟨rfl, rfl⟩
    simp only [LimitEntry.residualAllocSearchBodyProg]
    simp (config := { maxSteps := 10000000 })
      [wp_simp, hParams, hLocals, hValues, hCurrent]
    have hFrame : { params := s.params, locals := s.locals } = s := by
      cases s
      simp_all
    rw [hFrame]
    exact hNext

set_option Elab.async false in
theorem residualAllocBumpProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (order : OrderL) (ctx : Context)
    (data : InternalLoopResult.OutputData) (g0 : UInt64)
    (hAlloc : LimitResidualAllocPrepare.AllocLocalsAt base order ctx data)
    (hNeed8 : 8 ≤
      (orderArrayBytesU (ctx.result.book.length + 1)).toNat)
    (hTop : (g0 + 48 + orderArrayBytesU
      (ctx.result.book.length + 1)).toNat =
        g0.toNat + 48 +
          (orderArrayBytesU (ctx.result.book.length + 1)).toNat)
    (hFit32 : g0.toNat + 48 +
      (orderArrayBytesU (ctx.result.book.length + 1)).toNat < 4294967296)
    (hFit : g0.toNat + 48 +
      (orderArrayBytesU (ctx.result.book.length + 1)).toNat ≤
        st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536)
    (hg0 : st.globals.globals[0]? = some (.i64 g0))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q
      (fixedArrayAllocBumpStore st g0
        (orderArrayBytesU (ctx.result.book.length + 1)) 5)
      (bumpFrame base g0
        (orderArrayBytesU (ctx.result.book.length + 1))) env) :
    wp «module» (LimitEntry.residualAllocBumpProg ++ rest) Q st base env := by
  let need := orderArrayBytesU (ctx.result.book.length + 1)
  have hParams := hAlloc.orderLocals.fields.params
  have hLocals := hAlloc.orderLocals.fields.locals
  have hValues := hAlloc.orderLocals.fields.values
  have hNeed : base.locals[47] = .i64 need := by
    apply Option.some.inj
    calc
      some base.locals[47] = base.locals[47]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 need) := hAlloc.need
  have hResult : base.locals[52] = .i64 0 := by
    apply Option.some.inj
    calc
      some base.locals[52] = base.locals[52]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 0) := hAlloc.result
  simp only [LimitEntry.residualAllocBumpProg, List.cons_append,
    List.nil_append]
  wp_run_bump (hParams, hLocals, hValues, hNeed, hResult)
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp)]
  wp_run_bump (hParams, hLocals, hValues, hNeed, hResult)
  simp only [hg0]
  have hNoWrap : ¬g0 + 48 + need < g0 := by
    rw [UInt64.lt_iff_toNat_lt, hTop]
    omega
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simp [hNoWrap])]
  wp_run_bump (hParams, hLocals, hValues, hNeed, hResult)
  have hNoGrow := fixedArrayBump_no_grow g0 need st.mem.pages hTop hFit
    hPages
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simpa using hNoGrow)]
  wp_run_bump (hParams, hLocals, hValues, hNeed, hResult)
  simp only [hg0]
  try wp_run_bump (hParams, hLocals, hValues, hNeed, hResult)
  try simp
  have hRoot : (g0 + 48).toNat = g0.toNat + 48 :=
    fixedArrayBumpRoot_toNat g0 (by
      have hSize : UInt64.size = 18446744073709551616 := rfl
      rw [hSize]
      omega)
  have hsub48 : (g0 + 48 - 48).toNat = g0.toNat := by
    have hOffset : (48 : UInt64).toNat ≤ 48 := by decide
    have h := fixedArrayBumpRoot_sub_toNat g0 48 hRoot hOffset
    have h48 : (48 : UInt64).toNat = 48 := rfl
    rw [h48] at h
    simpa only [Nat.add_sub_cancel] using h
  have hsub40 : (g0 + 48 - 40).toNat = g0.toNat + 8 := by
    simpa using fixedArrayBumpRoot_sub_toNat g0 40 hRoot (by decide)
  have hsub32 : (g0 + 48 - 32).toNat = g0.toNat + 16 := by
    simpa using fixedArrayBumpRoot_sub_toNat g0 32 hRoot (by decide)
  have hsub24 : (g0 + 48 - 24).toNat = g0.toNat + 24 := by
    simpa using fixedArrayBumpRoot_sub_toNat g0 24 hRoot (by decide)
  have hsub16 : (g0 + 48 - 16).toNat = g0.toNat + 32 := by
    simpa using fixedArrayBumpRoot_sub_toNat g0 16 hRoot (by decide)
  have hsub8 : (g0 + 48 - 8).toNat = g0.toNat + 40 := by
    simpa using fixedArrayBumpRoot_sub_toNat g0 8 hRoot (by decide)
  have hBaseBound : g0.toNat % 4294967296 + 8 ≤
      st.mem.pages * 65536 := by
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hBase8Bound : (g0 + 48 - 40).toNat % 4294967296 + 8 ≤
      st.mem.pages * 65536 := by
    rw [hsub40, Nat.mod_eq_of_lt (by omega)]
    omega
  have hBase16Bound : (g0 + 48 - 32).toNat % 4294967296 + 8 ≤
      st.mem.pages * 65536 := by
    rw [hsub32, Nat.mod_eq_of_lt (by omega)]
    omega
  have hBase24Bound : (g0 + 48 - 24).toNat % 4294967296 + 8 ≤
      st.mem.pages * 65536 := by
    rw [hsub24, Nat.mod_eq_of_lt (by omega)]
    omega
  have hBase32Bound : (g0 + 48 - 16).toNat % 4294967296 + 8 ≤
      st.mem.pages * 65536 := by
    rw [hsub16, Nat.mod_eq_of_lt (by omega)]
    omega
  have hBase40Bound : (g0 + 48 - 8).toNat % 4294967296 + 8 ≤
      st.mem.pages * 65536 := by
    rw [hsub8, Nat.mod_eq_of_lt (by omega)]
    omega
  rw [if_neg (Nat.not_lt.mpr hBaseBound),
    if_neg (Nat.not_lt.mpr hBase8Bound),
    if_neg (Nat.not_lt.mpr hBase16Bound),
    if_neg (Nat.not_lt.mpr hBase24Bound),
    if_neg (Nat.not_lt.mpr hBase32Bound),
    if_neg (Nat.not_lt.mpr hBase40Bound)]
  simpa only [bumpFrame, fixedArrayAllocBumpStore, fixedArrayHeaderMem,
    toUInt32_eq_ofNat, hsub48, hsub40, hsub32, hsub24, hsub16, hsub8,
    need] using hNext

end Project.ClobLimit.LimitResidualBump
