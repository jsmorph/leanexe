import Project.ClobLimit.Program
import Project.FixedArrayAllocation
import Interpreter.Wasm.Wp.Tactic

/-!
# Internal partial-book bump allocation

The partial-fill book allocator reaches this body after its free-list search
returns no reusable node.  The body extends global 0 and writes one stride-five
fixed-array header.  Its result frame records the generated scratch locals.
-/

namespace Project.ClobLimit.InternalBookBump

open Wasm Project.Common Project.Clob Project.ClobLimit

set_option maxHeartbeats 8000000
set_option maxRecDepth 1048576

macro "wp_run_bump" "(" hParams:term "," hLocals:term "," hValues:term ")" : tactic => `(tactic|
  simp (config := { maxSteps := 10000000 }) [wp_simp,
    Locals.get, Locals.set?, Locals.validIndex,
    Function.toLocals, Function.numParams, Function.numLocals,
    List.take, List.drop, List.replicate, List.length, List.map,
    List.length_set, List.getElem?_set,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceSub,
    ValueType.zero, List.headD, ($hParams), ($hLocals), ($hValues)])

def allocFrame (base : Locals) (need previous current capacity next result :
    UInt64) : Locals :=
  { base with
    locals := ((((((base.locals.set 58 (.i64 need)).set 59
      (.i64 previous)).set 60 (.i64 current)).set 61
      (.i64 capacity)).set 62 (.i64 next)).set 63 (.i64 result)) }

def partialBookBumpProg : Wasm.Program :=
  [
  .localGet 74,
  .constI64 0,
  .eqI64,
  .iff 0 0 [
    .globalGet 0,
    .constI64 48,
    .addI64,
    .localGet 69,
    .addI64,
    .localSet 72,
    .localGet 72,
    .globalGet 0,
    .ltUI64,
    .iff 0 0 [
      .unreachable
    ] [],
    .localGet 72,
    .constI64 1,
    .subI64,
    .constI64 65536,
    .divUI64,
    .constI64 1,
    .addI64,
    .localSet 73,
    .memorySize,
    .extendUI32,
    .localGet 73,
    .ltUI64,
    .iff 0 0 [
      .localGet 73,
      .memorySize,
      .extendUI32,
      .subI64,
      .wrapI64,
      .memoryGrow,
      .const 4294967295,
      .eq,
      .iff 0 0 [
        .unreachable
      ] []
    ] [],
    .globalGet 0,
    .constI64 48,
    .addI64,
    .localSet 74,
    .localGet 72,
    .globalSet 0,
    .localGet 74,
    .constI64 48,
    .subI64,
    .wrapI64,
    .constI64 5501223100278326855,
    .store64 0,
    .localGet 74,
    .constI64 40,
    .subI64,
    .wrapI64,
    .constI64 1,
    .store64 0,
    .localGet 74,
    .constI64 32,
    .subI64,
    .wrapI64,
    .localGet 69,
    .store64 0,
    .localGet 74,
    .constI64 24,
    .subI64,
    .wrapI64,
    .constI64 2,
    .store64 0,
    .localGet 74,
    .constI64 16,
    .subI64,
    .wrapI64,
    .constI64 5,
    .store64 0,
    .localGet 74,
    .constI64 8,
    .subI64,
    .wrapI64,
    .constI64 0,
    .store64 0
  ] []
]

set_option Elab.async false in
theorem partialBookBumpProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (g0 need previous capacity next : UInt64)
    (hParams : base.params.length = 11)
    (hLocals : base.locals.length = 64)
    (hValues : base.values = [])
    (hNeed8 : 8 ≤ need.toNat)
    (hTop : (g0 + 48 + need).toNat =
      g0.toNat + 48 + need.toNat)
    (hFit32 : g0.toNat + 48 + need.toNat < 4294967296)
    (hFit : g0.toNat + 48 + need.toNat ≤ st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536)
    (hg0 : st.globals.globals[0]? = some (.i64 g0))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q
      (fixedArrayAllocBumpStore st g0 need 5)
      (allocFrame base need previous 0 (g0 + 48 + need)
        ((g0 + 48 + need - 1) / 65536 + 1) (g0 + 48)) env) :
    wp «module» (partialBookBumpProg ++ rest) Q st
      (allocFrame base need previous 0 capacity next 0) env := by
  simp only [partialBookBumpProg, List.cons_append, List.nil_append, allocFrame]
  wp_run_bump (hParams, hLocals, hValues)
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp)]
  wp_run_bump (hParams, hLocals, hValues)
  simp only [hg0]
  have hNoWrap : ¬g0 + 48 + need < g0 := by
    rw [UInt64.lt_iff_toNat_lt, hTop]
    omega
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simp [hNoWrap])]
  wp_run_bump (hParams, hLocals, hValues)
  have hNoGrow := fixedArrayBump_no_grow g0 need st.mem.pages hTop hFit hPages
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simpa using hNoGrow)]
  wp_run_bump (hParams, hLocals, hValues)
  simp only [hg0]
  try wp_run_bump (hParams, hLocals, hValues)
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
  have hFinalFrame :
      { params := base.params,
        locals := ((((((((base.locals.set 58 (.i64 need)).set 59
          (.i64 previous)).set 60 (.i64 0)).set 61
          (.i64 capacity)).set 62 (.i64 next)).set 63 (.i64 0)).set 61
          (.i64 (g0 + 48 + need))).set 62
          (.i64 ((g0 + 48 + need - 1) / 65536 + 1))).set 63
          (.i64 (g0 + 48)) } =
        allocFrame base need previous 0 (g0 + 48 + need)
          ((g0 + 48 + need - 1) / 65536 + 1) (g0 + 48) := by
    unfold allocFrame
    rw [hValues]
    congr 1
    apply List.ext_getElem?
    intro i
    by_cases h63 : 63 = i
    · subst i
      simp [List.getElem?_set]
    by_cases h62 : 62 = i
    · subst i
      simp [List.getElem?_set, h63]
    by_cases h61 : 61 = i
    · subst i
      simp [List.getElem?_set, h63, h62]
    · simp [List.getElem?_set, h63, h62, h61]
  rw [hFinalFrame]
  simpa only [fixedArrayAllocBumpStore, fixedArrayHeaderMem,
    toUInt32_eq_ofNat, hsub48, hsub40, hsub32, hsub24, hsub16, hsub8]
    using hNext

end Project.ClobLimit.InternalBookBump
