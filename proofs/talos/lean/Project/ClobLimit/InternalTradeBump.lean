import Project.ClobLimit.Program
import Project.FixedArrayAllocation
import Interpreter.Wasm.Wp.Tactic

/-!
# Internal trade bump allocation

The full- and partial-fill trade allocators reach this body after their
free-list search returns no reusable node.  The body extends global 0 and
writes one stride-four fixed-array header.  Its result frame records the
generated scratch locals.
-/

namespace Project.ClobLimit.InternalTradeBump

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
    locals := ((((((base.locals.set 57 (.i64 need)).set 58
      (.i64 previous)).set 59 (.i64 current)).set 60
      (.i64 capacity)).set 61 (.i64 next)).set 62 (.i64 result)) }

def tradeSearchBodyProg : Wasm.Program :=
  [
  .localGet 70,
  .constI64 0,
  .eqI64,
  .br_if 1,
  .localGet 73,
  .constI64 0,
  .neI64,
  .br_if 1,
  .localGet 70,
  .constI64 32,
  .subI64,
  .wrapI64,
  .load64 0,
  .localSet 71,
  .localGet 70,
  .constI64 8,
  .subI64,
  .wrapI64,
  .load64 0,
  .localSet 72,
  .localGet 71,
  .localGet 68,
  .geUI64,
  .iff 0 0 [
    .localGet 69,
    .constI64 0,
    .eqI64,
    .iff 0 0 [
      .localGet 72,
      .globalSet 1
    ] [
      .localGet 69,
      .constI64 8,
      .subI64,
      .wrapI64,
      .localGet 72,
      .store64 0
    ],
    .localGet 70,
    .constI64 48,
    .subI64,
    .wrapI64,
    .constI64 5501223100278326855,
    .store64 0,
    .localGet 70,
    .constI64 40,
    .subI64,
    .wrapI64,
    .constI64 1,
    .store64 0,
    .localGet 70,
    .constI64 32,
    .subI64,
    .wrapI64,
    .localGet 71,
    .store64 0,
    .localGet 70,
    .constI64 24,
    .subI64,
    .wrapI64,
    .constI64 2,
    .store64 0,
    .localGet 70,
    .constI64 16,
    .subI64,
    .wrapI64,
    .constI64 4,
    .store64 0,
    .localGet 70,
    .constI64 8,
    .subI64,
    .wrapI64,
    .constI64 0,
    .store64 0,
    .localGet 70,
    .localSet 73
  ] [
    .localGet 70,
    .localSet 69,
    .localGet 72,
    .localSet 70
  ],
  .br 0
]

def tradeSearchProg : Wasm.Program :=
  [.block 0 0 [.loop 0 0 tradeSearchBodyProg]]

def tradeSearchInitProg : Wasm.Program :=
  [
  .constI64 0,
  .localSet 73,
  .constI64 0,
  .localSet 69,
  .globalGet 1,
  .localSet 70
  ]

def tradeBumpProg : Wasm.Program :=
  [
  .localGet 73,
  .constI64 0,
  .eqI64,
  .iff 0 0 [
    .globalGet 0,
    .constI64 48,
    .addI64,
    .localGet 68,
    .addI64,
    .localSet 71,
    .localGet 71,
    .globalGet 0,
    .ltUI64,
    .iff 0 0 [
      .unreachable
    ] [],
    .localGet 71,
    .constI64 1,
    .subI64,
    .constI64 65536,
    .divUI64,
    .constI64 1,
    .addI64,
    .localSet 72,
    .memorySize,
    .extendUI32,
    .localGet 72,
    .ltUI64,
    .iff 0 0 [
      .localGet 72,
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
    .localSet 73,
    .localGet 71,
    .globalSet 0,
    .localGet 73,
    .constI64 48,
    .subI64,
    .wrapI64,
    .constI64 5501223100278326855,
    .store64 0,
    .localGet 73,
    .constI64 40,
    .subI64,
    .wrapI64,
    .constI64 1,
    .store64 0,
    .localGet 73,
    .constI64 32,
    .subI64,
    .wrapI64,
    .localGet 68,
    .store64 0,
    .localGet 73,
    .constI64 24,
    .subI64,
    .wrapI64,
    .constI64 2,
    .store64 0,
    .localGet 73,
    .constI64 16,
    .subI64,
    .wrapI64,
    .constI64 4,
    .store64 0,
    .localGet 73,
    .constI64 8,
    .subI64,
    .wrapI64,
    .constI64 0,
    .store64 0
  ] []
]

def tradeNoFitProg : Wasm.Program :=
  tradeSearchInitProg ++ tradeSearchProg ++ tradeBumpProg

set_option Elab.async false in
theorem tradeSearchProg_empty
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (need previous capacity next : UInt64)
    (hParams : base.params.length = 11)
    (hLocals : base.locals.length = 64)
    (hValues : base.values = [])
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q st
      (allocFrame base need previous 0 capacity next 0) env) :
    wp «module» (tradeSearchProg ++ rest) Q st
      (allocFrame base need previous 0 capacity next 0) env := by
  simp only [tradeSearchProg, List.cons_append, List.nil_append]
  apply wp_block_cons
  apply wp_loop_cons
    (Inv := fun st' s =>
      st' = st ∧ s = allocFrame base need previous 0 capacity next 0)
    (μ := fun _ _ => 0)
  · exact ⟨rfl, rfl⟩
  · rintro st' s ⟨rfl, rfl⟩
    simp only [tradeSearchBodyProg, allocFrame]
    wp_run_bump (hParams, hLocals, hValues)
    simpa only [allocFrame, hValues] using hNext

set_option Elab.async false in
theorem tradeBumpProg_spec
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
      (fixedArrayAllocBumpStore st g0 need 4)
      (allocFrame base need previous 0 (g0 + 48 + need)
        ((g0 + 48 + need - 1) / 65536 + 1) (g0 + 48)) env) :
    wp «module» (tradeBumpProg ++ rest) Q st
      (allocFrame base need previous 0 capacity next 0) env := by
  simp only [tradeBumpProg, List.cons_append, List.nil_append, allocFrame]
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
        locals := ((((((((base.locals.set 57 (.i64 need)).set 58
          (.i64 previous)).set 59 (.i64 0)).set 60
          (.i64 capacity)).set 61 (.i64 next)).set 62 (.i64 0)).set 60
          (.i64 (g0 + 48 + need))).set 61
          (.i64 ((g0 + 48 + need - 1) / 65536 + 1))).set 62
          (.i64 (g0 + 48)) } =
        allocFrame base need previous 0 (g0 + 48 + need)
          ((g0 + 48 + need - 1) / 65536 + 1) (g0 + 48) := by
    unfold allocFrame
    rw [hValues]
    congr 1
    apply List.ext_getElem?
    intro i
    by_cases h63 : 62 = i
    · subst i
      simp [List.getElem?_set]
    by_cases h62 : 61 = i
    · subst i
      simp [List.getElem?_set, h63]
    by_cases h61 : 60 = i
    · subst i
      simp [List.getElem?_set, h63, h62]
    · simp [List.getElem?_set, h63, h62, h61]
  rw [hFinalFrame]
  simpa only [fixedArrayAllocBumpStore, fixedArrayHeaderMem,
    toUInt32_eq_ofNat, hsub48, hsub40, hsub32, hsub24, hsub16, hsub8]
    using hNext

set_option Elab.async false in
theorem tradeNoFitProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (g0 need previous current capacity next result : UInt64)
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
    (hg1 : st.globals.globals[1]? = some (.i64 0))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q
      (fixedArrayAllocBumpStore st g0 need 4)
      (allocFrame base need 0 0 (g0 + 48 + need)
        ((g0 + 48 + need - 1) / 65536 + 1) (g0 + 48)) env) :
    wp «module» (tradeNoFitProg ++ rest) Q st
      (allocFrame base need previous current capacity next result) env := by
  have hBump := tradeBumpProg_spec env st base g0 need 0 capacity next
    hParams hLocals hValues hNeed8 hTop hFit32 hFit hPages hg0 Q rest hNext
  have hSearch := tradeSearchProg_empty env st base need 0 capacity next
    hParams hLocals hValues Q (tradeBumpProg ++ rest) hBump
  unfold tradeNoFitProg
  rw [List.append_assoc]
  simp only [tradeSearchInitProg, List.cons_append, List.nil_append,
    allocFrame]
  wp_run_bump (hParams, hLocals, hValues)
  simp only [hg1]
  have hOverwrite :
      ((((((((base.locals.set 57 (.i64 need)).set 58
        (.i64 previous)).set 59 (.i64 current)).set 60
        (.i64 capacity)).set 61 (.i64 next)).set 62 (.i64 0)).set 58
        (.i64 0)).set 59 (.i64 0)) =
      (((((base.locals.set 57 (.i64 need)).set 58 (.i64 0)).set 59
        (.i64 0)).set 60 (.i64 capacity)).set 61 (.i64 next)).set 62
        (.i64 0) := by
    apply List.ext_getElem?
    intro i
    by_cases h60 : 59 = i
    · subst i
      simp [List.getElem?_set]
    by_cases h59 : 58 = i
    · subst i
      simp [List.getElem?_set, h60]
    by_cases h63 : 62 = i
    · subst i
      simp [List.getElem?_set, h60, h59]
    · simp [List.getElem?_set, h60, h59, h63]
  rw [hOverwrite]
  simpa only [allocFrame, hValues] using hSearch

end Project.ClobLimit.InternalTradeBump
