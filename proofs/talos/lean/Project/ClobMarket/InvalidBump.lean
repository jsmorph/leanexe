import Project.ClobMarket.InvalidSearch
import Project.FixedArrayAllocation

/-!
# Invalid `market` bump allocation

The empty free-list search selects the bump allocator.  This phase writes the
stride-four header and advances the heap top while leaving the array length
and allocation counter to the final phase.  Its frame-generic theorem isolates
the artifact's scratch-local indices from the common allocation semantics.
-/

namespace Project.ClobMarket.InvalidBump

open Wasm Project.Common Project.Clob Project.ClobMarket

set_option maxRecDepth 1048576
set_option maxHeartbeats 8000000

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

def bumpFrame (base : Locals) (g0 : UInt64) : Locals :=
  { base with
    locals := ((base.locals.set 46 (.i64 (g0 + 56))).set 47
      (.i64 ((g0 + 56 - 1) / 65536 + 1))).set 48 (.i64 (g0 + 48))
    values := [] }

set_option Elab.async false in
theorem invalidBumpProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals) (g0 : UInt64)
    (hParams : base.params.length = 6)
    (hLocals : base.locals.length = 49)
    (hValues : base.values = [])
    (hNeed : base.locals[43]? = some (.i64 8))
    (hResult : base.locals[48]? = some (.i64 0))
    (hFit32 : g0.toNat + 56 < 4294967296)
    (hFit : g0.toNat + 56 ≤ st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536)
    (hg0 : st.globals.globals[0]? = some (.i64 g0))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.ClobMarket.«module» rest Q
      (fixedArrayAllocBumpStore st g0 8 4)
      (bumpFrame base g0) env) :
    wp Project.ClobMarket.«module» (Entry.invalidBumpProg ++ rest) Q st
      base env := by
  have hNeed' : base.locals[43] = .i64 8 := by
    apply Option.some.inj
    calc
      some base.locals[43] = base.locals[43]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 8) := hNeed
  have hResult' : base.locals[48] = .i64 0 := by
    apply Option.some.inj
    calc
      some base.locals[48] = base.locals[48]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 0) := hResult
  simp only [Entry.invalidBumpProg, Entry.invalidProg,
    Entry.outerBranch, func21]
  wp_run_bump (hParams, hLocals, hValues, hNeed', hResult')
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp)]
  wp_run_bump (hParams, hLocals, hValues, hNeed', hResult')
  simp only [hg0]
  have hTop : (g0 + 48 + 8).toNat = g0.toNat + 56 := by
    rw [UInt64.toNat_add, UInt64.toNat_add]
    have h48 : (48 : UInt64).toNat = 48 := rfl
    have h8 : (8 : UInt64).toNat = 8 := rfl
    rw [h48, h8]
    omega
  have hNoWrap : ¬g0 + 48 + 8 < g0 := by
    rw [UInt64.lt_iff_toNat_lt, hTop]
    omega
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simp [hNoWrap])]
  wp_run_bump (hParams, hLocals, hValues, hNeed', hResult')
  have hNoGrow := fixedArrayBump_no_grow g0 8 st.mem.pages
    (by simpa using hTop) (by simpa using hFit) hPages
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simpa using hNoGrow)]
  wp_run_bump (hParams, hLocals, hValues, hNeed', hResult')
  simp only [hg0]
  try wp_run_bump (hParams, hLocals, hValues, hNeed', hResult')
  try simp
  have hRoot : (g0 + 48).toNat = g0.toNat + 48 :=
    fixedArrayBumpRoot_toNat g0 (by
      have hSize : UInt64.size = 18446744073709551616 := rfl
      rw [hSize]
      omega)
  have hsub48 : (g0 + 48 - 48).toNat = g0.toNat := by
    have h := fixedArrayBumpRoot_sub_toNat g0 48 hRoot (by decide)
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
  have hTopValue : g0 + 48 + 8 = g0 + 56 := by
    rw [UInt64.add_assoc]
    rw [show (48 : UInt64) + 8 = 56 by decide]
  simpa only [bumpFrame, fixedArrayAllocBumpStore, fixedArrayHeaderMem,
    toUInt32_eq_ofNat, hsub48, hsub40, hsub32, hsub24, hsub16, hsub8,
    hTopValue] using hNext

end Project.ClobMarket.InvalidBump
