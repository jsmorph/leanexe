import Project.ClobFindBest.SearchFrame

namespace Project.ClobFindBest.SearchAdvance
open Wasm Project.Common Project.Clob Project.ClobFindBest.Model
  Project.ClobFindBest.SearchFrame Project.ClobFindBest.SearchProgram
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

structure AdvanceFrame (before after : Locals) (fuel owner ptr : UInt64) (taker : OrderL)
    (k : Nat) (best : Option Nat) : Prop where
  params : after.params = params (fuel-1) owner ptr taker (k+1) best
  locals : after.locals.length = 56
  values : after.values = []
  owner : after.locals[0]? = some (.i64 0)
  kept : ∀ i, 1 ≤ i → i ≤ 3 → after.locals[i]? = before.locals[i]?

theorem advance_spec (m : Wasm.Module) (env : HostEnv Unit) (st : Store Unit)
    (releaseId : Nat) (base : Locals) (fuel owner ptr : UInt64) (taker : OrderL)
    (k : Nat) (best next : Option Nat)
    (hParams : base.params = params fuel owner ptr taker k best)
    (hLocals : base.locals.length = 56) (hValues : base.values = [])
    (hOwner : base.locals[0]? = some (.i64 0))
    (hTag : base.locals[30]? = some (.i64 (optionTag next)))
    (hPayload : base.locals[31]? = some (.i64 (optionPayload next)))
    (hk : k < 4294967296) (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ final, AdvanceFrame base final fuel owner ptr taker k next → wp m rest Q st final env) :
    wp m (advance releaseId ++ rest) Q st base env := by
  have hOwner' := getElem_of_some hOwner
  have hTag' := getElem_of_some hTag
  have hPayload' := getElem_of_some hPayload
  have hkU : (UInt64.ofNat k).toNat = k := by u64_omega
  have hkadd : UInt64.ofNat k + 1 = UInt64.ofNat (k+1) := by
    apply UInt64.toNat.inj
    rw [toNat_add_one (by rw [hkU, size_eq]; omega), hkU,
      toNat_ofNat_lt (by rw [size_eq]; omega)]
  have hNoWrap : ¬UInt64.ofNat k+1 < UInt64.ofNat k := by
    rw [UInt64.lt_iff_toNat_lt, toNat_add_one (by rw [hkU, size_eq]; omega), hkU]
    omega
  simp only [advance, List.cons_append, List.nil_append]
  wp_run_with [hParams, params, hLocals, hValues, hOwner', hTag', hPayload']
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simp [hNoWrap])]
  wp_run_with [hParams, params, hLocals, hValues, hOwner', hTag', hPayload']
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simp)]
  wp_run_with [hParams, params, hLocals, hValues, hOwner', hTag', hPayload']
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simp)]
  wp_run_with [hParams, params, hLocals, hValues, hOwner', hTag', hPayload']
  by_cases hZero : owner = 0
  · refine wp_iff_cons rfl ?_
    rw [if_pos (by simp [hZero])]
    wp_run_with [hParams, params, hLocals, hValues, hOwner', hTag', hPayload']
    apply hNext
    refine ⟨?_, by simp [List.length_set, hLocals], rfl, ?_, ?_⟩
    · simp only [params, hkadd]
    · simp [hLocals, hZero]
    · intro i hLow hHigh
      simp (discharger := omega) [List.getElem?_set, hLocals]
  · refine wp_iff_cons rfl ?_
    rw [if_neg (by simp [hZero])]
    wp_run_with [hParams, params, hLocals, hValues, hOwner', hTag', hPayload']
    apply hNext
    refine ⟨?_, by simp [List.length_set, hLocals], rfl, ?_, ?_⟩
    · simp only [params, hkadd]
    · simp [hLocals, hZero]
    · intro i hLow hHigh
      simp (discharger := omega) [List.getElem?_set, hLocals]

#print axioms advance_spec
end Project.ClobFindBest.SearchAdvance
