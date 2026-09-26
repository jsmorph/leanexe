import Project.ClobFindBest.SearchFrame

namespace Project.ClobFindBest.SearchRead
open Wasm Project.Common Project.Clob Project.ClobFindBest.Model
  Project.ClobFindBest.SearchFrame Project.ClobFindBest.SearchProgram
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem read_spec (m : Wasm.Module) (env : HostEnv Unit) (st : Store Unit)
    (base : Locals) (fuel owner ptr : UInt64) (os : List OrderL) (taker : OrderL)
    (k : Nat) (best : Option Nat)
    (hParams : base.params = params fuel owner ptr taker k best)
    (hLocals : base.locals.length = 56) (hValues : base.values = [])
    (hLength : os.length < 4294967296) (hk : k < os.length) (hInput : OrdersAt st ptr os)
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ final, ReadFrame base final os[k]! → wp m rest Q st final env) :
    wp m (readCandidate ++ rest) Q st base env := by
  have hkU : (UInt64.ofNat k).toNat = k := by u64_omega
  have hlt : UInt64.ofNat k < UInt64.ofNat os.length := by
    rw [UInt64.lt_iff_toNat_lt, hkU, toNat_ofNat_lt (by rw [size_eq]; omega)]
    exact hk
  obtain ⟨⟨hHead, hHeadB⟩, hElems⟩ := hInput
  obtain ⟨⟨hr1, hb1⟩, ⟨hr2, hb2⟩, ⟨hr3, hb3⟩, ⟨hr4, hb4⟩, ⟨hr5, hb5⟩⟩ := hElems k hk
  have hSafeHead := Nat.not_lt.mpr hHeadB
  have hSafe1 := Nat.not_lt.mpr hb1
  have hSafe2 := Nat.not_lt.mpr hb2
  have hSafe3 := Nat.not_lt.mpr hb3
  have hSafe4 := Nat.not_lt.mpr hb4
  have hSafe5 := Nat.not_lt.mpr hb5
  simp only [readCandidate, List.cons_append, List.nil_append]
  wp_run_with [hParams, params, hLocals, hValues, hkU, hHead, hr1, hr2, hr3, hr4, hr5, hSafeHead, hSafe1, hSafe2, hSafe3, hSafe4, hSafe5]
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp [hlt])]
  wp_run_with [hParams, params, hLocals, hValues, hkU, hHead, hr1, hr2, hr3, hr4, hr5, hSafeHead, hSafe1, hSafe2, hSafe3, hSafe4, hSafe5]
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp [hlt])]
  wp_run_with [hParams, params, hLocals, hValues, hkU, hHead, hr1, hr2, hr3, hr4, hr5, hSafeHead, hSafe1, hSafe2, hSafe3, hSafe4, hSafe5]
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp [hlt])]
  wp_run_with [hParams, params, hLocals, hValues, hkU, hHead, hr1, hr2, hr3, hr4, hr5, hSafeHead, hSafe1, hSafe2, hSafe3, hSafe4, hSafe5]
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp [hlt])]
  wp_run_with [hParams, params, hLocals, hValues, hkU, hHead, hr1, hr2, hr3, hr4, hr5, hSafeHead, hSafe1, hSafe2, hSafe3, hSafe4, hSafe5]
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp [hlt])]
  wp_run_with [hParams, params, hLocals, hValues, hkU, hHead, hr1, hr2, hr3, hr4, hr5, hSafeHead, hSafe1, hSafe2, hSafe3, hSafe4, hSafe5]
  simp only [← List.getElem!_eq_getElem?_getD]
  apply hNext
  refine ⟨hParams.symm, by simp [List.length_set, hLocals], rfl, ?_, ?_⟩
  · constructor <;> simp [hLocals]
  · intro i hi
    simp (discharger := omega) [List.getElem?_set, hLocals]

#print axioms read_spec
end Project.ClobFindBest.SearchRead
