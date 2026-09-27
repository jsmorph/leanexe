import Project.ClobFindBest.LoopState

namespace Project.ClobFindBest.Loop
open Wasm Project.Common Project.Clob Project.ClobFindBest
  Project.ClobFindBest.Model Project.ProofKit.PackedFloatFrame

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

theorem advance_spec (env : HostEnv Unit) (st : Store Unit)
    (fuel owner ptr : UInt64) (taker : OrderL) (k : Nat) (best selected : Option Nat)
    (tag payload : UInt64) (scratch : List Value)
    (hk : k + 1 < UInt64.size) (hScratch : scratch.length = 52)
    (hTag : scratch[26]? = some (.i64 (optionTag selected)))
    (hPayload : scratch[27]? = some (.i64 (optionPayload selected)))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ next : List Value, next.length = 52 →
      wp module rest Q st (fbFrame (fuel-1) owner ptr taker (k+1) selected tag payload 0 next) env) :
    wp module (advanceCode ++ rest) Q st (fbFrame fuel owner ptr taker k best tag payload 0 scratch) env := by
  have hAdd : UInt64.ofNat k + 1 = UInt64.ofNat (k+1) := (UInt64.ofNat_add k 1).symm
  have hGuard : ¬ UInt64.ofNat (k+1) < UInt64.ofNat k := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' hk,
      UInt64.toNat_ofNat_of_lt' (by omega)]
    omega
  unfold advanceCode stepCode loopCode func7
  dsimp only
  wp_packed_frame [fbFrame, List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    hScratch, hAdd]
  norm_num
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hGuard)]
  wp_packed_frame [List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    hScratch, hTag, hPayload]
  norm_num
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame [List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    hScratch]
  norm_num
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame [List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    hScratch]
  norm_num
  refine wp_iff_cons rfl ?_
  by_cases hOwner : owner = 0
  · rw [ite_eq_left (by simp [hOwner])]
    wp_packed_frame [List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
      hScratch, hOwner, hAdd]
    norm_num
    rw [hAdd]
    simpa only [fbFrame, advanceScratch, hOwner, List.cons_append, List.nil_append] using
      hNext (advanceScratch scratch owner ptr taker k selected)
        ((advanceScratch_length scratch owner ptr taker k selected).trans hScratch)
  · rw [ite_eq_right (by simp [hOwner])]
    wp_packed_frame [List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
      hScratch, hAdd]
    norm_num
    rw [hAdd]
    simpa only [fbFrame, advanceScratch, List.cons_append, List.nil_append] using
      hNext (advanceScratch scratch owner ptr taker k selected)
        ((advanceScratch_length scratch owner ptr taker k selected).trans hScratch)

#print axioms advance_spec
end Project.ClobFindBest.Loop
