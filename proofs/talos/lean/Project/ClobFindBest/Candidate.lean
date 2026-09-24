import Project.ClobFindBest.LoopState

namespace Project.ClobFindBest.Loop
open Wasm Project.Common Project.Clob Project.ClobFindBest
  Project.ClobFindBest.Model Project.ClobFindBest.Helpers Project.ProofKit.PackedFloatFrame

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

def candidateScratch (scratch : List Value) (ptr : UInt64) (k : Nat) (candidate : OrderL) : List Value :=
  scratch |>.set 49 (.i64 ptr) |>.set 50 (.i64 (UInt64.ofNat k)) |>.set 0 (.i64 candidate.oid)
    |>.set 49 (.i64 ptr) |>.set 50 (.i64 (UInt64.ofNat k)) |>.set 1 (.i64 candidate.otrader)
    |>.set 49 (.i64 ptr) |>.set 50 (.i64 (UInt64.ofNat k)) |>.set 2 (.i64 candidate.oside)
    |>.set 49 (.i64 ptr) |>.set 50 (.i64 (UInt64.ofNat k)) |>.set 3 (.i64 candidate.oprice)
    |>.set 49 (.i64 ptr) |>.set 50 (.i64 (UInt64.ofNat k)) |>.set 4 (.i64 candidate.oqty)

theorem candidateScratch_length (scratch : List Value) (ptr : UInt64) (k : Nat) (candidate : OrderL) :
    (candidateScratch scratch ptr k candidate).length = scratch.length := by
  simp only [candidateScratch, List.length_set]

theorem candidate_spec (env : HostEnv Unit) (st : Store Unit)
    (fuel owner ptr : UInt64) (taker : OrderL) (os : List OrderL) (k : Nat)
    (best : Option Nat) (tag payload : UInt64) (scratch : List Value)
    (hlen : os.length < 4294967296) (hInput : OrdersAt st ptr os)
    (hk : k < os.length) (hBest : ∀ j, best = some j → j < os.length)
    (hScratch : scratch.length = 52)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module rest Q st
      (fbFrame fuel owner ptr taker k best tag payload 0
        (candidateScratch scratch ptr k os[k]!)) env) :
    wp module (stepCode.take 55 ++ rest) Q st
      (fbFrame fuel owner ptr taker k best tag payload 0 scratch) env := by
  obtain ⟨⟨hHead, hHeadB⟩, hElems⟩ := hInput
  have hlt : UInt64.ofNat k < UInt64.ofNat os.length := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' (by rw [size_eq]; omega),
      UInt64.toNat_ofNat_of_lt' (by rw [size_eq]; omega)]
    exact hk
  obtain ⟨⟨hr1, hb1⟩, ⟨hr2, hb2⟩, ⟨hr3, hb3⟩, ⟨hr4, hb4⟩, ⟨hr5, hb5⟩⟩ := hElems k hk
  unfold stepCode loopCode func7
  dsimp only
  wp_packed_frame [List.set, List.getElem?_cons_zero, List.getElem?_cons_succ, hScratch, hHead, fbFrame]
  norm_num [UInt64.toNat_ofNat, hHead, hr1, hr2, hr3, hr4, hr5, Nat.not_lt_of_ge hHeadB, Nat.not_lt_of_ge hb1,
    Nat.not_lt_of_ge hb2, Nat.not_lt_of_ge hb3, Nat.not_lt_of_ge hb4, Nat.not_lt_of_ge hb5]
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp [hHead, hlt])]
  wp_packed_frame [List.set, List.getElem?_cons_zero, List.getElem?_cons_succ, hScratch]
  norm_num [UInt64.toNat_ofNat, hHead, hr1, hr2, hr3, hr4, hr5, Nat.not_lt_of_ge hHeadB, Nat.not_lt_of_ge hb1,
    Nat.not_lt_of_ge hb2, Nat.not_lt_of_ge hb3, Nat.not_lt_of_ge hb4, Nat.not_lt_of_ge hb5]
  norm_num [UInt64.toNat_ofNat, hHead, hr1, hr2, hr3, hr4, hr5, Nat.not_lt_of_ge hHeadB, Nat.not_lt_of_ge hb1,
    Nat.not_lt_of_ge hb2, Nat.not_lt_of_ge hb3, Nat.not_lt_of_ge hb4, Nat.not_lt_of_ge hb5]
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp [hHead, hlt])]
  wp_packed_frame [List.set, List.getElem?_cons_zero, List.getElem?_cons_succ, hScratch]
  norm_num [UInt64.toNat_ofNat, hHead, hr1, hr2, hr3, hr4, hr5, Nat.not_lt_of_ge hHeadB, Nat.not_lt_of_ge hb1,
    Nat.not_lt_of_ge hb2, Nat.not_lt_of_ge hb3, Nat.not_lt_of_ge hb4, Nat.not_lt_of_ge hb5]
  norm_num [UInt64.toNat_ofNat, hHead, hr1, hr2, hr3, hr4, hr5, Nat.not_lt_of_ge hHeadB, Nat.not_lt_of_ge hb1,
    Nat.not_lt_of_ge hb2, Nat.not_lt_of_ge hb3, Nat.not_lt_of_ge hb4, Nat.not_lt_of_ge hb5]
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp [hHead, hlt])]
  wp_packed_frame [List.set, List.getElem?_cons_zero, List.getElem?_cons_succ, hScratch]
  norm_num [UInt64.toNat_ofNat, hHead, hr1, hr2, hr3, hr4, hr5, Nat.not_lt_of_ge hHeadB, Nat.not_lt_of_ge hb1,
    Nat.not_lt_of_ge hb2, Nat.not_lt_of_ge hb3, Nat.not_lt_of_ge hb4, Nat.not_lt_of_ge hb5]
  norm_num [UInt64.toNat_ofNat, hHead, hr1, hr2, hr3, hr4, hr5, Nat.not_lt_of_ge hHeadB, Nat.not_lt_of_ge hb1,
    Nat.not_lt_of_ge hb2, Nat.not_lt_of_ge hb3, Nat.not_lt_of_ge hb4, Nat.not_lt_of_ge hb5]
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp [hHead, hlt])]
  wp_packed_frame [List.set, List.getElem?_cons_zero, List.getElem?_cons_succ, hScratch]
  norm_num [UInt64.toNat_ofNat, hHead, hr1, hr2, hr3, hr4, hr5, Nat.not_lt_of_ge hHeadB, Nat.not_lt_of_ge hb1,
    Nat.not_lt_of_ge hb2, Nat.not_lt_of_ge hb3, Nat.not_lt_of_ge hb4, Nat.not_lt_of_ge hb5]
  norm_num [UInt64.toNat_ofNat, hHead, hr1, hr2, hr3, hr4, hr5, Nat.not_lt_of_ge hHeadB, Nat.not_lt_of_ge hb1,
    Nat.not_lt_of_ge hb2, Nat.not_lt_of_ge hb3, Nat.not_lt_of_ge hb4, Nat.not_lt_of_ge hb5]
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp [hHead, hlt])]
  wp_packed_frame [List.set, List.getElem?_cons_zero, List.getElem?_cons_succ, hScratch]
  norm_num [UInt64.toNat_ofNat, hHead, hr1, hr2, hr3, hr4, hr5, Nat.not_lt_of_ge hHeadB, Nat.not_lt_of_ge hb1,
    Nat.not_lt_of_ge hb2, Nat.not_lt_of_ge hb3, Nat.not_lt_of_ge hb4, Nat.not_lt_of_ge hb5]
  norm_num [UInt64.toNat_ofNat, hHead, hr1, hr2, hr3, hr4, hr5, Nat.not_lt_of_ge hHeadB, Nat.not_lt_of_ge hb1,
    Nat.not_lt_of_ge hb2, Nat.not_lt_of_ge hb3, Nat.not_lt_of_ge hb4, Nat.not_lt_of_ge hb5]
  simpa only [fbFrame, candidateScratch, List.getElem!_eq_getElem?_getD,
    List.cons_append, List.nil_append] using hNext

#print axioms candidate_spec
end Project.ClobFindBest.Loop
