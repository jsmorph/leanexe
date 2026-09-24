import Project.ClobFindBest.FrozenLoopState

namespace Project.ClobFindBest.Frozen.Loop
open Wasm Project.Common Project.Clob Project.ClobFindBest
  Project.ClobFindBest.Frozen.Model Project.ClobFindBest.Frozen.Helpers Project.ProofKit.PackedFloatFrame

set_option maxRecDepth 32768
set_option maxHeartbeats 400000

def prefixScratch (scratch : List Value) (owner ptr : UInt64) (taker : OrderL) (k : Nat) : List Value :=
  scratch |>.set 0 (.i64 owner)
    |>.set 1 (.i64 ptr)
    |>.set 2 (.i64 taker.oid)
    |>.set 3 (.i64 taker.otrader)
    |>.set 4 (.i64 taker.oside)
    |>.set 5 (.i64 taker.oprice)
    |>.set 6 (.i64 taker.oqty)
    |>.set 41 (.i64 (UInt64.ofNat k)) |>.set 42 (.i64 1)
    |>.set 43 (.i64 (UInt64.ofNat (k+1))) |>.set 7 (.i64 (UInt64.ofNat (k+1)))

theorem prefix_spec (env : HostEnv Unit) (st : Store Unit)
    (fuel owner ptr : UInt64) (taker : OrderL) (k : Nat) (best : Option Nat)
    (tag payload : UInt64) (scratch : List Value)
    (hk : k+1 < UInt64.size) (hScratch : scratch.length = 44)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module rest Q st
      (fbFrame fuel owner ptr taker k best tag payload 0 (prefixScratch scratch owner ptr taker k)) env) :
    wp module (stepCode.take 26 ++ rest) Q st
      (fbFrame fuel owner ptr taker k best tag payload 0 scratch) env := by
  have hAdd : UInt64.ofNat k + 1 = UInt64.ofNat (k+1) := (UInt64.ofNat_add k 1).symm
  have hGuard : ¬ UInt64.ofNat (k+1) < UInt64.ofNat k := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' hk,
      UInt64.toNat_ofNat_of_lt' (by omega)]
    omega
  unfold stepCode loopCode func7
  dsimp only
  wp_packed_frame [fbFrame, List.set, List.getElem?_cons_zero, List.getElem?_cons_succ, hScratch, hAdd]
  norm_num
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hGuard)]
  wp_packed_frame [List.set, List.getElem?_cons_zero, List.getElem?_cons_succ, hScratch, hAdd]
  norm_num
  rw [hAdd]
  simpa only [fbFrame, prefixScratch, List.cons_append, List.nil_append] using hNext

#print axioms prefix_spec
end Project.ClobFindBest.Frozen.Loop
