import Project.ClobFindBest.FrozenLoopState

namespace Project.ClobFindBest.Frozen.Loop
open Wasm Project.Common Project.Clob Project.ClobFindBest
  Project.ClobFindBest.Frozen.Model Project.ClobFindBest.Frozen.Helpers Project.ProofKit.PackedFloatFrame

set_option maxRecDepth 32768
set_option maxHeartbeats 400000

def advanceScratch (scratch : List Value) (owner ptr : UInt64) (taker : OrderL)
    (k : Nat) (selected : Option Nat) : List Value :=
  scratch |>.set 31 (.i64 (owner))
    |>.set 32 (.i64 (ptr))
    |>.set 33 (.i64 (taker.oid))
    |>.set 34 (.i64 (taker.otrader))
    |>.set 35 (.i64 (taker.oside))
    |>.set 36 (.i64 (taker.oprice))
    |>.set 37 (.i64 (taker.oqty))
    |>.set 38 (.i64 (UInt64.ofNat (k+1)))
    |>.set 39 (.i64 (optionTag selected))
    |>.set 40 (.i64 (optionPayload selected))
   

theorem advance_spec (env : HostEnv Unit) (st : Store Unit)
    (fuel owner ptr : UInt64) (taker : OrderL) (k : Nat) (best selected : Option Nat)
    (tag payload : UInt64) (scratch : List Value) (hScratch : scratch.length = 44)
    (h0 : scratch[0]? = some (.i64 (owner)))
    (h1 : scratch[1]? = some (.i64 (ptr)))
    (h2 : scratch[2]? = some (.i64 (taker.oid)))
    (h3 : scratch[3]? = some (.i64 (taker.otrader)))
    (h4 : scratch[4]? = some (.i64 (taker.oside)))
    (h5 : scratch[5]? = some (.i64 (taker.oprice)))
    (h6 : scratch[6]? = some (.i64 (taker.oqty)))
    (h7 : scratch[7]? = some (.i64 (UInt64.ofNat (k+1))))
    (hTag : scratch[29]? = some (.i64 (optionTag selected)))
    (hPayload : scratch[30]? = some (.i64 (optionPayload selected)))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ next : List Value, next.length = 44 →
      wp module rest Q st (fbFrame (fuel-1) owner ptr taker (k+1) selected tag payload 0 next) env) :
    wp module (stepCode.drop 36 ++ rest) Q st
      (fbFrame fuel owner ptr taker k best tag payload 0 scratch) env := by
  have hAdd : UInt64.ofNat k + 1 = UInt64.ofNat (k+1) := (UInt64.ofNat_add k 1).symm
  unfold stepCode loopCode func7
  dsimp only
  wp_packed_frame [fbFrame, List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    hScratch, h0, h1, h2, h3, h4, h5, h6, h7, hTag, hPayload]
  norm_num
  rw [hAdd]
  simpa only [fbFrame, advanceScratch, List.cons_append, List.nil_append] using
    hNext (advanceScratch scratch owner ptr taker k selected)
      (by simpa only [advanceScratch, List.length_set] using hScratch)

#print axioms advance_spec
end Project.ClobFindBest.Frozen.Loop
