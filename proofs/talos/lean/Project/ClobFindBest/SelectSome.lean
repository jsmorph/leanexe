import Project.ClobFindBest.SelectSomeTag
import Project.ClobFindBest.SelectSomePayload

namespace Project.ClobFindBest.Loop
open Wasm Project.Common Project.Clob Project.ClobFindBest
  Project.ClobFindBest.Model Project.ClobFindBest.Helpers Project.ProofKit.PackedFloatFrame

theorem select_some_spec (env : HostEnv Unit) (st : Store Unit)
    (fuel owner ptr : UInt64) (taker : OrderL) (os : List OrderL) (k j : Nat)
    (tag payload : UInt64) (scratch : List Value)
    (hlen : os.length < 4294967296) (hInput : OrdersAt st ptr os) (hj : j < os.length)
    (hScratch : scratch.length = 52)
    (h0 : scratch[0]? = some (.i64 os[k]!.oid))
    (h1 : scratch[1]? = some (.i64 os[k]!.otrader))
    (h2 : scratch[2]? = some (.i64 os[k]!.oside))
    (h3 : scratch[3]? = some (.i64 os[k]!.oprice))
    (h4 : scratch[4]? = some (.i64 os[k]!.oqty))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ next : List Value, next.length = 52 →
      next[26]? = some (.i64 (optionTag (bestStepL os taker k (some j)))) →
      next[27]? = some (.i64 (optionPayload (bestStepL os taker k (some j)))) →
      wp module rest Q st (fbFrame fuel owner ptr taker k (some j) tag payload 0 next) env) :
    wp module ((stepCode.drop 55).take 10 ++ rest) Q st
      (fbFrame fuel owner ptr taker k (some j) tag payload 0 scratch) env := by
  have hCode : (stepCode.drop 55).take 10 =
      (stepCode.drop 55).take 5 ++ (stepCode.drop 60).take 5 := rfl
  rw [hCode, List.append_assoc]
  apply select_some_tag_spec env st fuel owner ptr taker os k j tag payload scratch
    hlen hInput hj hScratch h0 h1 h2 h3 h4
  intro mid hMid hTag h0' h1' h2' h3' h4'
  apply select_some_payload_spec env st fuel owner ptr taker os k j tag payload mid
    hlen hInput hj hMid (h0'.trans h0) (h1'.trans h1) (h2'.trans h2) (h3'.trans h3) (h4'.trans h4)
  intro next hLen hPayload hTag'
  exact hNext next hLen (hTag'.trans hTag) hPayload

#print axioms select_some_spec
end Project.ClobFindBest.Loop
