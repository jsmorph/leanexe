import Project.ClobFindBest.SelectNone
import Project.ClobFindBest.SelectSome

namespace Project.ClobFindBest.Loop
open Wasm Project.Common Project.Clob Project.ClobFindBest
  Project.ClobFindBest.Model Project.ClobFindBest.Helpers Project.ProofKit.PackedFloatFrame

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem select_spec (env : HostEnv Unit) (st : Store Unit)
    (fuel owner ptr : UInt64) (taker : OrderL) (os : List OrderL) (k : Nat)
    (best : Option Nat) (tag payload : UInt64) (scratch : List Value)
    (hlen : os.length < 4294967296) (hInput : OrdersAt st ptr os)
    (hk : k < os.length) (hBest : ∀ j, best = some j → j < os.length)
    (hScratch : scratch.length = 52)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ next : List Value, next.length = 52 →
      next[26]? = some (.i64 (optionTag (bestStepL os taker k best))) →
      next[27]? = some (.i64 (optionPayload (bestStepL os taker k best))) →
      wp module rest Q st (fbFrame fuel owner ptr taker k best tag payload 0 next) env) :
    wp module (stepCode.take 65 ++ rest) Q st
      (fbFrame fuel owner ptr taker k best tag payload 0 scratch) env := by
  have hCode : stepCode.take 65 = stepCode.take 55 ++ (stepCode.drop 55).take 10 := rfl
  rw [hCode, List.append_assoc]
  apply candidate_spec env st fuel owner ptr taker os k best tag payload scratch hlen hInput hk hBest hScratch
  have hLen : (candidateScratch scratch ptr k os[k]!).length = 52 :=
    (candidateScratch_length scratch ptr k os[k]!).trans hScratch
  generalize hs : candidateScratch scratch ptr k os[k]! = loaded
  have h0 : loaded[0]? = some (.i64 os[k]!.oid) := by
    rw [← hs]; simp [candidateScratch, List.getElem?_set, hScratch]
  have h1 : loaded[1]? = some (.i64 os[k]!.otrader) := by
    rw [← hs]; simp [candidateScratch, List.getElem?_set, hScratch]
  have h2 : loaded[2]? = some (.i64 os[k]!.oside) := by
    rw [← hs]; simp [candidateScratch, List.getElem?_set, hScratch]
  have h3 : loaded[3]? = some (.i64 os[k]!.oprice) := by
    rw [← hs]; simp [candidateScratch, List.getElem?_set, hScratch]
  have h4 : loaded[4]? = some (.i64 os[k]!.oqty) := by
    rw [← hs]; simp [candidateScratch, List.getElem?_set, hScratch]
  rw [hs] at hLen
  cases best with
  | none =>
    exact select_none_spec env st fuel owner ptr taker os k tag payload loaded hLen
      h0 h1 h2 h3 h4 Q rest hNext
  | some j =>
    exact select_some_spec env st fuel owner ptr taker os k j tag payload loaded
      hlen hInput (hBest j rfl) hLen h0 h1 h2 h3 h4 Q rest hNext

#print axioms select_spec
end Project.ClobFindBest.Loop
