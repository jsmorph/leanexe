import Project.ClobFindBest.FrozenPrefix
import Project.ClobFindBest.FrozenSelectPayload
import Project.ClobFindBest.FrozenAdvance

namespace Project.ClobFindBest.Frozen.Loop
open Wasm Project.Common Project.Clob Project.ClobFindBest
  Project.ClobFindBest.Frozen.Model Project.ClobFindBest.Frozen.Helpers Project.ProofKit.PackedFloatFrame

set_option maxRecDepth 32768
set_option maxHeartbeats 400000

theorem step_spec (env : HostEnv Unit) (st : Store Unit)
    (fuel owner ptr : UInt64) (taker : OrderL) (os : List OrderL) (k : Nat)
    (best : Option Nat) (tag payload : UInt64) (scratch : List Value)
    (hlen : os.length < 4294967296) (hInput : OrdersAt st ptr os)
    (hk : k < os.length) (hBest : ∀ j, best = some j → j < os.length)
    (hScratch : scratch.length = 44)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ next : List Value, next.length = 44 →
      wp module rest Q st (fbFrame (fuel-1) owner ptr taker (k+1)
        (bestStepL os taker k best) tag payload 0 next) env) :
    wp module (stepCode ++ rest) Q st
      (fbFrame fuel owner ptr taker k best tag payload 0 scratch) env := by
  have hCode : stepCode = stepCode.take 26 ++ (stepCode.drop 26).take 5 ++
      (stepCode.drop 31).take 5 ++ stepCode.drop 36 := rfl
  rw [hCode]
  simp only [List.append_assoc]
  apply prefix_spec env st fuel owner ptr taker k best tag payload scratch
    (by rw [size_eq]; omega) hScratch
  let prepared := prefixScratch scratch owner ptr taker k
  have hPrepared : prepared.length = 44 := by
    simpa only [prepared, prefixScratch, List.length_set] using hScratch
  apply select_tag_spec env st fuel owner ptr taker os k best tag payload prepared
    hlen hInput hk hBest hPrepared
  intro tagged hTagged hTag t0 t1 t2 t3 t4 t5 t6 t7
  apply select_payload_spec env st fuel owner ptr taker os k best tag payload tagged
    hlen hInput hk hBest hTagged
  intro loaded hLoaded hPayload p0 p1 p2 p3 p4 p5 p6 p7 pTag
  apply advance_spec env st fuel owner ptr taker k best (bestStepL os taker k best)
    tag payload loaded hLoaded
  · rw [p0, t0]
    simp [prepared, prefixScratch, List.getElem?_set, hScratch]
  · rw [p1, t1]
    simp [prepared, prefixScratch, List.getElem?_set, hScratch]
  · rw [p2, t2]
    simp [prepared, prefixScratch, List.getElem?_set, hScratch]
  · rw [p3, t3]
    simp [prepared, prefixScratch, List.getElem?_set, hScratch]
  · rw [p4, t4]
    simp [prepared, prefixScratch, List.getElem?_set, hScratch]
  · rw [p5, t5]
    simp [prepared, prefixScratch, List.getElem?_set, hScratch]
  · rw [p6, t6]
    simp [prepared, prefixScratch, List.getElem?_set, hScratch]
  · rw [p7, t7]
    simp [prepared, prefixScratch, List.getElem?_set, hScratch]
  · exact pTag.trans hTag
  · exact hPayload
  · exact hNext

#print axioms step_spec
end Project.ClobFindBest.Frozen.Loop
