import Verified.TreeCopyLoopCode
import Verified.TreeNewCode

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

theorem wp_treeCopyRecord {m : Module} (hm : Runtime m) {host : HostEnv Unit} {heap : Heap}
    {store : Store Unit} {s : Locals} {shape : TreeShape} {src base : Nat} {source : UInt64}
    {slots : List LeanExe.Pipeline.Slot} {rest : Program} {Q : Assertion Unit}
    (hAt : heap.At store) (hCap : store.memoryCap m 0 ≤ 65535)
    (hLayout : NodeLayout shape (.record slots)) (hSource : NodeBorrowed heap store source (.record slots))
    (hTrap : TrapOK (!decide (heap.Within store m
      (allocCost (8 * shape.fields.length) * (Node.record slots).records))) Q)
    (hSrc : s.get src = some (.i64 source)) (hSrcBase : src < base)
    (hLow : s.params.length ≤ base) (hHigh : base + 6 ≤ s.positions)
    (hNext : ∀ heap' store' s' ptr,
      Step heap store (fun _ => True) heap' store' (Node.blocks store' ptr (.record slots)) →
      NodeOwned heap' store' ptr (.record slots) →
      (Node.blocks store' ptr (.record slots)).Pairwise regionsDisjoint → Frame base s s' →
      heap'.top.toNat ≤ heap.top.toNat + allocCost (8 * shape.fields.length) * (Node.record slots).records →
      wp m rest Q store' { s' with values := .i64 ptr :: s.values } host) :
    wp m (treeCopyAllocate shape base ++ treeCopyBegin base [.localGet src] [.constI64 0] ++
      [.localGet base, .localSet (base + 1), .block 0 0 [.loop 0 0 (treeCopyBody shape base)],
        .localGet base] ++ rest) Q store s host := by
  have hCost : allocCost (8 * shape.fields.length) ≤
      allocCost (8 * shape.fields.length) * (Node.record slots).records :=
    Nat.le_mul_of_pos_right _ (by simp only [Node.records]; omega)
  have hHigh0 : base < s.params.length + s.locals.length := Locals.lt_total (by omega)
  rw [List.append_assoc, List.append_assoc]
  refine wp_treeCopyNew hm (shape := shape) (dst := base) (input := src) (parent := none)
    (slots := slots) (rest := [.localGet base, .localSet (base + 1),
      .block 0 0 [.loop 0 0 (treeCopyBody shape base)], .localGet base] ++ rest)
    hAt hCap (hTrap.within (fun hRoom => hRoom.mono hCost)) hLayout hSource hSrc rfl
    (by omega) (by intro pos h; cases h) hLow hHigh0 ?_
  intro heap' store' ptr hNew hRecord hTop
  have hInv := CopyInv.start (limit := heap.top.toNat + allocCost (8 * shape.fields.length) *
    (Node.record slots).records) hSource hNew hRecord hTop (Nat.le_refl _)
  let sResult := setLocal s base (.i64 ptr)
  have hResult : sResult.get base = some (.i64 ptr) := Locals.get_setLocal_same hLow hHigh0
  have hFrameResult : Frame base s sResult := Frame.set hLow (by omega) (by omega)
  have hLow1 : sResult.params.length ≤ base + 1 := by change s.params.length ≤ base + 1; omega
  have hHigh1 : base + 1 < sResult.params.length + sResult.locals.length := by
    simp only [sResult, setLocal, List.length_set]
    exact Locals.lt_total (by omega)
  let sCopy := setLocal sResult (base + 1) (.i64 ptr)
  have hFrameCurrent : Frame base sResult sCopy := Frame.set hLow1 (by omega)
    (by rw [hFrameResult.positions]; omega)
  have hVars : CopyLocals base s ptr ptr sCopy := by
    refine ⟨hFrameResult.trans hFrameCurrent, ?_, Locals.get_setLocal_same hLow1 hHigh1, rfl⟩
    rw [Locals.get_setLocal_ne hLow1 (by omega)]
    exact hResult
  change wp m ([.localGet base, .localSet (base + 1),
    .block 0 0 [.loop 0 0 (treeCopyBody shape base)], .localGet base] ++ rest) Q store' sResult host
  simp only [List.cons_append, List.nil_append, wp_localGet_cons, hResult]
  refine wp_localSet_local hLow1 hHigh1 ?_
  refine wp_treeCopyLoop hm hInv hVars ?_ ?_ hCap hTrap ?_
  · change s.params.length ≤ base
    exact hLow
  · rw [hVars.frame.positions]
    exact hHigh
  intro heap'' store'' s' hOwned hApart hStep hBudget hFrame hGet hValues
  simp only [wp_localGet_cons, hGet]
  simpa only [hValues] using hNext heap'' store'' s' ptr hStep hOwned hApart hFrame hBudget

#print axioms wp_treeCopyRecord

end Verified
