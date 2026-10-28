import Verified.TreeMatchFacts

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime

theorem After.treeBody {Γ : List Ty} {env : Env Γ} {slots : List Slot}
    {L0 L1 live bodyIn : Nat → Bool} {base fieldBase : Nat} {heap0 heap heap' : Heap}
    {store0 store store' : Store Unit} {s0 s s' : Locals} {shape : TreeShape}
    {r : Fin shape.records} {rootMode : Mode}
    {words : (i : Fin (shape.words r)) → (shape.elem r i).denote}
    {arrays : (i : Fin (shape.arrays r)) → Array (shape.arrayElem r i).denote}
    {buffers : Fin (shape.buffers r) → LeanExe.Bytes}
    {children : Fin (shape.children r) → Tree shape}
    {fresh : List (Nat × Nat)} {t : Ty} {mode : Mode} {value : t.denote} {ws : List Value}
    (h0 : Holds env slots L0 base heap0 store0 s0)
    (hStep : Step heap0 store0 (Holds.KeepDying env slots L0 L1 store0 s0) heap store fresh)
    (hFrame : Frame base s0 s) (hOuter : Holds env slots L1 base heap store s)
    (hFields : Holds (Env.treeFields shape r words arrays buffers children env)
    (shape.slots r fieldBase rootMode slots)
      (fun i => decide (i < shape.bindCount r) || shift (shape.bindCount r) L1 i)
      (fieldBase + shape.bindWidth r) heap store s)
    (hFresh : ∀ (u : Ty) (x : Var (shape.context r []) u),
      ((shape.slots r fieldBase rootMode []).getD x.index default).mode = .owned → ∀ w,
      LocalsHold s ((shape.slots r fieldBase rootMode []).getD x.index default).loc u.types w →
      w.length = u.width → ∀ b ∈ u.blocks store w
        ((Env.treeFields shape r words arrays buffers children .nil).get x),
        b ∈ fresh)
    {heap1 : Heap} {store1 : Store Unit}
    (released : Evolves (Env.treeFields shape r words arrays buffers children env)
    (shape.slots r fieldBase rootMode slots)
      (fun i => decide (i < shape.bindCount r) || shift (shape.bindCount r) L1 i) bodyIn
      (fieldBase + shape.bindWidth r) heap store s heap1 store1 s)
    (body : After (Env.treeFields shape r words arrays buffers children env)
    (shape.slots r fieldBase rootMode slots)
      bodyIn (shift (shape.bindCount r) live) (fieldBase + shape.bindWidth r) heap1 store1 s
      t mode value heap' store' s' ws)
    (hBodyIn : ∀ i, bodyIn i = true →
      (decide (i < shape.bindCount r) || shift (shape.bindCount r) L1 i) = true)
    (hFinal : ∀ i, shift (shape.bindCount r) live i = true → bodyIn i = true)
    (hBase : base ≤ fieldBase + shape.bindWidth r)
    (hL1 : ∀ i, L1 i = true → L0 i = true) (hLive : ∀ i, live i = true → L1 i = true) :
    After env slots L0 live base heap0 store0 s0 t mode value heap' store' s' ws := by
  have hBody := After.prepend hFields released body hBodyIn hFinal
  rw [shape.slots_append r] at hBody
  have hCount : (shape.context r []).length = shape.bindCount r := by
    simp only [shape.context_length r, List.length_nil, Nat.add_zero]
  have hLength : (shape.slots r fieldBase rootMode []).length = (shape.context r []).length := by
    rw [shape.slots_length r, hCount]
  have hBound := hBody.ofHEq (shape.context_append r Γ).symm
    (Env.treeFields_append shape r words arrays buffers children env).symm
  apply After.bindPrefixStep h0 hStep hFrame hOuter (Frame.refl _ _) hLength
    (by simpa only [hCount] using hBound) hBase
  · intro keep hr u x hm w hold length b hb
    exact hr b (hFresh u x hm w hold length b hb)
  · intro i hi
    simpa [hCount, shift] using hi
  · exact hL1
  · exact hLive

end Verified
