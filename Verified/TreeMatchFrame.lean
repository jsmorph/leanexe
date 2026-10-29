import Verified.TreeContextAppend
import Verified.TreeMatchLocals

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime

theorem After.openTreeFields {Γ : List Ty} {env : Env Γ} {slots : List Slot}
    {L0 L1 : Nat → Bool} {base fieldBase : Nat} {heap0 heap : Heap}
    {store0 store : Store Unit} {s0 s s' : Locals} {shape : TreeShape} {r : Fin shape.records}
    {mode : Mode} {p : UInt64} {words : (i : Fin (shape.words r)) → (shape.elem r i).denote}
    {arrays : (i : Fin (shape.arrays r)) → Array (shape.arrayElem r i).denote}
    {buffers : Fin (shape.buffers r) → LeanExe.Bytes}
    {children : Fin (shape.children r) → Tree shape}
    (a : After env slots L0 L1 base heap0 store0 s0 (.tree shape) mode
      (.node r words arrays buffers children)
      heap store s [.i64 p])
    (hFrame : Frame base s s') (hBase : base ≤ fieldBase)
    (hStep : Step heap store (fun b => mode = .owned → regionsDisjoint b (block store p))
      heap (treeDetachStore mode store p) [])
    (hPrefix : Holds (Env.treeFields shape r words arrays buffers children .nil)
      (shape.slots r fieldBase mode [])
      (fun _ => true) (fieldBase + shape.bindWidth r) heap (treeDetachStore mode store p) s')
    (hSubset : ∀ (t : Ty) (x : Var (shape.context r []) t) (ws : List Value),
      LocalsHold s' ((shape.slots r fieldBase mode []).getD x.index default).loc t.types ws →
      ws.length = t.width →
      ∀ b ∈ t.regions ((shape.slots r fieldBase mode []).getD x.index default).mode
        (treeDetachStore mode store p) ws
          ((Env.treeFields shape r words arrays buffers children .nil).get x),
        b ∈ (Ty.tree shape).regions mode store [.i64 p] (.node r words arrays buffers children)) :
    Step heap0 store0 (Holds.KeepDying env slots L0 L1 store0 s0)
        heap (treeDetachStore mode store p)
        (mode.fresh store (.tree shape) [.i64 p] (.node r words arrays buffers children)) ∧
      Frame base s0 s' ∧
      Holds env slots L1 base heap (treeDetachStore mode store p) s' ∧
      Holds (Env.treeFields shape r words arrays buffers children env)
        (shape.slots r fieldBase mode slots)
        (fun i => decide (i < shape.bindCount r) || shift (shape.bindCount r) L1 i)
        (fieldBase + shape.bindWidth r) heap (treeDetachStore mode store p) s' ∧
      (∀ (t : Ty) (x : Var (shape.context r []) t),
        ((shape.slots r fieldBase mode []).getD x.index default).mode = .owned →
        ∀ ws, LocalsHold s' ((shape.slots r fieldBase mode []).getD x.index default).loc
          t.types ws →
        ws.length = t.width → ∀ b ∈ t.blocks (treeDetachStore mode store p) ws
          ((Env.treeFields shape r words arrays buffers children .nil).get x),
          b ∈ mode.fresh store (.tree shape) [.i64 p]
            (.node r words arrays buffers children)) := by
  have hParent (hm : mode = .owned) :
      block store p ∈ mode.fresh store (.tree shape) [.i64 p]
        (.node r words arrays buffers children) := by
    subst hm
    exact List.mem_cons_self
  have hKeep : ∀ (u : Ty) (y : Var Γ u), L1 y.index = true → ∀ wy,
      LocalsHold s (slots.getD y.index default).loc u.types wy → wy.length = u.width →
      ∀ c ∈ u.regions (slots.getD y.index default).mode store wy (env.get y),
        mode = .owned → regionsDisjoint c (block store p) := by
    intro u y hy wy hold length c hc hm
    exact regionsDisjoint_symm (a.apart u y hy (.inl hm) wy hold length
      (block store p) (by simpa only [Ty.regions, hm, Mode.fresh] using hParent hm) c hc)
  have hOuter := (a.holds.step hStep hKeep).agree hFrame
  have hWhole := a.step.transBoth hStep
    (keep := Holds.KeepDying env slots L0 L1 store0 s0)
    (fun _ hr => ⟨hr, fun hf hm => hf _ (hParent hm)⟩)
  have hMode : ∀ i, ((shape.slots r fieldBase mode []).getD i default).mode = .owned →
      mode = .owned := by
    intro i hi
    cases mode
    · rw [shape.slots_borrowed r] at hi; exact nomatch hi
    · rfl
  let LB := fun i => decide (i < shape.bindCount r) || shift (shape.bindCount r) L1 i
  have hLength : (shape.slots r fieldBase mode []).length = (shape.context r []).length := by
    simp only [shape.slots_length r, shape.context_length r, List.length_nil, Nat.add_zero]
  have hTail : Holds env slots (fun i => LB ((shape.context r []).length + i))
      (fieldBase + shape.bindWidth r) heap (treeDetachStore mode store p) s' := by
    apply (hOuter.mono (by omega)).live_mono
    intro i hi
    simpa [LB, shape.context_length r, shift] using hi
  have hCombined := Holds.append hLength (hPrefix.live_mono (fun _ _ => rfl)) hTail
    (fun t x hx ws hold length u y hy hm wy hwy hly b hb c hc => by
      have hy' : L1 y.index = true := by
        simpa [LB, shape.context_length r, shift] using hy
      have hwy0 := (a.holds.hold_agree hFrame hy' hly).mp hwy
      have hRegions := (a.holds.regions_after hStep hy' hwy0 hly
        (hKeep u y hy' wy hwy0 hly)).1
      rw [hRegions] at hc
      have hm' : mode = .owned ∨ (slots.getD y.index default).mode = .owned :=
        hm.imp_left (hMode x.index)
      exact a.apart u y hy' hm' wy hwy0 hly
        b (hSubset t x ws hold length b hb) c hc)
  rw [← shape.slots_append r] at hCombined
  have hBound := hCombined.ofHEq (shape.context_append r Γ)
    (Env.treeFields_append shape r words arrays buffers children env)
  refine ⟨by simpa only [List.append_nil] using hWhole, a.frame.trans hFrame, hOuter,
    hBound, ?_⟩
  intro t x hm ws hold length b hb
  have hRootMode := hMode x.index hm
  have hr : b ∈ t.regions ((shape.slots r fieldBase mode []).getD x.index default).mode
      (treeDetachStore mode store p) ws
        ((Env.treeFields shape r words arrays buffers children .nil).get x) := by
    rw [hm]; exact hb
  have h := hSubset t x ws hold length b hr
  simpa only [hRootMode, Mode.fresh, Ty.regions] using h

end Verified
