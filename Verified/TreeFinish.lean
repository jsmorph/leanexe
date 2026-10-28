import Verified.FieldsAdvance
import Verified.TreeAssembleTyped

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime

theorem wp_finishTree {Γ : List Ty} {env : Env Γ} {slots : List Slot}
    {L0 L1 live : Nat → Bool} {base fieldBase ptr h : Nat} {shape : TreeShape}
    {r : Fin shape.records}
    {heap heap1 heap2 : Heap} {store store1 store2 : Store Unit} {s s1 s2 : Locals}
    {words : (i : Fin (shape.words r)) → (shape.elem r i).denote}
    {children : Fin (shape.children r) → Tree shape}
    {ws : List Value} {p : UInt64} {m : Module} {host : HostEnv Unit}
    {rest : Program} {Q : Assertion Unit}
    (h0 : Holds env slots L0 base heap store s)
    (a : FieldsAfter env slots L0 L1 base heap store s
      (Env.prependFn (shape.words r) (shape.wordTy r) words
        (Env.prependRepeat (.tree shape) (shape.children r) children .nil)) heap1 store1 s1 ws)
    (hStep : Step heap1 store1 (Holds.KeepDying env slots L1 live store1 s1)
      heap2 store2 [block store2 p])
    (hFrame : Frame base s1 s2) (hHolds : Holds env slots live base heap2 store2 s2)
    (hL1 : ∀ i, L1 i = true → L0 i = true) (hLive : ∀ i, live i = true → L1 i = true)
    (hRaw : RecordStorage (shape.width r) heap2 store2 p)
    (hCount : store2.mem.read64 (p - 40).toUInt32 = 1)
    (hPtr : s2.get ptr = some (.i64 p)) (hStack : s2.values = s.values)
    (hh : s2.positions = h)
    (hLocals : LocalsHold s2 fieldBase
      (shape.wordTypes r ++ List.replicate (shape.children r) .i64) ws)
    (hRootApart : Holds.Apart env slots live store2 s2 (.treeHeader shape r) .owned [.i64 p] .unit)
    (hNext : ∀ store',
      After env slots L0 live base heap store s (.tree shape) .owned (.node r words arrays buffers children)
        heap2 store' s2 [.i64 p] →
      wp m rest Q store' { s2 with values := .i64 p :: s.values } host) :
    wp m (shape.tagStoreCode r ptr ++
      treeStoreFields h ptr (shape.wordTypes r) fieldBase (fieldBase + shape.words r)
        shape.fieldStart (shape.fields r) ++
      sealRecordCode (shape.width r) ptr (shape.mask r) ++ (.localGet ptr :: rest))
      Q store2 s2 host := by
  obtain ⟨a2, hBoth, hSame, hFresh⟩ := a.advance h0 hStep hFrame hHolds hL1 hLive
  have hApart : (block store2 p ::
      (Env.prependFn (shape.words r) (shape.wordTy r) words
        (Env.prependRepeat (.tree shape) (shape.children r) children .nil)).blocks store2
          ws).Pairwise regionsDisjoint := by
    refine List.pairwise_cons.mpr ⟨?_, a2.pairwise⟩
    intro b hb
    rw [hSame] at hb
    exact regionsDisjoint_symm (hFresh b hb (block store2 p) (by simp))
  have hKeepLive : ∀ (u : Ty) (x : Var Γ u), live x.index = true → ∀ wx,
      LocalsHold s2 (slots.getD x.index default).loc u.types wx → wx.length = u.width →
      ∀ c ∈ u.regions (slots.getD x.index default).mode store2 wx (env.get x),
        regionsDisjoint c (block store2 p) := by
    intro u x hx wx hold length c hc
    exact regionsDisjoint_symm (hRootApart u x hx (Or.inl rfl) wx hold length
      (block store2 p) (by simp [Ty.regions, Ty.blocks]) c hc)
  refine wp_assembleTree hh hRaw hStep.at_ hPtr hCount a2.rep hLocals hApart
    fun store3 hAt3 hRep hBlocks hWrite => ?_
  have hWhole := hBoth.transBoth hWrite
    (keep := Holds.KeepDying env slots L0 live store s)
    (fun r hr => ⟨hr, fun hApart => hApart (block store2 p)
      (List.mem_append_right _ (by simp))⟩)
  have hAfter : After env slots L0 live base heap store s (.tree shape) .owned
      (.node r words arrays buffers children) heap2 store3 s2 [.i64 p] := by
    refine ⟨?_, a2.frame, hHolds.step hWrite hKeepLive, hRep, ?_⟩
    · change Step heap store (Holds.KeepDying env slots L0 live store s) heap2 store3
        ((Ty.tree shape).blocks store3 [.i64 p] (.node r words arrays buffers children))
      rw [hBlocks]
      apply hWhole.mono (fun _ hr => hr)
      intro b hb
      apply List.mem_append_left []
      rcases List.mem_cons.mp hb with rfl | hb
      · exact List.mem_append_right _ (by simp)
      · exact List.mem_append_left _ hb
    · intro u x hx _ wx hold length b hb c hc
      change b ∈ (Ty.tree shape).blocks store3 [.i64 p] (.node r words arrays buffers children) at hb
      rw [hBlocks] at hb
      have hRegions := (hHolds.regions_after hWrite hx hold length
        (hKeepLive u x hx wx hold length)).1
      rw [hRegions] at hc
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hRootApart u x hx (Or.inl rfl) wx hold length (block store2 p)
          (by simp [Ty.regions, Ty.blocks]) c hc
      · exact a2.apart u x hx wx hold length b hb c hc
  rw [wp_localGet_cons, hPtr]
  simpa only [hStack] using hNext store3 hAfter

end Verified
