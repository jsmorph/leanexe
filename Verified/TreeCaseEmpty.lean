import Verified.TreeMatchBody
import Verified.CoercedRelease

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime

theorem spec_treeCase_empty {S : List Sig} {Γ : List Ty} {t : Ty} {shape : TreeShape}
    {m : Module} {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S}
    {host : HostEnv Unit} {pv : List Value} (hm : Runtime m)
    (x : Var Γ (.tree shape)) (empty : Expr S Γ t) (node : Expr S (shape.context Γ) t)
    (emptySpec : ∀ env slots paid live,
      CodeSpec m funs flags bounds fits host pv empty env slots paid live)
    (env : Env Γ) (slots : List Slot) (paid : List Bool) (live : Nat → Bool)
    (hNil : env.get x = .nil) :
    CodeSpec m funs flags bounds fits host pv (Expr.treeCase x empty node) env slots paid live := by
  intro h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap hNext
  let e := Expr.treeCase x empty node
  let L0 := fun i => live i || e.uses i
  let target := e.mode (slots.map Slot.mode)
  have hx : L0 x.index = true := by simp [L0, e, Expr.uses]
  obtain ⟨hBelow, ws, hold, hRep⟩ := hVars.get x hx
  obtain ⟨p, rfl, hNode⟩ := hRep
  have hp : p = 0 := by
    have hn := hNode.borrow
    rw [hNil] at hn
    exact hn
  subst p
  have hGet : s.get (slots.getD x.index default).loc = some (.i64 0) := by
    have hg := hold 0 (by simp)
    simpa [Ty.types, slotIndex] using hg
  have hMid := (treeCase_entryLive x empty node live).symm
  have hEntry : ∀ i, (live i || empty.uses i) = true → L0 i = true := by
    intro i hi
    simp only [L0, e, Expr.uses, Bool.or_eq_true] at hi ⊢
    tauto
  have hTarget : empty.mode (slots.map Slot.mode) = .owned → target = .owned := by
    intro hm
    simp [target, e, Expr.mode, hm, Mode.join]
  have hRoomE : base + t.width + max empty.width (copyWidth t) ≤ h := by
    simp only [Expr.width] at hRoom
    have := Nat.le_max_left (max empty.width (copyWidth t))
      (shape.bindCount + max treeCopyScratch (max node.width (copyWidth t)))
    omega
  have hPlaceE : empty.placeArgs = true := by
    simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
    exact hPlace.1
  have hBudget : TrapOK (!(empty.fits funs fits env) || !decide (heap.Within store m
      (dyingPot store s env slots paid L0 live +
        empty.allocs funs flags bounds (slots.map Slot.mode) paid live env +
        coerceCost t (empty.mode (slots.map Slot.mode)) target (empty.denote funs env)))) Q := by
    simpa only [trapFlag, Expr.aborts, Bool.true_or, Bool.true_and, Expr.allocs, Expr.fits,
      hNil, L0, e, target, Expr.mode, modeAt, Nat.add_assoc] using hTrap
  simp only [Expr.code, Expr.usesFast_eq, List.append_assoc, List.cons_append, List.nil_append,
    wp_localGet_cons, hGet, wp_eqzI64_cons]
  rw [wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  simp (config := { decide := true }) only [↓reduceIte]
  simp_rw [show ∀ i, (live i || decide (i = x.index) || empty.uses i ||
    node.uses (i + shape.bindCount)) = L0 i from congrFun hMid]
  have hModeCode : target = (empty.mode (slots.map Slot.mode)).join
      (node.mode (shape.modes (slots.getD x.index default).mode (slots.map Slot.mode))) := by
    simp only [target, e, Expr.mode, Slot.modes_getD]
  rw [← hModeCode]
  refine (emptySpec env slots paid live).releaseCoerced hm hTarget hh hpv
    (hVars.mono (Nat.le_add_right _ _)) hAt hCap (by omega) hRoomE hPlaceE hEntry
    (rest := storeCode h base t.types) (hBudget.imp (fun _ hi => hi))
    (fun heap1 store1 s1 ws a hTop => by
      have hh1 := a.frame.positions.trans hh
      rw [← List.append_nil (storeCode h base t.types)]
      refine wp_storeCode ws h base t.types s1 s.values a.rep.typed hh1
        (by rw [a.frame.params]; exact hBase) (by rw [Ty.types_length, hh1]; omega)
        (fun s2 hF hold _ => ?_)
      rw [wp_nil]
      change wp m (loadCode h base t.types ++ rest) Q store1
        { s2 with values := s.values } host
      refine wp_loadCode ws a.rep.typed (hF.positions.trans hh1) hold ?_
      have hLower := a.lower hVars (Nat.le_add_right _ _) (fun i hi => by simp [hi])
      have hFrame : Frame base s1 { s2 with values := s.values } := hF.trans Frame.ofValues
      have hAfter : After env slots L0 live base heap store s t target (empty.denote funs env)
          heap1 store1 { s2 with values := s.values } ws :=
        ⟨hLower.step, hLower.frame.trans hFrame, hLower.holds.agree hFrame, hLower.rep,
          hLower.apart.agree hLower.holds hFrame⟩
      apply hNext heap1 store1 _ ws
      · simpa only [e, L0, target, Expr.denote, hNil, Expr.mode] using hAfter
      · intro hf
        have hFit : empty.fits funs fits env = true := by
          simpa only [Expr.fits, hNil] using hf
        have ht := hTop hFit
        simpa only [e, L0, target, Expr.paid, Bool.false_eq_true, ↓reduceIte, Nat.add_zero,
          Expr.allocs, hNil, Expr.mode, modeAt, Nat.add_assoc] using ht)

end Verified
