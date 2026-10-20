import Verified.TailReleased
import Verified.TreeMatchFacts

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime

theorem tail_treeCase_empty {S : List Sig} {Γ params : List Ty} {result : Ty}
    {shape : TreeShape} {m : Module} {funs : Funs S} {flags : Flags S}
    {bounds : Bounds S} {fits : Fits S} {host : HostEnv Unit} {pv : List Value}
    (hm : Runtime m) (targetModes : List Mode) (x : Var Γ (.tree shape))
    (empty : TailBody S params result Γ) (node : TailBody S params result (shape.context Γ))
    (emptySpec : TailCodeSpec m funs flags bounds fits host pv targetModes empty)
    (env : Env Γ) (hNil : env.get x = .nil) :
    TailCodeSpecAt m funs flags bounds fits host pv targetModes (.treeCase x empty node) env := by
  intro slots paid nextPaid resultPaid h stateBase resultBase base exitLabel nextLabel heap
    store s hh hpv hVars hAt hCap hLow hState hResult hRoom hPlace hPaid Q hTrap hNext
  let outer := TailBody.treeCase x empty node
  let L0 := outer.uses
  have hx : L0 x.index = true := by simp [L0, outer, TailBody.uses]
  obtain ⟨_, ws, hold, rep⟩ := hVars.get x hx
  obtain ⟨p, rfl, root⟩ := rep
  have hp : p = 0 := by
    have hr := root.borrow
    rw [hNil] at hr
    exact hr
  subst p
  have hGet : s.get (slots.getD x.index default).loc = some (.i64 0) := by
    have hg := hold 0 (by simp)
    simpa [Ty.types, slotIndex] using hg
  have hEntry : ∀ i, empty.uses i = true → L0 i = true := by
    intro i hi
    simp [L0, outer, TailBody.uses, hi]
  have hRoomE : base + empty.width targetModes ≤ h := by
    simp only [TailBody.width] at hRoom
    have := Nat.le_max_left (empty.width targetModes)
      (shape.bindCount + max treeCopyScratch (node.width targetModes))
    omega
  have hPlaceE : empty.placeArgs targetModes (slots.map Slot.mode) = true := by
    simp only [TailBody.placeArgs, Bool.and_eq_true] at hPlace
    exact hPlace.1
  have hPaidE : resultPaid = true → empty.paidResult flags (slots.map Slot.mode) paid = true := by
    intro hp
    have hf := hPaid hp
    simp only [TailBody.paidResult, Bool.false_eq_true] at hf
  have hBudget : TrapOK (!(empty.fits funs fits env) || !decide (heap.Within store m
      (dyingPot store s env slots paid L0 (fun _ => false) +
        empty.allocs funs flags bounds targetModes nextPaid (slots.map Slot.mode) paid env))) Q := by
    simpa only [tailTrapFlag, TailBody.aborts, Bool.true_or, Bool.true_and,
      TailBody.allocs, TailBody.fits, hNil, L0, outer] using hTrap
  have hValue : empty.denote funs env = outer.denote funs env := by
    simp only [outer, TailBody.denote, hNil]
  simp only [TailBody.code, TailBody.usesFast_eq, List.append_assoc, List.cons_append,
    List.nil_append, wp_localGet_cons, hGet, wp_eqzI64_cons]
  rw [wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  simp (config := { decide := true }) only [↓reduceIte]
  simp_rw [← nat_beq_decide]
  change wp m (releaseWhere Γ slots (fun i => L0 i && !empty.uses i) ++
    empty.code targetModes h stateBase resultBase slots base (exitLabel + 1) (nextLabel + 1))
    _ store s host
  refine emptySpec.released hm hh hpv hVars hAt hCap hLow hState hResult hRoomE hPlaceE
    hPaidE hEntry (hBudget.imp (fun _ hi => hi)) (fun heap1 store1 s1 after hTop => ?_)
  have done := hNext heap1 store1 s1 (after.congr hValue) (fun hf => by
    have hfE : empty.fits funs fits env = true := by
      simpa only [outer, TailBody.fits, hNil] using hf
    have ht := hTop hfE
    change heap1.top.toNat +
      tailPot targetModes nextPaid resultPaid store1 after.words (outer.denote funs env) ≤ _
    rw [← hValue]
    simpa only [outer, TailBody.allocs, hNil, L0] using ht)
  have labelEq : (empty.denote funs env).elim (fun _ => nextLabel + 1) (fun _ => exitLabel + 1) =
      (outer.denote funs env).elim (fun _ => nextLabel) (fun _ => exitLabel) + 1 := by
    rw [hValue]
    cases outer.denote funs env <;> rfl
  rw [labelEq]
  exact done

#print axioms tail_treeCase_empty

end Verified
