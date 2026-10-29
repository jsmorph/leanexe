import Verified.TailBind

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime

def TailAfter.bind2 {Γ params : List Ty} {result valueTy firstTy secondTy : Ty}
    {env : Env Γ} {slots : List Slot} {L0 L1 LB : Nat → Bool}
    {base stateBase resultBase : Nat} {modes : List Mode}
    {heap heap1 heap2 : Heap} {store store1 store2 : Store Unit} {s s1 s2 s3 : Locals}
    {mode : Mode} {value : valueTy.denote} {first : firstTy.denote} {second : secondTy.denote}
    {sl0 sl1 : Slot} {words : List Value} {out : Sum (Env params) result.denote}
    (h0 : Holds env slots L0 base heap store s)
    (a1 : After env slots L0 L1 base heap store s valueTy mode value heap1 store1 s1 words)
    (frame : Frame base s1 s2)
    (aB : TailAfter (Env.cons first (Env.cons second env)) (sl0 :: sl1 :: slots) LB modes
      stateBase resultBase heap1 store1 s2 out heap2 store2 s3)
    (hNew : ∀ r, (∀ b ∈ mode.fresh store1 valueTy words value, regionsDisjoint r b) →
      (sl0.mode = .owned → ∀ w, LocalsHold s2 sl0.loc firstTy.types w → w.length = firstTy.width →
        ∀ b ∈ firstTy.blocks store1 w first, regionsDisjoint r b) ∧
      (sl1.mode = .owned → ∀ w, LocalsHold s2 sl1.loc secondTy.types w → w.length = secondTy.width →
        ∀ b ∈ secondTy.blocks store1 w second, regionsDisjoint r b))
    (hLB : ∀ i, LB (i + 2) = true → L1 i = true)
    (hL1 : ∀ i, L1 i = true → L0 i = true) (hBase : stateBase ≤ base) :
    TailAfter env slots L0 modes stateBase resultBase heap store s out heap2 store2 s3 := by
  refine ⟨aB.words, a1.step.trans aB.step fun r hr =>
    ⟨hr.mono fun _ hi _ => ⟨hi, rfl⟩, fun hFresh => ?_⟩,
    (a1.frame.mono hBase).trans ((frame.mono hBase).trans aB.frame), aB.rep⟩
  have hr1 : Holds.KeepDying env slots L1 (fun _ => false) store1 s1 r :=
    Holds.KeepDying.transfer h0 a1.step a1.frame hL1 (fun _ hi _ => hi)
      (hr.mono fun i hi _ => ⟨hL1 i hi, rfl⟩)
  obtain ⟨hNew0, hNew1⟩ := hNew r hFresh
  intro t x hx _ hxMode wx hxHold hxLength b hb
  cases x with
  | here => exact hNew0 hxMode wx hxHold hxLength b hb
  | there x =>
    cases x with
    | here => exact hNew1 hxMode wx hxHold hxLength b hb
    | there x =>
      change (slots.getD x.index default).mode = .owned at hxMode
      change LocalsHold s2 (slots.getD x.index default).loc t.types wx at hxHold
      have hx1 : L1 x.index = true := hLB _ hx
      exact hr1 t x hx1 rfl hxMode wx ((a1.holds.hold_agree frame hx1 hxLength).mp hxHold)
        hxLength b hb

#print axioms TailAfter.bind2
end Verified
