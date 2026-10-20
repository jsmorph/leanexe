import Verified.CoercedRelease

namespace Verified

open Wasm LeanExe.Pipeline

theorem CodeSpec.released {S : List Sig} {Γ : List Ty} {t : Ty} {m : Module}
    {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S}
    {host : HostEnv Unit} {pv : List Value} {e : Expr S Γ t} {env : Env Γ}
    {slots : List Slot} {paid : List Bool} {L0 live : Nat → Bool}
    (hm : Runtime m) (spec : CodeSpec m funs flags bounds fits host pv e env slots paid live)
    {h base : Nat} {heap : Heap} {store : Store Unit} {s : Locals}
    (hh : s.positions = h) (hpv : s.params = pv) (hVars : Holds env slots L0 base heap store s)
    (hAt : heap.At store) (hCap : store.memoryCap m 0 ≤ 65535)
    (hBase : s.params.length ≤ base) (hRoom : base + e.width ≤ h)
    (hPlace : e.placeArgs = true)
    (hEntry : ∀ i, (live i || e.uses i) = true → L0 i = true)
    {rest : Program} {Q : Assertion Unit}
    (hTrap : TrapOK (!(e.fits funs fits env) || !decide (heap.Within store m
      (dyingPot store s env slots paid L0 live +
        e.allocs funs flags bounds (slots.map Slot.mode) paid live env))) Q)
    (hNext : ∀ heap' store' s' ws,
      After env slots L0 live base heap store s t (e.mode (slots.map Slot.mode))
        (e.denote funs env) heap' store' s' ws →
      (e.fits funs fits env = true → heap'.top.toNat ≤ heap.top.toNat +
        dyingPot store s env slots paid L0 live +
        e.allocs funs flags bounds (slots.map Slot.mode) paid live env) →
      wp m rest Q store' { s' with values := ws.reverse ++ s.values } host) :
    wp m (releaseWhere Γ slots (fun i => L0 i && !(live i || e.uses i)) ++
      (e.code h slots base live ++ rest)) Q store s host := by
  refine wp_releaseWhere hm hVars hAt (fun i hi => by
      simp only [Bool.and_eq_true] at hi; exact hi.1)
    (fun heap1 store1 released hTop1 => ?_)
  have hLiveEq : (fun i => L0 i && !(L0 i && !(live i || e.uses i))) =
      (fun i => live i || e.uses i) := by
    funext i
    have hi := hEntry i
    cases h0 : L0 i <;> cases hl : live i <;> cases he : e.uses i <;> simp_all
  rw [hLiveEq] at released
  have hPot := dyingPot_evolves (paid := paid) hVars released hEntry
    (fun i => live i || e.uses i) live (fun _ hi => hi)
  have hPotLe : dyingPot store s env slots paid (fun i => live i || e.uses i) live ≤
      dyingPot store s env slots paid L0 live := dyingPot_mono hEntry (fun _ hi => hi)
  have hBudget : TrapOK (!(e.fits funs fits env) ||
      (true && !decide (heap.Within store m (dyingPot store s env slots paid L0 live +
        e.allocs funs flags bounds (slots.map Slot.mode) paid live env)))) Q := by
    simpa only [Bool.true_and] using hTrap
  refine spec h base heap1 store1 s hh hpv released.holds released.step.at_
    (by rw [released.step.cap m]; exact hCap) hBase hRoom hPlace _ _
    (hBudget.part id (fun _ => rfl) (fun _ hw => hw.shift
      (heap1 := heap1) (store1 := store1) (c1 := 0)
      (by have ht := congrArg UInt64.toNat hTop1; omega)
      (by rw [hPot]; omega) (released.step.cap m)))
    (fun heap2 store2 s2 ws a hTop2 => ?_)
  refine hNext heap2 store2 s2 ws
    (After.prepend hVars released a hEntry (fun i hi => by simp [hi])) (fun hf => ?_)
  have h2 := hTop2 hf
  have h1 := congrArg UInt64.toNat hTop1
  rw [hPot] at h2
  omega

end Verified
