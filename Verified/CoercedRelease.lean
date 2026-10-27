import Verified.OwnedExpr

namespace Verified

variable {pool : Bytes.LiteralPool}

open Wasm LeanExe.Pipeline

theorem CodeSpec.releaseCoerced {S : List Sig} {Γ : List Ty} {t : Ty} {m : Module}
    {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S}
    {host : HostEnv Unit} {pv : List Value} {e : Expr S Γ t} {env : Env Γ}
    {slots : List Slot} {paid : List Bool} {L0 live : Nat → Bool} {target : Mode}
    (hm : Runtime m) (spec : CodeSpec (pool := pool) m funs flags bounds fits host pv e env slots paid live)
    (hTarget : e.mode (slots.map Slot.mode) = .owned → target = .owned)
    {h base : Nat} {heap : Heap} {store : Store Unit} {s : Locals}
    (hh : s.positions = h) (hpv : s.params = pv) (hVars : Holds env slots L0 base heap store s)
    (hAt : heap.At store) (hSafe : pool.Safe env slots L0 heap store s)
    (hCap : store.memoryCap m 0 ≤ 65535)
    (hBase : s.params.length ≤ base) (hRoom : base + max e.width (copyWidth t) ≤ h)
    (hPlace : e.placeArgs = true)
    (hEntry : ∀ i, (live i || e.uses i) = true → L0 i = true)
    {rest : Program} {Q : Assertion Unit}
    (hTrap : TrapOK (!(e.fits funs fits env) || !decide (heap.Within store m
      (dyingPot store s env slots paid L0 live +
        e.allocs funs flags bounds (slots.map Slot.mode) paid live env +
        coerceCost t (e.mode (slots.map Slot.mode)) target (e.denote funs env)))) Q)
    (hNext : ∀ heap' store' s' ws,
      After env slots L0 live base heap store s t target (e.denote funs env)
        heap' store' s' ws →
      (e.fits funs fits env = true → heap'.top.toNat ≤ heap.top.toNat +
        dyingPot store s env slots paid L0 live +
        e.allocs funs flags bounds (slots.map Slot.mode) paid live env +
        coerceCost t (e.mode (slots.map Slot.mode)) target (e.denote funs env)) →
      wp m rest Q store' { s' with values := ws.reverse ++ s.values } host) :
    wp m (releaseWhere Γ slots (fun i => L0 i && !(live i || e.uses i)) ++
      (e.code (pool := pool) h slots base live ++
        (coerceCode h t (e.mode (slots.map Slot.mode)) target base ++ rest))) Q store s host := by
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
  refine spec.coerced hm hTarget hh hpv released.holds released.step.at_
    (hSafe.evolves hVars released hEntry)
    (by rw [released.step.cap m]; exact hCap) hBase hRoom hPlace
    (hTrap.allocPart id (fun _ hw => hw.shift (heap1 := heap1) (store1 := store1) (c1 := 0)
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
