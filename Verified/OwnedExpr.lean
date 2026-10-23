import Verified.ExprSpec

namespace Verified

variable {pool : Bytes.LiteralPool}

open Wasm LeanExe.Pipeline LeanExe.Runtime

theorem _root_.Wasm.TrapOK.allocPart {d d' : Bool} {P P' : Prop}
    [Decidable P] [Decidable P'] {Q : Assertion Unit}
    (h : TrapOK (d || !decide P) Q) (hd : d' = true → d = true)
    (hP : d = false → P → P') : TrapOK (d' || !decide P') Q := by
  have h' : TrapOK (d || (true && !decide P)) Q := by simpa only [Bool.true_and] using h
  exact h'.part (a' := true) hd (fun _ => rfl) hP

theorem CodeSpec.coerced {S : List Sig} {Γ : List Ty} {t : Ty} {m : Module}
    {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S}
    {host : HostEnv Unit} {pv : List Value} {e : Expr S Γ t} {env : Env Γ}
    {target : Mode} {slots : List Slot} {paid : List Bool} {live : Nat → Bool}
    (hm : Runtime m) (spec : CodeSpec (pool := pool) m funs flags bounds fits host pv e env slots paid live)
    (hTarget : e.mode (slots.map Slot.mode) = .owned → target = .owned)
    {h base : Nat} {heap : Heap} {store : Store Unit} {s : Locals}
    (hh : s.positions = h) (hpv : s.params = pv)
    (hVars : Holds env slots (fun i => live i || e.uses i) base heap store s)
    (hAt : heap.At store)
    (hSafe : pool.Safe env slots (fun i => live i || e.uses i) heap store s)
    (hCap : store.memoryCap m 0 ≤ 65535)
    (hBase : s.params.length ≤ base) (hRoom : base + max e.width (copyWidth t) ≤ h)
    (hPlace : e.placeArgs = true) {rest : Program} {Q : Assertion Unit}
    (hTrap : TrapOK (!(e.fits funs fits env) || !decide (heap.Within store m
      (dyingPot store s env slots paid (fun i => live i || e.uses i) live +
        e.allocs funs flags bounds (slots.map Slot.mode) paid live env +
        coerceCost t (e.mode (slots.map Slot.mode)) target (e.denote funs env)))) Q)
    (hNext : ∀ heap' store' s' ws,
      After env slots (fun i => live i || e.uses i) live base heap store s t target
        (e.denote funs env) heap' store' s' ws →
      (e.fits funs fits env = true → heap'.top.toNat ≤ heap.top.toNat +
        dyingPot store s env slots paid (fun i => live i || e.uses i) live +
        e.allocs funs flags bounds (slots.map Slot.mode) paid live env +
        coerceCost t (e.mode (slots.map Slot.mode)) target (e.denote funs env)) →
      wp m rest Q store' { s' with values := ws.reverse ++ s.values } host) :
    wp m (e.code (pool := pool) h slots base live ++
      (coerceCode h t (e.mode (slots.map Slot.mode)) target base ++ rest)) Q store s host := by
  have hBudget : TrapOK (!(e.fits funs fits env) || (true && !decide (heap.Within store m
      (dyingPot store s env slots paid (fun i => live i || e.uses i) live +
        e.allocs funs flags bounds (slots.map Slot.mode) paid live env +
        coerceCost t (e.mode (slots.map Slot.mode)) target (e.denote funs env))))) Q := by
    simpa only [Bool.true_and] using hTrap
  refine spec h base heap store s hh hpv hVars hAt hSafe hCap hBase
    (by have := Nat.le_max_left e.width (copyWidth t); omega) hPlace _ _
    (hBudget.part id (fun _ => rfl) (fun _ hw => hw.mono (by omega)))
    fun heap1 store1 s1 ws a1 hTop1 => ?_
  have hTop (hf : e.fits funs fits env = true) :
      heap1.top.toNat ≤ heap.top.toNat +
        dyingPot store s env slots paid (fun i => live i || e.uses i) live +
        e.allocs funs flags bounds (slots.map Slot.mode) paid live env := by
    have := hTop1 hf
    omega
  refine a1.coerce hm hTarget (le_refl _) (by rw [a1.frame.params]; exact hBase)
    (a1.frame.positions.trans hh)
    (by have := Nat.le_max_right e.width (copyWidth t); omega)
    (by rw [a1.step.cap m]; exact hCap) ?_ fun heap2 store2 s2 ws2 a2 hTop2 _ => ?_
  · intro hs ht hScalar
    apply hBudget.part (d' := false) (a' := true) (P' := heap1.Within store1 m (t.copyCost
      (e.denote funs env))) nofun (fun _ => rfl)
    intro hd hw
    have hf : e.fits funs fits env = true := by simpa using hd
    have hc : coerceCost t (e.mode (slots.map Slot.mode)) target (e.denote funs env) =
        t.copyCost (e.denote funs env) := by simp [coerceCost, hs, ht]
    exact hw.shift (by simpa only [Nat.add_assoc] using hTop hf)
      (by rw [hc]) (a1.step.cap m)
  · exact hNext heap2 store2 s2 ws2 a2 fun hf => by have := hTop hf; omega

theorem CodeSpec.owned {S : List Sig} {Γ : List Ty} {t : Ty} {m : Module}
    {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S}
    {host : HostEnv Unit} {pv : List Value} {e : Expr S Γ t} {env : Env Γ}
    {slots : List Slot} {paid : List Bool} {live : Nat → Bool}
    (hm : Runtime m) (spec : CodeSpec (pool := pool) m funs flags bounds fits host pv e env slots paid live)
    {h base : Nat} {heap : Heap} {store : Store Unit} {s : Locals}
    (hh : s.positions = h) (hpv : s.params = pv)
    (hVars : Holds env slots (fun i => live i || e.uses i) base heap store s)
    (hAt : heap.At store)
    (hSafe : pool.Safe env slots (fun i => live i || e.uses i) heap store s)
    (hCap : store.memoryCap m 0 ≤ 65535)
    (hBase : s.params.length ≤ base) (hRoom : base + max e.width (copyWidth t) ≤ h)
    (hPlace : e.placeArgs = true) {rest : Program} {Q : Assertion Unit}
    (hTrap : TrapOK (!(e.fits funs fits env) || !decide (heap.Within store m
      (dyingPot store s env slots paid (fun i => live i || e.uses i) live +
        e.allocs funs flags bounds (slots.map Slot.mode) paid live env +
        coerceCost t (e.mode (slots.map Slot.mode)) .owned (e.denote funs env)))) Q)
    (hNext : ∀ heap' store' s' ws,
      After env slots (fun i => live i || e.uses i) live base heap store s t .owned
        (e.denote funs env) heap' store' s' ws →
      (e.fits funs fits env = true → heap'.top.toNat ≤ heap.top.toNat +
        dyingPot store s env slots paid (fun i => live i || e.uses i) live +
        e.allocs funs flags bounds (slots.map Slot.mode) paid live env +
        coerceCost t (e.mode (slots.map Slot.mode)) .owned (e.denote funs env)) →
      wp m rest Q store' { s' with values := ws.reverse ++ s.values } host) :
    wp m (e.code (pool := pool) h slots base live ++
      (coerceCode h t (e.mode (slots.map Slot.mode)) .owned base ++ rest)) Q store s host :=
  CodeSpec.coerced (target := .owned) hm spec (fun _ => rfl) hh hpv hVars hAt hSafe hCap
    hBase hRoom hPlace hTrap hNext

end Verified
