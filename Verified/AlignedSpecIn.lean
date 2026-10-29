import Verified.AlignedReleaseChain
import LeanExe.ProofKit.AlignedFlagRules

/-!
The rest of the flagged specification layer: `CodeSpecInX`, the flagged `CodeSpecIn`, with its
bridges `CodeSpecInX.false_iff`, `CodeSpecInX.spec`, and `CodeSpecX.specIn`, the assembly lemmas
`specOfX` and `specInOfX`, and `seqX_spec`, the flagged `seq_spec`, through which every construct
with two operands runs them in order.  `After.alignedSeq` carries the first operand's alignment
across the second's step, as `After.seq` carries its representation.
-/

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

/-- `CodeSpecIn` under the flag. -/
def CodeSpecInX (strict : Bool) {S : List Sig} {Γ : List Ty} {t : Ty} (buy : Bool) (m : Module)
    (funs : Funs S) (flags : Flags S) (bounds : Bounds S) (fits : Fits S) (host : HostEnv Unit)
    (pv : List Value) (e : Expr S Γ t) (env : Env Γ) (slots : List Slot) (paid : List Bool)
    (live : Nat → Bool) (pool : Bytes.LiteralPool) : Prop :=
  ∀ (h base : Nat) (heap : Heap) (store : Store Unit) (s : Locals), s.positions = h → s.params = pv →
    Holds env slots (fun i => live i || e.uses i) base heap store s → heap.At store →
    (strict = true → HoldsA env slots (fun i => live i || e.uses i) heap store s) →
    pool.Safe env slots (fun i => live i || e.uses i) heap store s →
    store.memoryCap m 0 ≤ 65535 → s.params.length ≤ base → base + e.width ≤ h →
    e.placeArgs = true →
    ∀ (rest : Program) (Q : Assertion Unit),
    TrapOK (trapFlag m e slots heap store
      (dyingPot store s env slots paid (fun i => live i || e.uses i) live +
        e.allocs funs flags bounds (slots.map Slot.mode) paid live env +
        e.buysIn buy funs flags (slots.map Slot.mode) paid live env) (e.fits funs fits env)) Q →
    (∀ heap' store' s' ws,
      After env slots (fun i => live i || e.uses i) live base heap store s t
        (e.mode (slots.map Slot.mode)) (e.denote funs env) heap' store' s' ws →
      (strict = true → HoldsA env slots live heap' store' s' ∧
        Ty.AlignedVal (e.mode (slots.map Slot.mode)) store' t ws (e.denote funs env)) →
      (e.fits funs fits env = true →
        heap'.top.toNat +
            (if e.paidIn buy flags (slots.map Slot.mode) paid live then
              t.pot store' ws (e.denote funs env) else 0) ≤
          heap.top.toNat + dyingPot store s env slots paid (fun i => live i || e.uses i) live +
            e.allocs funs flags bounds (slots.map Slot.mode) paid live env +
            e.buysIn buy funs flags (slots.map Slot.mode) paid live env) →
      wpX strict m rest Q store' { s' with values := ws.reverse ++ s.values } host) →
    wpX strict m (e.code (pool := pool) h slots base live ++ rest) Q store s host

section

variable {S : List Sig} {Γ : List Ty} {t : Ty} {m : Module} {funs : Funs S}
  {flags : Flags S} {bounds : Bounds S} {fits : Fits S} {host : HostEnv Unit} {pv : List Value}
  {e : Expr S Γ t} {env : Env Γ} {slots : List Slot} {paid : List Bool} {live : Nat → Bool}
  {pool : Bytes.LiteralPool}

/-- At `strict = false`, `CodeSpecInX` is `CodeSpecIn`. -/
theorem CodeSpecInX.false_iff {buy : Bool} :
    CodeSpecInX false buy m funs flags bounds fits host pv e env slots paid live pool ↔
      CodeSpecIn buy m funs flags bounds fits host pv e env slots paid live pool := by
  constructor
  · intro hX h base heap store s hh hpv hVars hAt hSafe hCap hBase hRoom hPlace rest Q hTrap hNext
    exact hX h base heap store s hh hpv hVars hAt nofun hSafe hCap hBase hRoom hPlace rest Q hTrap
      fun heap' store' s' ws hA _ hb => hNext heap' store' s' ws hA hb
  · intro hC h base heap store s hh hpv hVars hAt _ hSafe hCap hBase hRoom hPlace rest Q hTrap hNext
    exact hC h base heap store s hh hpv hVars hAt hSafe hCap hBase hRoom hPlace rest Q hTrap
      fun heap' store' s' ws hA hb => hNext heap' store' s' ws hA nofun hb

theorem CodeSpecInX.spec {strict : Bool}
    (h : CodeSpecInX strict false m funs flags bounds fits host pv e env slots paid live pool) :
    CodeSpecX strict m funs flags bounds fits host pv e env slots paid live pool := by
  intro hh base heap store s hs hp hH hA hAl hSafe hCap hBase hRoom hPlace rest Q hTrap hNext
  exact h hh base heap store s hs hp hH hA hAl hSafe hCap hBase hRoom hPlace rest Q
    (by simpa only [Expr.buysIn, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] using hTrap)
    fun heap' store' s' ws a hAl' hle => hNext heap' store' s' ws a hAl' fun hf => by
      simpa only [Expr.paidIn, Expr.buysIn, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] using
        hle hf

theorem CodeSpecX.specIn {strict : Bool} (buy : Bool)
    (hp : e.bodyPaid flags (slots.map Slot.mode) paid live =
      e.paid flags (slots.map Slot.mode) paid live)
    (hb : e.buys funs flags (slots.map Slot.mode) paid live env = 0)
    (h : CodeSpecX strict m funs flags bounds fits host pv e env slots paid live pool) :
    CodeSpecInX strict buy m funs flags bounds fits host pv e env slots paid live pool := by
  intro hh base heap store s hs hpv hH hA hAl hSafe hCap hBase hRoom hPlace rest Q hTrap hNext
  have hZero : e.buysIn buy funs flags (slots.map Slot.mode) paid live env = 0 := by
    cases buy <;> simp only [Expr.buysIn, hb, Bool.false_eq_true, ↓reduceIte]
  exact h hh base heap store s hs hpv hH hA hAl hSafe hCap hBase hRoom hPlace rest Q
    (by simpa only [hZero, Nat.add_zero] using hTrap)
    fun heap' store' s' ws a hAl' hle => hNext heap' store' s' ws a hAl' fun hf => by
      have := hle hf
      cases buy <;>
        simpa only [Expr.paidIn, Expr.buysIn, hp, hb, Bool.false_eq_true, ↓reduceIte,
          Nat.add_zero] using this

end

/-- `specOf` under the flag. -/
theorem specOfX {strict : Bool} {S : List Sig} {m : Module} {funs : Funs S} {flags : Flags S}
    {bounds : Bounds S} {fits : Fits S} {host : HostEnv Unit} {pv : List Value}
    {pool : Bytes.LiteralPool} {Γ : List Ty} {t : Ty} {e : Expr S Γ t}
    (h : ∀ buy env slots paid live, CodeSpecInX strict buy m funs flags bounds fits host pv
      e env slots paid live pool) :
    ∀ env slots paid live, CodeSpecX strict m funs flags bounds fits host pv e env slots
      paid live pool :=
  fun env slots paid live => (h false env slots paid live).spec

/-- `specInOf` under the flag. -/
theorem specInOfX {strict : Bool} {S : List Sig} {m : Module} {funs : Funs S} {flags : Flags S}
    {bounds : Bounds S} {fits : Fits S} {host : HostEnv Unit} {pv : List Value}
    {pool : Bytes.LiteralPool} {Γ : List Ty} {t : Ty} {e : Expr S Γ t}
    (hp : ∀ modes paid live, e.bodyPaid flags modes paid live = e.paid flags modes paid live)
    (hb : ∀ modes paid live env, e.buys funs flags modes paid live env = 0)
    (h : ∀ env slots paid live, CodeSpecX strict m funs flags bounds fits host pv e env slots
      paid live pool) :
    ∀ buy env slots paid live, CodeSpecInX strict buy m funs flags bounds fits host pv e env
      slots paid live pool :=
  fun buy env slots paid live => CodeSpecX.specIn buy (hp _ _ _) (hb _ _ _ _) (h env slots paid live)

/-- The first of two values in a row keeps its alignment across the second's step. -/
theorem After.alignedSeq {Γ : List Ty} {env : Env Γ} {slots : List Slot} {L0 L1 live : Nat → Bool}
    {base : Nat} {heap heap1 heap2 : Heap} {store store1 store2 : Store Unit}
    {s s1 s2 : Locals} {t u : Ty} {m1 m2 : Mode} {v1 : t.denote} {v2 : u.denote}
    {ws1 ws2 vs : List Value}
    (a1 : After env slots L0 L1 base heap store s t m1 v1 heap1 store1 s1 ws1)
    (a2 : After env slots L1 live base heap1 store1 { s1 with values := vs } u m2 v2 heap2
      store2 s2 ws2)
    (h : Ty.AlignedVal m1 store1 t ws1 v1) : Ty.AlignedVal m1 store2 t ws1 v1 := by
  have hKeep1 : ∀ c ∈ t.regions m1 store1 ws1 v1,
      Holds.KeepDying env slots L1 live store1 { s1 with values := vs } c := by
    intro c hc w x hx _ hm wx hwx hlx b hb
    have hb' : b ∈ w.regions (slots.getD x.index default).mode store1 wx (env.get x) := by
      rw [hm]; exact hb
    exact a1.apart w x hx (Or.inr hm) wx hwx hlx c hc b hb'
  exact h.step a2.step a1.rep hKeep1

section Cases

variable {S : List Sig} {m : Module} {funs : Funs S} {flags : Flags S} {bounds : Bounds S}
  {fits : Fits S} {host : HostEnv Unit} {pv : List Value}

/-- `seq_spec` under the flag. -/
theorem seqX_spec {strict : Bool} {Γ : List Ty} {t u : Ty} {l : Expr S Γ t} {r : Expr S Γ u}
    {pool : Bytes.LiteralPool}
    (lSpec : ∀ env slots paid live,
      CodeSpecX strict m funs flags bounds fits host pv l env slots paid live pool)
    (rSpec : ∀ env slots paid live,
      CodeSpecX strict m funs flags bounds fits host pv r env slots paid live pool)
    (env : Env Γ) (slots : List Slot) (paid : List Bool) (live : Nat → Bool) (h base : Nat)
    (heap : Heap) (store : Store Unit) (s : Locals) (hh : s.positions = h) (hpv : s.params = pv)
    (hVars : Holds env slots (fun i => live i || (l.uses i || r.uses i)) base heap store s)
    (hAt : heap.At store)
    (hAl : strict = true → HoldsA env slots (fun i => live i || (l.uses i || r.uses i)) heap store s)
    (hSafe : pool.Safe env slots (fun i => live i || (l.uses i || r.uses i)) heap store s)
    (hCap : store.memoryCap m 0 ≤ 65535) (hBase : s.params.length ≤ base)
    (hRoomL : base + l.width ≤ h) (hRoomR : base + r.width ≤ h)
    (hPlaceL : l.placeArgs = true) (hPlaceR : r.placeArgs = true) (rest : Program)
    (Q : Assertion Unit) {d a : Bool}
    (hTrap : TrapOK (d || (a && !decide (heap.Within store m
      (dyingPot store s env slots paid (fun i => live i || (l.uses i || r.uses i)) live +
        (l.allocs funs flags bounds (slots.map Slot.mode) paid (fun i => live i || r.uses i) env +
          r.allocs funs flags bounds (slots.map Slot.mode) paid live env))))) Q)
    (hdl : (!l.fits funs fits env) = true → d = true)
    (hdr : (!r.fits funs fits env) = true → d = true)
    (hal : (l.aborts || slots.any (·.mode == .owned)) = true → a = true)
    (har : (r.aborts || slots.any (·.mode == .owned)) = true → a = true)
    (hNext : ∀ heap2 store2 s2 ws1 ws2,
      Step heap store (Holds.KeepDying env slots (fun i => live i || (l.uses i || r.uses i)) live
          store s) heap2 store2
        ((l.mode (slots.map Slot.mode)).fresh store2 t ws1 (l.denote funs env) ++
          (r.mode (slots.map Slot.mode)).fresh store2 u ws2 (r.denote funs env)) →
      Frame base s s2 → Holds env slots live base heap2 store2 s2 →
      t.Rep (l.mode (slots.map Slot.mode)) heap2 store2 ws1 (l.denote funs env) →
      u.Rep (r.mode (slots.map Slot.mode)) heap2 store2 ws2 (r.denote funs env) →
      Holds.Apart env slots live store2 s2 t (l.mode (slots.map Slot.mode)) ws1
        (l.denote funs env) →
      Holds.Apart env slots live store2 s2 u (r.mode (slots.map Slot.mode)) ws2
        (r.denote funs env) →
      (∀ x ∈ t.regions (l.mode (slots.map Slot.mode)) store2 ws1 (l.denote funs env),
        ∀ y ∈ (r.mode (slots.map Slot.mode)).fresh store2 u ws2 (r.denote funs env),
          regionsDisjoint x y) →
      (d = false → heap2.top.toNat ≤ heap.top.toNat +
        dyingPot store s env slots paid (fun i => live i || (l.uses i || r.uses i)) live +
        (l.allocs funs flags bounds (slots.map Slot.mode) paid (fun i => live i || r.uses i) env +
          r.allocs funs flags bounds (slots.map Slot.mode) paid live env)) →
      (strict = true → HoldsA env slots live heap2 store2 s2 ∧
        Ty.AlignedVal (l.mode (slots.map Slot.mode)) store2 t ws1 (l.denote funs env) ∧
        Ty.AlignedVal (r.mode (slots.map Slot.mode)) store2 u ws2 (r.denote funs env)) →
      wpX strict m rest Q store2 { s2 with values := ws2.reverse ++ (ws1.reverse ++ s.values) }
        host) :
    wpX strict m (l.code (pool := pool) h slots base (fun i => live i || r.uses i) ++
      (r.code (pool := pool) h slots base live ++ rest))
      Q store s host := by
  have hIn : ∀ i, (live i || r.uses i || l.uses i) = true →
      (live i || (l.uses i || r.uses i)) = true := fun i h => live_seq _ _ _ h
  have hVarsL := hVars.live_mono hIn
  have hdl' : d = false → l.fits funs fits env = true := fun hd => by
    cases hl : l.fits funs fits env
    · rw [hdl (by simp [hl])] at hd; exact nomatch hd
    · rfl
  have hdr' : d = false → r.fits funs fits env = true := fun hd => by
    cases hr : r.fits funs fits env
    · rw [hdr (by simp [hr])] at hd; exact nomatch hd
    · rfl
  have hSplit : dyingPot store s env slots paid (fun i => live i || (l.uses i || r.uses i)) live =
      dyingPot store s env slots paid (fun i => live i || r.uses i || l.uses i)
          (fun i => live i || r.uses i) +
        dyingPot store s env slots paid (fun i => live i || r.uses i) live := by
    rw [dyingPot_split _ (fun i => live i || r.uses i) _ (fun i h => by simp_all)
      (fun i h => by simp [h])]
    congr 1
    exact dyingPot_congr (fun i => by
      cases live i <;> cases l.uses i <;> cases r.uses i <;> rfl) fun _ => rfl
  refine lSpec env slots paid _ h base heap store s hh hpv hVarsL hAt
    (fun hs => (hAl hs).live_mono hIn) (hSafe.mono hIn)
    hCap hBase hRoomL hPlaceL _ _
      (hTrap.part hdl hal fun _ hw => hw.mono (by rw [hSplit]; omega))
    fun heap1 store1 s1 ws1 a1 hA1 hTop1 => ?_
  have hDr : dyingPot store1 { s1 with values := ws1.reverse ++ s.values } env slots paid
      (fun i => live i || r.uses i) live =
        dyingPot store s env slots paid (fun i => live i || r.uses i) live := by
    rw [dyingPot_values]
    exact dyingPot_after hVarsL a1 (fun i h => by simp [h]) _ _ fun _ h => h
  refine rSpec env slots paid live h base heap1 store1 { s1 with values := ws1.reverse ++ s.values }
    (a1.frame.positions.trans hh) (a1.frame.params.trans hpv) (a1.holds.agree Frame.ofValues)
    a1.step.at_ (fun hs => (hA1 hs).1.values _)
    (((hSafe.mono hIn).after hVarsL a1 (fun i hi => by simp [hi])).1.values _)
    (by rw [a1.step.cap m]; exact hCap)
    (by show s1.params.length ≤ base; rw [a1.frame.params]; exact hBase) hRoomR hPlaceR _ _
    (hTrap.part hdr har fun hd hw => by
      have := hTop1 (hdl' hd)
      rw [hDr]
      exact hw.shift
          (c1 := dyingPot store s env slots paid (fun i => live i || r.uses i || l.uses i)
          (fun i => live i || r.uses i) +
          l.allocs funs flags bounds (slots.map Slot.mode) paid (fun i => live i || r.uses i) env)
        (by omega) (by rw [hSplit]; omega) (a1.step.cap m))
    fun heap2 store2 s2 ws2 a2 hA2 hTop2 => ?_
  obtain ⟨hStep, hFrame, hRep1, hApart1, hDisjoint⟩ :=
    After.seq hVarsL a1 a2 (fun i h => by simp [h]) fun i h => by simp [h]
  exact hNext heap2 store2 s2 ws1 ws2
    (hStep.mono (fun _ hr => hr.mono fun i h1 h2 => ⟨hIn i h1, h2⟩) fun _ hb => hb) hFrame
    a2.holds hRep1 a2.rep hApart1 a2.apart hDisjoint (fun hd => by
      have := hTop1 (hdl' hd); have := hTop2 (hdr' hd); rw [hDr] at this; rw [hSplit]; omega)
    fun hs => ⟨(hA2 hs).1, After.alignedSeq a1 a2 (hA1 hs).2, (hA2 hs).2⟩

end Cases

end Verified
