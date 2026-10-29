import Verified.AlignedControl

/-!
The loops under the flag.  A loop's state is held in the loop's mode and passed to the condition
as a borrowed variable, so `Ty.AlignedVal.toBorrowed` gives a borrowed value's alignment from an
owned one's: every region that a borrowed value protects starts at a block's start plus 48 or is
a block (`nodeOwned_slotRegions_aligned`).  `After.releaseX` is `After.release` under the flag,
and `CodeSpecWithX` is `CodeSpecWith`, the specification with a given bound, under the flag.  The
invariant of each WebAssembly `loop` adds `HoldsA` of the outer variables live in the loop and the
alignment of the state.
-/

namespace Verified

variable {pool : Bytes.LiteralPool}

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

section

variable {heap : Heap} {store : Store Unit}

mutual

/-- Every region that a record protects as a borrowed value starts at a multiple of 8 when every
block of the owned record does. -/
theorem nodeOwned_slotRegions_aligned : {p : UInt64} → {n : Node} →
    NodeOwned heap store p n → (∀ b ∈ Node.blocks store p n, b.1 % 8 = 0) →
    ∀ r ∈ Node.slotRegions store p n, r.1 % 8 = 0
  | _, .null, _, _, r, hr => by simp [Node.slotRegions] at hr
  | p, .record slots, ⟨hH, hS⟩, hb, r, hr => by
    simp only [Node.slotRegions, List.mem_cons] at hr
    rcases hr with rfl | hr
    · have h0 := hb (block store p) (by simp [Node.blocks])
      have := hH.base
      simp only [block] at h0
      dsimp only
      omega
    · exact slotsOwned_slotRegions_aligned hS
        (fun b h => hb b (by simp only [Node.blocks, List.mem_cons]; exact Or.inr h)) r hr

theorem slotsOwned_slotRegions_aligned {p : UInt64} : {i : Nat} → {slots : List LeanExe.Pipeline.Slot} →
    SlotsOwned heap store p i slots → (∀ b ∈ slotsBlocks store p i slots, b.1 % 8 = 0) →
    ∀ r ∈ slotsRegions store p i slots, r.1 % 8 = 0
  | _, [], _, _, r, hr => by simp [slotsRegions] at hr
  | _, .word _ :: _, ⟨_, hS⟩, hb, r, hr =>
    slotsOwned_slotRegions_aligned hS (by simpa only [slotsBlocks] using hb) r
      (by simpa only [slotsRegions] using hr)
  | _, .child _ :: _, ⟨hN, hS⟩, hb, r, hr => by
    simp only [slotsRegions, List.mem_append] at hr
    rcases hr with hr | hr
    · exact nodeOwned_slotRegions_aligned hN
        (fun b h => hb b (by simp only [slotsBlocks, List.mem_append]; exact Or.inl h)) r hr
    · exact slotsOwned_slotRegions_aligned hS
        (fun b h => hb b (by simp only [slotsBlocks, List.mem_append]; exact Or.inr h)) r hr
  | i, .array _ :: _, ⟨hA, hS⟩, hb, r, hr => by
    simp only [slotsRegions, List.mem_cons] at hr
    rcases hr with rfl | hr
    · have h0 := hb (block store (store.mem.read64 (slotAddress p i))) (by simp [slotsBlocks])
      have := hA.base
      simp only [block] at h0
      dsimp only
      omega
    · exact slotsOwned_slotRegions_aligned hS
        (fun b h => hb b (by simp only [slotsBlocks, List.mem_cons]; exact Or.inr h)) r hr
  | _, .bytes _ :: _, ⟨_, hS⟩, hb, r, hr => by
    simp only [slotsRegions, List.mem_append] at hr
    rcases hr with hr | hr
    · exact hb r (by simp only [slotsBlocks, List.mem_append]; exact Or.inl hr)
    · exact slotsOwned_slotRegions_aligned hS
        (fun b h => hb b (by simp only [slotsBlocks, List.mem_append]; exact Or.inr h)) r hr

end

/-- An owned value read as a borrowed one is aligned when the owned value is. -/
theorem Ty.AlignedVal.borrowOf : {t : Ty} → {ws : List Value} → {v : t.denote} →
    t.Rep .owned heap store ws v → Ty.AlignedVal .owned store t ws v →
    Ty.AlignedVal .borrowed store t ws v
  | .elem _, _, _, _, _ => fun r hr => by simp [Ty.regions, Ty.reads] at hr
  | .bytes, _, _, _, h => fun r hr => ⟨(h r hr).1, nofun⟩
  | .pair a b, _, _, ⟨first, second, hws, h1, h2, _⟩, h => by
    subst hws
    have hl := h1.length
    exact Ty.AlignedVal.pair hl (Ty.AlignedVal.borrowOf h1 (h.fst hl))
      (Ty.AlignedVal.borrowOf h2 (h.snd hl))
  | .array _, _, _, ⟨ptr, hws, ha⟩, h => by
    subst hws
    have hp := Ty.AlignedVal.array (mode := .owned) ha h
    intro r hr
    simp only [Ty.regions, Ty.reads, List.mem_singleton] at hr
    subst hr
    exact ⟨hp, nofun⟩
  | .tree _, _, _, ⟨ptr, hws, ha⟩, h => by
    subst hws
    intro r hr
    exact ⟨nodeOwned_slotRegions_aligned ha.1 (fun b hb => (h b hb).1) r hr, nofun⟩
  | .treeHeader _ _, _, _, _, _ => fun r hr => by simp [Ty.regions, Ty.reads] at hr

/-- A value of either mode read as a borrowed one is aligned when it is. -/
theorem Ty.AlignedVal.toBorrowed {mode : Mode} {t : Ty} {ws : List Value} {v : t.denote}
    (hRep : t.Rep mode heap store ws v) (h : Ty.AlignedVal mode store t ws v) :
    Ty.AlignedVal .borrowed store t ws v := by
  cases mode
  · exact h
  · exact Ty.AlignedVal.borrowOf hRep h

/-- The invariant does not depend on the operand stack. -/
theorem HoldsA.ofValues {Γ : List Ty} {env : Env Γ} {slots : List Slot} {live : Nat → Bool}
    {s : Locals} {vs : List Value} (h : HoldsA env slots live heap store { s with values := vs }) :
    HoldsA env slots live heap store s := h

end

section

variable {m : Module} {host : HostEnv Unit}

/-- `After.release` under the flag. -/
theorem After.releaseX {strict : Bool} (hm : Runtime m) (hRA : strict = true → ReleaseAligned m)
    {Γ : List Ty} {env : Env Γ} {slots : List Slot}
    {L0 L1 live sel : Nat → Bool} {base : Nat} {heap heap1 : Heap} {store store1 : Store Unit}
    {s s1 : Locals} {t : Ty} {mode : Mode} {v : t.denote} {ws vals : List Value}
    {rest : Program} {Q : Assertion Unit}
    (h0 : Holds env slots L0 base heap store s)
    (a : After env slots L0 L1 base heap store s t mode v heap1 store1 s1 ws)
    (hA : strict = true → HoldsA env slots L1 heap1 store1 s1 ∧ Ty.AlignedVal mode store1 t ws v)
    (hL1 : ∀ i, L1 i = true → L0 i = true) (hSel : ∀ i, sel i = true → L1 i = true)
    (hLive : ∀ i, live i = true → (L1 i && !sel i) = true)
    (hNext : ∀ heap2 store2,
      After env slots L0 live base heap store s t mode v heap2 store2 s1 ws →
      heap2.top = heap1.top → t.regions mode store2 ws v = t.regions mode store1 ws v →
      (strict = true → HoldsA env slots live heap2 store2 s1 ∧
        Ty.AlignedVal mode store2 t ws v) →
      wpX strict m rest Q store2 { s1 with values := vals } host) :
    wpX strict m (releaseWhere Γ slots sel ++ rest) Q store1 { s1 with values := vals } host := by
  refine wpX_releaseWhere hm hRA (a.holds.agree Frame.ofValues) a.step.at_
    (fun hs => (hA hs).1.values _) hSel fun heap2 store2 e hTop hA2 => ?_
  have e' := e.mono hLive
  have hLiveL1 : ∀ i, live i = true → L1 i = true := fun i h => by
    have := hLive i h
    simp only [Bool.and_eq_true] at this
    exact this.1
  have hKeepV : ∀ r ∈ t.regions mode store1 ws v,
      Holds.KeepDying env slots L1 live store1 { s1 with values := vals } r := by
    intro r hr u x hx _ hmx wx hwx hlx b hb
    have hb' : b ∈ u.regions (slots.getD x.index default).mode store1 wx (env.get x) := by
      rw [hmx]; exact hb
    exact a.apart u x hx (Or.inr hmx) wx hwx hlx r hr b hb'
  obtain ⟨hRep, hSame, -⟩ := a.rep.step e'.step hKeepV
  have hStep := a.step.transBoth (keep := Holds.KeepDying env slots L0 live store s) e'.step
    fun r hr =>
    ⟨hr.mono fun i h1 h2 => ⟨h1, by
        cases hl : live i with
        | false => rfl
        | true => rw [hLiveL1 i hl] at h2; exact nomatch h2⟩,
      fun _ => Holds.KeepDying.transfer h0 a.step a.frame hL1
        (fun i h1 _ => h1) (hr.mono fun i h1 h2 => ⟨hL1 _ h1, h2⟩)⟩
  refine hNext heap2 store2 ⟨hStep.mono (fun _ h => h) fun b hb => ?_, a.frame,
    e'.holds.agree Frame.ofValues, hRep, ?_⟩ hTop hSame
    (fun hs => ⟨((hA2 hs).live_mono hLive).ofValues, fun r hr => (hA hs).2 r (hSame ▸ hr)⟩)
  · rw [Mode.fresh_congr hSame] at hb
    exact List.mem_append_left _ hb
  · exact Holds.Apart.transfer (a.holds.live_mono hLiveL1) (a.apart.live_mono hLiveL1) e'.step
      Frame.ofValues (fun u y hy wy hwy hly => a.holds.keepDying hLiveL1 hy hwy hly) hSame

/-- The release of the owned variables that `sel` selects after an expression's code, those live
in `L1` and not in `live`, gives the facts of the code and the release for `live`.  The value lies
apart from the released blocks, so its words still represent it, and `top` is unchanged. -/
theorem After.release (hm : Runtime m) {Γ : List Ty} {env : Env Γ} {slots : List Slot}
    {L0 L1 live sel : Nat → Bool} {base : Nat} {heap heap1 : Heap} {store store1 : Store Unit}
    {s s1 : Locals} {t : Ty} {mode : Mode} {v : t.denote} {ws vals : List Value}
    {rest : Program} {Q : Assertion Unit}
    (h0 : Holds env slots L0 base heap store s)
    (a : After env slots L0 L1 base heap store s t mode v heap1 store1 s1 ws)
    (hL1 : ∀ i, L1 i = true → L0 i = true) (hSel : ∀ i, sel i = true → L1 i = true)
    (hLive : ∀ i, live i = true → (L1 i && !sel i) = true)
    (hNext : ∀ heap2 store2,
      After env slots L0 live base heap store s t mode v heap2 store2 s1 ws →
      heap2.top = heap1.top → t.regions mode store2 ws v = t.regions mode store1 ws v →
      wp m rest Q store2 { s1 with values := vals } host) :
    wp m (releaseWhere Γ slots sel ++ rest) Q store1 { s1 with values := vals } host :=
  After.releaseX (strict := false) hm nofun h0 a nofun hL1 hSel hLive
    (fun heap2 store2 a1 a2 a3 _ => hNext heap2 store2 a1 a2 a3)

end

/-- `CodeSpecWith` under the flag. -/
def CodeSpecWithX (strict : Bool) {S : List Sig} {Γ : List Ty} {t : Ty} (pays : Bool)
    (bound : Nat) (m : Module) (funs : Funs S) (flags : Flags S) (bounds : Bounds S)
    (fits : Fits S) (host : HostEnv Unit) (pv : List Value) (e : Expr S Γ t) (env : Env Γ)
    (slots : List Slot) (paid : List Bool) (live : Nat → Bool) (pool : Bytes.LiteralPool) : Prop :=
  ∀ (h base : Nat) (heap : Heap) (store : Store Unit) (s : Locals), s.positions = h → s.params = pv →
    Holds env slots (fun i => live i || e.uses i) base heap store s → heap.At store →
    (strict = true → HoldsA env slots (fun i => live i || e.uses i) heap store s) →
    pool.Safe env slots (fun i => live i || e.uses i) heap store s →
    store.memoryCap m 0 ≤ 65535 → s.params.length ≤ base → base + e.width ≤ h →
    e.placeArgs = true →
    ∀ (rest : Program) (Q : Assertion Unit),
    TrapOK (trapFlag m e slots heap store
      (dyingPot store s env slots paid (fun i => live i || e.uses i) live + bound)
      (e.fits funs fits env)) Q →
    (∀ heap' store' s' ws,
      After env slots (fun i => live i || e.uses i) live base heap store s t
        (e.mode (slots.map Slot.mode)) (e.denote funs env) heap' store' s' ws →
      (strict = true → HoldsA env slots live heap' store' s' ∧
        Ty.AlignedVal (e.mode (slots.map Slot.mode)) store' t ws (e.denote funs env)) →
      (e.fits funs fits env = true →
        heap'.top.toNat + (if pays then t.pot store' ws (e.denote funs env) else 0) ≤
          heap.top.toNat + dyingPot store s env slots paid (fun i => live i || e.uses i) live +
            bound) →
      wpX strict m rest Q store' { s' with values := ws.reverse ++ s.values } host) →
    wpX strict m (e.code (pool := pool) h slots base live ++ rest) Q store s host

/-- At `strict = false`, `CodeSpecWithX` is `CodeSpecWith`. -/
theorem CodeSpecWithX.false_iff {S : List Sig} {Γ : List Ty} {t : Ty} {pays : Bool}
    {bound : Nat} {m : Module} {funs : Funs S} {flags : Flags S} {bounds : Bounds S}
    {fits : Fits S} {host : HostEnv Unit} {pv : List Value} {e : Expr S Γ t} {env : Env Γ}
    {slots : List Slot} {paid : List Bool} {live : Nat → Bool} {pool : Bytes.LiteralPool} :
    CodeSpecWithX false pays bound m funs flags bounds fits host pv e env slots paid live pool ↔
      CodeSpecWith pays bound m funs flags bounds fits host pv e env slots paid live pool := by
  constructor
  · intro hX h base heap store s hh hpv hVars hAt hSafe hCap hBase hRoom hPlace rest Q hTrap hNext
    exact hX h base heap store s hh hpv hVars hAt nofun hSafe hCap hBase hRoom hPlace rest Q hTrap
      fun heap' store' s' ws hA _ hb => hNext heap' store' s' ws hA hb
  · intro hC h base heap store s hh hpv hVars hAt _ hSafe hCap hBase hRoom hPlace rest Q hTrap hNext
    exact hC h base heap store s hh hpv hVars hAt hSafe hCap hBase hRoom hPlace rest Q hTrap
      fun heap' store' s' ws hA hb => hNext heap' store' s' ws hA nofun hb


theorem CodeSpecX.of_with {strict : Bool} {S : List Sig} {Γ : List Ty} {t : Ty} {m : Module}
    {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S} {host : HostEnv Unit}
    {pv : List Value} {e : Expr S Γ t} {env : Env Γ} {slots : List Slot} {paid : List Bool}
    {live : Nat → Bool} {pool : Bytes.LiteralPool} {bound : Nat}
    (hb : e.allocs funs flags bounds (slots.map Slot.mode) paid live env = bound)
    (h : CodeSpecWithX strict (e.paid flags (slots.map Slot.mode) paid live) bound m funs flags
      bounds fits host pv e env slots paid live pool) :
    CodeSpecX strict m funs flags bounds fits host pv e env slots paid live pool := by
  unfold CodeSpecX
  rw [hb]
  exact h

theorem CodeSpec.of_with {S : List Sig} {Γ : List Ty} {t : Ty} {m : Module} {funs : Funs S}
    {flags : Flags S} {bounds : Bounds S} {fits : Fits S} {host : HostEnv Unit} {pv : List Value}
    {e : Expr S Γ t} {env : Env Γ} {slots : List Slot} {paid : List Bool} {live : Nat → Bool}
    {pool : Bytes.LiteralPool} {bound : Nat}
    (hb : e.allocs funs flags bounds (slots.map Slot.mode) paid live env = bound)
    (h : CodeSpecWith (e.paid flags (slots.map Slot.mode) paid live) bound m funs flags bounds fits
      host pv e env slots paid live pool) :
    CodeSpec m funs flags bounds fits host pv e env slots paid live pool :=
  CodeSpecX.false_iff.mp (CodeSpecX.of_with (strict := false) hb (CodeSpecWithX.false_iff.mpr h))

section Cases

variable {S : List Sig} {m : Module} {funs : Funs S} {flags : Flags S} {bounds : Bounds S}
  {fits : Fits S} {host : HostEnv Unit} {pv : List Value} {strict : Bool}

/-- `LeanExe.loop` with a condition: the count in local `base`, the initial state, coerced to the
loop's mode, from local `base + 2` on, and the index in local `base + 1`.  The invariant at the top
of the WebAssembly `loop` holds the count, the index `i`, and the state after `i` passes, with the
facts of `After` for the outer variables live in the loop, those live after it or used by the
condition or the body.  Each pass leaves at the count, then runs the condition with the state as a
borrowed variable, in which no variable dies, so `After.test` keeps the invariant at its heap.  A
false condition leaves with the state, which `loopState_stop` shows is the loop's value.
Otherwise the pass releases a state that the body does not use, runs the body, coerces its value
to the loop's mode, and stores it as the next state.  After the loop the outer variables that only
the condition or the body uses are released. -/
theorem specX_loop_with (hm : Runtime m) (hRA : strict = true → ReleaseAligned m)
    (hCopy : CopyCodeX strict m host) {Γ' : List Ty} {tTy : Ty} {count : Expr S Γ' .word}
    {init : Expr S Γ' tTy} {cond : Expr S (tTy :: Γ') .bool}
    {body : Expr S (tTy :: .word :: Γ') tTy}
    (countSpec : ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv count env
        slots paid live)
    (initSpec : ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv init env slots paid live)
    (condSpec : ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv cond env slots paid live)
    (bodySpec : ∀ buy env slots paid live, CodeSpecInX strict (pool := pool) buy m funs flags bounds fits host
        pv body env slots paid live) :
    ∀ env slots paid live (ps : Bool),
      (ps = true → Expr.statePaid flags (slots.map Slot.mode) paid live init cond body = true) →
      ((Expr.loop count init cond body).paid flags (slots.map Slot.mode) paid live = true →
        ps = true) →
      CodeSpecWithX strict (pool := pool)
        ((Expr.loop count init cond body).paid flags (slots.map Slot.mode) paid live)
        (Expr.loopBound ps funs flags bounds (slots.map Slot.mode) paid live count init cond body
          env)
        m funs flags bounds fits host pv (Expr.loop count init cond body) env slots paid live := by
  intro env slots paid live ps hpsS hlpS h base heap store s hh hpv hVars hAt hAl hSafe hCap hBase
      hRoom hPlace rest Q hTrap hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hc := Nat.le_max_left count.width (max (1 + max init.width (copyWidth tTy))
    (2 + tTy.width + max (max cond.width body.width) (copyWidth tTy)))
  have hi := (Nat.le_max_left (1 + max init.width (copyWidth tTy))
    (2 + tTy.width + max (max cond.width body.width) (copyWidth tTy))).trans
    (Nat.le_max_right count.width _)
  have hb := (Nat.le_max_right (1 + max init.width (copyWidth tTy))
    (2 + tTy.width + max (max cond.width body.width) (copyWidth tTy))).trans
    (Nat.le_max_right count.width _)
  have hi1 := Nat.le_max_left init.width (copyWidth tTy)
  have hi2 := Nat.le_max_right init.width (copyWidth tTy)
  have hb1 := Nat.le_max_left (max cond.width body.width) (copyWidth tTy)
  have hb2 := Nat.le_max_right (max cond.width body.width) (copyWidth tTy)
  have hcd := Nat.le_max_left cond.width body.width
  have hbd := Nat.le_max_right cond.width body.width
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  obtain ⟨⟨⟨hPc, hPi⟩, hPcd⟩, hPb⟩ := hPlace
  have hOwnedA : (Expr.loop count init cond body).mode (slots.map Slot.mode) = .owned →
      ((Expr.loop count init cond body).aborts || slots.any (·.mode == .owned)) = true :=
    fun ht => by
      have := (Expr.loop count init cond body).mode_owned (slots.map Slot.mode) ht
      rw [Slot.any_map] at this
      exact this
  have hdl : (Expr.loop count init cond body).fits funs fits env = true →
      count.fits funs fits env = true ∧ init.fits funs fits env = true ∧
        Expr.loopFitsRest funs fits cond body env (count.denote funs env).toNat 0 (init.denote funs env) = true :=
    fun hd => by
      simp only [Expr.fits, Bool.and_eq_true] at hd
      exact ⟨hd.1.1, hd.1.2, hd.2⟩
  have hT := Expr.loopBound_def ps funs flags bounds (slots.map Slot.mode) paid live count init cond
    body env
  simp only [Expr.code, loopCode, Expr.usesFast_eq, List.append_assoc, List.cons_append,
    List.nil_append]
  -- The count, in local `base`.
  have hCountIn : ∀ i, ((live i || cond.uses (i + 1) || body.uses (i + 2) || init.uses i) ||
      count.uses i) = true → (live i || (Expr.loop count init cond body).uses i) = true :=
    fun i h => by simp only [Expr.uses]; exact loop_live_count _ _ _ _ _ h
  -- The variables that die in the count and in the initial state.  The others that die in the
  -- loop are released after it, and their potential is dropped.
  have hDw : dyingPot store s env slots paid
        (fun i => (live i || cond.uses (i + 1) || body.uses (i + 2) || init.uses i) ||
          count.uses i) (fun i => live i || cond.uses (i + 1) || body.uses (i + 2) || init.uses i) +
      dyingPot store s env slots paid
        (fun i => live i || cond.uses (i + 1) || body.uses (i + 2) || init.uses i)
        (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) ≤
      dyingPot store s env slots paid (fun i => live i || (Expr.loop count init cond body).uses i)
        live := by
    rw [dyingPot_split _ (fun i => live i || cond.uses (i + 1) || body.uses (i + 2) || init.uses i)
      _ (fun i h => hCountIn i (by simp [h])) (fun i h => by simp [h]),
      dyingPot_split (fun i => live i || cond.uses (i + 1) || body.uses (i + 2) || init.uses i)
      (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) live (fun i h => by simp [h])
      (fun i h => by simp [h])]
    rw [dyingPot_congr (L0 := fun i => live i || (Expr.loop count init cond body).uses i)
      (L0' := fun i => (live i || cond.uses (i + 1) || body.uses (i + 2) || init.uses i) ||
        count.uses i) (fun i => by
          simp only [Expr.uses]
          cases live i <;> cases count.uses i <;> cases init.uses i <;>
            cases cond.uses (i + 1) <;> cases body.uses (i + 2) <;> rfl) fun _ => rfl]
    omega
  refine countSpec env slots paid _ h base heap
    store s hh hpv (hVars.live_mono hCountIn) hAt
    (fun hs => (hAl hs).live_mono hCountIn) (hSafe.mono hCountIn) hCap hBase (by omega) hPc _ _
    (hTrap.part (fun h => by simp only [Bool.not_eq_true'] at h; simp [Expr.fits, h])
      (fun h => by simp only [Expr.aborts]; exact loop_trap_count _ _ _ _ _ h)
      fun _ hw => hw.mono (by rw [hT]; omega))
    fun heap1 store1 s1 ws1 a1 hAlK hTopK => ?_
  have hR1 := a1.rep
  simp only [Ty.rep_word] at hR1
  subst hR1
  have e1 := a1.toEvolves rfl
  have hp1 : s1.params = s.params := e1.frame.params
  have hh1 : s1.positions = h := e1.frame.positions.trans hh
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  have hLow1 : ({ s1 with values := s.values } : Locals).params.length ≤ base := by
    show s1.params.length ≤ base; rw [hp1]; exact hBase
  have hHigh1 : base < s1.positions := by rw [hh1]; omega
  refine wpX_localSet_local hLow1 (Locals.lt_total hHigh1) ?_
  have f2 : Frame base s1
      (setLocal { s1 with values := s.values } base (.i64 (count.denote funs env))) :=
    Frame.setValues hLow1 le_rfl hHigh1
  have hF2 : Frame base s
      (setLocal { s1 with values := s.values } base (.i64 (count.denote funs env))) :=
    e1.frame.trans f2
  have hN2 : (setLocal { s1 with values := s.values } base
      (.i64 (count.denote funs env))).get base = some (.i64 (count.denote funs env)) :=
    Locals.get_setLocal_same hLow1 (Locals.lt_total hHigh1)
  have e1' : Evolves env slots
      (fun i => (live i || cond.uses (i + 1) || body.uses (i + 2) || init.uses i) || count.uses i)
      (fun i => live i || cond.uses (i + 1) || body.uses (i + 2) || init.uses i) base heap store s
      heap1 store1
      (setLocal { s1 with values := s.values } base (.i64 (count.denote funs env))) :=
    Evolves.mk e1.step hF2 (e1.holds.agree f2)
  have hAlE1 : strict = true → HoldsA env slots
      (fun i => live i || cond.uses (i + 1) || body.uses (i + 2) || init.uses i) heap1 store1
      (setLocal { s1 with values := s.values } base (.i64 (count.denote funs env))) :=
    fun hs => HoldsA.agree e1.holds (hAlK hs).1 f2
  -- The initial state, coerced to the loop's mode, in the locals from `base + 2` on.
  have hDi : dyingPot store1
      (setLocal { s1 with values := s.values } base (.i64 (count.denote funs env))) env slots paid
      (fun i => live i || cond.uses (i + 1) || body.uses (i + 2) || init.uses i)
      (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) =
    dyingPot store s env slots paid
      (fun i => live i || cond.uses (i + 1) || body.uses (i + 2) || init.uses i)
      (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) :=
    dyingPot_evolves (hVars.live_mono hCountIn) e1' (fun i h => by simp [h]) _ _ fun _ h => h
  refine initSpec env slots paid _ h
    (base + 1) heap1 store1 _ (hF2.positions.trans hh) (hF2.params.trans hpv)
    (e1'.holds.mono (Nat.le_succ base))
    e1'.step.at_ hAlE1
    ((hSafe.mono hCountIn).evolves (hVars.live_mono hCountIn) e1' (fun i hi => by simp [hi]))
    (by rw [e1'.step.cap m]; exact hCap) (by rw [hF2.params]; omega) (by omega) hPi
    _ _ (hTrap.part (fun h => by simp only [Bool.not_eq_true'] at h; simp [Expr.fits, h])
      (fun h => by simp only [Expr.aborts]; exact loop_trap_init _ _ _ _ _ h)
      fun hd hw => by
        have := hTopK (hdl (fits_of_not hd)).1
        rw [hDi]
        exact hw.shift (heap1 := heap1) (store1 := store1)
          (c1 := dyingPot store s env slots paid
            (fun i => (live i || cond.uses (i + 1) || body.uses (i + 2) || init.uses i) ||
              count.uses i)
            (fun i => live i || cond.uses (i + 1) || body.uses (i + 2) || init.uses i) +
            count.allocs funs flags bounds (slots.map Slot.mode) paid
              (fun i => live i || cond.uses (i + 1) || body.uses (i + 2) || init.uses i) env)
          (by omega) (by rw [hT]; omega) (e1'.step.cap m))
    fun heap2 storeV _ wsV aV hAlV hTopI => ?_
  have hTop2 : (Expr.loop count init cond body).fits funs fits env = true →
      heap2.top.toNat ≤ heap.top.toNat +
        (dyingPot store s env slots paid
            (fun i => live i || (Expr.loop count init cond body).uses i)
          live +
        (count.allocs funs flags bounds (slots.map Slot.mode) paid
        (fun i => live i || cond.uses (i + 1) || body.uses (i + 2) || init.uses i) env +
        init.allocs funs flags bounds (slots.map Slot.mode) paid
        (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) env)) := fun hd => by
    have := hTopK (hdl hd).1; have := hTopI (hdl hd).2.1; rw [hDi] at this; omega
  refine After.coerceX hCopy aV hAlV (fun h => by simp [Mode.join, h]) le_rfl
    (by rw [aV.frame.params, hF2.params]; omega) (aV.frame.positions.trans (hF2.positions.trans hh))
    (by omega) (by rw [aV.step.cap m, e1'.step.cap m]; exact hCap)
    (fun hs ht _ => hTrap.alloc (hOwnedA ht) fun hd hw => by
      have hcc : coerceCost tTy (init.mode (slots.map Slot.mode))
          ((init.mode (slots.map Slot.mode)).join
            (body.mode (.borrowed :: .borrowed :: slots.map Slot.mode)))
          (init.denote funs env) = tTy.copyCost (init.denote funs env) := by
        rw [coerceCost, ite_eq_left ⟨hs, ht⟩]
      exact hw.shift (hTop2 (fits_of_not hd)) (by rw [hT]; omega)
        (by rw [aV.step.cap m, e1'.step.cap m]))
    fun heap2' store2 s3 ws0 a2 hTopCo hSame0 hAl2 => ?_
  -- The first state's potential: a paid initial value's, which the coercion keeps, or the credit.
  have hTopEntry : (Expr.loop count init cond body).fits funs fits env = true →
      heap2'.top.toNat +
          (if ps = true then
            tTy.pot store2 ws0 (init.denote funs env) else 0) +
          Expr.loopRest funs flags bounds (slots.map Slot.mode) paid live ps init cond body env
            (count.denote funs env).toNat 0 (init.denote funs env) ≤
        heap.top.toNat +
          (dyingPot store s env slots paid
              (fun i => live i || (Expr.loop count init cond body).uses i)
            live +
          Expr.loopBound ps funs flags bounds (slots.map Slot.mode) paid live count init cond body env) := fun hd => by
    have hK := hTopK (hdl hd).1
    have hI := hTopI (hdl hd).2.1
    rw [hDi] at hI
    have hE := loop_entry_pot (ps := ps)
      (ip := init.paid flags (slots.map Slot.mode) paid
        (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)))
      (P0 := tTy.pot storeV wsV (init.denote funs env))
      (P1 := tTy.pot store2 ws0 (init.denote funs env)) (C := tTy.credit (init.denote funs env))
      (fun _ hip => by
        obtain ⟨rfl, rfl⟩ := hSame0 (Expr.mode_of_paid init hip)
        rfl)
      (fun hps _ => by
        have hr := a2.rep
        rw [Expr.statePaid_mode (hpsS hps)] at hr
        exact Ty.pot_le_credit tTy ws0 _ hr)
    rw [hT]
    omega
  have hF3 : Frame base s s3 := hF2.trans (a2.frame.mono (Nat.le_succ base))
  have hh3 : s3.positions = h := hF3.positions.trans hh
  have hN3 : s3.get base = some (.i64 (count.denote funs env)) :=
    (a2.frame.below base (by omega)).1.trans hN2
  have a0 := (After.prepend (hVars.live_mono hCountIn) e1'
    (a2.lower e1'.holds (Nat.le_succ base) fun i h => by simp [h]) (fun i h => by simp [h])
    fun i h => by simp [h]).liveIn hCountIn
  refine wpX_storeCode ws0 h (base + 2) tTy.types s3 s.values a0.rep.typed hh3
    (by rw [hF3.params]; omega) (by rw [Ty.types_length, hh3]; omega)
    fun s4 hF4 hold4 _ => ?_
  -- The index, in local `base + 1`.
  simp only [wpX_constI64_cons]
  have hh4 : s4.positions = h := hF4.positions.trans hh3
  have hLow4 : ({ s4 with values := s.values } : Locals).params.length ≤ base + 1 := by
    show s4.params.length ≤ base + 1; rw [hF4.params, hF3.params]; omega
  have hHigh4 : base + 1 < s4.positions := by rw [hh4]; omega
  refine wpX_localSet_local (s := s4) (vs := s.values) hLow4 (Locals.lt_total hHigh4) ?_
  have f5 : Frame (base + 1) s4 (setLocal { s4 with values := s.values } (base + 1) (.i64 0)) :=
    Frame.setValues hLow4 le_rfl hHigh4
  have hF5 : Frame base s3 (setLocal { s4 with values := s.values } (base + 1) (.i64 0)) :=
    (hF4.mono (base := base) (by omega)).trans (f5.mono (base := base) (by omega))
  have hN5 : (setLocal { s4 with values := s.values } (base + 1) (.i64 0)).get base =
      some (.i64 (count.denote funs env)) := by
    rw [(((hF4.mono (base := base + 1) (by omega)).trans f5).below base (by omega)).1]
    exact hN3
  have hI5 : (setLocal { s4 with values := s.values } (base + 1) (.i64 0)).get (base + 1) =
      some (.i64 0) :=
    Locals.get_setLocal_same hLow4 (Locals.lt_total hHigh4)
  have hold5 : LocalsHold (setLocal { s4 with values := s.values } (base + 1) (.i64 0))
      (base + 2) tTy.types ws0 :=
    hold4.keep (lo := base + 2) (by simp)
      (fun j hj _ => ⟨by rw [Locals.get_setLocal_ne hLow4 (by omega)]; rfl,
        by rw [Locals.get_setLocal_ne hLow4 (by omega)]; rfl,
        by rw [Locals.get_setLocal_ne hLow4 (by omega)]; rfl⟩) le_rfl
      (by rw [a0.rep.length, hh4]; omega)
  -- The exit at either test: the release of the outer variables that only the loop uses, and the
  -- load of the state.
  have hExit : ∀ heapX stX sX wsX (vals : List Value), vals = s.values →
      LocalsHold sX (base + 2) tTy.types wsX →
      After env slots (fun i => live i || (Expr.loop count init cond body).uses i)
        (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) base heap store s tTy
        ((init.mode (slots.map Slot.mode)).join
          (body.mode (.borrowed :: .borrowed :: slots.map Slot.mode)))
        ((Expr.loop count init cond body).denote funs env) heapX stX sX wsX →
      (strict = true → HoldsA env slots (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) heapX stX sX ∧
        Ty.AlignedVal ((init.mode (slots.map Slot.mode)).join
          (body.mode (.borrowed :: .borrowed :: slots.map Slot.mode))) stX tTy wsX
          ((Expr.loop count init cond body).denote funs env)) →
      ((Expr.loop count init cond body).fits funs fits env = true →
        heapX.top.toNat +
            (if ps = true then
              tTy.pot stX wsX ((Expr.loop count init cond body).denote funs env) else 0) ≤
          heap.top.toNat +
          (dyingPot store s env slots paid
              (fun i => live i || (Expr.loop count init cond body).uses i)
            live +
          Expr.loopBound ps funs flags bounds (slots.map Slot.mode) paid live count init cond body env)) →
      wpX strict m (releaseWhere Γ' slots (fun i => (cond.uses (i + 1) || body.uses (i + 2)) && !live i) ++
        (loadCode h (base + 2) tTy.types ++ rest)) Q stX { sX with values := vals } host := by
    intro heapX stX sX wsX vals hv holdX aX hAlX hTopX
    subst hv
    refine After.releaseX hm hRA (live := live)
      (sel := fun i => (cond.uses (i + 1) || body.uses (i + 2)) && !live i) hVars aX hAlX
      (fun i h => by simp only [Expr.uses]; exact loop_live_state _ _ _ _ _ h)
      (fun i h => by simp only [Bool.and_eq_true] at h; exact loop_sel _ _ _ h.1)
      (fun i h => by simp [h]) fun heap' store' a' hTopR hReg hAl' => ?_
    refine wpX_loadCode wsX a'.rep.typed (aX.frame.positions.trans hh) holdX ?_
    refine hNext heap' store' sX wsX a' hAl' fun hd => ?_
    have h1 := hTopX hd
    have h2 := congrArg UInt64.toNat hTopR
    -- The loop's value has the last state's potential, which the release keeps.
    have hP : (if ps = true then
          tTy.pot store' wsX ((Expr.loop count init cond body).denote funs env) else 0) =
        (if ps = true then
          tTy.pot stX wsX ((Expr.loop count init cond body).denote funs env) else 0) := by
      split
      · next hps => rw [Ty.pot_of_regions (Expr.statePaid_mode (hpsS hps)) hReg]
      · rfl
    -- A paid loop has a paid state.
    have hLoopPaid : (if (Expr.loop count init cond body).paid flags (slots.map Slot.mode) paid live =
          true then tTy.pot store' wsX ((Expr.loop count init cond body).denote funs env) else 0) ≤
        (if ps = true then
          tTy.pot store' wsX ((Expr.loop count init cond body).denote funs env) else 0) := by
      split
      · next hlp =>
        rw [ite_eq_left (hlpS hlp)]
      · exact Nat.zero_le _
    rw [hP] at hLoopPaid
    omega
  -- The loop.  The invariant holds the count, the index `i`, and the state after `i` passes, and
  -- the count less the index decreases.
  refine wpX_block_cons ?_
  refine wpX_loop_cons
    (fun st si => ∃ heapI wsI, ∃ i : UInt64, i ≤ count.denote funs env ∧
      si.get base = some (.i64 (count.denote funs env)) ∧ si.get (base + 1) = some (.i64 i) ∧
      LocalsHold si (base + 2) tTy.types wsI ∧
      After env slots (fun i => live i || (Expr.loop count init cond body).uses i)
        (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) base heap store s tTy
        ((init.mode (slots.map Slot.mode)).join
          (body.mode (.borrowed :: .borrowed :: slots.map Slot.mode)))
        (loopState (init.denote funs env)
          (fun i acc => bif cond.denote funs (.cons acc env) then
            body.denote funs (.cons acc (.cons i env)) else acc) i.toNat) heapI st si wsI ∧
      (strict = true → HoldsA env slots (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) heapI st si ∧
        Ty.AlignedVal ((init.mode (slots.map Slot.mode)).join
          (body.mode (.borrowed :: .borrowed :: slots.map Slot.mode))) st tTy wsI
          (loopState (init.denote funs env)
            (fun i acc => bif cond.denote funs (.cons acc env) then
              body.denote funs (.cons acc (.cons i env)) else acc) i.toNat)) ∧
      ((Expr.loop count init cond body).fits funs fits env = true →
        Expr.loopFitsRest funs fits cond body env ((count.denote funs env).toNat - i.toNat) i
          (loopState (init.denote funs env)
            (fun i acc => bif cond.denote funs (.cons acc env) then
              body.denote funs (.cons acc (.cons i env)) else acc) i.toNat) = true ∧
        heapI.top.toNat +
            (if ps = true then
              tTy.pot st wsI (loopState (init.denote funs env)
                (fun i acc => bif cond.denote funs (.cons acc env) then
                  body.denote funs (.cons acc (.cons i env)) else acc) i.toNat) else 0) +
          Expr.loopRest funs flags bounds (slots.map Slot.mode) paid live ps init cond body env
          ((count.denote funs env).toNat - i.toNat) i
          (loopState (init.denote funs env)
            (fun i acc => bif cond.denote funs (.cons acc env) then
              body.denote funs (.cons acc (.cons i env)) else acc) i.toNat) ≤
          heap.top.toNat +
            (dyingPot store s env slots paid
              (fun i => live i || (Expr.loop count init cond body).uses i) live +
            Expr.loopBound ps funs flags bounds (slots.map Slot.mode) paid live count init cond body env)))
    (fun _ s' => match s'.get (base + 1) with
      | some (.i64 i) => (count.denote funs env).toNat - i.toNat
      | _ => 0)
    ⟨heap2', ws0, 0, UInt64.zero_le, hN5, hI5, hold5, a0.reframe hF5,
      fun hs => ⟨HoldsA.agree a0.holds (hAl2 hs).1 hF5, by
        simpa only [UInt64.toNat_zero, loopState] using (hAl2 hs).2⟩, fun hd =>
      ⟨by simpa only [UInt64.toNat_zero, Nat.sub_zero, loopState] using (hdl hd).2.2,
        by simpa only [UInt64.toNat_zero, Nat.sub_zero, loopState] using hTopEntry hd⟩⟩ ?_
  rintro st si ⟨heapI, wsI, i, hiN, hNi, hii, holdi, aI, hAlI, hInv⟩
  simp only [wpX_localGet_cons, Locals.get_values, hii, hNi, wpX_geUI64_cons, wpX_br_if_cons]
  by_cases hge : count.denote funs env ≤ i
  · -- The index reached the count.
    simp (config := { decide := true }) only [ge_iff_le, hge, ↓reduceIte, List.take_zero,
      List.drop_zero, List.nil_append]
    have hieq := UInt64.le_antisymm hiN hge
    have hden : (Expr.loop count init cond body).denote funs env =
        loopState (init.denote funs env)
          (fun i acc => bif cond.denote funs (.cons acc env) then
            body.denote funs (.cons acc (.cons i env)) else acc) i.toNat := by
      rw [hieq, loopState_eq]; rfl
    rw [hieq, loopState_eq] at aI hAlI
    refine hExit _ _ _ _ _ rfl holdi aI hAlI fun hd => ?_
    have := (hInv hd).2
    rw [hieq, Nat.sub_self, Expr.loopRest_zero] at this
    rw [hden, hieq]
    omega
  -- One more pass, if the condition holds.
  have hlt : i < count.denote funs env := UInt64.not_le.mp hge
  have hk : (count.denote funs env).toNat - i.toNat =
      ((count.denote funs env).toNat - i.toNat - 1) + 1 := by
    have := UInt64.lt_iff_toNat_lt.mp hlt; omega
  have hsucc : (i + 1).toNat = i.toNat + 1 := by
    have := UInt64.lt_iff_toNat_lt.mp hlt
    have := (count.denote funs env).toNat_lt
    rw [UInt64.toNat_add]; simp; omega
  simp (config := { decide := true }) only [ge_iff_le, hge, ↓reduceIte]
  have hhi : si.positions = h := aI.frame.positions.trans hh
  -- The pass's frames, from the invariant.
  have hFitsI : (Expr.loop count init cond body).fits funs fits env = true →
      Expr.loopFitsRest funs fits cond body env ((count.denote funs env).toNat - i.toNat - 1 + 1) i
        (loopState (init.denote funs env)
          (fun i acc => bif cond.denote funs (.cons acc env) then
            body.denote funs (.cons acc (.cons i env)) else acc) i.toNat) = true :=
    fun hd => by rw [← hk]; exact (hInv hd).1
  have hFitsC : (Expr.loop count init cond body).fits funs fits env = true → cond.fits funs fits (.cons (loopState (init.denote funs env)
      (fun i acc => bif cond.denote funs (.cons acc env) then
        body.denote funs (.cons acc (.cons i env)) else acc) i.toNat) env) = true :=
    fun hd => Expr.loopFitsRest_cond (hFitsI hd)
  -- The condition's context: the state, borrowed, as variable 0.
  have hdAll : ∀ j, cond.uses (j + 1) = true →
      (live j || cond.uses (j + 1) || body.uses (j + 2)) = true := fun j h => by simp [h]
  have hVarsC : Holds (Env.cons (loopState (init.denote funs env)
        (fun i acc => bif cond.denote funs (.cons acc env) then
          body.denote funs (.cons acc (.cons i env)) else acc) i.toNat) env)
      (⟨base + 2, .borrowed⟩ :: slots)
      (fun j => (j == 0 ||
        shift 1 (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) j) || cond.uses j)
      (base + 2 + tTy.width) heapI st si :=
    Holds.push ((aI.holds.mono (by omega)).live_mono fun j hj => cond_live_outer _ _ hdAll j hj)
      holdi aI.rep.borrow
      ((aI.apart.borrow aI.rep).live_mono fun j hj => cond_live_outer _ _ hdAll j hj)
  have hSafeI := (hSafe.after hVars aI
    (fun j hj => by simp only [Expr.uses]; exact loop_live_state _ _ _ _ _ hj)).1
  have hSafeC : pool.Safe
      (Env.cons (loopState (init.denote funs env)
        (fun i acc => bif cond.denote funs (.cons acc env) then
          body.denote funs (.cons acc (.cons i env)) else acc) i.toNat) env)
      (⟨base + 2, .borrowed⟩ :: slots)
      (fun j => (j == 0 ||
        shift 1 (fun k => live k || cond.uses (k + 1) || body.uses (k + 2)) j) || cond.uses j)
      heapI st si :=
    (hSafeI.mono fun j hj => cond_live_outer _ _ hdAll j hj).push
      holdi aI.rep.borrow (by simp only [Mode.fresh]; exact fun _ _ _ hMem => nomatch hMem)
  -- No variable dies in the condition: the outer ones it uses stay live, and the state is
  -- borrowed.
  have hDc : dyingPot st si (Env.cons (loopState (init.denote funs env)
        (fun i acc => bif cond.denote funs (.cons acc env) then
          body.denote funs (.cons acc (.cons i env)) else acc) i.toNat) env)
      (⟨base + 2, .borrowed⟩ :: slots) (false :: paid)
      (fun j => (j == 0 || shift 1 (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) j) ||
        cond.uses j)
      (fun j => j == 0 || shift 1 (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) j) =
      0 :=
    dyingPot_eq_zero fun j h => cond_live _ _ hdAll j h
  refine condSpec _ (⟨base + 2, .borrowed⟩ :: slots) (false :: paid) _ h
    (base + 2 + tTy.width) heapI st si hhi (aI.frame.params.trans hpv) hVarsC aI.step.at_
    (fun hs => HoldsA.push ((hAlI hs).1.live_mono fun j hj => cond_live_outer _ _ hdAll j hj) holdi
      aI.rep.length (Ty.AlignedVal.toBorrowed aI.rep (hAlI hs).2))
    hSafeC
    (by rw [aI.step.cap m]; exact hCap)
    (by rw [aI.frame.params]; omega) (by omega) hPcd _ _
    ((hTrap.part (fun h => by
          cases hw : (Expr.loop count init cond body).fits funs fits env
          · rfl
          · exact absurd (hFitsC hw) (by simpa using h)) (fun h => by
      have h' : (cond.aborts || slots.any (·.mode == .owned)) = true := by
        simpa [List.any_cons] using h
      simp only [Expr.aborts]; exact loop_trap_cond _ _ _ _ _ h') fun hd hw => hw.of_le
        (by
          have := (hInv (fits_of_not hd)).2
          have := Expr.loopRest_cond_le (funs := funs) (flags := flags) (bounds := bounds)
            (modes := slots.map Slot.mode) (paid := paid) (live := live) (ps := ps) (init := init)
                (cond := cond)
            (body := body) (env := env) (n := (count.denote funs env).toNat - i.toNat - 1) (i := i)
            (x := loopState (init.denote funs env)
              (fun i acc => bif cond.denote funs (.cons acc env) then
                body.denote funs (.cons acc (.cons i env)) else acc) i.toNat)
          rw [← hk] at this
          rw [hDc]
          simp only [List.map_cons]; omega)
        (aI.step.cap m)).imp fun _ h => h)
    fun heapC stC sC wsC aC hAlC hTopC => ?_
  have hRC := aC.rep
  simp only [Ty.rep_bool] at hRC
  subst hRC
  have aI2 := After.test aI aC (by omega) (cond_live _ _ hdAll) rfl
  have hAlI2 : strict = true → HoldsA env slots (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) heapC stC sC ∧
      Ty.AlignedVal ((init.mode (slots.map Slot.mode)).join
          (body.mode (.borrowed :: .borrowed :: slots.map Slot.mode))) stC tTy wsI
        (loopState (init.denote funs env)
            (fun i acc => bif cond.denote funs (.cons acc env) then
              body.denote funs (.cons acc (.cons i env)) else acc) i.toNat) := fun hs =>
    ⟨(hAlC hs).1.pop.live_mono fun j h => by simpa [shift] using h, fun r hr =>
      (hAlI hs).2 r (by rw [After.test_regions aI aC (cond_live _ _ hdAll)] at hr; exact hr)⟩
  -- The condition keeps the state's blocks, and so its potential.
  have hPotC : (if ps = true then
        tTy.pot stC wsI (loopState (init.denote funs env)
          (fun i acc => bif cond.denote funs (.cons acc env) then
            body.denote funs (.cons acc (.cons i env)) else acc) i.toNat) else 0) =
      (if ps = true then
        tTy.pot st wsI (loopState (init.denote funs env)
          (fun i acc => bif cond.denote funs (.cons acc env) then
            body.denote funs (.cons acc (.cons i env)) else acc) i.toNat) else 0) := by
    split
    · next hps =>
      rw [Ty.pot_of_regions (Expr.statePaid_mode (hpsS hps))
        (After.test_regions aI aC (cond_live _ _ hdAll))]
    · rfl
  have hiiC : sC.get (base + 1) = some (.i64 i) :=
    (aC.frame.below (base + 1) (by omega)).1.trans hii
  have hNiC : sC.get base = some (.i64 (count.denote funs env)) :=
    (aC.frame.below base (by omega)).1.trans hNi
  have holdC : LocalsHold sC (base + 2) tTy.types wsI :=
    (LocalsHold.frame aC.frame (by rw [aI.rep.length, Ty.types_length])
      (by rw [Ty.types_length])).mpr holdi
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    wpX_eqzI64_cons, wpX_br_if_cons]
  cases hcv : cond.denote funs (Env.cons (loopState (init.denote funs env)
      (fun i acc => bif cond.denote funs (.cons acc env) then
        body.denote funs (.cons acc (.cons i env)) else acc) i.toNat) env)
  · -- The condition fails: the state stays for the remaining passes.
    simp (config := { decide := true }) only [↓reduceIte, List.take_zero, List.drop_zero,
      List.nil_append]
    have hStop := loopState_stop (init.denote funs env)
      (fun acc => cond.denote funs (.cons acc env))
      (fun i acc => body.denote funs (.cons acc (.cons i env))) hcv _
      (UInt64.le_iff_toNat_le.mp hiN)
    have hden : (Expr.loop count init cond body).denote funs env =
        loopState (init.denote funs env)
          (fun i acc => bif cond.denote funs (.cons acc env) then
            body.denote funs (.cons acc (.cons i env)) else acc) i.toNat := by
      rw [← hStop, loopState_eq]; rfl
    rw [← hStop, loopState_eq] at aI2 hAlI2
    refine hExit _ _ _ _ _ rfl holdC aI2 hAlI2 fun hd => ?_
    have h1 := (hInv hd).2
    rw [hk, Expr.loopRest_false hcv] at h1
    have h2 := hTopC (hFitsC hd)
    rw [hDc] at h2
    simp only [List.map_cons] at h2
    rw [hden, hPotC]
    omega
  simp (config := { decide := true }) only [↓reduceIte]
  -- The condition holds: the pass runs the body.
  set sB : Locals := { sC with values := si.values }
  have aB0 := aI2.reframe (Frame.ofValues (s := sC) (values := si.values))
  have holdB : LocalsHold sB (base + 2) tTy.types wsI := holdC
  have hiiB : sB.get (base + 1) = some (.i64 i) := hiiC
  have hNiB : sB.get base = some (.i64 (count.denote funs env)) := hNiC
  have holdIdx : LocalsHold sB (base + 1) Ty.word.types [.i64 i] := fun k hk => by
    obtain rfl : k = 0 := by simpa using hk
    simpa [Ty.types, slotIndex] using hiiB
  have hhB : sB.positions = h := aB0.frame.positions.trans hh
  have hRoomi : base + 2 + tTy.width + max body.width (copyWidth tTy) ≤ h := by omega
  -- The body's context: the state as variable 0 and the index as variable 1.
  have hIdx := Holds.push (t := .word) (v := i) (mode := .borrowed)
    (live' := fun j => decide (j + 1 < 2) ||
      shift 2 (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) (j + 1) ||
        body.uses (j + 1))
    ((aB0.holds.mono (Nat.le_add_right base 1)).live_mono fun j h => by simpa using h) holdIdx
    rfl
    (Holds.Apart.ofScalar rfl)
  have hVarsB : Holds (Env.cons (loopState (init.denote funs env)
        (fun i acc => bif cond.denote funs (.cons acc env) then
            body.denote funs (.cons acc (.cons i env)) else acc) i.toNat)
        (Env.cons (t := .word) i env))
      (⟨base + 2, (init.mode (slots.map Slot.mode)).join
        (body.mode (.borrowed :: .borrowed :: slots.map Slot.mode))⟩ ::
        ⟨base + 1, .borrowed⟩ :: slots)
      (fun j => decide (j < 2) ||
        shift 2 (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) j || body.uses j)
      (base + 2 + tTy.width) heapC stC sB :=
    Holds.push (hIdx.mono (base' := base + 2) (by simp [Ty.width])) holdB aB0.rep
      (Holds.Apart.push (u := .word) (v := i) (mv := .borrowed)
        (live' := fun j => decide (j + 1 < 2) ||
          shift 2 (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) (j + 1) ||
            body.uses (j + 1))
        (aB0.apart.live_mono fun j h => by simpa using h) holdIdx rfl
        fun _ _ _ c hc => by simp [Ty.regions, Ty.reads] at hc)
  have hAlB : strict = true → HoldsA (Env.cons (loopState (init.denote funs env)
        (fun i acc => bif cond.denote funs (.cons acc env) then
            body.denote funs (.cons acc (.cons i env)) else acc) i.toNat)
        (Env.cons (t := .word) i env))
      (⟨base + 2, (init.mode (slots.map Slot.mode)).join
        (body.mode (.borrowed :: .borrowed :: slots.map Slot.mode))⟩ ::
        ⟨base + 1, .borrowed⟩ :: slots)
      (fun j => decide (j < 2) ||
        shift 2 (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) j || body.uses j)
      heapC stC sB := fun hs =>
    HoldsA.push (HoldsA.push (t := .word) (v := i) (mode := .borrowed)
      (live' := fun j => decide (j + 1 < 2) ||
        shift 2 (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) (j + 1) ||
          body.uses (j + 1))
      (((hAlI2 hs).1.values si.values).live_mono fun j h => by simpa using h) holdIdx rfl
      (Ty.AlignedVal.scalar rfl)) holdB aB0.rep.length (hAlI2 hs).2
  obtain ⟨hSafeB0, hFreshB0⟩ := hSafe.after hVars aB0
    (fun j hj => by simp only [Expr.uses]; exact loop_live_state _ _ _ _ _ hj)
  have hSafeIdx : pool.Safe (.cons (t := .word) i env) (⟨base + 1, .borrowed⟩ :: slots)
      (fun j => decide (j + 1 < 2) ||
        shift 2 (fun k => live k || cond.uses (k + 1) || body.uses (k + 2)) (j + 1) ||
          body.uses (j + 1)) heapC stC sB :=
    (hSafeB0.mono fun j hj => by simpa using hj).push
      holdIdx (show Ty.word.Rep .borrowed heapC stC [.i64 i] i from rfl)
      (by simp only [Mode.fresh]; exact fun _ _ _ hMem => nomatch hMem)
  have hSafeB : pool.Safe
      (Env.cons (loopState (init.denote funs env)
        (fun i acc => bif cond.denote funs (.cons acc env) then
          body.denote funs (.cons acc (.cons i env)) else acc) i.toNat)
        (Env.cons (t := .word) i env))
      (⟨base + 2, (init.mode (slots.map Slot.mode)).join
        (body.mode (.borrowed :: .borrowed :: slots.map Slot.mode))⟩ ::
        ⟨base + 1, .borrowed⟩ :: slots)
      (fun j => decide (j < 2) ||
        shift 2 (fun k => live k || cond.uses (k + 1) || body.uses (k + 2)) j || body.uses j)
      heapC stC sB := hSafeIdx.push holdB aB0.rep hFreshB0
  have hRelease : (if (init.mode (slots.map Slot.mode)).join
        (body.mode (.borrowed :: .borrowed :: slots.map Slot.mode)) = .owned ∧
        body.uses 0 = false then releaseCode tTy (base + 2) else []) =
      (if body.uses 0 = false then [0] else []).flatMap
        (releaseVar (tTy :: .word :: Γ') (⟨base + 2, (init.mode (slots.map Slot.mode)).join
          (body.mode (.borrowed :: .borrowed :: slots.map Slot.mode))⟩ ::
          ⟨base + 1, .borrowed⟩ :: slots)) := by
    cases body.uses 0 <;>
      cases (init.mode (slots.map Slot.mode)).join
        (body.mode (.borrowed :: .borrowed :: slots.map Slot.mode)) <;> simp [releaseVar]
  rw [hRelease]
  have hInv' := fun hd => by
    have h1 := (hInv hd).2
    rw [hk, Expr.loopRest_true hcv] at h1
    exact h1
  have hTopC' := fun hd => by
    have h2 := hTopC (hFitsC hd)
    rw [hDc] at h2
    simp only [List.map_cons] at h2
    exact h2
  have hFitsB : (Expr.loop count init cond body).fits funs fits env = true →
      body.fits funs fits (.cons (loopState (init.denote funs env)
        (fun i acc => bif cond.denote funs (.cons acc env) then
          body.denote funs (.cons acc (.cons i env)) else acc) i.toNat) (.cons i env)) = true ∧
      Expr.loopFitsRest funs fits cond body env ((count.denote funs env).toNat - i.toNat - 1) (i + 1)
        (body.denote funs (.cons (loopState (init.denote funs env)
          (fun i acc => bif cond.denote funs (.cons acc env) then
            body.denote funs (.cons acc (.cons i env)) else acc) i.toNat) (.cons i env))) = true :=
    fun hd => Expr.loopFitsRest_body (hFitsI hd) hcv
  refine wpX_releaseVars hm hRA _ (by split <;> simp) hVarsB aB0.step.at_ hAlB
    (by split <;> simp) fun heap2 store2 e2 hTopRel hA2 => ?_
  have e2' := e2.mono
    (live' := fun j =>
      shift 2 (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) j || body.uses j)
    fun j h => by
      match j with
      | 0 =>
        have h0 : body.uses 0 = true := by simpa [shift] using h
        simp [h0]
      | 1 => simp
      | k + 2 => split <;> simpa using h
  have hA2' : strict = true → HoldsA (Env.cons (loopState (init.denote funs env)
        (fun i acc => bif cond.denote funs (.cons acc env) then
            body.denote funs (.cons acc (.cons i env)) else acc) i.toNat)
        (Env.cons (t := .word) i env))
      (⟨base + 2, (init.mode (slots.map Slot.mode)).join
        (body.mode (.borrowed :: .borrowed :: slots.map Slot.mode))⟩ ::
        ⟨base + 1, .borrowed⟩ :: slots)
      (fun j => shift 2 (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) j ||
        body.uses j) heap2 store2 sB :=
    fun hs => (hA2 hs).live_mono fun j h => by
      match j with
      | 0 =>
        have h0 : body.uses 0 = true := by simpa [shift] using h
        simp [h0]
      | 1 => simp
      | k + 2 => split <;> simpa using h
  -- The only paid variable that can die in the body is the state, when the body uses it.
  have hDbody : dyingPot store2 sB (Env.cons (loopState (init.denote funs env)
        (fun i acc => bif cond.denote funs (.cons acc env) then
            body.denote funs (.cons acc (.cons i env)) else acc) i.toNat)
        (Env.cons (t := .word) i env))
      (⟨base + 2, (init.mode (slots.map Slot.mode)).join
        (body.mode (.borrowed :: .borrowed :: slots.map Slot.mode))⟩ ::
        ⟨base + 1, .borrowed⟩ :: slots)
      (ps :: false :: paid)
      (fun j => shift 2 (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) j ||
        body.uses j)
      (shift 2 fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) ≤
      (if ps = true then
        tTy.pot st wsI (loopState (init.denote funs env)
          (fun i acc => bif cond.denote funs (.cons acc env) then
            body.denote funs (.cons acc (.cons i env)) else acc) i.toNat) else 0) := by
    rw [dyingPot_evolves hVarsB e2' (fun j h => live_right _ _ _ h) _ _ fun _ h => h, ← hPotC,
      ← holdB.read_eq (by rw [aB0.rep.length, Ty.types_length])]
    exact dyingPot_le_head _ _ _ _ _ loop_body_dies
  refine bodySpec (ps) _ _
    (ps :: false :: paid)
    (shift 2 fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) h
    (base + 2 + tTy.width) heap2 store2 sB hhB (aB0.frame.params.trans hpv) e2'.holds e2'.step.at_ hA2'
    (hSafeB.evolves hVarsB e2' (fun j hj => live_right _ _ _ hj))
    (by rw [e2'.step.cap m, aB0.step.cap m]; exact hCap) (by rw [aB0.frame.params]; omega)
    (by omega) hPb _ _
    ((hTrap.part (fun h => by
          cases hw : (Expr.loop count init cond body).fits funs fits env
          · rfl
          · exact absurd (hFitsB hw).1 (by simpa using h)) (fun h => by
      have hmo := (Expr.loop count init cond body).mode_owned (slots.map Slot.mode)
      rw [Slot.any_map] at hmo
      simp only [List.any_cons, Expr.aborts] at h ⊢
      exact loop_trap_body _ _ _ _ _ _ _ (fun hv => hmo (beq_iff_eq.mp hv)) rfl h) fun hd hw =>
        hw.of_le (by
          have := hInv' (fits_of_not hd); have := hTopC' (fits_of_not hd)
          have := congrArg UInt64.toNat hTopRel
          have := hDbody
          simp only [List.map_cons, Expr.buysIn]; omega)
        (by rw [e2'.step.cap m, aB0.step.cap m])).imp
        fun _ h => h)
    fun heap6 _ s6b _ aBb hAlBb hTopB => ?_
  have hp6 : s6b.params = s.params := aBb.frame.params.trans aB0.frame.params
  refine After.coerceX hCopy aBb hAlBb
    (fun h => loop_mode (f := fun md => body.mode (md :: .borrowed :: slots.map Slot.mode)) h)
    le_rfl (by rw [hp6]; omega) (aBb.frame.positions.trans hhB) (by omega)
    (by rw [aBb.step.cap m, e2'.step.cap m, aB0.step.cap m]; exact hCap)
    (fun hs ht _ => (hTrap.alloc (hOwnedA ht) fun hd hw => by
      have hcc : coerceCost tTy
          (body.mode (((init.mode (slots.map Slot.mode)).join
            (body.mode (.borrowed :: .borrowed :: slots.map Slot.mode))) :: .borrowed ::
            slots.map Slot.mode))
          ((init.mode (slots.map Slot.mode)).join
            (body.mode (.borrowed :: .borrowed :: slots.map Slot.mode)))
          (body.denote funs (.cons (loopState (init.denote funs env)
              (fun i acc => bif cond.denote funs (.cons acc env) then
                body.denote funs (.cons acc (.cons i env)) else acc) i.toNat) (.cons i env))) =
          tTy.copyCost (body.denote funs (.cons (loopState (init.denote funs env)
              (fun i acc => bif cond.denote funs (.cons acc env) then
                body.denote funs (.cons acc (.cons i env)) else acc) i.toNat) (.cons i env))) := by
        rw [coerceCost, ite_eq_left ⟨by simpa only [List.map_cons] using hs, ht⟩]
      exact hw.of_le (by
          have := hInv' (fits_of_not hd); have := hTopC' (fits_of_not hd)
          have := congrArg UInt64.toNat hTopRel
          have h6 := hTopB (hFitsB (fits_of_not hd)).1
          have := hDbody
          simp only [List.map_cons, Expr.buysIn] at h6
          omega)
        (by rw [aBb.step.cap m, e2'.step.cap m, aB0.step.cap m])).imp fun _ h => h)
    fun heap6' store6 s6 ws6 aB hTopCo2 hSame6 hAl6 => ?_
  have hp6 : s6.params = s.params := aB.frame.params.trans aB0.frame.params
  have hh6 : s6.positions = h := aB.frame.positions.trans hhB
  refine wpX_storeCode ws6 h (base + 2) tTy.types s6 si.values aB.rep.typed hh6
    (by rw [hp6]; omega) (by rw [Ty.types_length, hh6]; omega) fun s7 hF7 hold7 _ => ?_
  have hp7' : s7.params = s.params := hF7.params.trans hp6
  have hh7 : s7.positions = h := hF7.positions.trans hh6
  have hget7 : ∀ j < base + 2, s7.get j = sB.get j := fun j hj => by
    rw [(hF7.below j hj).1]
    exact (aB.frame.below j (by omega)).1
  -- The next index, in local `base + 1`.
  simp only [wpX_localGet_cons, Locals.get_values, hget7 (base + 1) (by omega), hiiB,
    wpX_constI64_cons, wpX_addI64_cons]
  have hLow7 : ({ s7 with values := si.values } : Locals).params.length ≤ base + 1 := by
    show s7.params.length ≤ base + 1; rw [hp7']; omega
  have hHigh7 : base + 1 < s7.positions := by rw [hh7]; omega
  refine wpX_localSet_local (s := s7) (vs := si.values) hLow7 (Locals.lt_total hHigh7) ?_
  have hget8 : (setLocal { s7 with values := si.values } (base + 1) (.i64 (i + 1))).get
      (base + 1) = some (.i64 (i + 1)) :=
    Locals.get_setLocal_same hLow7 (Locals.lt_total hHigh7)
  have hold8 : LocalsHold (setLocal { s7 with values := si.values } (base + 1)
      (.i64 (i + 1))) (base + 2) tTy.types ws6 :=
    hold7.keep (lo := base + 2) (by simp)
      (fun j hj _ => ⟨by rw [Locals.get_setLocal_ne hLow7 (by omega)]; rfl,
        by rw [Locals.get_setLocal_ne hLow7 (by omega)]; rfl,
        by rw [Locals.get_setLocal_ne hLow7 (by omega)]; rfl⟩) le_rfl
      (by rw [aB.rep.length, hh7]; omega)
  -- The state after `i + 1` iterations: the facts of the body's code for the outer context.
  have aB' := After.prepend hVarsB e2' aB (fun j h => live_right _ _ _ h) fun j h => by
    simp [h]
  have hNew : ∀ r, (∀ b ∈ ((init.mode (slots.map Slot.mode)).join
        (body.mode (.borrowed :: .borrowed :: slots.map Slot.mode))).fresh stC tTy wsI
        (loopState (init.denote funs env)
          (fun i acc => bif cond.denote funs (.cons acc env) then
            body.denote funs (.cons acc (.cons i env)) else acc) i.toNat),
        regionsDisjoint r b) →
      ((init.mode (slots.map Slot.mode)).join
          (body.mode (.borrowed :: .borrowed :: slots.map Slot.mode)) = .owned → ∀ w,
        LocalsHold sB (base + 2) tTy.types w → w.length = tTy.width →
        ∀ b ∈ tTy.blocks stC w (loopState (init.denote funs env)
          (fun i acc => bif cond.denote funs (.cons acc env) then
            body.denote funs (.cons acc (.cons i env)) else acc) i.toNat),
        regionsDisjoint r b) ∧
      (Mode.borrowed = .owned → ∀ w, LocalsHold sB (base + 1) Ty.word.types w →
        w.length = Ty.word.width →
        ∀ b ∈ Ty.word.blocks stC w i, regionsDisjoint r b) := by
    intro r hFresh
    refine ⟨fun hmo w hw hlw b hb => ?_, fun hmo => nomatch hmo⟩
    obtain rfl := LocalsHold.unique hw holdB (hlw.trans aB0.rep.length.symm)
    rw [hmo] at hFresh
    exact hFresh b hb
  have aNext := After.bind2 hVars aB0 (Frame.refl base sB) aB' (by omega) hNew
    (fun j h => by simpa using h)
    (fun j h => by simp only [Expr.uses]; exact loop_live_state _ _ _ _ _ h) fun _ h => h
  have hv : loopState (init.denote funs env)
      (fun i acc => bif cond.denote funs (.cons acc env) then
            body.denote funs (.cons acc (.cons i env)) else acc) (i + 1).toNat =
      body.denote funs (.cons (loopState (init.denote funs env)
        (fun i acc => bif cond.denote funs (.cons acc env) then
            body.denote funs (.cons acc (.cons i env)) else acc) i.toNat) (.cons i env)) := by
    rw [hsucc, loopState, UInt64.ofNat_toNat]
    simp only [hcv, Bool.cond_true]
  rw [wpX_br_cons]
  dsimp only
  refine ⟨⟨heap6', ws6, i + 1, UInt64.le_iff_toNat_le.mpr ?_, ?_, hget8, hold8, ?_, ?_, ?_⟩, ?_⟩
  · have := UInt64.lt_iff_toNat_lt.mp hlt
    omega
  · rw [Locals.get_setLocal_ne hLow7 (by omega), Locals.get_values, hget7 base (by omega)]
    exact hNiB
  · rw [hv]
    exact aNext.reframe ((hF7.mono (base := base) (by omega)).trans
      ((Frame.setValues (s := s7) (vs := si.values) (base := base + 1) hLow7 le_rfl
        hHigh7).mono (base := base)
        (by omega)))
  · intro hs
    have hF8 : Frame base s6
        (setLocal { s7 with values := si.values } (base + 1) (.i64 (i + 1))) :=
      (hF7.mono (base := base) (by omega)).trans
        ((Frame.setValues (s := s7) (vs := si.values) (base := base + 1) hLow7 le_rfl
          hHigh7).mono (base := base) (by omega))
    refine ⟨HoldsA.agree aNext.holds ((hAl6 hs).1.pop.pop.live_mono fun j h => by
      simpa [shift] using h) hF8, ?_⟩
    rw [hv]
    exact (hAl6 hs).2
  · intro hd
    rw [hv, hsucc, show (count.denote funs env).toNat - (i.toNat + 1) =
      (count.denote funs env).toNat - i.toNat - 1 by omega]
    refine ⟨(hFitsB hd).2, ?_⟩
    have := hInv' hd; have := hTopC' hd; have := congrArg UInt64.toNat hTopRel
    have h6 := hTopB (hFitsB hd).1
    simp only [List.map_cons] at h6 hTopCo2
    -- The body's value, which is paid when the state is, keeps its potential through the
    -- coercion, the identity on an owned value.
    simp only [Expr.buysIn] at h6
    have := loop_body_pot (Expr.statePaid_body_of hpsS)
      (fun hps => by
        obtain ⟨rfl, rfl⟩ := hSame6 (Expr.mode_of_paidIn body (Expr.statePaid_body_of hpsS hps))
        rfl)
      h6 hDbody hTopCo2
    omega
  · have := UInt64.lt_iff_toNat_lt.mp hlt
    simp only [hget8]
    omega

/-- A loop: the bound of `spec_loop_with` at the state's flag, or, for a state of pair type that
is paid, at the flag whose bound is smaller. -/
theorem specX_loop (hm : Runtime m) (hRA : strict = true → ReleaseAligned m)
    (hCopy : CopyCodeX strict m host) {Γ' : List Ty} {tTy : Ty} {count : Expr S Γ' .word}
    {init : Expr S Γ' tTy} {cond : Expr S (tTy :: Γ') .bool}
    {body : Expr S (tTy :: .word :: Γ') tTy}
    (countSpec : ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv count env
        slots paid live)
    (initSpec : ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv init env slots paid live)
    (condSpec : ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv cond env slots paid live)
    (bodySpec : ∀ buy env slots paid live, CodeSpecInX strict (pool := pool) buy m funs flags bounds fits host
        pv body env slots paid live) :
    ∀ env slots paid live,
      CodeSpecX strict (pool := pool) m funs flags bounds fits host pv (Expr.loop count init cond body) env slots paid live := by
  intro env slots paid live
  have hT := Expr.allocs_loop funs flags bounds (slots.map Slot.mode) paid live count init cond body
    env
  have core := specX_loop_with hm hRA hCopy countSpec initSpec condSpec bodySpec env slots paid live
  by_cases hmin :
      (Expr.statePaid flags (slots.map Slot.mode) paid live init cond body && tTy.isPair) = true
  · rw [ite_eq_left hmin] at hT
    simp only [Bool.and_eq_true] at hmin
    have hnp : (Expr.loop count init cond body).paid flags (slots.map Slot.mode) paid live = false := by
      simp only [Expr.paid, hmin.2, Bool.not_true, Bool.and_false]
    by_cases hle : Expr.loopBound false funs flags bounds (slots.map Slot.mode) paid live count init
        cond body env ≤
      Expr.loopBound true funs flags bounds (slots.map Slot.mode) paid live count init cond body env
    · rw [Nat.min_eq_left hle] at hT
      exact CodeSpecX.of_with hT (core false (fun h => nomatch h) fun h => by
        rw [hnp] at h; exact nomatch h)
    · rw [Nat.min_eq_right (by omega)] at hT
      exact CodeSpecX.of_with hT (core true (fun _ => hmin.1) fun _ => rfl)
  · rw [ite_eq_right hmin] at hT
    exact CodeSpecX.of_with hT (core _ id (Expr.paid_loop flags _ paid live count init cond body))

theorem specX_fold (hm : Runtime m) (hRA : strict = true → ReleaseAligned m)
    (hCopy : CopyCodeX strict m host) {Γ' : List Ty} {e : Elem} {t : Ty}
    (x : Var Γ' (.array e)) {init : Expr S Γ' t}
    {body : Expr S (.elem e :: t :: .word :: Γ') t}
    (initSpec : ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv init env
      slots paid live)
    (bodySpec : ∀ buy env slots paid live, CodeSpecInX strict (pool := pool) buy m funs flags bounds fits
      host pv body env slots paid live) :
    ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv (Expr.fold x init body)
      env slots paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt hAl hSafe hCap hBase hRoom
    hPlace rest Q hTrap hNext
  obtain ⟨_, _, _, hRep⟩ := hVars.1 _ x (by simp [Expr.uses])
  have hValue := Expr.foldExpand_denote x init body funs env hRep.array_size_lt
  have hLoop : CodeSpecX strict (pool := pool) m funs flags bounds fits host pv (Expr.foldExpand x init body)
      env slots paid live :=
    specX_loop hm hRA hCopy (specX_size hm (readReleaseX hm hRA) x) initSpec (specX_bool true)
      (fun buy => specX_letE hm hRA (specX_get (readReleaseX hm hRA) (.there (.there x))
        (specX_var hCopy (.there .here)))
        (bodySpec buy))
      env slots paid live
  simp only [CodeSpecX, trapFlag, Expr.foldExpand_uses, Expr.foldExpand_width,
    Expr.foldExpand_placeArgs, Expr.foldExpand_aborts, Expr.foldExpand_allocs,
    Expr.foldExpand_fits, Expr.foldExpand_mode, Expr.foldExpand_paid, Expr.foldExpand_code,
    hValue] at hLoop
  exact hLoop h base heap store s hh hpv hVars hAt hAl hSafe hCap hBase hRoom hPlace rest Q hTrap hNext

end Cases

end Verified
