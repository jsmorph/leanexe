import Verified.AlignedReaders

/-!
The constructs that bind or choose under the flag.  `After.coerceX` is `After.coerce` with the
copy as `CopyCodeX`: a copy leaves an aligned heap and an aligned owned value, and a value that
needs no copy keeps its alignment.  `wpX_releaseWhere` is `wp_releaseWhere` from
`wpX_releaseVars`, and `wpX_storeCode` carries `wp_storeCode`, whose code is free of 64-bit
accesses.  Each construct is its original in `ExprCorrect.lean` with these and the changes of
`AlignedScalar.lean`.  Storing words in locals from `base` on leaves the variables, which lie
below `base`, and so `HoldsA`, as they were (`HoldsA.agree`).
-/

namespace Verified

variable {pool : Bytes.LiteralPool}

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

theorem storeCode_free (h : Nat) : (loc : Nat) → (tys : List ValueType) →
    freeCode (storeCode h loc tys) = true
  | _, [] => rfl
  | loc, _ :: tys => by
    simp [storeCode, freeCode_append, freeCode, freeInst, storeCode_free h (loc + 1) tys]

/-- `wp_storeCode` under the flag. -/
theorem wpX_storeCode {α : Type} {strict : Bool} {m : Module} {Q : Assertion α}
    {store : Store α} {host : HostEnv α} {rest : Program} (vals : List Value) (h loc : Nat)
    (tys : List ValueType) (s : Locals) (vs : List Value) (hw : vals.length = tys.length)
    (hh : s.positions = h) (hLow : s.params.length ≤ loc) (hHigh : loc + tys.length ≤ s.positions)
    (hNext : ∀ s', Frame loc s s' → LocalsHold s' loc tys vals →
      (∀ j, loc + tys.length ≤ j → j < s.positions →
        s'.get j = s.get j ∧ s'.get (j + s.positions) = s.get (j + s.positions) ∧
          s'.get (j + 2 * s.positions) = s.get (j + 2 * s.positions)) →
      wpX strict m rest Q store { s' with values := vs } host) :
    wpX strict m (storeCode h loc tys ++ rest) Q store { s with values := vals.reverse ++ vs }
      host := by
  refine wpX_append_free (storeCode_free h loc tys) ?_
  have := wp_storeCode (m := m) (host := host) (rest := []) (Q := ThenX strict m rest Q host)
    vals h loc tys s vs hw hh hLow hHigh fun s' hF hold habove =>
      wp_nil.mpr (hNext s' hF hold habove)
  rwa [List.append_nil] at this

/-- `wp_releaseWhere` under the flag. -/
theorem wpX_releaseWhere {strict : Bool} {m : Module} (hm : Runtime m)
    (hRA : strict = true → ReleaseAligned m) {host : HostEnv Unit} {Γ : List Ty}
    {env : Env Γ} {slots : List Slot} {base : Nat} {sel live : Nat → Bool} {heap : Heap}
    {store : Store Unit} {s : Locals} {rest : Program} {Q : Assertion Unit}
    (hVars : Holds env slots live base heap store s) (hAt : heap.At store)
    (hA : strict = true → HoldsA env slots live heap store s)
    (hSel : ∀ i, sel i = true → live i = true)
    (hNext : ∀ heap' store', Evolves env slots live (fun i => live i && !sel i) base heap store
      s heap' store' s → heap'.top = heap.top →
      (strict = true → HoldsA env slots (fun i => live i && !sel i) heap' store' s) →
      wpX strict m rest Q store' s host) :
    wpX strict m (releaseWhere Γ slots sel ++ rest) Q store s host := by
  unfold releaseWhere
  have hSame : ∀ i < Γ.length,
      (((List.range Γ.length).filter sel).contains i) = sel i := by
    intro i hi
    cases h : sel i <;> simp [List.mem_filter, hi, h]
  refine wpX_releaseVars hm hRA _ (List.nodup_range.filter _) hVars hAt hA
    (fun i hi => hSel i (List.mem_filter.mp hi).2) fun heap' store' e hTop hA' =>
      hNext heap' store' ?_ hTop (fun hs => (hA' hs).live_mono fun i h => ?_)
  · exact ⟨e.step.mono (fun r hr => hr.congr fun i hi h1 h2 => ⟨h1, by rw [← hSame i hi]; exact h2⟩)
      (fun _ h => h), e.frame,
      e.holds.live_mono' fun i hi h => by rw [hSame i hi]; exact h⟩
  · simp only [Bool.and_eq_true] at h ⊢
    refine ⟨h.1, ?_⟩
    by_cases hi : i < Γ.length
    · rw [hSame i hi]; exact h.2
    · simp [List.mem_filter, hi]

/-- The release of the owned variables that `sel` selects among those live, which leaves
`top`. -/
theorem wp_releaseWhere {m : Module} (hm : Runtime m) {host : HostEnv Unit} {Γ : List Ty}
    {env : Env Γ} {slots : List Slot} {base : Nat} {sel live : Nat → Bool} {heap : Heap}
    {store : Store Unit} {s : Locals} {rest : Program} {Q : Assertion Unit}
    (hVars : Holds env slots live base heap store s) (hAt : heap.At store)
    (hSel : ∀ i, sel i = true → live i = true)
    (hNext : ∀ heap' store', Evolves env slots live (fun i => live i && !sel i) base heap store
      s heap' store' s → heap'.top = heap.top → wp m rest Q store' s host) :
    wp m (releaseWhere Γ slots sel ++ rest) Q store s host :=
  wpX_releaseWhere (strict := false) hm nofun hVars hAt nofun hSel
    (fun heap' store' a1 a2 _ => hNext heap' store' a1 a2)

section

variable {m : Module} {host : HostEnv Unit}

/-- `After.coerce` under the flag. -/
theorem After.coerceX {strict : Bool} (hCopy : CopyCodeX strict m host) {Γ : List Ty}
    {env : Env Γ} {slots : List Slot} {liveIn live : Nat → Bool} {h base base' : Nat}
    {heap : Heap} {store : Store Unit} {s : Locals} {t : Ty} {source target : Mode}
    {v : t.denote} {heap1 : Heap} {store1 : Store Unit} {s1 : Locals} {ws vs : List Value}
    {rest : Program} {Q : Assertion Unit}
    (a : After env slots liveIn live base heap store s t source v heap1 store1 s1 ws)
    (hA : strict = true → HoldsA env slots live heap1 store1 s1 ∧
      Ty.AlignedVal source store1 t ws v)
    (hTarget : source = .owned → target = .owned) (hBase' : base ≤ base')
    (hLow : s1.params.length ≤ base') (hh : s1.positions = h) (hRoom : base' + copyWidth t ≤ h)
    (hCap : store1.memoryCap m 0 ≤ 65535)
    (hTrap : source = .borrowed → target = .owned → t.scalar = false →
      TrapOK (!decide (heap1.Within store1 m (t.copyCost v))) Q)
    (hNext : ∀ heap2 store2 s2 ws2,
      After env slots liveIn live base heap store s t target v heap2 store2 s2 ws2 →
      heap2.top.toNat ≤ heap1.top.toNat + coerceCost t source target v →
      (source = .owned → store2 = store1 ∧ ws2 = ws) →
      (strict = true → HoldsA env slots live heap2 store2 s2 ∧
        Ty.AlignedVal target store2 t ws2 v) →
      wpX strict m rest Q store2 { s2 with values := ws2.reverse ++ vs } host) :
    wpX strict m (coerceCode h t source target base' ++ rest) Q store1
      { s1 with values := ws.reverse ++ vs } host := by
  by_cases hC : source = .borrowed ∧ target = .owned ∧ t.scalar = false
  · obtain ⟨hs, ht, hScalar⟩ := hC
    subst hs ht
    have hW : copyWidth t = t.width + t.copyScratch := by
      simp [copyWidth, hScalar]
    simp only [coerceCode, and_self, hScalar, ↓reduceIte, List.append_assoc]
    refine wpX_storeCode ws h base' t.types s1 vs a.rep.typed hh hLow
      (by rw [Ty.types_length, hh]; omega) fun s2 hF2 hold2 _ => ?_
    refine hCopy t a.step.at_ hCap (hTrap rfl rfl hScalar)
      (hF2.positions.trans hh) a.rep
      hold2 (le_refl _) (by rw [hF2.params]; omega)
      (by simp only [Locals.positions_values, hF2.positions, hh]; omega)
      (fun hs => ⟨(hA hs).1.1, (hA hs).2⟩)
      fun heap3 store3 s3 ws3 hStep3 hRep3 hF3 hTop3 hAl3 => ?_
    have hF13 : Frame base s1 s3 :=
      (hF2.mono hBase').trans (Frame.ofValues.trans (hF3.mono (by omega)))
    have hF : Frame base s s3 := a.frame.trans hF13
    have hStep0 := a.step
    simp only [Mode.fresh] at hStep0
    have hHolds3 := a.holds.step hStep3 fun _ _ _ _ _ _ _ _ => trivial
    refine hNext heap3 store3 s3 ws3 ⟨?_, hF, hHolds3.agree hF13, hRep3, ?_⟩
      (by simpa [coerceCost] using hTop3) nofun
      (fun hs => ⟨HoldsA.agree hHolds3 (HoldsA.step a.holds (hA hs).1 hStep3 (hAl3 hs).1
        fun _ _ _ _ _ _ _ _ => trivial) hF13, (hAl3 hs).2⟩)
    · exact hStep0.trans hStep3 fun _ hr => ⟨hr, fun _ => trivial⟩
    · intro u y hy _ wy hwy hly b hb c hc
      have hwy' := (a.holds.hold_agree hF13 hy hly).mp hwy
      obtain ⟨hSame, hFresh⟩ := a.holds.regions_after hStep3 hy hwy' hly fun _ _ => trivial
      rw [hSame] at hc
      exact regionsDisjoint_symm (hFresh c hc b hb)
  · have hEmpty : coerceCode h t source target base' = [] := by
      simp only [coerceCode]; rw [ite_eq_right hC]
    rw [hEmpty, List.nil_append]
    have hSame : source = target ∨ t.scalar = true := by
      cases source <;> cases target
      · exact Or.inl rfl
      · exact Or.inr (by simpa using hC)
      · exact absurd (hTarget rfl) nofun
      · exact Or.inl rfl
    rcases hSame with rfl | hScalar
    · exact hNext heap1 store1 s1 ws a (Nat.le_add_right _ _) (fun _ => ⟨rfl, rfl⟩) hA
    · refine hNext heap1 store1 s1 ws ⟨?_, a.frame, a.holds, ?_, ?_⟩ (Nat.le_add_right _ _)
        (fun _ => ⟨rfl, rfl⟩) (fun hs => ⟨(hA hs).1, Ty.AlignedVal.scalar hScalar⟩)
      · have hStep := a.step
        rw [Mode.fresh_scalar hScalar] at hStep ⊢
        exact hStep
      · cases target
        · exact a.rep.borrow
        · exact a.rep.owned hScalar
      · intro u y hy hm wy hwy hly b hb
        rw [Ty.regions_scalar t hScalar] at hb
        exact nomatch hb

end

/-- The invariant of a context with a first variable that holds `ws`, from that of the rest. -/
theorem HoldsA.push {Γ : List Ty} {env : Env Γ} {slots : List Slot} {heap : Heap}
    {store : Store Unit} {s : Locals} {t : Ty} {v : t.denote} {mode : Mode} {base : Nat}
    {live' : Nat → Bool} (h : HoldsA env slots (fun i => live' (i + 1)) heap store s)
    {ws : List Value} (hold : LocalsHold s base t.types ws) (hl : ws.length = t.width)
    (hv : Ty.AlignedVal mode store t ws v) :
    HoldsA (Env.cons v env) (⟨base, mode⟩ :: slots) live' heap store s := by
  refine ⟨h.1, fun t' x hx wx hwx hlx => ?_⟩
  cases x with
  | here =>
    change LocalsHold s base t.types wx at hwx
    obtain rfl := LocalsHold.unique hwx hold (hlx.trans hl.symm)
    exact hv
  | there y => exact h.2 t' y hx wx hwx hlx

/-- The invariant of a context without its first variable. -/
theorem HoldsA.pop {Γ : List Ty} {env : Env Γ} {slots : List Slot} {heap : Heap}
    {store : Store Unit} {s : Locals} {t : Ty} {v : t.denote} {sl : Slot} {live' : Nat → Bool}
    (h : HoldsA (Env.cons v env) (sl :: slots) live' heap store s) :
    HoldsA env slots (fun i => live' (i + 1)) heap store s :=
  ⟨h.1, fun t' x hx => h.2 t' (.there x) hx⟩

/-- A pair is aligned when its components are. -/
theorem Ty.AlignedVal.pair {mode : Mode} {store : Store Unit} {a b : Ty} {ws1 ws2 : List Value}
    {v1 : a.denote} {v2 : b.denote} (hl : ws1.length = a.width)
    (h1 : Ty.AlignedVal mode store a ws1 v1) (h2 : Ty.AlignedVal mode store b ws2 v2) :
    Ty.AlignedVal mode store (.pair a b) (ws1 ++ ws2) (v1, v2) := fun r hr => by
  rw [Ty.regions_append hl] at hr
  rcases List.mem_append.mp hr with hr | hr
  · exact h1 r hr
  · exact h2 r hr

/-- The first component of an aligned pair is aligned. -/
theorem Ty.AlignedVal.fst {mode : Mode} {store : Store Unit} {a b : Ty} {ws1 ws2 : List Value}
    {v : a.denote × b.denote} (h : Ty.AlignedVal mode store (.pair a b) (ws1 ++ ws2) v)
    (hl : ws1.length = a.width) : Ty.AlignedVal mode store a ws1 v.1 := fun r hr =>
  h r (by rw [Ty.regions_append hl]; exact List.mem_append_left _ hr)

/-- The second component of an aligned pair is aligned. -/
theorem Ty.AlignedVal.snd {mode : Mode} {store : Store Unit} {a b : Ty} {ws1 ws2 : List Value}
    {v : a.denote × b.denote} (h : Ty.AlignedVal mode store (.pair a b) (ws1 ++ ws2) v)
    (hl : ws1.length = a.width) : Ty.AlignedVal mode store b ws2 v.2 := fun r hr =>
  h r (by rw [Ty.regions_append hl]; exact List.mem_append_right _ hr)

section Cases

variable {S : List Sig} {m : Module} {funs : Funs S} {flags : Flags S} {bounds : Bounds S}
  {fits : Fits S} {host : HostEnv Unit} {pv : List Value} {strict : Bool}

/-- `ite_branch` under the flag. -/
theorem ite_branchX (hm : Runtime m) (hRA : strict = true → ReleaseAligned m)
    (hCopy : CopyCodeX strict m host) {Γ' : List Ty} {tTy : Ty} {c : Expr S Γ' .bool}
    {thenE elseE b : Expr S Γ' tTy} {buy : Bool}
    (bSpec : ∀ env slots paid live, CodeSpecInX strict (pool := pool) buy m funs flags bounds
      fits host pv b env slots paid live)
    {env : Env Γ'} {slots : List Slot} {paid : List Bool} {live : Nat → Bool} {h base : Nat}
    {heap : Heap} {store : Store Unit} {s : Locals} {rest : Program} {Q : Assertion Unit}
    (hh : s.positions = h) (hpv : s.params = pv)
    (hVars : Holds env slots (fun i => live i || (Expr.ite c thenE elseE).uses i) base heap
      store s)
    (hSafe : pool.Safe env slots (fun i => live i || (Expr.ite c thenE elseE).uses i)
      heap store s)
    (hCap : store.memoryCap m 0 ≤ 65535) (hBase : s.params.length ≤ base)
    (hRoomB : base + tTy.width + max b.width (copyWidth tTy) ≤ h)
    {B cA Db K : Nat} {wf P : Bool}
    (hTrap : TrapOK (trapFlag m (Expr.ite c thenE elseE) slots heap store B wf) Q)
    (hNext : ∀ heap' store' s' ws,
      After env slots (fun i => live i || (Expr.ite c thenE elseE).uses i) live base heap store s
        tTy ((Expr.ite c thenE elseE).mode (slots.map Slot.mode))
        ((Expr.ite c thenE elseE).denote funs env) heap' store' s' ws →
      (strict = true → HoldsA env slots live heap' store' s' ∧
        Ty.AlignedVal ((Expr.ite c thenE elseE).mode (slots.map Slot.mode)) store' tTy ws
          ((Expr.ite c thenE elseE).denote funs env)) →
      (wf = true → heap'.top.toNat +
          (if P = true then tTy.pot store' ws ((Expr.ite c thenE elseE).denote funs env) else 0) ≤
        heap.top.toNat + B) →
      wpX strict m rest Q store' { s' with values := ws.reverse ++ s.values } host)
    {heap1 : Heap} {store1 : Store Unit} {s1 : Locals}
    (e1 : Evolves env slots (fun i => live i || (Expr.ite c thenE elseE).uses i)
      (fun i => live i || thenE.uses i || elseE.uses i) base heap store s heap1 store1
      { s1 with values := s.values })
    (hAl1 : strict = true → HoldsA env slots (fun i => live i || thenE.uses i || elseE.uses i)
      heap1 store1 { s1 with values := s.values })
    (hTop1 : wf = true → heap1.top.toNat ≤ heap.top.toNat + cA)
    (hB : B = cA + (Db + (b.allocs funs flags bounds (slots.map Slot.mode) paid live env +
      coerceCost tTy (b.mode (slots.map Slot.mode))
        ((Expr.ite c thenE elseE).mode (slots.map Slot.mode)) (b.denote funs env) +
      (b.buysIn buy funs flags (slots.map Slot.mode) paid live env + K))))
    (hDb : dyingPot store s env slots paid (fun i => live i || b.uses i) live ≤ Db)
    (hbd : wf = true → b.fits funs fits env = true)
    (hbPlace : b.placeArgs = true)
    (hbu : ∀ i, b.uses i = true → (thenE.uses i || elseE.uses i) = true)
    (hba : b.aborts = true → (Expr.ite c thenE elseE).aborts = true)
    (hval : b.denote funs env = (Expr.ite c thenE elseE).denote funs env)
    (hbm : b.mode (slots.map Slot.mode) = .owned →
      (Expr.ite c thenE elseE).mode (slots.map Slot.mode) = .owned)
    (hPm : P = true → (Expr.ite c thenE elseE).mode (slots.map Slot.mode) = .owned)
    (hK : P = true → b.paidIn buy flags (slots.map Slot.mode) paid live = false →
      tTy.credit (b.denote funs env) ≤ K)
    (Qb : Assertion Unit) (hQbTrap : ∀ st, Q (.Trap st "unreachable") → Qb (.Trap st "unreachable"))
    (hQb : ∀ st' s', wpX strict m (loadCode h base tTy.types ++ rest) Q st'
      { s' with values := s.values } host → Qb (.Fallthrough st' s')) :
    wpX strict m (releaseWhere Γ' slots (fun i => (live i || thenE.uses i || elseE.uses i) &&
        !(live i || b.uses i)) ++
      (b.code (pool := pool) h slots (base + tTy.width) live ++
        (coerceCode h tTy (b.mode (slots.map Slot.mode))
          ((Expr.ite c thenE elseE).mode (slots.map Slot.mode)) (base + tTy.width) ++
          storeCode h base tTy.types))) Qb store1 { s1 with values := s.values } host := by
  have hp1 : s1.params = s.params := e1.frame.params
  have hh1 : s1.positions = h := e1.frame.positions.trans hh
  have hTrapB : TrapOK (trapFlag m (Expr.ite c thenE elseE) slots heap store B wf) Qb :=
    hTrap.imp hQbTrap
  have hwf : (!wf) = false → wf = true := fun hd => by simpa using hd
  have hbd' : (!wf) = false → b.fits funs fits env = true := fun hd => hbd (hwf hd)
  have hSubMid : ∀ i, (live i || b.uses i) = true →
      (live i || thenE.uses i || elseE.uses i) = true := fun i =>
    ite_live_branch _ _ _ _ (hbu i)
  refine wpX_releaseWhere hm hRA e1.holds e1.step.at_ hAl1
    (fun i h => by simp only [Bool.and_eq_true] at h; exact h.1)
    fun heap2 store2 e2 hTop2 hA2 => ?_
  have hEq : (fun i => (live i || thenE.uses i || elseE.uses i) &&
      !((live i || thenE.uses i || elseE.uses i) && !(live i || b.uses i))) =
      (fun i => live i || b.uses i) := by
    funext i
    exact live_released _ _ (hSubMid i)
  rw [hEq] at e2 hA2
  have hEntry : ∀ i, (live i || thenE.uses i || elseE.uses i) = true →
      (live i || (Expr.ite c thenE elseE).uses i) = true := fun i h => by
    simp only [Expr.uses]; exact ite_live_entry _ _ _ _ h
  have hDb2 : dyingPot store2 { s1 with values := s.values } env slots paid
      (fun i => live i || b.uses i) live =
        dyingPot store s env slots paid (fun i => live i || b.uses i) live := by
    rw [dyingPot_evolves e1.holds e2 hSubMid _ _ fun _ h => h,
      dyingPot_evolves hVars e1 hEntry _ _ hSubMid]
  rw [← List.append_nil (storeCode h base tTy.types)]
  have hbw := Nat.le_max_left b.width (copyWidth tTy)
  have hcw := Nat.le_max_right b.width (copyWidth tTy)
  refine bSpec env slots paid live h (base + tTy.width) heap2 store2 { s1 with values := s.values }
    hh1 (hp1.trans hpv) (e2.holds.mono (by omega)) e2.step.at_ hA2
    ((hSafe.evolves hVars e1 hEntry).evolves e1.holds e2 hSubMid)
    (by rw [e2.step.cap m, e1.step.cap m]; exact hCap)
    (by show s1.params.length ≤ base + tTy.width; rw [hp1]; omega)
    (by omega) hbPlace _ _ (hTrapB.part (fun h => by
          cases hw : wf
          · rfl
          · simp [hbd hw] at h) (fun h => by
          simp only [Bool.or_eq_true] at h ⊢; exact h.imp_left hba) fun hd hw => by
        rw [hB] at hw
        exact (hw.after (heap1 := heap2) (store1 := store2)
          (by have := hTop1 (hwf hd); have := congrArg UInt64.toNat hTop2; omega)
          (by rw [e2.step.cap m, e1.step.cap m])).mono (by rw [hDb2]; omega))
    fun heap3 store3 s3 ws3 a3 hAl3 hTop3 => ?_
  have hp3 : s3.params = s.params := a3.frame.params.trans hp1
  have hh3 : s3.positions = h := a3.frame.positions.trans hh1
  refine After.coerceX hCopy a3 hAl3 hbm le_rfl (by rw [hp3]; omega) hh3 (by omega)
    (by rw [a3.step.cap m, e2.step.cap m, e1.step.cap m]; exact hCap)
    (fun hs ht _ => hTrapB.alloc (by
      have := (Expr.ite c thenE elseE).mode_owned (slots.map Slot.mode) ht
      rw [Slot.any_map] at this; exact this) fun hd hw => by
        have h3 := hw.shift (heap1 := heap3) (store1 := store3)
          (c1 := cA + Db + b.allocs funs flags bounds (slots.map Slot.mode) paid live env +
            b.buysIn buy funs flags (slots.map Slot.mode) paid live env)
          (c2 := coerceCost tTy (b.mode (slots.map Slot.mode))
            ((Expr.ite c thenE elseE).mode (slots.map Slot.mode)) (b.denote funs env))
          (by have := hTop3 (hbd' hd); have := hTop1 (hwf hd); have := congrArg UInt64.toNat hTop2
              omega)
          (by rw [hB]; omega)
          (by rw [a3.step.cap m, e2.step.cap m, e1.step.cap m])
        simpa [coerceCost, hs, ht] using h3)
    fun heap4 store4 s4 ws4 a4 hTop4 hSame4 hAl4 => ?_
  have hp4 : s4.params = s.params := a4.frame.params.trans hp1
  have hh4 : s4.positions = h := a4.frame.positions.trans hh1
  refine wpX_storeCode ws4 h base tTy.types s4 s.values a4.rep.typed hh4 (by rw [hp4]; omega)
    (by rw [Ty.types_length, hh4]; omega) fun s5 hF5 hold _ => ?_
  rw [wpX_nil]
  refine hQb _ _ (wpX_loadCode ws4 a4.rep.typed (hF5.positions.trans hh4) hold ?_)
  have hLower := a4.lower e2.holds (Nat.le_add_right _ _) (fun i h => by simp [h])
  have e12 := Evolves.trans hVars e1 e2 hSubMid hEntry
  have aAll := After.prepend hVars e12 hLower (fun i h => hEntry i (hSubMid i h))
    (fun i h => by simp [h])
  have hF45 : Frame base s4 { s5 with values := s.values } := hF5.trans Frame.ofValues
  have hFrame : Frame base s { s5 with values := s.values } := aAll.frame.trans hF45
  rw [hval] at aAll
  refine hNext heap4 store4 _ ws4 ⟨aAll.step, hFrame, aAll.holds.agree hF45, aAll.rep, ?_⟩
    (fun hs => ⟨HoldsA.agree hLower.holds (hAl4 hs).1 hF45, hval ▸ (hAl4 hs).2⟩)
    fun hd => by
      have := hTop1 hd; have := hTop3 (hbd hd); have := congrArg UInt64.toNat hTop2
      have hPot : (if P = true then
            tTy.pot store4 ws4 ((Expr.ite c thenE elseE).denote funs env) else 0) ≤
          (if b.paidIn buy flags (slots.map Slot.mode) paid live = true then
            tTy.pot store3 ws3 (b.denote funs env) else 0) + K := by
        by_cases hP : P = true
        · by_cases hbP : b.paidIn buy flags (slots.map Slot.mode) paid live = true
          · obtain ⟨rfl, rfl⟩ := hSame4 (Expr.mode_of_paidIn b hbP)
            rw [ite_eq_left hP, ite_eq_left hbP, ← hval]
            omega
          · have hRep4 := a4.rep
            rw [hPm hP] at hRep4
            have hle := Ty.pot_le_credit tTy ws4 _ hRep4
            have hk := hK hP (by simpa using hbP)
            rw [ite_eq_left hP, ite_eq_right hbP, ← hval]
            omega
        · rw [ite_eq_right hP]
          omega
      rw [hB]; omega
  exact aAll.apart.agree aAll.holds hF45

/-- An `if`: the condition, then each branch as `ite_branch` describes. -/
theorem specX_ite (hm : Runtime m) (hRA : strict = true → ReleaseAligned m)
    (hCopy : CopyCodeX strict m host) {Γ' : List Ty} {tTy : Ty} {c : Expr S Γ' .bool}
    {thenE elseE : Expr S Γ' tTy} {buy : Bool}
    (cSpec : ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv c env slots paid live)
    (thenSpec : ∀ env slots paid live, CodeSpecInX strict (pool := pool) buy m funs flags bounds fits host pv
        thenE env slots paid live)
    (elseSpec : ∀ env slots paid live, CodeSpecInX strict (pool := pool) buy m funs flags bounds fits host pv
        elseE env slots paid live) :
    ∀ env slots paid live, CodeSpecInX strict (pool := pool) buy m funs flags bounds fits host pv
        (Expr.ite c thenE elseE) env slots paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt hAl hSafe hCap hBase hRoom
      hPlace rest Q hTrap
    hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hc : c.width ≤ max c.width (tTy.width + max (max thenE.width elseE.width)
      (copyWidth tTy)) := Nat.le_max_left ..
  have hb : tTy.width + max (max thenE.width elseE.width) (copyWidth tTy) ≤
      max c.width (tTy.width + max (max thenE.width elseE.width) (copyWidth tTy)) :=
    Nat.le_max_right ..
  have ht : thenE.width ≤ max thenE.width elseE.width := Nat.le_max_left ..
  have he : elseE.width ≤ max thenE.width elseE.width := Nat.le_max_right ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  obtain ⟨⟨hPlaceC, hPlaceT⟩, hPlaceE⟩ := hPlace
  simp only [Expr.code, Expr.usesFast_eq, List.append_assoc, List.cons_append, List.nil_append]
  have hMid : ∀ i, ((live i || thenE.uses i || elseE.uses i) || c.uses i) = true →
      (live i || (Expr.ite c thenE elseE).uses i) = true := by
    intro i h; simp only [Expr.uses]; exact ite_live_cond _ _ _ _ h
  -- The variables that die in the `if` die in the condition or after it.
  have hSplitI : dyingPot store s env slots paid
      (fun i => live i || (Expr.ite c thenE elseE).uses i)
      live =
        dyingPot store s env slots paid (fun i => (live i || thenE.uses i || elseE.uses i) ||
          c.uses i) (fun i => live i || thenE.uses i || elseE.uses i) +
        dyingPot store s env slots paid (fun i => live i || thenE.uses i || elseE.uses i) live := by
    rw [dyingPot_split _ (fun i => live i || thenE.uses i || elseE.uses i) _
      (fun i h => hMid i (by simp [h])) (fun i h => by simp [h])]
    congr 1
    exact dyingPot_congr (fun i => by
      simp only [Expr.uses]
      cases live i <;> cases c.uses i <;> cases thenE.uses i <;> cases elseE.uses i <;> rfl)
      fun _ => rfl
  refine cSpec env slots paid _ h base heap store s hh hpv (hVars.live_mono hMid) hAt
    (fun hs => (hAl hs).live_mono hMid) (hSafe.mono hMid) hCap hBase
    (by omega) hPlaceC _ _
    (hTrap.part (by flag_tac) (fun h => by simp only [Expr.aborts]; exact ite_trap_cond _ _ _ _ h)
      fun _ hw => hw.mono (by rw [hSplitI]; simp only [Expr.allocs]; omega))
    fun heap1 store1 s1 ws1 a1 hAl1 hTop1 => ?_
  have hR1 := a1.rep
  simp only [Ty.rep_bool] at hR1
  subst hR1
  have e1 : Evolves env slots (fun i => live i || (Expr.ite c thenE elseE).uses i)
      (fun i => live i || thenE.uses i || elseE.uses i) base heap store s heap1 store1
      { s1 with values := s.values } := by
    have e := (a1.toEvolves rfl).values s.values
    exact ⟨e.step.mono (fun r hr => hr.mono fun i h1 h2 => ⟨hMid i h1, h2⟩) fun _ h => h,
      e.frame, e.holds⟩
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    wpX_eqzI64_cons]
  have hAlE1 : strict = true → HoldsA env slots (fun i => live i || thenE.uses i || elseE.uses i)
      heap1 store1 { s1 with values := s.values } := fun hs => (hAl1 hs).1.values _
  refine wpX_iff_cons rfl ?_
  have hModeT : thenE.mode (slots.map Slot.mode) = .owned →
      (Expr.ite c thenE elseE).mode (slots.map Slot.mode) = .owned :=
    fun h => by simp [Expr.mode, h, Mode.join]
  have hModeE : elseE.mode (slots.map Slot.mode) = .owned →
      (Expr.ite c thenE elseE).mode (slots.map Slot.mode) = .owned := fun h => by
    simp only [Expr.mode, h]
    cases thenE.mode (slots.map Slot.mode) <;> rfl
  have hRoomT : base + tTy.width + max thenE.width (copyWidth tTy) ≤ h := by
    have := Nat.max_le.mpr ⟨ht.trans (Nat.le_max_left _ (copyWidth tTy)), Nat.le_max_right _ _⟩
    omega
  have hRoomE : base + tTy.width + max elseE.width (copyWidth tTy) ≤ h := by
    have := Nat.max_le.mpr ⟨he.trans (Nat.le_max_left _ (copyWidth tTy)), Nat.le_max_right _ _⟩
    omega
  have hNextB : ∀ heap' store' s' ws,
      After env slots (fun i => live i || (Expr.ite c thenE elseE).uses i) live base heap store s
        tTy ((Expr.ite c thenE elseE).mode (slots.map Slot.mode))
        ((Expr.ite c thenE elseE).denote funs env) heap' store' s' ws →
      (strict = true → HoldsA env slots live heap' store' s' ∧
        Ty.AlignedVal ((Expr.ite c thenE elseE).mode (slots.map Slot.mode)) store' tTy ws
          ((Expr.ite c thenE elseE).denote funs env)) →
      ((Expr.ite c thenE elseE).fits funs fits env = true →
        heap'.top.toNat +
            (if (Expr.ite c thenE elseE).paidIn buy flags (slots.map Slot.mode) paid live = true then
              tTy.pot store' ws ((Expr.ite c thenE elseE).denote funs env) else 0) ≤
          heap.top.toNat +
          (dyingPot store s env slots paid (fun i => live i || (Expr.ite c thenE elseE).uses i)
            live + (Expr.ite c thenE elseE).allocs funs flags bounds (slots.map Slot.mode) paid live
              env +
            (Expr.ite c thenE elseE).buysIn buy funs flags (slots.map Slot.mode) paid live env)) →
      wpX strict m rest Q store' { s' with values := ws.reverse ++ s.values } host :=
    fun heap' store' s' ws a hA hT => hNext heap' store' s' ws a hA fun hf => by
      have := hT hf; omega
  have hPm : (Expr.ite c thenE elseE).paidIn buy flags (slots.map Slot.mode) paid live = true →
      (Expr.ite c thenE elseE).mode (slots.map Slot.mode) = .owned :=
    Expr.mode_of_paidIn _
  have hTopC : (Expr.ite c thenE elseE).fits funs fits env = true →
      heap1.top.toNat ≤ heap.top.toNat +
        (dyingPot store s env slots paid (fun i => (live i || thenE.uses i || elseE.uses i) ||
          c.uses i) (fun i => live i || thenE.uses i || elseE.uses i) +
          c.allocs funs flags bounds (slots.map Slot.mode) paid
            (fun i => live i || thenE.uses i || elseE.uses i) env) := fun hd => by
    have := hTop1 (by simp only [Expr.fits, Bool.and_eq_true] at hd; exact hd.1)
    omega
  cases hcv : c.denote funs env
  · simp (config := { decide := true }) only [↓reduceIte]
    have hBuys : (Expr.ite c thenE elseE).buysIn buy funs flags (slots.map Slot.mode) paid live env =
        elseE.buysIn buy funs flags (slots.map Slot.mode) paid live env +
          (if buy then tTy.buyCost (thenE.bodyPaid flags (slots.map Slot.mode) paid live)
            (elseE.bodyPaid flags (slots.map Slot.mode) paid live) (elseE.denote funs env)
          else 0) := by
      cases buy <;> simp [Expr.buysIn, Expr.buys, hcv]
    exact ite_branchX hm hRA hCopy elseSpec hh hpv hVars hSafe hCap hBase hRoomE hTrap hNextB e1 hAlE1
      hTopC
      (P := (Expr.ite c thenE elseE).paidIn buy flags (slots.map Slot.mode) paid live)
      (K := if buy then tTy.buyCost (thenE.bodyPaid flags (slots.map Slot.mode) paid live)
        (elseE.bodyPaid flags (slots.map Slot.mode) paid live) (elseE.denote funs env) else 0)
      (Db := dyingPot store s env slots paid (fun i => live i || thenE.uses i || elseE.uses i) live)
      (by rw [hSplitI, hBuys]; simp only [Expr.allocs, Expr.mode, hcv, Bool.false_eq_true, ↓reduceIte]
          omega)
      (show dyingPot store s env slots paid (fun i => live i || elseE.uses i) live ≤
          dyingPot store s env slots paid (fun i => live i || thenE.uses i || elseE.uses i) live
        from dyingPot_mono (fun i h => by
          simp only [Bool.or_eq_true] at h ⊢; rcases h with h | h <;> simp [h]) fun _ h => h)
      (show (Expr.ite c thenE elseE).fits funs fits env = true → elseE.fits funs fits env = true
        from fun h => by
          simp only [Expr.fits, hcv, Bool.and_eq_true, Bool.false_eq_true, ↓reduceIte] at h
          exact h.2) hPlaceE
      (fun i h => by simp [h]) (fun h => by simp [Expr.aborts, h])
      (by simp [Expr.denote, hcv]) hModeE hPm
      (fun hP hb => by
        cases buy
        · simp only [Expr.paidIn, Bool.false_eq_true, ↓reduceIte, Expr.paid,
            Bool.and_eq_true] at hP hb
          simp [hP.2] at hb
        · simp only [Expr.paidIn, ↓reduceIte, Expr.bodyPaid, Bool.or_eq_true] at hP hb
          have hT : thenE.bodyPaid flags (slots.map Slot.mode) paid live = true :=
            hP.resolve_right (by simp [hb])
          simp [Ty.buyCost, hT, hb]) _ (fun _ h => h)
      fun _ _ h => by simpa using h
  · simp (config := { decide := true }) only [↓reduceIte]
    have hBuys : (Expr.ite c thenE elseE).buysIn buy funs flags (slots.map Slot.mode) paid live env =
        thenE.buysIn buy funs flags (slots.map Slot.mode) paid live env +
          (if buy then tTy.buyCost (elseE.bodyPaid flags (slots.map Slot.mode) paid live)
            (thenE.bodyPaid flags (slots.map Slot.mode) paid live) (thenE.denote funs env)
          else 0) := by
      cases buy <;> simp [Expr.buysIn, Expr.buys, hcv]
    exact ite_branchX hm hRA hCopy thenSpec hh hpv hVars hSafe hCap hBase hRoomT hTrap hNextB e1 hAlE1
      hTopC
      (P := (Expr.ite c thenE elseE).paidIn buy flags (slots.map Slot.mode) paid live)
      (K := if buy then tTy.buyCost (elseE.bodyPaid flags (slots.map Slot.mode) paid live)
        (thenE.bodyPaid flags (slots.map Slot.mode) paid live) (thenE.denote funs env) else 0)
      (Db := dyingPot store s env slots paid (fun i => live i || thenE.uses i || elseE.uses i) live)
      (by rw [hSplitI, hBuys]; simp only [Expr.allocs, Expr.mode, hcv, ↓reduceIte]; omega)
      (show dyingPot store s env slots paid (fun i => live i || thenE.uses i) live ≤
          dyingPot store s env slots paid (fun i => live i || thenE.uses i || elseE.uses i) live
        from dyingPot_mono (fun i h => by
          simp only [Bool.or_eq_true] at h ⊢; rcases h with h | h <;> simp [h]) fun _ h => h)
      (fun h => by simp only [Expr.fits, hcv, Bool.and_eq_true] at h; simpa using h.2) hPlaceT
      (fun i h => by simp [h]) (fun h => by simp [Expr.aborts, h])
      (by simp [Expr.denote, hcv]) hModeT hPm
      (fun hP hb => by
        cases buy
        · simp only [Expr.paidIn, Bool.false_eq_true, ↓reduceIte, Expr.paid,
            Bool.and_eq_true] at hP hb
          simp [hP.1] at hb
        · simp only [Expr.paidIn, ↓reduceIte, Expr.bodyPaid, Bool.or_eq_true] at hP hb
          have hE : elseE.bodyPaid flags (slots.map Slot.mode) paid live = true :=
            hP.resolve_left (by simp [hb])
          simp [Ty.buyCost, hE, hb]) _ (fun _ h => h)
      fun _ _ h => by simpa using h

/-- A `let` binding: the value's code, the store of its words from local `base` on, the release
of the value when it is owned and the body does not use it, and the body's code. -/
theorem specX_letE (hm : Runtime m) (hRA : strict = true → ReleaseAligned m) {Γ' : List Ty} {sTy tTy : Ty} {value : Expr S Γ' sTy}
    {body : Expr S (sTy :: Γ') tTy} {buy : Bool}
    (valueSpec : ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv value env
        slots paid live)
    (bodySpec : ∀ env slots paid live, CodeSpecInX strict (pool := pool) buy m funs flags bounds fits host pv
        body env slots paid live) :
    ∀ env slots paid live, CodeSpecInX strict (pool := pool) buy m funs flags bounds fits host pv
        (Expr.letE value body) env slots paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt hAl hSafe hCap hBase hRoom
      hPlace rest Q hTrap
    hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hValueRoom : value.width ≤ max value.width body.width := Nat.le_max_left ..
  have hBodyRoom : body.width ≤ max value.width body.width := Nat.le_max_right ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, Expr.usesFast_eq, List.append_assoc]
  have hV : ∀ i, ((live i || body.uses (i + 1)) || value.uses i) = true →
      (live i || (Expr.letE value body).uses i) = true := fun i h => by
    simp only [Expr.uses]; exact live_seq _ _ _ h
  -- The variables that die in the `let` die in the value or in the body.
  have hSplitL : dyingPot store s env slots paid
      (fun i => live i || (Expr.letE value body).uses i) live =
        dyingPot store s env slots paid (fun i => live i || body.uses (i + 1) || value.uses i)
          (fun i => live i || body.uses (i + 1)) +
        dyingPot store s env slots paid (fun i => live i || body.uses (i + 1)) live := by
    rw [dyingPot_split _ (fun i => live i || body.uses (i + 1)) _
      (fun i h => hV i (by simp [h])) (fun i h => by simp [h])]
    congr 1
    exact dyingPot_congr (fun i => by
      simp only [Expr.uses]
      cases live i <;> cases value.uses i <;> cases body.uses (i + 1) <;> rfl) fun _ => rfl
  refine valueSpec env slots paid (fun i => live i || body.uses (i + 1)) h (base + sTy.width) heap
    store s hh hpv ((hVars.mono (by omega)).live_mono hV) hAt
    (fun hs => (hAl hs).live_mono hV) (hSafe.mono hV) hCap (by omega) (by omega) hPlace.1 _
        _
    (hTrap.part (by flag_tac) (fun h => by simp only [Expr.aborts]; exact trap_left _ _ _ h)
      fun _ hw => hw.mono (by rw [hSplitL]; simp only [Expr.allocs]; omega))
    fun heap1 store1 s1 ws1 a1 hAl1 hTop1 => ?_
  have hp1 : s1.params = s.params := a1.frame.params
  have hh1 : s1.positions = h := a1.frame.positions.trans hh
  have a1' := a1.lower (hVars.live_mono hV) (Nat.le_add_right _ _) fun i h => by simp [h]
  refine wpX_storeCode ws1 h base sTy.types s1 s.values a1.rep.typed hh1 (by rw [hp1]; omega)
    (by rw [Ty.types_length, hh1]; omega) fun s2 hF2 hold _ => ?_
  have f2 : Frame base s1 { s2 with values := s.values } := hF2.trans Frame.ofValues
  have hp2 : s2.params = s.params := hF2.params.trans hp1
  have hh2 : ({ s2 with values := s.values } : Locals).positions = h := f2.positions.trans hh1
  have hold' : LocalsHold { s2 with values := s.values } base sTy.types ws1 := hold
  -- The body's context: the value as variable 0, in the locals from `base` on.
  have hVarsB : Holds (Env.cons (value.denote funs env) env)
      (⟨base, value.mode (slots.map Slot.mode)⟩ :: slots)
      (fun i => i == 0 || shift 1 live i || body.uses i) (base + sTy.width) heap1 store1
      { s2 with values := s.values } :=
    Holds.push ((a1'.holds.agree f2).live_mono fun i h => by
        simpa using h)
      hold' a1.rep ((a1'.apart.agree a1'.holds f2).live_mono
        fun i h => by simpa using h)
  have hAlB : strict = true → HoldsA (Env.cons (value.denote funs env) env)
      (⟨base, value.mode (slots.map Slot.mode)⟩ :: slots)
      (fun i => i == 0 || shift 1 live i || body.uses i) heap1 store1
      { s2 with values := s.values } := fun hs =>
    HoldsA.push ((HoldsA.agree a1'.holds (hAl1 hs).1 f2).live_mono fun i h => by simpa using h)
      hold' a1.rep.length (hAl1 hs).2
  have hSafeB : pool.Safe (Env.cons (value.denote funs env) env)
      (⟨base, value.mode (slots.map Slot.mode)⟩ :: slots)
      (fun i => i == 0 || shift 1 live i || body.uses i) heap1 store1
      { s2 with values := s.values } :=
    (hSafe.mono hV).bind (hVars.live_mono hV) a1'
      (fun i hi => by simp [hi]) (fun i hi => by simpa using hi) f2 hold'
  have hRelease : (if value.mode (slots.map Slot.mode) = .owned ∧ body.uses 0 = false then
      releaseCode sTy base else []) =
      (if body.uses 0 = false then [0] else []).flatMap
        (releaseVar (sTy :: Γ') (⟨base, value.mode (slots.map Slot.mode)⟩ :: slots)) := by
    cases body.uses 0 <;> cases value.mode (slots.map Slot.mode) <;> simp [releaseVar]
  rw [hRelease]
  have hd1 : (Expr.letE value body).fits funs fits env = true → value.fits funs fits env = true :=
    fun hd => by simp only [Expr.fits, Bool.and_eq_true] at hd; exact hd.1
  have hd3 : (Expr.letE value body).fits funs fits env = true →
      body.fits funs fits (.cons (value.denote funs env) env) = true := fun hd => by
    simp only [Expr.fits, Bool.and_eq_true] at hd; exact hd.2
  refine wpX_releaseVars hm hRA _ (by split <;> simp) hVarsB a1.step.at_ hAlB (by split <;> simp)
    fun heap2 store2 e2 hTop2 hA2 => ?_
  have e2' := e2.mono (live' := fun i => shift 1 live i || body.uses i) fun i h => by
    cases i with
    | zero =>
      have h0 : body.uses 0 = true := by simpa [shift] using h
      simp [h0]
    | succ k => split <;> simpa using h
  have hA2' : strict = true → HoldsA (Env.cons (value.denote funs env) env)
      (⟨base, value.mode (slots.map Slot.mode)⟩ :: slots)
      (fun i => shift 1 live i || body.uses i) heap2 store2 { s2 with values := s.values } :=
    fun hs => (hA2 hs).live_mono fun i h => by
      cases i with
      | zero =>
        have h0 : body.uses 0 = true := by simpa [shift] using h
        simp [h0]
      | succ k => split <;> simpa using h
  -- The body's dying variables: the value's variable, whose potential is the value's when paid,
  -- and the others, whose potential the value's code and the release keep.
  have hDb : dyingPot store2 { s2 with values := s.values } (Env.cons (value.denote funs env) env)
      (⟨base, value.mode (slots.map Slot.mode)⟩ :: slots)
      (value.paid flags (slots.map Slot.mode) paid (fun i => live i || body.uses (i + 1)) :: paid)
      (fun i => shift 1 live i || body.uses i) (shift 1 live) ≤
        (if value.paid flags (slots.map Slot.mode) paid (fun i => live i || body.uses (i + 1)) = true then
          sTy.pot store1 ws1 (value.denote funs env) else 0) +
        dyingPot store s env slots paid (fun i => live i || body.uses (i + 1)) live := by
    rw [dyingPot_evolves hVarsB e2' (fun i h => by
      simp only [Bool.or_eq_true] at h ⊢; rcases h with h | h <;> simp [h]) _ _ fun _ h => h,
      dyingPot_cons]
    have hTail : dyingPot store1 { s2 with values := s.values } env slots paid
        (fun i => shift 1 live (i + 1) || body.uses (i + 1)) (fun i => shift 1 live (i + 1)) =
          dyingPot store s env slots paid (fun i => live i || body.uses (i + 1)) live := by
      rw [dyingPot_congr (L0' := fun i => live i || body.uses (i + 1)) (L1' := live)
        (fun i => by simp [shift]) (fun i => by simp [shift])]
      exact dyingPot_step (hVars.live_mono hV) a1'.step (a1'.frame.trans f2)
        (fun i h => by simp [h]) _ _ fun _ h => h
    rw [hTail, hold'.read_eq (by rw [a1.rep.length, Ty.types_length])]
    refine Nat.add_le_add_right ?_ _
    split
    · next hc =>
      simp only [Bool.and_eq_true] at hc
      simp only [hc.1.2, ↓reduceIte, le_refl]
    · exact Nat.zero_le _
  have hbuys : (Expr.letE value body).buysIn buy funs flags (slots.map Slot.mode) paid live env =
      body.buysIn buy funs flags ((⟨base, value.mode (slots.map Slot.mode)⟩ :: slots).map Slot.mode)
        (value.paid flags (slots.map Slot.mode) paid (fun i => live i || body.uses (i + 1)) ::
          paid) (shift 1 live) (.cons (value.denote funs env) env) :=
    rfl
  refine bodySpec _ _
    (value.paid flags (slots.map Slot.mode) paid (fun i => live i || body.uses (i + 1)) :: paid)
    (shift 1 live) h (base + sTy.width) heap2 store2
    { s2 with values := s.values } hh2 (hp2.trans hpv) e2'.holds e2'.step.at_ hA2'
    (hSafeB.evolves hVarsB e2' (fun i hi => live_right _ _ _ hi))
    (by rw [e2'.step.cap m, a1.step.cap m]; exact hCap)
    (by show s2.params.length ≤ base + sTy.width; rw [hp2]; omega)
    (by omega) hPlace.2 _ _
    (hTrap.part (by flag_tac) (fun h => by
      have hmo := value.mode_owned (slots.map Slot.mode)
      rw [Slot.any_map] at hmo
      simp only [List.any_cons, Expr.aborts] at h ⊢
      exact let_trap_body _ _ _ _ (fun hv => hmo (by simpa using hv)) h) fun hd hw => by
        have h1 := hTop1 (hd1 (fits_of_not hd)); have := congrArg UInt64.toNat hTop2
        dsimp only at h1
        refine hw.of_le ?_ (by rw [e2'.step.cap m, a1.step.cap m])
        rw [hSplitL, hbuys]
        simp only [Expr.allocs, List.map_cons]
        omega)
    fun heap3 store3 s3 ws3 aB hAlB3 hTop3 => ?_
  have aB' := After.prepend hVarsB e2' aB (fun i h => live_right _ _ _ h) fun i h => by simp [h]
  exact hNext heap3 store3 s3 ws3
    ((After.bind (hVars.live_mono hV) a1' f2 hold' aB' (fun i h => by simpa using h)
      (fun i h => by simp [h]) fun i h => by simp [h]).liveIn hV)
    (fun hs => ⟨(hAlB3 hs).1.pop.live_mono fun i h => by simpa [shift] using h, (hAlB3 hs).2⟩)
    fun hd => by
      have h1 := hTop1 (hd1 hd); have h3 := hTop3 (hd3 hd); have := congrArg UInt64.toNat hTop2
      dsimp only at h1
      have hpot : (if (Expr.letE value body).paidIn buy flags (slots.map Slot.mode) paid live = true
            then tTy.pot store3 ws3 ((Expr.letE value body).denote funs env) else 0) =
          (if body.paidIn buy flags ((⟨base, value.mode (slots.map Slot.mode)⟩ :: slots).map Slot.mode)
              (value.paid flags (slots.map Slot.mode) paid (fun i => live i || body.uses (i + 1)) ::
                paid) (shift 1 live) = true then
            tTy.pot store3 ws3 (body.denote funs (.cons (value.denote funs env) env)) else 0) :=
        rfl
      rw [hpot, hbuys, hSplitL]
      simp only [Expr.allocs, List.map_cons] at h3 ⊢
      omega

section

variable {pool : Bytes.LiteralPool}
variable {S : List Sig} {m : Module} {funs : Funs S} {flags : Flags S} {bounds : Bounds S}
  {fits : Fits S} {host : HostEnv Unit}
  {pv : List Value}

/-- A `let` binding: the value's code, the store of its words from local `base` on, the release
of the value when it is owned and the body does not use it, and the body's code. -/
theorem spec_letE (hm : Runtime m) {Γ' : List Ty} {sTy tTy : Ty} {value : Expr S Γ' sTy}
    {body : Expr S (sTy :: Γ') tTy} {buy : Bool}
    (valueSpec : ∀ env slots paid live, CodeSpec (pool := pool) m funs flags bounds fits host pv value env
        slots paid live)
    (bodySpec : ∀ env slots paid live, CodeSpecIn (pool := pool) buy m funs flags bounds fits host pv
        body env slots paid live) :
    ∀ env slots paid live, CodeSpecIn (pool := pool) buy m funs flags bounds fits host pv
        (Expr.letE value body) env slots paid live :=
  fun env slots paid live =>
    CodeSpecInX.false_iff.mp (specX_letE (strict := false) hm nofun
      (fun env slots paid live => CodeSpecX.false_iff.mpr (valueSpec env slots paid live))
      (fun env slots paid live => CodeSpecInX.false_iff.mpr (bodySpec env slots paid live)) env
      slots paid live)

end

/-- A pair: the code of each component, each followed by its coercion to the pair's mode. -/
theorem specX_pair (hCopy : CopyCodeX strict m host) {Γ' : List Ty} {sTy tTy : Ty} {first : Expr S Γ' sTy}
    {second : Expr S Γ' tTy}
    (firstSpec : ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv first env
        slots paid live)
    (secondSpec : ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv second env
        slots paid live) :
    ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv (Expr.pair first second) env
        slots paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt hAl hSafe hCap hBase hRoom
      hPlace rest Q hTrap
    hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have h1 : first.width ≤ max first.width second.width := Nat.le_max_left ..
  have h2 : second.width ≤ max first.width second.width := Nat.le_max_right ..
  have hc1 : copyWidth sTy ≤ max (copyWidth sTy) (copyWidth tTy) := Nat.le_max_left ..
  have hc2 : copyWidth tTy ≤ max (copyWidth sTy) (copyWidth tTy) := Nat.le_max_right ..
  have hw := Nat.le_max_left (max first.width second.width) (max (copyWidth sTy) (copyWidth tTy))
  have hc := Nat.le_max_right (max first.width second.width) (max (copyWidth sTy) (copyWidth tTy))
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, Expr.usesFast_eq, List.append_assoc]
  have hIn : ∀ i, ((live i || second.uses i) || first.uses i) = true →
      (live i || (Expr.pair first second).uses i) = true := fun i h => by
    simp only [Expr.uses]; exact live_seq _ _ _ h
  have hVarsL := hVars.live_mono hIn
  have hOwnedA : (Expr.pair first second).mode (slots.map Slot.mode) = .owned →
      ((Expr.pair first second).aborts || slots.any (·.mode == .owned)) = true := fun ht => by
    have := (Expr.pair first second).mode_owned (slots.map Slot.mode) ht
    rw [Slot.any_map] at this
    exact this
  have hdF : (Expr.pair first second).fits funs fits env = true → first.fits funs fits env = true :=
    fun hd => by simp only [Expr.fits, Bool.and_eq_true] at hd; exact hd.1
  have hdS : (Expr.pair first second).fits funs fits env = true →
      second.fits funs fits env = true := fun hd => by
    simp only [Expr.fits, Bool.and_eq_true] at hd; exact hd.2
  have hB : (Expr.pair first second).allocs funs flags bounds (slots.map Slot.mode) paid live env =
      first.allocs funs flags bounds (slots.map Slot.mode) paid (fun i => live i || second.uses i) env +
        coerceCost sTy (first.mode (slots.map Slot.mode))
          ((first.mode (slots.map Slot.mode)).join (second.mode (slots.map Slot.mode)))
          (first.denote funs env) +
        second.allocs funs flags bounds (slots.map Slot.mode) paid live env +
        coerceCost tTy (second.mode (slots.map Slot.mode))
          ((first.mode (slots.map Slot.mode)).join (second.mode (slots.map Slot.mode)))
          (second.denote funs env) := by
    simp only [Expr.allocs]
  -- The variables that die in the pair die in the first component or in the second.
  have hSplitP : dyingPot store s env slots paid
      (fun i => live i || (Expr.pair first second).uses i)
      live =
        dyingPot store s env slots paid (fun i => live i || second.uses i || first.uses i)
          (fun i => live i || second.uses i) +
        dyingPot store s env slots paid (fun i => live i || second.uses i) live := by
    rw [dyingPot_split _ (fun i => live i || second.uses i) _
      (fun i h => hIn i (by simp [h])) (fun i h => by simp [h])]
    congr 1
    exact dyingPot_congr (fun i => by
      simp only [Expr.uses]
      cases live i <;> cases first.uses i <;> cases second.uses i <;> rfl) fun _ => rfl
  refine firstSpec env slots paid _ h base heap store s hh hpv hVarsL hAt
    (fun hs => (hAl hs).live_mono hIn) (hSafe.mono hIn) hCap hBase (by omega) hPlace.1 _ _
    (hTrap.part (by flag_tac) (fun h => by simp only [Expr.aborts]; exact trap_left _ _ _ h)
      fun _ hw => hw.mono (by rw [hB, hSplitP]; omega))
    fun heap0 store0 s0 ws0 a0 hAl0 hTopF => ?_
  refine After.coerceX hCopy a0 hAl0 (fun h => by simp [Mode.join, h]) le_rfl
    (by rw [a0.frame.params]; exact hBase) (a0.frame.positions.trans hh) (by omega)
    (by rw [a0.step.cap m]; exact hCap) (fun hs ht _ => hTrap.alloc (hOwnedA ht) fun hd hw => by
      have hcc : coerceCost sTy (first.mode (slots.map Slot.mode))
          ((first.mode (slots.map Slot.mode)).join (second.mode (slots.map Slot.mode)))
          (first.denote funs env) =
          sTy.copyCost (first.denote funs env) := by rw [coerceCost, ite_eq_left ⟨hs, ht⟩]
      have := hTopF (hdF (fits_of_not hd))
      exact hw.shift (c1 := dyingPot store s env slots paid
          (fun i => live i || second.uses i || first.uses i) (fun i => live i || second.uses i) +
        first.allocs funs flags bounds (slots.map Slot.mode) paid (fun i => live i || second.uses i) env)
        (by omega) (by rw [hB, hSplitP]; omega) (a0.step.cap m))
    fun heap1 store1 s1 ws1 a1 hTopC1 hSame1 hAl1 => ?_
  have hDs : dyingPot store1 { s1 with values := ws1.reverse ++ s.values } env slots paid
      (fun i => live i || second.uses i) live =
        dyingPot store s env slots paid (fun i => live i || second.uses i) live := by
    rw [dyingPot_values]
    exact dyingPot_after hVarsL a1 (fun i h => by simp [h]) _ _ fun _ h => h
  refine secondSpec env slots paid live h base heap1 store1
    { s1 with values := ws1.reverse ++ s.values } (a1.frame.positions.trans hh)
    (a1.frame.params.trans hpv) (a1.holds.agree Frame.ofValues) a1.step.at_
    (fun hs => (hAl1 hs).1.values _)
    (((hSafe.mono hIn).after hVarsL a1 (fun i hi => by simp [hi])).1.values _)
    (by rw [a1.step.cap m]; exact hCap)
    (by show s1.params.length ≤ base; rw [a1.frame.params]; exact hBase) (by omega) hPlace.2 _ _
    (hTrap.part (by flag_tac) (fun h => by simp only [Expr.aborts]; exact trap_right _ _ _ h)
      fun hd hw => by
        rw [hDs]
        exact hw.shift (heap1 := heap1) (store1 := store1)
          (c1 := dyingPot store s env slots paid (fun i => live i || second.uses i || first.uses i)
            (fun i => live i || second.uses i) +
            first.allocs funs flags bounds (slots.map Slot.mode) paid (fun i => live i || second.uses i)
            env + coerceCost sTy (first.mode (slots.map Slot.mode))
            ((first.mode (slots.map Slot.mode)).join (second.mode (slots.map Slot.mode)))
              (first.denote funs env))
          (by have := hTopF (hdF (fits_of_not hd)); have := hTopC1; omega)
          (by rw [hB, hSplitP]; omega) (a1.step.cap m))
    fun heap3 store3 s3 ws3 a3 hAl3 hTopS => ?_
  refine After.coerceX hCopy a3 hAl3 (fun h => by
      simp only [Mode.join, h]; cases first.mode (slots.map Slot.mode) <;> rfl) le_rfl
    (by rw [a3.frame.params, a1.frame.params]; exact hBase)
    (a3.frame.positions.trans (a1.frame.positions.trans hh)) (by omega)
    (by rw [a3.step.cap m, a1.step.cap m]; exact hCap)
    (fun hs ht _ => hTrap.alloc (hOwnedA ht) fun hd hw => by
      have hcc : coerceCost tTy (second.mode (slots.map Slot.mode))
          ((first.mode (slots.map Slot.mode)).join (second.mode (slots.map Slot.mode)))
          (second.denote funs env) =
          tTy.copyCost (second.denote funs env) := by rw [coerceCost, ite_eq_left ⟨hs, ht⟩]
      exact hw.shift (heap1 := heap3) (store1 := store3)
        (c1 := dyingPot store s env slots paid (fun i => live i || second.uses i || first.uses i)
          (fun i => live i || second.uses i) +
          first.allocs funs flags bounds (slots.map Slot.mode) paid (fun i => live i || second.uses i)
          env + coerceCost sTy (first.mode (slots.map Slot.mode))
          ((first.mode (slots.map Slot.mode)).join (second.mode (slots.map Slot.mode)))
            (first.denote funs env) +
          dyingPot store s env slots paid (fun i => live i || second.uses i) live +
          second.allocs funs flags bounds (slots.map Slot.mode) paid live env)
        (by have := hTopF (hdF (fits_of_not hd)); have := hTopC1
            have := hTopS (hdS (fits_of_not hd)); rw [hDs] at this; omega)
        (by rw [hB, hSplitP]; omega)
        (by rw [a3.step.cap m, a1.step.cap m]))
    fun heap2 store2 s2 ws2 a2 hTopC2 hSame2 hAl2 => ?_
  obtain ⟨hStep, hFrame, hRep1, hApart1, hDisjoint⟩ :=
    After.seq hVarsL a1 a2 (fun i h => by simp [h]) fun i h => by simp [h]
  have hl1 := hRep1.length
  have hv := hNext heap2 store2 s2 (ws1 ++ ws2) ⟨by
      rw [Mode.fresh_pair hl1]
      exact hStep.mono (fun _ hr => hr.mono fun i h1 h2 => ⟨hIn i h1, h2⟩) fun _ hb => hb,
    hFrame, a2.holds, ⟨ws1, ws2, rfl, hRep1, a2.rep, fun hmo x hx y hy => by
      have hmo' : (first.mode (slots.map Slot.mode)).join (second.mode (slots.map Slot.mode)) =
          .owned := hmo
      rw [hmo'] at hDisjoint
      exact hDisjoint x hx y hy⟩, fun w y hy hmo wy hwy hly b hb c hc => by
      rw [Ty.regions_append hl1] at hb
      rcases List.mem_append.mp hb with hb | hb
      · exact hApart1 w y hy hmo wy hwy hly b hb c hc
      · exact a2.apart w y hy hmo wy hwy hly b hb c hc⟩
      (fun hs => ⟨(hAl2 hs).1, Ty.AlignedVal.pair hl1 (After.alignedSeq a1 a2 (hAl1 hs).2)
        (hAl2 hs).2⟩)
      (fun hd => by
        have hF := hTopF (hdF hd)
        have hS := hTopS (hdS hd)
        rw [hDs] at hS
        have hRegions1 := After.seq_regions a1 a2
        have hValue : (Expr.pair first second).denote funs env =
            (first.denote funs env, second.denote funs env) := rfl
        rw [hB, hSplitP, hValue]
        simp only [Ty.pot, List.take_left' hl1, List.drop_left' hl1]
        refine pair_top hF hTopC1 hS hTopC2 (fun hp => ?_) (fun hp => ?_)
        · simp only [Expr.paid, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hp
          rcases hp.1.2 with hp1 | hc1
          · obtain ⟨rfl, rfl⟩ := hSame1 (Expr.mode_of_paid first hp1)
            exact Or.inl ⟨hp1, Ty.pot_of_regions hp.1.1 hRegions1⟩
          · exact Or.inr (Ty.pot_creditFree sTy hc1 _ _)
        · simp only [Expr.paid, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hp
          rcases hp.2 with hp2 | hc2
          · obtain ⟨rfl, rfl⟩ := hSame2 (Expr.mode_of_paid second hp2)
            exact Or.inl ⟨hp2, rfl⟩
          · exact Or.inr (Ty.pot_creditFree tTy hc2 _ _))
  simpa [List.reverse_append, List.append_assoc] using hv


/-- A binding of a pair's components: the pair's code, the stores of its components' words, the
release of each component that is owned and that the body does not use, and the body's code. -/
theorem specX_letPair (hm : Runtime m) (hRA : strict = true → ReleaseAligned m) {Γ' : List Ty} {sTy tTy uTy : Ty}
    {e : Expr S Γ' (.pair sTy tTy)} {body : Expr S (tTy :: sTy :: Γ') uTy} {buy : Bool}
    (eSpec : ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv e env slots paid live)
    (bodySpec : ∀ env slots paid live, CodeSpecInX strict (pool := pool) buy m funs flags bounds fits host pv
        body env slots paid live) :
    ∀ env slots paid live, CodeSpecInX strict (pool := pool) buy m funs flags bounds fits host pv
        (Expr.letPair e body) env slots paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt hAl hSafe hCap hBase hRoom
      hPlace rest Q hTrap
    hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hER : e.width ≤ max e.width body.width := Nat.le_max_left ..
  have hBR : body.width ≤ max e.width body.width := Nat.le_max_right ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, Expr.usesFast_eq, List.append_assoc]
  have hV : ∀ i, ((live i || body.uses (i + 2)) || e.uses i) = true →
      (live i || (Expr.letPair e body).uses i) = true := fun i h => by
    simp only [Expr.uses]; exact live_seq _ _ _ h
  -- The variables that die in the binding die in the pair or in the body.
  have hSplitL : dyingPot store s env slots paid
      (fun i => live i || (Expr.letPair e body).uses i) live =
        dyingPot store s env slots paid (fun i => live i || body.uses (i + 2) || e.uses i)
          (fun i => live i || body.uses (i + 2)) +
        dyingPot store s env slots paid (fun i => live i || body.uses (i + 2)) live := by
    rw [dyingPot_split _ (fun i => live i || body.uses (i + 2)) _
      (fun i h => hV i (by simp [h])) (fun i h => by simp [h])]
    congr 1
    exact dyingPot_congr (fun i => by
      simp only [Expr.uses]
      cases live i <;> cases e.uses i <;> cases body.uses (i + 2) <;> rfl) fun _ => rfl
  refine eSpec env slots paid _ h
    (base + sTy.width + tTy.width) heap store s hh hpv ((hVars.mono (by omega)).live_mono hV) hAt
    (fun hs => (hAl hs).live_mono hV) (hSafe.mono hV)
        hCap
    (by omega) (by omega) hPlace.1
    _ _ (hTrap.part (by flag_tac) (fun h => by simp only [Expr.aborts]; exact trap_left _ _ _ h)
      fun _ hw => hw.mono (by rw [hSplitL]; simp only [Expr.allocs]; omega))
    fun heap1 store1 s1 ws a1 hAl1 hTop1 => ?_
  have hp1 : s1.params = s.params := a1.frame.params
  have hh1 : s1.positions = h := a1.frame.positions.trans hh
  have a1' := a1.lower (hVars.live_mono hV) (by omega) fun i h => by simp [h]
  obtain ⟨wf, wsec, rfl, hRf, hRs, hDisj⟩ := a1.rep
  have hlf := hRf.length
  have hls := hRs.length
  rw [List.reverse_append, List.append_assoc]
  refine wpX_storeCode wsec h (base + sTy.width) tTy.types s1 (wf.reverse ++ s.values) hRs.typed
    hh1 (by rw [hp1]; omega) (by rw [Ty.types_length, hh1]; omega) fun s2 hF2 hold2 _ => ?_
  have hh2 : s2.positions = h := hF2.positions.trans hh1
  refine wpX_storeCode wf h base sTy.types s2 s.values hRf.typed hh2 (by rw [hF2.params, hp1]; omega)
    (by rw [Ty.types_length, hh2]; omega) fun s3 hF3 hold1 habove3 => ?_
  have hold1' : LocalsHold { s3 with values := s.values } base sTy.types wf := hold1
  have hold2' : LocalsHold { s3 with values := s.values } (base + sTy.width) tTy.types wsec :=
    hold2.keep hF3.positions habove3 (by rw [Ty.types_length]) (by rw [hls, hh2]; omega)
  have f3 : Frame base s1 { s3 with values := s.values } :=
    (hF2.mono (by omega)).trans (hF3.trans Frame.ofValues)
  have hp3 : s3.params = s.params := hF3.params.trans (hF2.params.trans hp1)
  -- The body's context: the second component as variable 0 and the first as variable 1.
  have hVars1 := (a1'.holds.agree f3)
  have hApart := a1'.apart.agree a1'.holds f3
  have hVarsB : Holds (Env.cons (e.denote funs env).2 (Env.cons (e.denote funs env).1 env))
      (⟨base + sTy.width, e.mode (slots.map Slot.mode)⟩ ::
        ⟨base, e.mode (slots.map Slot.mode)⟩ :: slots)
      (fun i => decide (i < 2) || shift 2 live i || body.uses i)
      (base + sTy.width + tTy.width) heap1 store1 { s3 with values := s.values } := by
    refine Holds.push (Holds.push (hVars1.live_mono fun i h => by simpa using h) hold1' hRf
      ((hApart.fst hlf).live_mono fun i h => by simpa using h)) hold2' hRs ?_
    refine Holds.Apart.push ((hApart.snd hlf).live_mono fun i h => by simpa using h) hold1' hlf
      fun hmo b hb c hc => ?_
    have hmo' : e.mode (slots.map Slot.mode) = .owned := by simpa using hmo
    rw [hmo'] at hb hc hDisj
    exact regionsDisjoint_symm (hDisj rfl c hc b hb)
  have hAlB : strict = true → HoldsA
      (Env.cons (e.denote funs env).2 (Env.cons (e.denote funs env).1 env))
      (⟨base + sTy.width, e.mode (slots.map Slot.mode)⟩ ::
        ⟨base, e.mode (slots.map Slot.mode)⟩ :: slots)
      (fun i => decide (i < 2) || shift 2 live i || body.uses i) heap1 store1
      { s3 with values := s.values } := fun hs =>
    HoldsA.push (HoldsA.push ((HoldsA.agree a1'.holds (hAl1 hs).1 f3).live_mono
        fun i h => by simpa using h) hold1' hlf ((hAl1 hs).2.fst hlf))
      hold2' hls ((hAl1 hs).2.snd hlf)
  have hSafeB : pool.Safe
      (Env.cons (e.denote funs env).2 (Env.cons (e.denote funs env).1 env))
      (⟨base + sTy.width, e.mode (slots.map Slot.mode)⟩ ::
        ⟨base, e.mode (slots.map Slot.mode)⟩ :: slots)
      (fun i => decide (i < 2) || shift 2 live i || body.uses i)
      heap1 store1 { s3 with values := s.values } :=
    (hSafe.mono hV).bind2 (hVars.live_mono hV) a1'
      (fun i hi => by simp [hi]) (fun i hi => by simpa [shift] using hi)
      f3 hRf hRs hold1' hold2'
  have hRelease : ∀ rest' : Program,
      (if e.mode (slots.map Slot.mode) = .owned ∧ body.uses 1 = false then
        releaseCode sTy base else []) ++
      ((if e.mode (slots.map Slot.mode) = .owned ∧ body.uses 0 = false then
        releaseCode tTy (base + sTy.width) else []) ++ rest') =
      ((if body.uses 1 = false then [1] else []) ++
        (if body.uses 0 = false then [0] else [])).flatMap
        (releaseVar (tTy :: sTy :: Γ') (⟨base + sTy.width, e.mode (slots.map Slot.mode)⟩ ::
          ⟨base, e.mode (slots.map Slot.mode)⟩ :: slots)) ++ rest' := by
    intro rest'
    cases body.uses 1 <;> cases body.uses 0 <;> cases e.mode (slots.map Slot.mode) <;>
      simp [releaseVar]
  rw [hRelease]
  have hd1 : (Expr.letPair e body).fits funs fits env = true → e.fits funs fits env = true :=
    fun hd => by simp only [Expr.fits, Bool.and_eq_true] at hd; exact hd.1
  have hd3 : (Expr.letPair e body).fits funs fits env = true →
      body.fits funs fits (.cons (e.denote funs env).2 (.cons (e.denote funs env).1 env)) = true :=
    fun hd => by simp only [Expr.fits, Bool.and_eq_true] at hd; exact hd.2
  refine wpX_releaseVars hm hRA _ (by split <;> split <;> simp) hVarsB a1.step.at_ hAlB
    (by split <;> split <;> simp) fun heap2 store2 e2 hTop2 hA2 => ?_
  have e2' := e2.mono (live' := fun i => shift 2 live i || body.uses i) fun i h => by
    match i with
    | 0 =>
      have h0 : body.uses 0 = true := by simpa [shift] using h
      simp [h0]
    | 1 =>
      have h1 : body.uses 1 = true := by simpa [shift] using h
      simp [h1]
    | k + 2 => split <;> split <;> simpa using h
  have hA2' : strict = true → HoldsA
      (Env.cons (e.denote funs env).2 (Env.cons (e.denote funs env).1 env))
      (⟨base + sTy.width, e.mode (slots.map Slot.mode)⟩ ::
        ⟨base, e.mode (slots.map Slot.mode)⟩ :: slots)
      (fun i => shift 2 live i || body.uses i) heap2 store2 { s3 with values := s.values } :=
    fun hs => (hA2 hs).live_mono fun i h => by
      match i with
      | 0 =>
        have h0 : body.uses 0 = true := by simpa [shift] using h
        simp [h0]
      | 1 =>
        have h1 : body.uses 1 = true := by simpa [shift] using h
        simp [h1]
      | k + 2 => split <;> split <;> simpa using h
  -- The body's dying variables: the components, paid when the pair is, whose potential is the
  -- pair's, and the others, whose potential the pair's code and the releases keep.
  have hPotE : (Ty.pair sTy tTy).pot store1 (wf ++ wsec) (e.denote funs env) =
      sTy.pot store1 wf (e.denote funs env).1 + tTy.pot store1 wsec (e.denote funs env).2 := by
    simp only [Ty.pot, List.take_left' hlf, List.drop_left' hlf]
  have hDb : dyingPot store2 { s3 with values := s.values }
      (Env.cons (e.denote funs env).2 (Env.cons (e.denote funs env).1 env))
      (⟨base + sTy.width, e.mode (slots.map Slot.mode)⟩ ::
        ⟨base, e.mode (slots.map Slot.mode)⟩ :: slots)
      (e.paid flags (slots.map Slot.mode) paid (fun i => live i || body.uses (i + 2)) ::
        e.paid flags (slots.map Slot.mode) paid (fun i => live i || body.uses (i + 2)) :: paid)
      (fun i => shift 2 live i || body.uses i) (shift 2 live) ≤
        (if e.paid flags (slots.map Slot.mode) paid (fun i => live i || body.uses (i + 2)) = true
          then (Ty.pair sTy tTy).pot store1 (wf ++ wsec) (e.denote funs env) else 0) +
        dyingPot store s env slots paid (fun i => live i || body.uses (i + 2)) live := by
    rw [dyingPot_evolves hVarsB e2' (fun i h => by
      simp only [Bool.or_eq_true] at h ⊢; rcases h with h | h <;> simp [h]) _ _ fun _ h => h,
      dyingPot_cons, dyingPot_cons]
    rw [dyingPot_congr (L0' := fun i => live i || body.uses (i + 2)) (L1' := live)
      (fun i => by simp [shift]) (fun i => by simp [shift])]
    rw [dyingPot_step (hVars.live_mono hV) a1'.step (a1'.frame.trans f3)
      (fun i h => by simp [h]) _ _ fun _ h => h]
    dsimp only
    rw [hold2'.read_eq (by rw [hls, Ty.types_length]), hold1'.read_eq (by rw [hlf, Ty.types_length]),
      hPotE]
    by_cases hpp : e.paid flags (slots.map Slot.mode) paid (fun i => live i || body.uses (i + 2)) = true
    · rw [ite_eq_left hpp]
      split <;> split <;> omega
    · simp only [hpp, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      omega
  have hbuys : (Expr.letPair e body).buysIn buy funs flags (slots.map Slot.mode) paid live env =
      body.buysIn buy funs flags ((⟨base + sTy.width, e.mode (slots.map Slot.mode)⟩ ::
          ⟨base, e.mode (slots.map Slot.mode)⟩ :: slots).map Slot.mode)
        (e.paid flags (slots.map Slot.mode) paid (fun i => live i || body.uses (i + 2)) ::
          e.paid flags (slots.map Slot.mode) paid (fun i => live i || body.uses (i + 2)) ::
            paid) (shift 2 live)
        (.cons (e.denote funs env).2 (.cons (e.denote funs env).1 env)) :=
    rfl
  refine bodySpec _ _
    (e.paid flags (slots.map Slot.mode) paid (fun i => live i || body.uses (i + 2)) ::
      e.paid flags (slots.map Slot.mode) paid (fun i => live i || body.uses (i + 2)) :: paid)
    (shift 2 live) h (base + sTy.width + tTy.width)
    heap2 store2
    { s3 with values := s.values } (f3.positions.trans hh1) (hp3.trans hpv) e2'.holds e2'.step.at_ hA2'
    (hSafeB.evolves hVarsB e2' (fun i hi => live_right _ _ _ hi))
    (by rw [e2'.step.cap m, a1.step.cap m]; exact hCap)
    (by show s3.params.length ≤ base + sTy.width + tTy.width; rw [hp3]; omega)
    (by omega) hPlace.2 _ _
    (hTrap.part (by flag_tac) (fun h => by
      have hmo := e.mode_owned (slots.map Slot.mode)
      rw [Slot.any_map] at hmo
      simp only [List.any_cons, Expr.aborts] at h ⊢
      exact let_trap_body2 _ _ _ _ (fun hv => hmo (by simpa using hv)) h) fun hd hw => by
        have h1 := hTop1 (hd1 (fits_of_not hd)); have := congrArg UInt64.toNat hTop2
        have hDb' := hDb
        refine hw.of_le ?_ (by rw [e2'.step.cap m, a1.step.cap m])
        rw [hSplitL, hbuys]
        simp only [Expr.allocs, List.map_cons]
        by_cases hpp :
            e.paid flags (slots.map Slot.mode) paid (fun i => live i || body.uses (i + 2)) = true
        · rw [ite_eq_left hpp] at h1 hDb'; omega
        · rw [ite_eq_right hpp] at h1 hDb'; omega)
    fun heap3 store3 s4 ws4 aB hAlB3 hTop3 => ?_
  have aB' := After.prepend hVarsB e2' aB (fun i h => live_right _ _ _ h) fun i h => by simp [h]
  have hNew : ∀ r, (∀ b ∈ (e.mode (slots.map Slot.mode)).fresh store1 (.pair sTy tTy) (wf ++ wsec)
      (e.denote funs env), regionsDisjoint r b) →
      ((e.mode (slots.map Slot.mode)) = .owned → ∀ w,
        LocalsHold { s3 with values := s.values } (base + sTy.width) tTy.types w →
        w.length = tTy.width →
        ∀ b ∈ tTy.blocks store1 w (e.denote funs env).2, regionsDisjoint r b) ∧
      ((e.mode (slots.map Slot.mode)) = .owned → ∀ w,
        LocalsHold { s3 with values := s.values } base sTy.types w → w.length = sTy.width →
        ∀ b ∈ sTy.blocks store1 w (e.denote funs env).1, regionsDisjoint r b) := by
    intro r hFresh
    rw [Mode.fresh_pair hlf] at hFresh
    refine ⟨fun hmo w hw hlw b hb => ?_, fun hmo w hw hlw b hb => ?_⟩
    · obtain rfl := LocalsHold.unique hw hold2' (hlw.trans hls.symm)
      rw [hmo] at hFresh
      exact hFresh b (List.mem_append_right _ hb)
    · obtain rfl := LocalsHold.unique hw hold1' (hlw.trans hlf.symm)
      rw [hmo] at hFresh
      exact hFresh b (List.mem_append_left _ hb)
  exact hNext heap3 store3 s4 ws4
    ((After.bind2 (hVars.live_mono hV) a1' f3 aB' (by omega) hNew
      (fun i h => by simpa using h) (fun i h => by simp [h]) fun i h => by simp [h]).liveIn hV)
    (fun hs => ⟨(hAlB3 hs).1.pop.pop.live_mono fun i h => by simpa [shift] using h,
      (hAlB3 hs).2⟩)
    fun hd => by
      have h1 := hTop1 (hd1 hd); have h3 := hTop3 (hd3 hd); have := congrArg UInt64.toNat hTop2
      have hDb' := hDb
      have hpot : (if (Expr.letPair e body).paidIn buy flags (slots.map Slot.mode) paid live = true
            then uTy.pot store3 ws4 ((Expr.letPair e body).denote funs env) else 0) =
          (if body.paidIn buy flags ((⟨base + sTy.width, e.mode (slots.map Slot.mode)⟩ ::
              ⟨base, e.mode (slots.map Slot.mode)⟩ :: slots).map Slot.mode)
              (e.paid flags (slots.map Slot.mode) paid (fun i => live i || body.uses (i + 2)) ::
                e.paid flags (slots.map Slot.mode) paid (fun i => live i || body.uses (i + 2)) ::
                  paid) (shift 2 live) = true then
            uTy.pot store3 ws4 (body.denote funs
              (.cons (e.denote funs env).2 (.cons (e.denote funs env).1 env))) else 0) :=
        rfl
      rw [hpot, hbuys, hSplitL]
      simp only [List.map_cons] at h3 ⊢
      simp only [Expr.allocs]
      by_cases hpp :
          e.paid flags (slots.map Slot.mode) paid (fun i => live i || body.uses (i + 2)) = true
      · rw [ite_eq_left hpp] at h1 hDb'; omega
      · rw [ite_eq_right hpp] at h1 hDb'; omega

section

variable {pool : Bytes.LiteralPool}
variable {S : List Sig} {m : Module} {funs : Funs S} {flags : Flags S} {bounds : Bounds S}
  {fits : Fits S} {host : HostEnv Unit}
  {pv : List Value}

/-- A binding of a pair's components: the pair's code, the stores of its components' words, the
release of each component that is owned and that the body does not use, and the body's code. -/
theorem spec_letPair (hm : Runtime m) {Γ' : List Ty} {sTy tTy uTy : Ty}
    {e : Expr S Γ' (.pair sTy tTy)} {body : Expr S (tTy :: sTy :: Γ') uTy} {buy : Bool}
    (eSpec : ∀ env slots paid live, CodeSpec (pool := pool) m funs flags bounds fits host pv e env slots paid live)
    (bodySpec : ∀ env slots paid live, CodeSpecIn (pool := pool) buy m funs flags bounds fits host pv
        body env slots paid live) :
    ∀ env slots paid live, CodeSpecIn (pool := pool) buy m funs flags bounds fits host pv
        (Expr.letPair e body) env slots paid live :=
  fun env slots paid live =>
    CodeSpecInX.false_iff.mp (specX_letPair (strict := false) hm nofun
      (fun env slots paid live => CodeSpecX.false_iff.mpr (eSpec env slots paid live))
      (fun env slots paid live => CodeSpecInX.false_iff.mpr (bodySpec env slots paid live)) env
      slots paid live)

end

end Cases

end Verified
