import Verified.AlignedTreeMemory
import Verified.FieldsMixed

/-!
The construction of a tree under the flag.  A tree's fields are evaluated in order and each is
coerced to owned (`CodeSpecX.coerced`, `CodeSpecX.owned`); `FieldsAligned` states that the
blocks of the owned fields start and end at multiples of 8, which `FieldsAligned.prepend`
carries as `FieldsAfter.prepend` carries the fields' facts.  The record's own block comes from
`alloc` or from a detached header, and the tree's blocks are the record's and its fields'
(`wp_assembleTree`), so the tree is aligned when they are.
-/

namespace Verified

variable {pool : Bytes.LiteralPool}

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

/-- The blocks of the owned values `values`, whose words are `words`, start and end at multiples
of 8. -/
def FieldsAligned {ps : List Ty} (store : Store Unit) (values : Env ps) (words : List Value) :
    Prop :=
  ∀ b ∈ values.blocks store words, b.1 % 8 = 0 ∧ b.2 % 8 = 0

theorem FieldsAligned.nil {store : Store Unit} : FieldsAligned store Env.nil [] :=
  fun _ hb => nomatch hb

/-- The alignment of a value prepended to fields, as `FieldsAfter.prepend` prepends its facts. -/
theorem FieldsAligned.prepend {Γ ps : List Ty} {env : Env Γ} {slots : List Slot}
    {L0 L1 live : Nat → Bool} {base : Nat} {heap heap1 heap2 : Heap}
    {store store1 store2 : Store Unit} {s s1 s2 : Locals} {t : Ty} {value : t.denote}
    {values : Env ps} {first words vs : List Value}
    (a1 : After env slots L0 L1 base heap store s t .owned value heap1 store1 s1 first)
    (a2 : FieldsAfter env slots L1 live base heap1 store1 { s1 with values := vs }
      values heap2 store2 s2 words)
    (h1 : Ty.AlignedVal .owned store1 t first value) (h2 : FieldsAligned store2 values words) :
    FieldsAligned store2 (Env.cons value values) (first ++ words) := by
  have hKeep1 : ∀ c ∈ t.blocks store1 first value,
      Holds.KeepDying env slots L1 live store1 { s1 with values := vs } c := by
    intro c hc u x hx _ hm wx hwx hlx b hb
    have hb' : b ∈ u.regions (slots.getD x.index default).mode store1 wx (env.get x) := by
      rw [hm]; exact hb
    exact a1.apart u x hx (Or.inl rfl) wx hwx hlx c hc b hb'
  obtain ⟨-, hSame1, -⟩ := a1.rep.step a2.step hKeep1
  have hSame : t.blocks store2 first value = t.blocks store1 first value := hSame1
  intro b hb
  rw [Env.blocks_cons a1.rep.length] at hb
  rcases List.mem_append.mp hb with hb | hb
  · rw [hSame] at hb
    exact ⟨(h1 b hb).1, (h1 b hb).2 rfl⟩
  · exact h2 b hb

section


theorem CodeSpecX.coerced {strict : Bool} {S : List Sig} {Γ : List Ty} {t : Ty} {m : Module}
    {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S}
    {host : HostEnv Unit} {pv : List Value} {e : Expr S Γ t} {env : Env Γ}
    {target : Mode} {slots : List Slot} {paid : List Bool} {live : Nat → Bool}
    (hCopy : CopyCodeX strict m host) (spec : CodeSpecX strict (pool := pool) m funs flags bounds fits host pv e env slots paid live)
    (hTarget : e.mode (slots.map Slot.mode) = .owned → target = .owned)
    {h base : Nat} {heap : Heap} {store : Store Unit} {s : Locals}
    (hh : s.positions = h) (hpv : s.params = pv)
    (hVars : Holds env slots (fun i => live i || e.uses i) base heap store s)
    (hAt : heap.At store)
    (hAl : strict = true → HoldsA env slots (fun i => live i || e.uses i) heap store s)
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
      (strict = true → HoldsA env slots live heap' store' s' ∧
        Ty.AlignedVal target store' t ws (e.denote funs env)) →
      (e.fits funs fits env = true → heap'.top.toNat ≤ heap.top.toNat +
        dyingPot store s env slots paid (fun i => live i || e.uses i) live +
        e.allocs funs flags bounds (slots.map Slot.mode) paid live env +
        coerceCost t (e.mode (slots.map Slot.mode)) target (e.denote funs env)) →
      wpX strict m rest Q store' { s' with values := ws.reverse ++ s.values } host) :
    wpX strict m (e.code (pool := pool) h slots base live ++
      (coerceCode h t (e.mode (slots.map Slot.mode)) target base ++ rest)) Q store s host := by
  have hBudget : TrapOK (!(e.fits funs fits env) || (true && !decide (heap.Within store m
      (dyingPot store s env slots paid (fun i => live i || e.uses i) live +
        e.allocs funs flags bounds (slots.map Slot.mode) paid live env +
        coerceCost t (e.mode (slots.map Slot.mode)) target (e.denote funs env))))) Q := by
    simpa only [Bool.true_and] using hTrap
  refine spec h base heap store s hh hpv hVars hAt hAl hSafe hCap hBase
    (by have := Nat.le_max_left e.width (copyWidth t); omega) hPlace _ _
    (hBudget.part id (fun _ => rfl) (fun _ hw => hw.mono (by omega)))
    fun heap1 store1 s1 ws a1 hAl1 hTop1 => ?_
  have hTop (hf : e.fits funs fits env = true) :
      heap1.top.toNat ≤ heap.top.toNat +
        dyingPot store s env slots paid (fun i => live i || e.uses i) live +
        e.allocs funs flags bounds (slots.map Slot.mode) paid live env := by
    have := hTop1 hf
    omega
  refine a1.coerceX hCopy hAl1 hTarget (le_refl _) (by rw [a1.frame.params]; exact hBase)
    (a1.frame.positions.trans hh)
    (by have := Nat.le_max_right e.width (copyWidth t); omega)
    (by rw [a1.step.cap m]; exact hCap) ?_ fun heap2 store2 s2 ws2 a2 hTop2 _ hAl2 => ?_
  · intro hs ht hScalar
    apply hBudget.part (d' := false) (a' := true) (P' := heap1.Within store1 m (t.copyCost
      (e.denote funs env))) nofun (fun _ => rfl)
    intro hd hw
    have hf : e.fits funs fits env = true := by simpa using hd
    have hc : coerceCost t (e.mode (slots.map Slot.mode)) target (e.denote funs env) =
        t.copyCost (e.denote funs env) := by simp [coerceCost, hs, ht]
    exact hw.shift (by simpa only [Nat.add_assoc] using hTop hf)
      (by rw [hc]) (a1.step.cap m)
  · exact hNext heap2 store2 s2 ws2 a2 hAl2 fun hf => by have := hTop hf; omega

theorem CodeSpecX.owned {strict : Bool} {S : List Sig} {Γ : List Ty} {t : Ty} {m : Module}
    {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S}
    {host : HostEnv Unit} {pv : List Value} {e : Expr S Γ t} {env : Env Γ}
    {slots : List Slot} {paid : List Bool} {live : Nat → Bool}
    (hCopy : CopyCodeX strict m host) (spec : CodeSpecX strict (pool := pool) m funs flags bounds fits host pv e env slots paid live)
    {h base : Nat} {heap : Heap} {store : Store Unit} {s : Locals}
    (hh : s.positions = h) (hpv : s.params = pv)
    (hVars : Holds env slots (fun i => live i || e.uses i) base heap store s)
    (hAt : heap.At store)
    (hAl : strict = true → HoldsA env slots (fun i => live i || e.uses i) heap store s)
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
      (strict = true → HoldsA env slots live heap' store' s' ∧
        Ty.AlignedVal .owned store' t ws (e.denote funs env)) →
      (e.fits funs fits env = true → heap'.top.toNat ≤ heap.top.toNat +
        dyingPot store s env slots paid (fun i => live i || e.uses i) live +
        e.allocs funs flags bounds (slots.map Slot.mode) paid live env +
        coerceCost t (e.mode (slots.map Slot.mode)) .owned (e.denote funs env)) →
      wpX strict m rest Q store' { s' with values := ws.reverse ++ s.values } host) :
    wpX strict m (e.code (pool := pool) h slots base live ++
      (coerceCode h t (e.mode (slots.map Slot.mode)) .owned base ++ rest)) Q store s host :=
  CodeSpecX.coerced (target := .owned) hCopy spec (fun _ => rfl) hh hpv hVars hAt hAl hSafe hCap
    hBase hRoom hPlace hTrap hNext

theorem fieldsWidth_specX {strict : Bool} {S : List Sig} {Γ : List Ty} {m : Module} {funs : Funs S}
    {flags : Flags S} {bounds : Bounds S} {fits : Fits S} {host : HostEnv Unit}
    {pv : List Value} (hCopy : CopyCodeX strict m host) {env : Env Γ} {slots : List Slot} {paid : List Bool}
    {h base fieldBase scratch w : Nat} {d : Bool} :
    (ps : List Ty) → (args : (i : Fin ps.length) → Expr S Γ (ps.get i)) →
    (L : Nat → Nat → Bool) →
    (∀ i, (ps.get i).width = w) →
    (∀ i k, (L (i.val + 1) k || (args i).uses k) = L i.val k) →
    (∀ i, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv (args i) env slots paid
      (L (i.val + 1))) →
    (∀ i, (args i).placeArgs = true) →
    (∀ i, (!(args i).fits funs fits env) = true → d = true) →
    base ≤ fieldBase → fieldBase + w * ps.length ≤ scratch →
    (∀ i, scratch + max (args i).width (copyWidth (ps.get i)) ≤ h) →
    ∀ (heap : Heap) (store : Store Unit) (s : Locals),
    s.positions = h → s.params = pv → s.params.length ≤ base →
    Holds env slots (L 0) base heap store s → heap.At store →
    (strict = true → HoldsA env slots (L 0) heap store s) →
    pool.Safe env slots (L 0) heap store s → store.memoryCap m 0 ≤ 65535 →
    ∀ (rest : Program) (Q : Assertion Unit),
    TrapOK (d || !decide (heap.Within store m
      (dyingPot store s env slots paid (L 0) (L ps.length) +
        argsSum (fieldCost funs flags bounds (slots.map Slot.mode) paid L args env)))) Q →
    (∀ heap' store' s' ws,
      FieldsAfter env slots (L 0) (L ps.length) base heap store s
        (Env.ofFn fun i => (args i).denote funs env) heap' store' s' ws →
      (strict = true → HoldsA env slots (L ps.length) heap' store' s' ∧
        FieldsAligned store' (Env.ofFn fun i => (args i).denote funs env) ws) →
      Frame fieldBase s s' → LocalsHold s' fieldBase (ps.flatMap Ty.types) ws →
      (d = false → heap'.top.toNat ≤ heap.top.toNat +
        dyingPot store s env slots paid (L 0) (L ps.length) +
        argsSum (fieldCost funs flags bounds (slots.map Slot.mode) paid L args env)) →
      wpX strict m rest Q store' { s' with values := s.values } host) →
    wpX strict m (argsCode (fun i => (args i).code (pool := pool) h slots scratch (L (i.val + 1)) ++
      coerceCode h (ps.get i) ((args i).mode (slots.map Slot.mode)) .owned scratch ++
      storeCode h (fieldBase + w * i.val) (ps.get i).types) ++ rest) Q store s host
  | [], _, L, _, _, _, _, _, _, _, _, heap, store, s, _, _, _, hVars, hAt, hAl, _, _, rest, Q, _,
      hNext => by
    simpa only [argsCode, List.nil_append, Env.ofFn] using
      hNext heap store s [] (FieldsAfter.nil hAt hVars) (fun hs => ⟨hAl hs, FieldsAligned.nil⟩)
        (Frame.refl fieldBase s)
        (fun k hk => nomatch hk) (fun _ => by simp [argsSum])
  | p :: ps, args, L, hWidth, hLink, hSpec, hPlace, hd, hBaseField, hScratch,
      hRoom, heap, store, s, hh, hpv, hBase, hVars, hAt, hAl, hSafe, hCap, rest, Q, hTrap, hNext => by
    let first : Fin (p :: ps).length := ⟨0, by simp⟩
    have hTyLen : p.types.length = w := (Ty.types_length p).trans (hWidth first)
    simp only [List.length_cons, Nat.mul_succ] at hScratch
    have hIn : (fun k => L 1 k || (args first).uses k) = L 0 := funext (hLink first)
    have h01 : ∀ k, L 1 k = true → L 0 k = true := by
      intro k hk
      rw [← hLink first k, hk]
      rfl
    have hTailLive : ∀ k, L (ps.length + 1) k = true → L 1 k = true := by
      intro k hk
      have hMono : ∀ n, n ≤ ps.length → L (n + 1) k = true → L 1 k = true := by
        intro n hn
        induction n with
        | zero => exact id
        | succ n ih =>
          intro hn1
          apply ih (by omega)
          rw [← hLink ⟨n + 1, by simp; omega⟩ k, hn1]
          rfl
      exact hMono ps.length (le_refl _) hk
    have hSplit := dyingPot_split (store := store) (s := s) (env := env) (slots := slots)
      (paid := paid) (L 0) (L 1) (L (ps.length + 1)) h01 hTailLive
    have hf (hdv : d = false) : (args first).fits funs fits env = true := by
      cases hv : (args first).fits funs fits env
      · rw [hd first (by simp [hv])] at hdv
        exact nomatch hdv
      · rfl
    have hSum : argsSum (fieldCost funs flags bounds (slots.map Slot.mode) paid L args env) =
        fieldCost funs flags bounds (slots.map Slot.mode) paid L args env first +
          argsSum (fieldCost funs flags bounds (slots.map Slot.mode) paid (fun n => L (n + 1))
            (fun i : Fin ps.length => args i.succ) env) := rfl
    simp only [argsCode, List.append_assoc]
    refine (hSpec first).owned hCopy hh hpv
      (by rw [hIn]; exact hVars.mono (by omega)) hAt (fun hs => by rw [hIn]; exact hAl hs)
      (by rw [hIn]; exact hSafe)
      hCap (by omega) (hRoom first)
      (hPlace first) (rest := storeCode h fieldBase p.types ++ _)
      (hTrap.allocPart (hd first) (fun _ hw => hw.mono (by
        rw [hIn]
        simp only [List.length_cons]
        rw [hSum, hSplit]
        simp only [fieldCost, first, Nat.zero_add]
        omega))) fun heap1 store1 s1 ws1 a1 hAl1 hTop1 => ?_
    rw [hIn] at a1 hTop1
    have hLen : ws1.length = w := a1.rep.length.trans (hWidth first)
    refine wpX_storeCode ws1 h fieldBase p.types s1 s.values
      (hLen.trans hTyLen.symm) (a1.frame.positions.trans hh)
      (by rw [a1.frame.params]; omega)
      (by rw [hTyLen, a1.frame.positions, hh]; have := hRoom first; omega)
      fun sStored hStore holdFirst _ => ?_
    let sNext : Locals := { sStored with values := s.values }
    have hFrame1 : Frame fieldBase s sNext :=
      (a1.frame.mono (by omega)).trans (hStore.trans Frame.ofValues)
    have aStored : After env slots (L 0) (L 1) base heap store s p .owned
        ((args first).denote funs env) heap1 store1 sNext ws1 :=
      (a1.lower hVars (by omega) h01).reframe ((hStore.mono hBaseField).trans Frame.ofValues)
    have hDr : dyingPot store1 sNext env slots paid (L 1) (L (ps.length + 1)) =
        dyingPot store s env slots paid (L 1) (L (ps.length + 1)) :=
      dyingPot_after hVars aStored h01 _ _ (fun _ hi => hi)
    have hTail := fieldsWidth_specX hCopy ps (fun i => args i.succ) (fun n => L (n + 1))
      (fun i => hWidth i.succ) (fun i => hLink i.succ)
      (fun i => hSpec i.succ) (fun i => hPlace i.succ) (fun i => hd i.succ)
      (fieldBase := fieldBase + w) (by omega) (by omega) (fun i => hRoom i.succ)
      heap1 store1 sNext (hFrame1.positions.trans hh) (hFrame1.params.trans hpv)
      (by rw [hFrame1.params]; exact hBase) aStored.holds aStored.step.at_
      (fun hs => HoldsA.after hVars (hAl hs) aStored h01 (hAl1 hs).1.1)
      ((hSafe.after hVars aStored h01).1)
      (by rw [aStored.step.cap m]; exact hCap) rest Q
      (hTrap.allocPart id (fun hdv hw => by
        rw [hDr]
        apply hw.shift (heap1 := heap1) (store1 := store1)
          (by simpa only [fieldCost, Nat.add_assoc] using hTop1 (hf hdv))
          (by simp only [List.length_cons]; rw [hSum, hSplit]
              simp only [fieldCost, first, Nat.zero_add]; omega)
          (aStored.step.cap m)))
      (fun heap2 store2 s2 ws2 a2 hAl2 hFrame2 holdRest hTop2 => by
        have aBoth := FieldsAfter.prepend hVars aStored a2 h01 hTailLive
        refine hNext heap2 store2 s2 (ws1 ++ ws2) aBoth
          (fun hs => ⟨(hAl2 hs).1, FieldsAligned.prepend aStored a2 (hAl1 hs).2 (hAl2 hs).2⟩)
          (hFrame1.trans (hFrame2.mono (by omega))) ?_ ?_
        · rw [List.flatMap_cons]
          apply (LocalsHold.append (tys1 := p.types)
            (tys2 := ps.flatMap Ty.types) (first := ws1) (second := ws2)
            (hLen.trans hTyLen.symm)).mpr
          refine ⟨?_, ?_⟩
          · intro k hk
            have hStored := holdFirst k hk
            have hSlot := Frame.slot hFrame2 (p := fieldBase + k) (by omega) (p.types.getD k .i64)
            rw [hFrame2.positions, hSlot]
            exact hStored
          · simpa only [hLen] using holdRest
        · intro hdv
          have h1 := hTop1 (hf hdv)
          have h2 := hTop2 hdv
          rw [hDr] at h2
          simp only [List.length_cons]
          rw [hSum, hSplit]
          simp only [fieldCost, first, Nat.zero_add]
          simp only [first, Nat.zero_add] at h1
          omega)
    have hIndex : ∀ n : Nat, fieldBase + w + w * n = fieldBase + w * (n + 1) := fun n => by
      rw [Nat.mul_succ]
      omega
    simp only [hIndex] at hTail
    simpa only [Fin.val_succ, List.get_cons_succ', List.append_assoc] using hTail

theorem fields_specX {strict : Bool} {S : List Sig} {Γ : List Ty} {m : Module} {funs : Funs S}
    {flags : Flags S} {bounds : Bounds S} {fits : Fits S} {host : HostEnv Unit}
    {pv : List Value} (hCopy : CopyCodeX strict m host) {env : Env Γ} {slots : List Slot} {paid : List Bool}
    {h base fieldBase scratch : Nat} {d : Bool}
    (ps : List Ty) (args : (i : Fin ps.length) → Expr S Γ (ps.get i))
    (L : Nat → Nat → Bool)
    (hWidth : ∀ i, (ps.get i).width = 1)
    (hLink : ∀ i k, (L (i.val + 1) k || (args i).uses k) = L i.val k)
    (hSpec : ∀ i, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv (args i) env slots paid
      (L (i.val + 1)))
    (hPlace : ∀ i, (args i).placeArgs = true)
    (hd : ∀ i, (!(args i).fits funs fits env) = true → d = true)
    (hBaseField : base ≤ fieldBase) (hScratch : fieldBase + ps.length ≤ scratch)
    (hRoom : ∀ i, scratch + max (args i).width (copyWidth (ps.get i)) ≤ h)
    (heap : Heap) (store : Store Unit) (s : Locals)
    (hh : s.positions = h) (hpv : s.params = pv) (hBase : s.params.length ≤ base)
    (hVars : Holds env slots (L 0) base heap store s) (hAt : heap.At store)
    (hAl : strict = true → HoldsA env slots (L 0) heap store s)
    (hSafe : pool.Safe env slots (L 0) heap store s) (hCap : store.memoryCap m 0 ≤ 65535)
    (rest : Program) (Q : Assertion Unit)
    (hTrap : TrapOK (d || !decide (heap.Within store m
      (dyingPot store s env slots paid (L 0) (L ps.length) +
        argsSum (fieldCost funs flags bounds (slots.map Slot.mode) paid L args env)))) Q)
    (hNext : ∀ heap' store' s' ws,
      FieldsAfter env slots (L 0) (L ps.length) base heap store s
        (Env.ofFn fun i => (args i).denote funs env) heap' store' s' ws →
      (strict = true → HoldsA env slots (L ps.length) heap' store' s' ∧
        FieldsAligned store' (Env.ofFn fun i => (args i).denote funs env) ws) →
      Frame fieldBase s s' → LocalsHold s' fieldBase (ps.flatMap Ty.types) ws →
      (d = false → heap'.top.toNat ≤ heap.top.toNat +
        dyingPot store s env slots paid (L 0) (L ps.length) +
        argsSum (fieldCost funs flags bounds (slots.map Slot.mode) paid L args env)) →
      wpX strict m rest Q store' { s' with values := s.values } host) :
    wpX strict m (argsCode (fun i => (args i).code (pool := pool) h slots scratch (L (i.val + 1)) ++
      coerceCode h (ps.get i) ((args i).mode (slots.map Slot.mode)) .owned scratch ++
      storeCode h (fieldBase + i.val) (ps.get i).types) ++ rest) Q store s host := by
  have hRun := fieldsWidth_specX (w := 1) hCopy ps args L hWidth hLink hSpec hPlace hd hBaseField
    (by rw [Nat.one_mul]; exact hScratch) hRoom heap store s hh hpv hBase hVars hAt hAl hSafe hCap
    rest Q hTrap hNext
  simpa only [Nat.one_mul] using hRun

end

end Verified
