import Verified.FieldsExpr
import Verified.Bytes.Normalize

namespace Verified

variable {pool : Bytes.LiteralPool}

open Wasm LeanExe.Pipeline LeanExe.Runtime

/-- The words of buffers, a root and a length each, in which the root of every empty buffer
is 0. -/
def Bytes.Normal : List Value → Prop
  | [] => True
  | [_] => True
  | root :: length :: rest => (length = .i64 0 → root = .i64 0) ∧ Bytes.Normal rest

/-- An owned empty buffer whose object a step releases: the value is the same buffer, with
root 0. -/
theorem After.releaseBytes {Γ : List Ty} {env : Env Γ} {slots : List Slot} {L0 L : Nat → Bool}
    {base : Nat} {heap heap1 heap2 : Heap} {store store1 store2 : Store Unit} {s s1 : Locals}
    {v : LeanExe.Bytes} {p length : UInt64}
    (a : After env slots L0 L base heap store s .bytes .owned v heap1 store1 s1
      [.i64 p, .i64 length])
    (hStep : Step heap1 store1 (fun r => ∀ b ∈ Bytes.regions store1 p, regionsDisjoint r b)
      heap2 store2 [])
    (hEmpty : v.data.size = 0) :
    After env slots L0 L base heap store s .bytes .owned v heap2 store2 s1
      [.i64 0, .i64 length] := by
  have hBlocks : Ty.blocks store1 .bytes [.i64 p, .i64 length] v = Bytes.regions store1 p :=
    Bytes.roots_regions store1 p length
  have hKeep : ∀ (u : Ty) (y : Var Γ u), L y.index = true → ∀ wy,
      LocalsHold s1 (slots.getD y.index default).loc u.types wy → wy.length = u.width →
      ∀ c ∈ u.regions (slots.getD y.index default).mode store1 wy (env.get y),
        ∀ b ∈ Bytes.regions store1 p, regionsDisjoint c b := fun u y hy wy hwy hly c hc b hb =>
    regionsDisjoint_symm (a.apart u y hy (Or.inl rfl) wy hwy hly b
      (by change b ∈ Ty.blocks store1 .bytes [.i64 p, .i64 length] v; rw [hBlocks]; exact hb)
      c hc)
  have hStep2 := a.step.transBoth (keep := Holds.KeepDying env slots L0 L store s) hStep
    fun _ hr => ⟨hr, fun hf b hb => hf b (by
      change b ∈ Ty.blocks store1 .bytes [.i64 p, .i64 length] v; rw [hBlocks]; exact hb)⟩
  obtain ⟨root, len, hWords, hRep⟩ := a.rep
  simp only [List.cons.injEq, Value.i64.injEq, and_true] at hWords
  obtain ⟨rfl, rfl⟩ := hWords
  refine ⟨hStep2.mono (fun _ h => h) fun b hb => by
      simp [Mode.fresh, Ty.blocks, Bytes.roots] at hb,
    a.frame, a.holds.step hStep hKeep,
    ⟨0, _, rfl, hRep.length_eq, Or.inl ⟨rfl, hEmpty⟩⟩, ?_⟩
  intro u y hy _ wy hwy hly b hb
  simp [Ty.regions, Ty.blocks, Bytes.roots] at hb

/-- Buffer arguments evaluated in order, each coerced to owned, stored in two locals from
`fieldBase + 2 * i` on, and normalized, so that the root of an empty buffer is 0. -/
theorem bytesFields_spec {S : List Sig} {Γ : List Ty} {m : Module} {funs : Funs S}
    {flags : Flags S} {bounds : Bounds S} {fits : Fits S} {host : HostEnv Unit}
    {pv : List Value} (hm : Runtime m) {env : Env Γ} {slots : List Slot} {paid : List Bool}
    {h base fieldBase scratch : Nat} {d : Bool} :
    (ps : List Ty) → (args : (i : Fin ps.length) → Expr S Γ (ps.get i)) →
    (L : Nat → Nat → Bool) →
    (∀ i, ps.get i = .bytes) →
    (∀ i k, (L (i.val + 1) k || (args i).uses k) = L i.val k) →
    (∀ i, CodeSpec (pool := pool) m funs flags bounds fits host pv (args i) env slots paid
      (L (i.val + 1))) →
    (∀ i, (args i).placeArgs = true) →
    (∀ i, (!(args i).fits funs fits env) = true → d = true) →
    base ≤ fieldBase → fieldBase + 2 * ps.length ≤ scratch →
    (∀ i, scratch + max (args i).width (copyWidth (ps.get i)) ≤ h) →
    ∀ (heap : Heap) (store : Store Unit) (s : Locals),
    s.positions = h → s.params = pv → s.params.length ≤ base →
    Holds env slots (L 0) base heap store s → heap.At store →
    pool.Safe env slots (L 0) heap store s → store.memoryCap m 0 ≤ 65535 →
    ∀ (rest : Program) (Q : Assertion Unit),
    TrapOK (d || !decide (heap.Within store m
      (dyingPot store s env slots paid (L 0) (L ps.length) +
        argsSum (fieldCost funs flags bounds (slots.map Slot.mode) paid L args env)))) Q →
    (∀ heap' store' s' ws,
      FieldsAfter env slots (L 0) (L ps.length) base heap store s
        (Env.ofFn fun i => (args i).denote funs env) heap' store' s' ws →
      Frame fieldBase s s' → LocalsHold s' fieldBase (ps.flatMap Ty.types) ws →
      Bytes.Normal ws →
      (d = false → heap'.top.toNat ≤ heap.top.toNat +
        dyingPot store s env slots paid (L 0) (L ps.length) +
        argsSum (fieldCost funs flags bounds (slots.map Slot.mode) paid L args env)) →
      wp m rest Q store' { s' with values := s.values } host) →
    wp m (argsCode (fun i => (args i).code (pool := pool) h slots scratch (L (i.val + 1)) ++
      coerceCode h (ps.get i) ((args i).mode (slots.map Slot.mode)) .owned scratch ++
      storeCode h (fieldBase + 2 * i.val) (ps.get i).types ++
      Bytes.normalizeCode (fieldBase + 2 * i.val) (fieldBase + 2 * i.val + 1)) ++ rest)
      Q store s host
  | [], _, L, _, _, _, _, _, _, _, _, heap, store, s, _, _, _, hVars, hAt, _, _, rest, Q, _,
      hNext => by
    simpa only [argsCode, List.nil_append, Env.ofFn] using
      hNext heap store s [] (FieldsAfter.nil hAt hVars) (Frame.refl fieldBase s)
        (fun k hk => nomatch hk) trivial (fun _ => by simp [argsSum])
  | p :: ps, args, L, hBytes, hLink, hSpec, hPlace, hd, hBaseField, hScratch,
      hRoom, heap, store, s, hh, hpv, hBase, hVars, hAt, hSafe, hCap, rest, Q, hTrap, hNext => by
    let first : Fin (p :: ps).length := ⟨0, by simp⟩
    have hp : p = .bytes := hBytes first
    subst hp
    have hTyLen : Ty.bytes.types.length = 2 := rfl
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
    refine (hSpec first).owned hm hh hpv
      (by rw [hIn]; exact hVars.mono (by omega)) hAt (by rw [hIn]; exact hSafe)
      hCap (by omega) (hRoom first)
      (hPlace first) (rest := storeCode h fieldBase Ty.bytes.types ++ _)
      (hTrap.allocPart (hd first) (fun _ hw => hw.mono (by
        rw [hIn]
        simp only [List.length_cons]
        rw [hSum, hSplit]
        simp only [fieldCost, first, Nat.zero_add]
        omega))) fun heap1 store1 s1 ws1 a1 hTop1 => ?_
    rw [hIn] at a1 hTop1
    have hLen : ws1.length = 2 := a1.rep.length
    refine wp_storeCode ws1 h fieldBase Ty.bytes.types s1 s.values
      (hLen.trans hTyLen.symm) (a1.frame.positions.trans hh)
      (by rw [a1.frame.params]; omega)
      (by rw [hTyLen, a1.frame.positions, hh]; have := hRoom first; omega)
      fun sStored hStore holdFirst _ => ?_
    let sNext : Locals := { sStored with values := s.values }
    have hFrame1 : Frame fieldBase s sNext :=
      (a1.frame.mono (by omega)).trans (hStore.trans Frame.ofValues)
    have aStored : After env slots (L 0) (L 1) base heap store s .bytes .owned
        ((args first).denote funs env) heap1 store1 sNext ws1 :=
      (a1.lower hVars (by omega) h01).reframe ((hStore.mono hBaseField).trans Frame.ofValues)
    -- The rest of the arguments, from a normalized first buffer.
    have key : ∀ (heap1' : Heap) (store1' : Store Unit) (sCore : Locals) (ws1' : List Value),
        After env slots (L 0) (L 1) base heap store s .bytes .owned
          ((args first).denote funs env) heap1' store1' { sCore with values := s.values } ws1' →
        Frame fieldBase s { sCore with values := s.values } →
        LocalsHold { sCore with values := s.values } fieldBase Ty.bytes.types ws1' →
        ws1'.length = 2 → heap1'.top.toNat ≤ heap1.top.toNat → Bytes.Normal ws1' →
        wp m (argsCode (fun i : Fin ps.length =>
          (args i.succ).code (pool := pool) h slots scratch (L (i.val + 1 + 1)) ++
          coerceCode h (ps.get i) ((args i.succ).mode (slots.map Slot.mode)) .owned scratch ++
          storeCode h (fieldBase + 2 * (i.val + 1)) (ps.get i).types ++
          Bytes.normalizeCode (fieldBase + 2 * (i.val + 1)) (fieldBase + 2 * (i.val + 1) + 1)) ++
          rest) Q store1' { sCore with values := s.values } host := by
      intro heap1' store1' sCore ws1' aNorm hFrameNorm holdNorm hLenNorm hTopNorm hNormal
      have hDr : dyingPot store1' { sCore with values := s.values } env slots paid (L 1)
          (L (ps.length + 1)) = dyingPot store s env slots paid (L 1) (L (ps.length + 1)) :=
        dyingPot_after hVars aNorm h01 _ _ (fun _ hi => hi)
      have hTail := bytesFields_spec hm ps (fun i => args i.succ) (fun n => L (n + 1))
        (fun i => hBytes i.succ) (fun i => hLink i.succ)
        (fun i => hSpec i.succ) (fun i => hPlace i.succ) (fun i => hd i.succ)
        (fieldBase := fieldBase + 2) (by omega) (by omega) (fun i => hRoom i.succ)
        heap1' store1' { sCore with values := s.values } (hFrameNorm.positions.trans hh)
        (hFrameNorm.params.trans hpv)
        (by rw [hFrameNorm.params]; exact hBase) aNorm.holds aNorm.step.at_
        ((hSafe.after hVars aNorm h01).1)
        (by rw [aNorm.step.cap m]; exact hCap) rest Q
        (hTrap.allocPart id (fun hdv hw => by
          rw [hDr]
          apply hw.shift (heap1 := heap1') (store1 := store1')
            (le_trans hTopNorm
              (by simpa only [fieldCost, Nat.add_assoc] using hTop1 (hf hdv)))
            (by simp only [List.length_cons]; rw [hSum, hSplit]
                simp only [fieldCost, first, Nat.zero_add]; omega)
            (aNorm.step.cap m)))
        (fun heap2 store2 s2 ws2 a2 hFrame2 holdRest hNormalRest hTop2 => by
          have aBoth := FieldsAfter.prepend hVars aNorm a2 h01 hTailLive
          refine hNext heap2 store2 s2 (ws1' ++ ws2) aBoth
            (hFrameNorm.trans (hFrame2.mono (by omega))) ?_ ?_ ?_
          · rw [List.flatMap_cons]
            apply (LocalsHold.append (tys1 := Ty.bytes.types)
              (tys2 := ps.flatMap Ty.types) (first := ws1') (second := ws2)
              (hLenNorm.trans hTyLen.symm)).mpr
            refine ⟨?_, ?_⟩
            · intro k hk
              have hStored := holdNorm k hk
              have hSlot := Frame.slot hFrame2 (p := fieldBase + k) (by omega)
                (Ty.bytes.types.getD k .i64)
              rw [hFrame2.positions, hSlot]
              exact hStored
            · simpa only [hLenNorm] using holdRest
          · obtain ⟨w0, w1, rfl⟩ := List.length_eq_two.mp hLenNorm
            exact ⟨hNormal.1, hNormalRest⟩
          · intro hdv
            have h1 := hTop1 (hf hdv)
            have h2 := hTop2 hdv
            rw [hDr] at h2
            simp only [List.length_cons]
            rw [hSum, hSplit]
            simp only [fieldCost, first, Nat.zero_add]
            simp only [first, Nat.zero_add] at h1
            omega)
      have hIndex : ∀ n : Nat, fieldBase + 2 + 2 * n = fieldBase + 2 * (n + 1) := fun n => by
        omega
      simp only [hIndex] at hTail
      exact hTail
    obtain ⟨root, length, rfl, hRep⟩ := aStored.rep
    have hRootLocal : sNext.get fieldBase = some (.i64 root) := by
      have := holdFirst 0 (by simp)
      simpa [slotIndex, Ty.types] using this
    have hLengthLocal : sNext.get (fieldBase + 1) = some (.i64 length) := by
      have := holdFirst 1 (by simp)
      simpa [slotIndex, Ty.types] using this
    have hLowRoot : sNext.params.length ≤ fieldBase := by
      rw [hFrame1.params]; omega
    have hHighRoot : fieldBase < sNext.params.length + sNext.locals.length :=
      Locals.lt_total (by rw [hFrame1.positions, hh]; have := hRoom first; omega)
    have hRoomRoot : fieldBase + 1 < sNext.positions := by
      rw [hFrame1.positions, hh]; have := hRoom first; omega
    refine Bytes.wp_normalize hm aStored.step.at_ hRep hRootLocal hLengthLocal hLowRoot hHighRoot
      (fun hZero => ?_) (fun hFull => ?_)
    · subst hZero
      have hEmpty : ((args first).denote funs env).data.size = 0 := by
        have := hRep.length_eq
        simpa using this.symm
      obtain ⟨hRelease, hTopRelease⟩ := hRep.release_step aStored.step.at_
      have aNorm := (aStored.releaseBytes hRelease hEmpty).reframe
        ((Frame.setValues (vs := s.values) (v := .i64 0) hLowRoot hBaseField
          (by omega)).trans (Frame.ofValues (values := s.values)))
      have holdNorm : LocalsHold { setLocal sNext fieldBase (.i64 0) with values := s.values }
          fieldBase Ty.bytes.types [.i64 0, .i64 0] := by
        intro k hk
        match k, hk with
        | 0, _ =>
          show (setLocal sNext fieldBase (.i64 0)).get fieldBase = some (.i64 0)
          exact Locals.get_setLocal_same hLowRoot hHighRoot
        | 1, _ =>
          have hne : fieldBase + 1 ≠ fieldBase := by omega
          show (setLocal sNext fieldBase (.i64 0)).get (fieldBase + 1) = some (.i64 0)
          rw [Locals.get_setLocal_ne hLowRoot hne]
          exact hLengthLocal
        | k + 2, hk => simp at hk
      have hRun := key _ _ (setLocal sNext fieldBase (.i64 0)) [.i64 0, .i64 0] aNorm
        (hFrame1.trans ((Frame.setValues (vs := s.values) (v := .i64 0) hLowRoot
          (Nat.le_refl _) (by omega)).trans (Frame.ofValues (values := s.values))))
        holdNorm rfl (by rw [hTopRelease]) ⟨fun _ => rfl, trivial⟩
      simpa only [Fin.val_succ, List.get_cons_succ', List.append_assoc, Nat.mul_zero,
        Nat.add_zero] using hRun
    · have hRun := key heap1 store1 sNext [.i64 root, .i64 length] aStored hFrame1 holdFirst rfl
        (Nat.le_refl _) ⟨fun h => absurd (by simpa using h) hFull, trivial⟩
      simpa only [Fin.val_succ, List.get_cons_succ', List.append_assoc, Nat.mul_zero,
        Nat.add_zero] using hRun

end Verified
