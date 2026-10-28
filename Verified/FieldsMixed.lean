import Verified.FieldsBytes

namespace Verified

variable {pool : Bytes.LiteralPool}

open Wasm LeanExe.Pipeline LeanExe.Runtime

/-- The code after the store of an argument of type `t` in the locals from `loc` on: the
normalization of a buffer, and nothing for a value of another type. -/
def Ty.normalizeCode : Ty → Nat → Program
  | .bytes, loc => Bytes.normalizeCode loc (loc + 1)
  | _, _ => []

/-- The first local of argument `i` among arguments of the types `ps`, relative to the first
argument's. -/
def fieldOffset (ps : List Ty) (i : Nat) : Nat := ((ps.take i).map Ty.width).sum

theorem fieldOffset_zero (ps : List Ty) : fieldOffset ps 0 = 0 := by
  simp [fieldOffset]

theorem fieldOffset_succ (p : Ty) (ps : List Ty) (i : Nat) :
    fieldOffset (p :: ps) (i + 1) = p.width + fieldOffset ps i := by
  simp [fieldOffset]

/-- The words of a value of type `t` whose buffer, if it is one, has root 0 when it is empty. -/
def Ty.Normal : Ty → List Value → Prop
  | .bytes, ws => Bytes.Normal ws
  | _, _ => True

/-- The words of values of the types `ps`, each as `Ty.Normal` states. -/
def FieldsNormal : List Ty → List Value → Prop
  | [], _ => True
  | p :: ps, ws => p.Normal (ws.take p.width) ∧ FieldsNormal ps (ws.drop p.width)

/-- Arguments evaluated in order, each coerced to owned and stored in the locals from
`fieldBase` plus the widths of the arguments before it, a buffer then normalized so that the
root of an empty buffer is 0. -/
theorem fieldsMixed_spec {S : List Sig} {Γ : List Ty} {m : Module} {funs : Funs S}
    {flags : Flags S} {bounds : Bounds S} {fits : Fits S} {host : HostEnv Unit}
    {pv : List Value} (hm : Runtime m) {env : Env Γ} {slots : List Slot} {paid : List Bool}
    {h base fieldBase scratch : Nat} {d : Bool} :
    (ps : List Ty) → (args : (i : Fin ps.length) → Expr S Γ (ps.get i)) →
    (L : Nat → Nat → Bool) →
    (∀ i k, (L (i.val + 1) k || (args i).uses k) = L i.val k) →
    (∀ i, CodeSpec (pool := pool) m funs flags bounds fits host pv (args i) env slots paid
      (L (i.val + 1))) →
    (∀ i, (args i).placeArgs = true) →
    (∀ i, (!(args i).fits funs fits env) = true → d = true) →
    base ≤ fieldBase → fieldBase + (ps.map Ty.width).sum ≤ scratch →
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
      FieldsNormal ps ws →
      (d = false → heap'.top.toNat ≤ heap.top.toNat +
        dyingPot store s env slots paid (L 0) (L ps.length) +
        argsSum (fieldCost funs flags bounds (slots.map Slot.mode) paid L args env)) →
      wp m rest Q store' { s' with values := s.values } host) →
    wp m (argsCode (fun i => (args i).code (pool := pool) h slots scratch (L (i.val + 1)) ++
      coerceCode h (ps.get i) ((args i).mode (slots.map Slot.mode)) .owned scratch ++
      storeCode h (fieldBase + fieldOffset ps i.val) (ps.get i).types ++
      (ps.get i).normalizeCode (fieldBase + fieldOffset ps i.val)) ++ rest)
      Q store s host
  | [], _, L, _, _, _, _, _, _, _, heap, store, s, _, _, _, hVars, hAt, _, _, rest, Q, _,
      hNext => by
    simpa only [argsCode, List.nil_append, Env.ofFn] using
      hNext heap store s [] (FieldsAfter.nil hAt hVars) (Frame.refl fieldBase s)
        (fun k hk => nomatch hk) trivial (fun _ => by simp [argsSum])
  | p :: ps, args, L, hLink, hSpec, hPlace, hd, hBaseField, hScratch,
      hRoom, heap, store, s, hh, hpv, hBase, hVars, hAt, hSafe, hCap, rest, Q, hTrap, hNext => by
    let first : Fin (p :: ps).length := ⟨0, by simp⟩
    have hTyLen : p.types.length = p.width := Ty.types_length p
    simp only [List.map_cons, List.sum_cons] at hScratch
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
      (hPlace first) (rest := storeCode h fieldBase p.types ++ _)
      (hTrap.allocPart (hd first) (fun _ hw => hw.mono (by
        rw [hIn]
        simp only [List.length_cons]
        rw [hSum, hSplit]
        simp only [fieldCost, first, Nat.zero_add]
        omega))) fun heap1 store1 s1 ws1 a1 hTop1 => ?_
    rw [hIn] at a1 hTop1
    have hLen : ws1.length = p.width := a1.rep.length
    refine wp_storeCode ws1 h fieldBase p.types s1 s.values
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
    -- The rest of the arguments, from the first argument's normalized words.
    have key : ∀ (heap1' : Heap) (store1' : Store Unit) (sCore : Locals) (ws1' : List Value),
        After env slots (L 0) (L 1) base heap store s p .owned
          ((args first).denote funs env) heap1' store1' { sCore with values := s.values } ws1' →
        Frame fieldBase s { sCore with values := s.values } →
        LocalsHold { sCore with values := s.values } fieldBase p.types ws1' →
        ws1'.length = p.width → heap1'.top.toNat ≤ heap1.top.toNat → p.Normal ws1' →
        wp m (argsCode (fun i : Fin ps.length =>
          (args i.succ).code (pool := pool) h slots scratch (L (i.val + 1 + 1)) ++
          coerceCode h (ps.get i) ((args i.succ).mode (slots.map Slot.mode)) .owned scratch ++
          storeCode h (fieldBase + (p.width + fieldOffset ps i.val)) (ps.get i).types ++
          (ps.get i).normalizeCode (fieldBase + (p.width + fieldOffset ps i.val))) ++
          rest) Q store1' { sCore with values := s.values } host := by
      intro heap1' store1' sCore ws1' aNorm hFrameNorm holdNorm hLenNorm hTopNorm hNormal
      have hDr : dyingPot store1' { sCore with values := s.values } env slots paid (L 1)
          (L (ps.length + 1)) = dyingPot store s env slots paid (L 1) (L (ps.length + 1)) :=
        dyingPot_after hVars aNorm h01 _ _ (fun _ hi => hi)
      have hTail := fieldsMixed_spec hm ps (fun i => args i.succ) (fun n => L (n + 1))
        (fun i => hLink i.succ)
        (fun i => hSpec i.succ) (fun i => hPlace i.succ) (fun i => hd i.succ)
        (fieldBase := fieldBase + p.width) (by omega) (by omega) (fun i => hRoom i.succ)
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
            apply (LocalsHold.append (tys1 := p.types)
              (tys2 := ps.flatMap Ty.types) (first := ws1') (second := ws2)
              (hLenNorm.trans hTyLen.symm)).mpr
            refine ⟨?_, ?_⟩
            · intro k hk
              have hStored := holdNorm k hk
              have hSlot := Frame.slot hFrame2 (p := fieldBase + k) (by omega)
                (p.types.getD k .i64)
              rw [hFrame2.positions, hSlot]
              exact hStored
            · simpa only [hLenNorm] using holdRest
          · refine ⟨?_, ?_⟩
            · rw [List.take_left' hLenNorm]
              exact hNormal
            · rw [List.drop_left' hLenNorm]
              exact hNormalRest
          · intro hdv
            have h1 := hTop1 (hf hdv)
            have h2 := hTop2 hdv
            rw [hDr] at h2
            simp only [List.length_cons]
            rw [hSum, hSplit]
            simp only [fieldCost, first, Nat.zero_add]
            simp only [first, Nat.zero_add] at h1
            omega)
      simpa only [Nat.add_assoc] using hTail
    cases p
    case bytes =>
      have hWidth : Ty.bytes.width = 2 := rfl
      rw [hWidth] at hScratch
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
      refine Bytes.wp_normalize hm aStored.step.at_ hRep hRootLocal hLengthLocal hLowRoot
        hHighRoot (fun hZero => ?_) (fun hFull => ?_)
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
        simpa only [Fin.val_succ, List.get_cons_succ', List.get_cons_zero, List.append_assoc,
          fieldOffset_succ, fieldOffset_zero, Nat.add_zero] using hRun
      · have hRun := key heap1 store1 sNext [.i64 root, .i64 length] aStored hFrame1 holdFirst
          rfl (Nat.le_refl _) ⟨fun h => absurd (by simpa using h) hFull, trivial⟩
        simpa only [Fin.val_succ, List.get_cons_succ', List.get_cons_zero, List.append_assoc,
          fieldOffset_succ, fieldOffset_zero, Nat.add_zero] using hRun
    all_goals
      have hRun := key heap1 store1 sNext ws1 aStored hFrame1 holdFirst hLen (Nat.le_refl _)
        trivial
      show wp m ([] ++ _) Q store1 _ host
      rw [List.nil_append]
      simpa only [Fin.val_succ, List.get_cons_succ', List.append_assoc, fieldOffset_succ] using hRun

#print axioms fieldsMixed_spec

end Verified
