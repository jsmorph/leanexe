import Verified.OwnedExpr
import Verified.FieldsAfter

namespace Verified

variable {pool : Bytes.LiteralPool}

open Wasm LeanExe.Pipeline LeanExe.Runtime

def fieldCost {S : List Sig} {Γ : List Ty} {ps : List Ty} (funs : Funs S) (flags : Flags S)
    (bounds : Bounds S) (modes : List Mode) (paid : List Bool) (L : Nat → Nat → Bool)
    (args : (i : Fin ps.length) → Expr S Γ (ps.get i)) (env : Env Γ)
    (i : Fin ps.length) : Nat :=
  (args i).allocs funs flags bounds modes paid (L (i.val + 1)) env +
    coerceCost (ps.get i) ((args i).mode modes) .owned ((args i).denote funs env)

theorem fields_spec {S : List Sig} {Γ : List Ty} {m : Module} {funs : Funs S}
    {flags : Flags S} {bounds : Bounds S} {fits : Fits S} {host : HostEnv Unit}
    {pv : List Value} (hm : Runtime m) {env : Env Γ} {slots : List Slot} {paid : List Bool}
    {h base fieldBase scratch : Nat} {d : Bool} :
    (ps : List Ty) → (args : (i : Fin ps.length) → Expr S Γ (ps.get i)) →
    (L : Nat → Nat → Bool) →
    (∀ i, (ps.get i).width = 1) → (∀ i, (ps.get i).types = [.i64]) →
    (∀ i k, (L (i.val + 1) k || (args i).uses k) = L i.val k) →
    (∀ i, CodeSpec (pool := pool) m funs flags bounds fits host pv (args i) env slots paid (L (i.val + 1))) →
    (∀ i, (args i).placeArgs = true) →
    (∀ i, (!(args i).fits funs fits env) = true → d = true) →
    base ≤ fieldBase → fieldBase + ps.length ≤ scratch →
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
      Frame fieldBase s s' → LocalsHold s' fieldBase (List.replicate ps.length .i64) ws →
      (d = false → heap'.top.toNat ≤ heap.top.toNat +
        dyingPot store s env slots paid (L 0) (L ps.length) +
        argsSum (fieldCost funs flags bounds (slots.map Slot.mode) paid L args env)) →
      wp m rest Q store' { s' with values := s.values } host) →
    wp m (argsCode (fun i => (args i).code (pool := pool) h slots scratch (L (i.val + 1)) ++
      coerceCode h (ps.get i) ((args i).mode (slots.map Slot.mode)) .owned scratch ++
      storeCode h (fieldBase + i.val) (ps.get i).types) ++ rest) Q store s host
  | [], _, L, _, _, _, _, _, _, _, _, _, heap, store, s, _, _, _, hVars, hAt, _, _, rest, Q, _,
      hNext => by
    simpa only [argsCode, List.nil_append, Env.ofFn] using
      hNext heap store s [] (FieldsAfter.nil hAt hVars) (Frame.refl fieldBase s)
        (fun k hk => nomatch hk) (fun _ => by simp [argsSum])
  | p :: ps, args, L, hWidth, hTypes, hLink, hSpec, hPlace, hd, hBaseField, hScratch,
      hRoom, heap, store, s, hh, hpv, hBase, hVars, hAt, hSafe, hCap, rest, Q, hTrap, hNext => by
    let first : Fin (p :: ps).length := ⟨0, by simp⟩
    have hTypes0 : p.types = [.i64] := hTypes first
    simp only [List.length_cons] at hScratch
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
    have hLen : ws1.length = 1 := a1.rep.length.trans (hWidth first)
    refine wp_storeCode ws1 h fieldBase p.types s1 s.values
      (by rw [hTypes0]; exact hLen) (a1.frame.positions.trans hh)
      (by rw [a1.frame.params]; omega)
      (by rw [hTypes0, a1.frame.positions, hh]; simp; have := hRoom first; omega)
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
    have hTail := fields_spec hm ps (fun i => args i.succ) (fun n => L (n + 1))
      (fun i => hWidth i.succ) (fun i => hTypes i.succ) (fun i => hLink i.succ)
      (fun i => hSpec i.succ) (fun i => hPlace i.succ) (fun i => hd i.succ)
      (fieldBase := fieldBase + 1) (by omega) (by omega) (fun i => hRoom i.succ)
      heap1 store1 sNext (hFrame1.positions.trans hh) (hFrame1.params.trans hpv)
      (by rw [hFrame1.params]; exact hBase) aStored.holds aStored.step.at_
      ((hSafe.after hVars aStored h01).1)
      (by rw [aStored.step.cap m]; exact hCap) rest Q
      (hTrap.allocPart id (fun hdv hw => by
        rw [hDr]
        apply hw.shift (heap1 := heap1) (store1 := store1)
          (by simpa only [fieldCost, Nat.add_assoc] using hTop1 (hf hdv))
          (by simp only [List.length_cons]; rw [hSum, hSplit]
              simp only [fieldCost, first, Nat.zero_add]; omega)
          (aStored.step.cap m)))
      (fun heap2 store2 s2 ws2 a2 hFrame2 holdRest hTop2 => by
        have aBoth := FieldsAfter.prepend hVars aStored a2 h01 hTailLive
        refine hNext heap2 store2 s2 (ws1 ++ ws2) aBoth
          (hFrame1.trans (hFrame2.mono (by omega))) ?_ ?_
        · rw [List.length_cons, List.replicate_succ]
          apply (LocalsHold.append (tys1 := [.i64])
            (tys2 := List.replicate ps.length .i64) (first := ws1) (second := ws2) hLen).mpr
          refine ⟨?_, ?_⟩
          · rw [hTypes0] at holdFirst
            intro k hk
            have hk0 : k = 0 := by omega
            subst hk0
            simpa only [slotIndex, Nat.add_zero, List.getD_cons_zero] using
              (hFrame2.below fieldBase (by omega)).1.trans (holdFirst 0 (by omega))
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
    simpa only [Fin.val_succ, List.get_cons_succ', Nat.add_assoc, Nat.add_comm 1,
      List.append_assoc] using hTail

end Verified
