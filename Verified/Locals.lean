import Verified.Compile
import Verified.LocalFrame

namespace Verified

open Wasm

/-- Positions `loc` to `loc + vals.length - 1` hold `vals`, word `k` in the local of its type
`tys[k]`. -/
def LocalsHold (s : Locals) (loc : Nat) (tys : List ValueType) (vals : List Value) : Prop :=
  ∀ k (hk : k < vals.length), s.get (slotIndex s.positions (loc + k) (tys.getD k .i64)) = some vals[k]

/-- Loading positions that hold `vals` pushes `vals` in order. -/
theorem wp_loadCode {m : Module} {Q : Assertion α} {store : Store α} {host : HostEnv α}
    (vals : List Value) {h loc : Nat} {tys : List ValueType} {s : Locals} {rest : Program}
    (hw : vals.length = tys.length) (hh : s.positions = h) (hold : LocalsHold s loc tys vals)
    (hk : wp m rest Q store { s with values := vals.reverse ++ s.values } host) :
    wp m (loadCode h loc tys ++ rest) Q store s host := by
  induction vals generalizing loc tys s with
  | nil =>
    cases tys with
    | nil => simpa [loadCode] using hk
    | cons _ _ => exact absurd hw (by simp)
  | cons v vs ih =>
    cases tys with
    | nil => exact absurd hw (by simp)
    | cons ty tys =>
      have h0 : s.get (slotIndex h loc ty) = some v := by
        have := hold 0 (by simp)
        rw [hh] at this
        simpa using this
      simp only [loadCode, List.cons_append, wp_localGet_cons, h0]
      refine ih (s := { s with values := v :: s.values }) (by simpa using hw) (by simpa using hh)
        (fun k hk => ?_) ?_
      · have := hold (k + 1) (by simp; omega)
        rw [show loc + (k + 1) = loc + 1 + k by omega] at this
        simpa [-Locals.get] using this
      · simpa [List.append_assoc] using hk

/-- Storing the top words `vals` of the stack, of types `tys`, at positions `loc` on leaves them
there, keeps the frame below `loc`, and changes no position above them below the position bound. -/
theorem wp_storeCode {m : Module} {Q : Assertion α} {store : Store α} {host : HostEnv α}
    {rest : Program} (vals : List Value) (h loc : Nat) (tys : List ValueType) (s : Locals)
    (vs : List Value) (hw : vals.length = tys.length) (hh : s.positions = h)
    (hLow : s.params.length ≤ loc) (hHigh : loc + tys.length ≤ s.positions)
    (hNext : ∀ s', Frame loc s s' → LocalsHold s' loc tys vals →
      (∀ j, loc + tys.length ≤ j → j < s.positions →
        s'.get j = s.get j ∧ s'.get (j + s.positions) = s.get (j + s.positions) ∧
          s'.get (j + 2 * s.positions) = s.get (j + 2 * s.positions)) →
      wp m rest Q store { s' with values := vs } host) :
    wp m (storeCode h loc tys ++ rest) Q store { s with values := vals.reverse ++ vs } host := by
  induction vals generalizing loc tys s vs rest with
  | nil =>
    cases tys with
    | nil =>
      exact hNext s (Frame.refl loc s) (fun k hk => absurd hk (by simp)) fun _ _ _ => ⟨rfl, rfl, rfl⟩
    | cons _ _ => exact absurd hw (by simp)
  | cons v vals ih =>
    cases tys with
    | nil => exact absurd hw (by simp)
    | cons ty tys =>
      simp only [storeCode, List.append_assoc, List.reverse_cons, List.cons_append,
        List.nil_append, List.length_cons] at hHigh ⊢
      have hw' : vals.length = tys.length := by simpa using hw
      refine ih (loc + 1) tys s (v :: vs) hw' hh (by omega) (by omega)
        fun s1 hF1 hold1 habove1 => ?_
      have hh1 : s1.positions = s.positions := hF1.positions
      have hb := slotIndex_bounds (s := s) ty hLow (by omega)
      rw [← hh]
      have hp1 : s1.params.length = s.params.length := by rw [hF1.params]
      have hl1 : s1.locals.length = s.locals.length := hF1.length
      have hLow1 : s1.params.length ≤ slotIndex s.positions loc ty := by rw [hp1]; exact hb.1
      have hHigh1 : slotIndex s.positions loc ty < s1.params.length + s1.locals.length := by
        rw [hp1, hl1]; exact hb.2
      refine wp_localSet_local hLow1 hHigh1 ?_
      have hne : ∀ j, j < loc ∨ loc + 1 + tys.length ≤ j → j < s.positions →
          j ≠ slotIndex s.positions loc ty ∧ j + s.positions ≠ slotIndex s.positions loc ty ∧
            j + 2 * s.positions ≠ slotIndex s.positions loc ty := by
        intro j hj hjh
        cases ty <;> simp only [slotIndex] <;> omega
      refine hNext (setLocal { s1 with values := vs } (slotIndex s.positions loc ty) v)
        ⟨hF1.params, by simp [setLocal, hl1], (fun j hj => ?_), (fun j hj => ?_)⟩ (fun k hk => ?_)
        fun j hj hjh => ?_
      · have hn := hne j (Or.inl hj) (by omega)
        rw [Locals.get_setLocal_ne (s := { s1 with values := vs }) hLow1 hn.1,
          Locals.get_setLocal_ne (s := { s1 with values := vs }) hLow1 hn.2.1]
        exact hF1.below j (by omega)
      · rw [Locals.get_setLocal_ne (s := { s1 with values := vs }) hLow1 (by
          cases ty <;> simp only [slotIndex] <;> omega)]
        exact hF1.below32 j (by omega)
      · simp only [Locals.positions_setLocal, Locals.positions_values, hh1]
        cases k with
        | zero =>
          simpa [-Locals.get] using Locals.get_setLocal_same (s := { s1 with values := vs })
            (v := v) (i := slotIndex s.positions loc ty) hLow1 hHigh1
        | succ k =>
          have hk' : k < vals.length := by simp at hk; omega
          simp only [List.getD_cons_succ, List.getElem_cons_succ]
          have hold := hold1 k hk'
          rw [show loc + 1 + k = loc + (k + 1) by omega, hh1] at hold
          have hne' : slotIndex s.positions (loc + (k + 1)) (tys.getD k .i64) ≠
              slotIndex s.positions loc ty := by
            have : loc + (k + 1) < s.positions := by simp at hk; omega
            cases ty <;> cases tys.getD k .i64 <;> simp only [slotIndex] <;> omega
          rw [Locals.get_setLocal_ne (s := { s1 with values := vs }) hLow1 hne']
          simpa [-Locals.get] using hold
      · simp only [List.length_cons] at hj
        have hn := hne j (Or.inr (by omega)) hjh
        rw [Locals.get_setLocal_ne (s := { s1 with values := vs }) hLow1 hn.1,
          Locals.get_setLocal_ne (s := { s1 with values := vs }) hLow1 hn.2.1,
          Locals.get_setLocal_ne (s := { s1 with values := vs }) hLow1 hn.2.2]
        exact habove1 j (by omega) hjh


/-- Parameter copying preserves earlier positions and stores each parameter in its typed slot. -/
theorem wp_paramCopyCode {m : Module} {Q : Assertion α} {store : Store α} {host : HostEnv α}
    {h : Nat} : (tys : List ValueType) → (p : Nat) → ∀ {s : Locals} {rest : Program},
    p + tys.length ≤ s.params.length → s.params.length ≤ h → s.positions = h →
    (∀ s', Frame p s s' → s'.values = s.values →
      (∀ q, p ≤ q → q < p + tys.length →
        s'.get (slotIndex h q (tys.getD (q - p) .i64)) = s.get q) →
      wp m rest Q store s' host) →
    wp m (paramCopyCode h p tys ++ rest) Q store s host
  | [], _, s, _, _, _, _, hNext => by
    simpa [paramCopyCode] using
      hNext s (Frame.refl _ s) rfl (fun q h1 h2 => by simp at h2; omega)
  | ty :: tys, p, s, rest, hP, hH, hh, hNext => by
    simp only [List.length_cons] at hP
    by_cases hf : ty = .f64 ∨ ty = .f32
    · have hCode : paramCopyCode h p (ty :: tys) =
          [.localGet p, .localSet (slotIndex h p ty)] ++ paramCopyCode h (p + 1) tys := by
        rcases hf with rfl | rfl <;> rfl
      have hLow : s.params.length ≤ slotIndex h p ty := by
        rcases hf with rfl | rfl <;> simp only [slotIndex] <;> omega
      have hHigh : slotIndex h p ty < s.params.length + s.locals.length := by
        have total : 3 * s.positions ≤ s.params.length + s.locals.length := by
          simp only [Locals.positions]; omega
        rcases hf with rfl | rfl <;> simp only [slotIndex] <;> omega
      obtain ⟨v, hv⟩ : ∃ v, s.get p = some v :=
        ⟨s.params[p], by simp [Locals.get, show p < s.params.length by omega]⟩
      rw [hCode]
      simp only [List.cons_append, List.nil_append, wp_localGet_cons, hv]
      refine wp_localSet_local (s := s) (vs := s.values) hLow hHigh ?_
      let s0 := setLocal s (slotIndex h p ty) v
      have frame : Frame p s s0 := by
        change Frame p s (setLocal s (slotIndex h p ty) v)
        rw [← hh]
        exact Frame.setSlot ty (by simpa [hh] using hLow) le_rfl (by omega)
      refine wp_paramCopyCode tys (p + 1) (s := s0)
        (by simp only [s0, setLocal]; omega) (by simpa [s0, setLocal] using hH)
        (frame.positions.trans hh) fun s' fr values copy => ?_
      refine hNext s' (frame.trans (fr.mono (by omega))) values fun q hq hq' => ?_
      simp only [List.length_cons] at hq'
      by_cases head : q = p
      · subst q
        simp only [Nat.sub_self, List.getD_cons_zero]
        have same := fr.slot (p := p) (by omega) ty
        rw [frame.positions, hh] at same
        rw [same]
        exact (Locals.get_setLocal_same hLow hHigh).trans hv.symm
      · have shift : q - p = q - (p + 1) + 1 := by omega
        rw [shift, List.getD_cons_succ, copy q (by omega) (by omega)]
        apply Locals.get_setLocal_ne hLow
        rcases hf with rfl | rfl <;> simp only [slotIndex] <;> omega
    · have hCode : paramCopyCode h p (ty :: tys) = paramCopyCode h (p + 1) tys := by
        cases ty <;> first | rfl | exact False.elim (hf (Or.inl rfl)) | exact False.elim (hf (Or.inr rfl))
      rw [hCode]
      refine wp_paramCopyCode tys (p + 1) (by omega) hH hh fun s' fr values copy => ?_
      refine hNext s' (fr.mono (by omega)) values fun q hq hq' => ?_
      simp only [List.length_cons] at hq'
      by_cases head : q = p
      · subst q
        have index : slotIndex h p ty = p := by
          cases ty <;> first | rfl | exact False.elim (hf (Or.inl rfl)) | exact False.elim (hf (Or.inr rfl))
        simp only [Nat.sub_self, List.getD_cons_zero, index]
        simp only [Locals.get, fr.params, show p < s.params.length by omega, ↓reduceIte]
      · have shift : q - p = q - (p + 1) + 1 := by omega
        rw [shift, List.getD_cons_succ]
        exact copy q (by omega) (by omega)


end Verified
