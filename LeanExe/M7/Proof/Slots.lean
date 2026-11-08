import LeanExe.M7.Proof.Sim
import LeanExe.ProofKit.Locals

/-!
The pieces that the simulation of each form uses: the inversion of the generator's helpers,
which return `.ok` only when every offset fits the 12-bit immediates and every height has a
slot; the memory after the loads and stores of slot code; the distinctness of the slots of a
frame; and the relation after the store of a value into an operand slot or into a local's slot.
-/

namespace LeanExe.M7

open Wasm LeanExe.ProofKit

variable {P : Platform} {σ : Nat → UInt32} {code : UInt32 → Option UInt16}

/-! ## The generator's helpers -/

theorem except_bind_ok {ε α β : Type} {e : Except ε α} {f : α → Except ε β} {b : β} :
    (e >>= f) = .ok b ↔ ∃ a, e = .ok a ∧ f a = .ok b := by
  cases e <;> simp [bind, Except.bind]

theorem except_pure_ok {ε α : Type} {a b : α} : (pure a : Except ε α) = .ok b ↔ a = b := by
  simp [pure, Except.pure]

theorem except_throw_ok {ε α : Type} {e : ε} {b : α} : ¬ (throw e : Except ε α) = .ok b := by
  simp [throw, throwThe, MonadExceptOf.throw]

theorem imm_ok {n : Nat} {x : Fin 4096} (h : imm n = .ok x) : ∃ hn : n < 4096, x = ⟨n, hn⟩ := by
  unfold imm at h
  split at h
  · rename_i hn
    exact ⟨hn, (except_pure_ok.mp h).symm⟩
  · exact absurd h except_throw_ok

theorem ldPair_ok {lo hi : Fin 8} {o : Nat} {l : List Instr} (h : ldPair lo hi o = .ok l) :
    ∃ h0 h1, l = [.ldrSp lo ⟨o, h0⟩, .ldrSp hi ⟨o + 4, h1⟩] := by
  unfold ldPair at h
  simp only [except_bind_ok, except_pure_ok] at h
  obtain ⟨x, hx, y, hy, rfl⟩ := h
  obtain ⟨p0, rfl⟩ := imm_ok hx
  obtain ⟨p1, rfl⟩ := imm_ok hy
  exact ⟨p0, p1, rfl⟩

theorem stPair_ok {lo hi : Fin 8} {o : Nat} {l : List Instr} (h : stPair lo hi o = .ok l) :
    ∃ h0 h1, l = [.strSp lo ⟨o, h0⟩, .strSp hi ⟨o + 4, h1⟩] := by
  unfold stPair at h
  simp only [except_bind_ok, except_pure_ok] at h
  obtain ⟨x, hx, y, hy, rfl⟩ := h
  obtain ⟨p0, rfl⟩ := imm_ok hx
  obtain ⟨p1, rfl⟩ := imm_ok hy
  exact ⟨p0, p1, rfl⟩

theorem copySlot_ok {s d : Nat} {l : List Instr} (h : copySlot s d = .ok l) :
    ∃ h0 h1 h2 h3, l = [.ldrSp 0 ⟨s, h0⟩, .ldrSp 1 ⟨s + 4, h1⟩, .strSp 0 ⟨d, h2⟩,
      .strSp 1 ⟨d + 4, h3⟩] := by
  unfold copySlot at h
  simp only [except_bind_ok, except_pure_ok] at h
  obtain ⟨x, hx, y, hy, rfl⟩ := h
  obtain ⟨p0, p1, rfl⟩ := ldPair_ok hx
  obtain ⟨p2, p3, rfl⟩ := stPair_ok hy
  exact ⟨p0, p1, p2, p3, rfl⟩

theorem Env.op_ok {E : Env} {h o : Nat} (e : E.op h = .ok o) :
    h < E.frame.height ∧ o = E.frame.opAt h := by
  unfold Env.op at e
  split at e
  · rename_i o' ho
    obtain ⟨h1, h2⟩ := Frame.opOff_eq ho
    exact ⟨h1, (except_pure_ok.mp e).symm.trans h2⟩
  · exact absurd e except_throw_ok

theorem Env.loc_ok {E : Env} {i o : Nat} (e : E.loc i = .ok o) : E.frame.localOff i = some o := by
  unfold Env.loc at e
  split at e
  · rename_i o' ho
    rw [ho, except_pure_ok.mp e]
  · exact absurd e except_throw_ok

/-! ## The slots of a frame -/

/-- The slots of two different locals do not overlap. -/
theorem Frame.localOff_disjoint {fr : Frame} {i i' o o' : Nat} (h : fr.localOff i = some o)
    (h' : fr.localOff i' = some o') (hne : i ≠ i') : o + 8 ≤ o' ∨ o' + 8 ≤ o := by
  have hs := fr.size_eq
  have hl := fr.lrOff_eq
  rcases Frame.localOff_eq h with ⟨hi, rfl⟩ | ⟨j, hj, hji, rfl⟩ <;>
    rcases Frame.localOff_eq h' with ⟨hi', rfl⟩ | ⟨j', hj', hji', rfl⟩
  · omega
  · omega
  · omega
  · have : j ≠ j' := fun e => hne (by rw [e] at hji; rw [hji] at hji'; exact Option.some.inj hji')
    omega

/-- A local's slot lies within the frame and the parameters, apart from every operand slot and
from the slot of LR. -/
theorem Frame.localOff_bounds {fr : Frame} {i o : Nat} (h : fr.localOff i = some o) :
    o % 8 = 0 ∧ o + 8 ≤ fr.size + 8 * fr.params ∧ o ≠ fr.lrOff ∧
      ∀ k < fr.height, o + 8 ≤ fr.opAt k ∨ fr.opAt k + 8 ≤ o := by
  have hs := fr.size_eq
  have hl := fr.lrOff_eq
  rcases Frame.localOff_eq h with ⟨hi, rfl⟩ | ⟨j, hj, -, rfl⟩
  · refine ⟨by omega, by omega, by omega, fun k hk => ?_⟩
    simp only [Frame.opAt]; omega
  · refine ⟨by omega, by omega, by omega, fun k hk => ?_⟩
    simp only [Frame.opAt]; omega

theorem Frame.opAt_bounds (fr : Frame) {k : Nat} (hk : k < fr.height) :
    fr.opAt k % 8 = 0 ∧ fr.opAt k + 8 ≤ fr.lrOff ∧ fr.lrOff + 8 = fr.size := by
  have hs := fr.size_eq
  have hl := fr.lrOff_eq
  simp only [Frame.opAt]
  omega

/-! ## Memory after stores -/

/-- Two word stores at the offsets `x` and `x + 4` from SP leave every byte from the end of the
slot up, when the slot lies below 2^32. -/
theorem store2_above {m : UInt32 → UInt8} {sp w0 w1 : UInt32} {x : Nat}
    (hx : sp.toNat + x + 8 ≤ 4294967296) {a : UInt32} (ha : sp.toNat + x + 8 ≤ a.toNat) :
    store32 (store32 m (sp + UInt32.ofNat x) w0) (sp + UInt32.ofNat (x + 4)) w1 a = m a := by
  have := toNat_lt32 a
  have := toNat_lt32 sp
  have e : ∀ c, c ≤ x + 4 → (a - (sp + UInt32.ofNat c)).toNat = a.toNat - sp.toNat - c :=
    fun c hc => by
      rw [UInt32.toNat_sub, UInt32.toNat_add, UInt32.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
  rw [store32_far, store32_far]
  · rw [UInt32.lt_iff_toNat_lt, e x (by omega), show (4 : UInt32).toNat = 4 from rfl]; omega
  · rw [UInt32.lt_iff_toNat_lt, e (x + 4) (by omega), show (4 : UInt32).toNat = 4 from rfl]
    omega

/-- Two word stores at the offsets `x` and `x + 4` from SP leave every byte below SP, when the slot
lies below 2^32. -/
theorem store2_below {m : UInt32 → UInt8} {sp w0 w1 : UInt32} {x : Nat}
    (hx : sp.toNat + x + 8 ≤ 4294967296) {a : UInt32} (ha : a.toNat < sp.toNat) :
    store32 (store32 m (sp + UInt32.ofNat x) w0) (sp + UInt32.ofNat (x + 4)) w1 a = m a := by
  have := toNat_lt32 a
  have := toNat_lt32 sp
  have e : ∀ c, c ≤ x + 4 →
      (a - (sp + UInt32.ofNat c)).toNat = a.toNat + 4294967296 - sp.toNat - c := fun c hc => by
    rw [UInt32.toNat_sub, UInt32.toNat_add, UInt32.toNat_ofNat']
    simp only [Nat.reducePow]
    omega
  rw [store32_far, store32_far]
  · rw [UInt32.lt_iff_toNat_lt, e x (by omega), show (4 : UInt32).toNat = 4 from rfl]; omega
  · rw [UInt32.lt_iff_toNat_lt, e (x + 4) (by omega), show (4 : UInt32).toNat = 4 from rfl]
    omega

/-- The bytes below the stack's limit after the store of two words into a slot of the frame or
the parameters. -/
theorem keepsBelow_store2 {E : Env} {ms t : State} {x : Nat} {w0 w1 : UInt32}
    (hf : FrameOk P E.frame E.limit ms)
    (hmem : t.mem = store32 (store32 ms.mem (ms.sp + UInt32.ofNat x) w0)
      (ms.sp + UInt32.ofNat (x + 4)) w1)
    (hx : x + 8 ≤ E.frame.size + 8 * E.frame.params) : KeepsBelow E.limit ms t := by
  have hfit := hf.fits
  have hl := hf.limit
  intro a ha
  rw [hmem]
  exact store2_below (by omega) (by omega)

/-- The bytes below the stack's limit after the store of two words into the operand slot of
height `k`. -/
theorem keepsBelow_write_op {E : Env} {ms t : State} {k : Nat} {w0 w1 : UInt32}
    (hf : FrameOk P E.frame E.limit ms)
    (hmem : t.mem = store32 (store32 ms.mem (ms.sp + UInt32.ofNat (E.frame.opAt k)) w0)
      (ms.sp + UInt32.ofNat (E.frame.opAt k + 4)) w1)
    (hk : k < E.frame.height) : KeepsBelow E.limit ms t := by
  obtain ⟨hk8, hklr, hlrs⟩ := E.frame.opAt_bounds hk
  exact keepsBelow_store2 hf hmem (by omega)

/-- The bytes below the stack's limit after the store of two words into the slot of local `i`. -/
theorem keepsBelow_write_local {E : Env} {ms t : State} {i dst : Nat} {w0 w1 : UInt32}
    (hf : FrameOk P E.frame E.limit ms)
    (hmem : t.mem = store32 (store32 ms.mem (ms.sp + UInt32.ofNat dst) w0)
      (ms.sp + UInt32.ofNat (dst + 4)) w1)
    (hdst : E.frame.localOff i = some dst) : KeepsBelow E.limit ms t := by
  obtain ⟨hd8, hdb, -, -⟩ := Frame.localOff_bounds hdst
  exact keepsBelow_store2 hf hmem hdb

/-! ## The relation after stores -/

/-- The relation after the store of `r` into the operand slot of height `k`, the top of the new
stack `r :: vs`, where `vs` holds the values of the heights below `k` in their slots. -/
theorem Inv.write_op {E : Env} {σs σ' : List ValueType} {sl : Locals} {ms t : State} {k : Nat}
    {w0 w1 : UInt32} {vs : List Value} {r : Value} (hinv : Inv P E σs sl ms) (hsp : t.sp = ms.sp)
    (hmem : t.mem = store32 (store32 ms.mem (ms.sp + UInt32.ofNat (E.frame.opAt k)) w0)
      (ms.sp + UInt32.ofNat (E.frame.opAt k + 4)) w1)
    (hk : k < E.frame.height) (hvs : vs.length = k)
    (hbelow : ∀ h v, vs.reverse[h]? = some v → ValAt ms (E.frame.opAt h) v)
    (hr : SlotRel r w0 w1) (hty : Typed σ' (r :: vs)) :
    Inv P E σ' { sl with values := r :: vs } t := by
  have hf := hinv.frame.fits
  obtain ⟨hk8, hklr, hlrs⟩ := E.frame.opAt_bounds hk
  have hop : ∀ h, E.frame.opAt h = 8 * (E.frame.out + E.frame.named.length + h) := fun _ => rfl
  have hlr := E.frame.lrOff_eq
  refine ⟨by simp; omega, fun h v hv => ?_, hinv.count, fun i v o hv ho => ?_,
    hinv.ltypes, hinv.frame.congr hsp, hty⟩
  · simp only [List.reverse_cons] at hv
    by_cases hh : h < vs.length
    · rw [List.getElem?_append_left (by simpa using hh)] at hv
      have e1 := hop h
      have e2 := hop k
      exact (hbelow h v hv).congr hsp (slotSame_store2 hmem (by omega) (by omega) (by omega))
    · rw [List.getElem?_append_right (by simp; omega)] at hv
      simp only [List.length_reverse] at hv
      by_cases he : h = vs.length
      · subst he
        simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hv
        subst hv
        rw [← hvs] at hmem
        have e3 := hop vs.length
        exact valAt_store2 hsp hmem (by omega) hr
      · rw [List.getElem?_eq_none (by simp; omega)] at hv
        cases hv
  · obtain ⟨ho8, hob, -, hop⟩ := Frame.localOff_bounds ho
    exact (hinv.locals i v o hv ho).congr hsp (slotSame_store2 hmem (by omega) (by omega)
      (hop k hk))

/-- The words of the LR slot and the bytes from the end of the parameters up after the store of
two words into the operand slot of height `k`. -/
theorem keeps_write_op {E : Env} {ms t : State} {k : Nat} {w0 w1 : UInt32}
    (hf : FrameOk P E.frame E.limit ms)
    (hmem : t.mem = store32 (store32 ms.mem (ms.sp + UInt32.ofNat (E.frame.opAt k)) w0)
      (ms.sp + UInt32.ofNat (E.frame.opAt k + 4)) w1)
    (hk : k < E.frame.height) : BodyKeeps E.frame ms.sp ms t := by
  have hfit := hf.fits
  obtain ⟨hk8, hklr, hlrs⟩ := E.frame.opAt_bounds hk
  refine ⟨?_, fun a ha => ?_⟩
  · rw [hmem, load32_store32_off (by omega) (by omega) (by omega),
      load32_store32_off (by omega) (by omega) (by omega)]
  · rw [hmem]; exact store2_above (by omega) (by omega)

/-- The operand slots below the height `k` after the store of two words into the slot of `k`. -/
theorem below_write_op {E : Env} {ms t : State} {k b : Nat} {w0 w1 : UInt32}
    (hf : FrameOk P E.frame E.limit ms)
    (hmem : t.mem = store32 (store32 ms.mem (ms.sp + UInt32.ofNat (E.frame.opAt k)) w0)
      (ms.sp + UInt32.ofNat (E.frame.opAt k + 4)) w1)
    (hk : k < E.frame.height) (hb : b ≤ k) : Below E.frame b ms t := by
  have hfit := hf.fits
  obtain ⟨hk8, hklr, hlrs⟩ := E.frame.opAt_bounds hk
  intro h hh
  refine slotSame_store2 hmem (by omega) (by simp only [Frame.opAt] at *; omega) ?_
  simp only [Frame.opAt] at *; omega

/-- The relation after the store of `v`, the top of the stack `v :: vs`, into the slot of local
`i`, which `local.set` performs. -/
theorem Inv.write_local {E : Env} {σs σ' : List ValueType} {sl s' : Locals} {ms t : State}
    {i dst : Nat} {w0 w1 : UInt32} {v : Value} {vs : List Value} (hinv : Inv P E σs sl ms)
    (hsp : t.sp = ms.sp)
    (hmem : t.mem = store32 (store32 ms.mem (ms.sp + UInt32.ofNat dst) w0)
      (ms.sp + UInt32.ofNat (dst + 4)) w1)
    (hdst : E.frame.localOff i = some dst) (hv : sl.values = v :: vs)
    (hil : i < (sl.params ++ sl.locals).length)
    (hs' : s'.params ++ s'.locals = (sl.params ++ sl.locals).set i v) (hr : SlotRel v w0 w1)
    (htv : ∀ ty, E.localTypes[i]? = some ty → HasType ty v) (hty : Typed σ' vs) :
    Inv P E σ' { s' with values := vs } t := by
  have hf := hinv.frame.fits
  obtain ⟨hd8, hdb, -, hdop⟩ := Frame.localOff_bounds hdst
  have hh := hinv.height
  rw [hv] at hh
  refine ⟨by simp at hh ⊢; omega, fun h v' hv' => ?_, ?_, fun j v' o' hj ho' => ?_,
    fun j v' ty o' hj hty' ho' => ?_, hinv.frame.congr hsp, hty⟩
  · have hl : h < vs.length := by
      have := (List.getElem?_eq_some_iff.mp hv').1; simpa using this
    have hst := hinv.stack h v' (by
      rw [hv, List.reverse_cons, List.getElem?_append_left (by simpa using hl)]; exact hv')
    exact hst.congr hsp (slotSame_store2 hmem (by omega)
      (by have := E.frame.opAt_bounds (k := h) (by simp at hh; omega); omega)
      ((hdop h (by simp at hh; omega)).symm))
  · show (s'.params ++ s'.locals).length = _
    rw [hs', List.length_set, hinv.count]
  · change (s'.params ++ s'.locals)[j]? = some v' at hj
    rw [hs'] at hj
    by_cases hji : j = i
    · subst hji
      rw [List.getElem?_set_self hil, Option.some.injEq] at hj
      subst hj
      rw [hdst, Option.some.injEq] at ho'
      subst ho'
      exact valAt_store2 hsp hmem (by omega) hr
    · rw [List.getElem?_set_ne (Ne.symm hji)] at hj
      obtain ⟨ho8, hob, -, -⟩ := Frame.localOff_bounds ho'
      exact (hinv.locals j v' o' hj ho').congr hsp (slotSame_store2 hmem (by omega) (by omega)
        (Frame.localOff_disjoint ho' hdst hji))
  · change (s'.params ++ s'.locals)[j]? = some v' at hj
    rw [hs'] at hj
    by_cases hji : j = i
    · subst hji
      rw [List.getElem?_set_self hil, Option.some.injEq] at hj
      subst hj
      exact htv ty hty'
    · rw [List.getElem?_set_ne (Ne.symm hji)] at hj
      exact hinv.ltypes j v' ty o' hj hty' ho'

/-- The word of the LR slot, the bytes from the end of the parameters up, and the operand slots
after the store of two words into the slot of local `i`. -/
theorem keeps_write_local {E : Env} {ms t : State} {i dst b : Nat} {w0 w1 : UInt32}
    (hf : FrameOk P E.frame E.limit ms)
    (hmem : t.mem = store32 (store32 ms.mem (ms.sp + UInt32.ofNat dst) w0)
      (ms.sp + UInt32.ofNat (dst + 4)) w1)
    (hdst : E.frame.localOff i = some dst) (hb : b ≤ E.frame.height) :
    BodyKeeps E.frame ms.sp ms t ∧ Below E.frame b ms t := by
  have hfit := hf.fits
  have hs := E.frame.size_eq
  have hl := E.frame.lrOff_eq
  obtain ⟨hd8, hdb, hdlr, hdop⟩ := Frame.localOff_bounds hdst
  refine ⟨⟨?_, fun a ha => ?_⟩, fun h hh => ?_⟩
  · rw [hmem, load32_store32_off (by omega) (by omega) (by omega),
      load32_store32_off (by omega) (by omega) (by omega)]
  · rw [hmem]; exact store2_above (by omega) (by omega)
  · have := E.frame.opAt_bounds (k := h) (by omega)
    exact slotSame_store2 hmem (by omega) (by omega) (hdop h (by omega)).symm

end LeanExe.M7
