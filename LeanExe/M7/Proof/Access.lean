import LeanExe.M7.Proof.Bounds

/-!
The simulation of the forms that access the area, `load64`, `store64`, `globalGet`, and
`globalSet`, and of `wrapI64`, which the compiler emits before each address.  A program with these
forms has an area, so `StoreOk` gives the store relation of `LeanExe/M7/Proof/Store.lean`, and the
alignment premise gives `AlignedOne`, which makes each 64-bit access's address a multiple of 8.
`run_load64` and `run_store64` run the bounds test of `run_bounds` and the two word accesses at
`areaMemory` plus the address plus the offset, and `StoreRel.load` and `StoreRel.write` relate those
words to Talos's `read64` and `write64`.  An access outside memory traps in Talos, whose outcome
gives no claim, so the proofs follow the model only through accesses inside memory, whose address
has a high word of 0.  A global's slot lies at `areaHeader + 8 (i + 1)`.  A store into the area lies
below the stack's limit, so it keeps every slot, which `AboveSame` states.
-/

namespace LeanExe.M7

open Wasm LeanExe.ProofKit

variable {P : Platform} {σ : Nat → UInt32} {code : UInt32 → Option UInt16}

/-! ## Words and addresses -/

/-- A store of the word that a load read leaves the memory as it was. -/
theorem store32_load32 (m : UInt32 → UInt8) (a : UInt32) : store32 m a (load32 m a) = m := by
  funext b
  simp only [store32]
  split
  · rename_i hlt
    obtain ⟨k, hk, rfl⟩ : ∃ k, k < 4 ∧ b = a + UInt32.ofNat k := by
      refine ⟨(b - a).toNat, ?_, ?_⟩
      · rw [UInt32.lt_iff_toNat_lt] at hlt; exact hlt
      · apply UInt32.toNat_inj.mp
        have := toNat_lt32 a
        have := toNat_lt32 b
        rw [UInt32.toNat_add, UInt32.toNat_ofNat', UInt32.toNat_sub]
        simp only [Nat.reducePow]
        omega
    have hd : a + UInt32.ofNat k - a = UInt32.ofNat k := by
      rw [UInt32.add_comm, UInt32.add_sub_cancel]
    rw [hd]
    apply UInt8.toNat_inj.mp
    have e := toNat_byte (load32 m a) (UInt32.ofNat k) k
      (by rw [UInt32.toNat_ofNat']; simp only [Nat.reducePow]; omega) hk
    rw [UInt8.toNat_toUInt32] at e
    rw [e, toNat_load32_of (f := fun j => m (a + UInt32.ofNat j)) fun j _ => rfl]
    have h0 := (m (a + UInt32.ofNat 0)).toNat_lt
    have h1 := (m (a + UInt32.ofNat 1)).toNat_lt
    have h2 := (m (a + UInt32.ofNat 2)).toNat_lt
    have h3 := (m (a + UInt32.ofNat 3)).toNat_lt
    simp only [Nat.reducePow] at h0 h1 h2 h3
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;>
      simp only [Nat.mul_zero, Nat.reduceMul, Nat.reducePow] <;> omega
  · rfl

theorem areaHeader_toNat : areaHeader.toNat = 536870912 := rfl

theorem areaMemory_toNat : areaMemory.toNat = 536875008 := rfl

theorem areaHeader_mod4 : areaHeader % 4 = 0 := by decide

/-- Byte `w + off` of the memory: `areaMemory + w + off` is the area's byte `4096 + w + off`. -/
theorem memAddr {w : UInt32} {off : Nat} (h : w.toNat + off < 65536) :
    areaMemory + w + UInt32.ofNat off = areaHeader + UInt32.ofNat (4096 + (w.toNat + off)) := by
  apply UInt32.toNat_inj.mp
  rw [toNat_add_ofNat (a := areaHeader) (by rw [areaHeader_toNat]; omega), areaHeader_toNat,
    UInt32.toNat_add, UInt32.toNat_add, UInt32.toNat_ofNat', areaMemory_toNat]
  simp only [Nat.reducePow]
  omega

/-- A word of the area at an offset that is a multiple of 4 passes the checks of a load and a
store. -/
theorem StoreRel.word {area lim : UInt32} {cap : Nat} {gts : List ValueType} {α : Type}
    {st : Store α} {s : State} (h : StoreRel P area lim cap gts st s) (ha : area % 4 = 0) {o : Nat}
    (ho : o % 4 = 0) (hn : o + 4 ≤ areaSize cap) : WordOk P (area + UInt32.ofNat o) :=
  wordOk_of_ram h.ram ha ho hn

/-- The size word's number, the memory's size in bytes less 8, for a memory of one page. -/
theorem StoreRel.size_toNat {lim : UInt32} {gts : List ValueType} {α : Type} {st : Store α}
    {s : State} (h : StoreRel P areaHeader lim areaPages gts st s) :
    (load32 s.mem areaHeader).toNat = st.mem.pages * 65536 - 8 ∧ 1 ≤ st.mem.pages ∧
      st.mem.pages ≤ 1 := by
  have hp := h.pages
  have hp1 : st.mem.pages ≤ 1 := hp.2
  refine ⟨?_, hp.1, hp1⟩
  rw [h.size, UInt32.toNat_ofNat']
  simp only [Nat.reducePow]
  omega

/-- The byte at `c` keeps its value under a word store whose four bytes end at or below `c`. -/
theorem store32_low {m : UInt32 → UInt8} {b v c : UInt32} (h : b.toNat + 4 ≤ c.toNat) :
    store32 m b v c = m c := by
  apply store32_far
  rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; omega),
    show (4 : UInt32).toNat = 4 from rfl]
  omega

/-- The byte at `c` keeps its value under a word store at a higher address, below 2^32 - 4. -/
theorem store32_high {m : UInt32 → UInt8} {b v c : UInt32} (h : c.toNat < b.toNat)
    (hb : b.toNat + 4 ≤ 4294967296) : store32 m b v c = m c := by
  apply store32_far
  rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_sub, show (4 : UInt32).toNat = 4 from rfl]
  have := toNat_lt32 c
  simp only [Nat.reducePow]
  omega

/-! ## Memory changed below SP -/

/-- Every byte from `sp` up keeps in `t` its value in `s`. -/
def AboveSame (sp : UInt32) (s t : State) : Prop :=
  ∀ c : UInt32, sp.toNat ≤ c.toNat → t.mem c = s.mem c

theorem ValAt.of_above {s t : State} {o : Nat} {v : Value} (h : ValAt s o v) (hsp : t.sp = s.sp)
    (ha : AboveSame s.sp s t) (ho : s.sp.toNat + o + 8 ≤ 4294967296) : ValAt t o v := by
  unfold ValAt at h ⊢
  rw [hsp, load32_above ha (by rw [toNat_add_ofNat (by omega)]; omega)
      (by rw [toNat_add_ofNat (by omega)]; omega),
    load32_above ha (by rw [toNat_add_ofNat (by omega)]; omega)
      (by rw [toNat_add_ofNat (by omega)]; omega)]
  exact h

theorem BodyKeeps.of_above {fr : Frame} {lim : UInt32} {s t : State} (hf : FrameOk P fr lim s)
    (ha : AboveSame s.sp s t) : BodyKeeps fr s.sp s t := by
  have hfit := hf.fits
  have hs := fr.size_eq
  refine ⟨load32_above ha (by rw [toNat_add_ofNat (by omega)]; omega)
    (by rw [toNat_add_ofNat (by omega)]; omega), fun c hc => ha c (by omega)⟩

theorem Below.of_above {fr : Frame} {lim : UInt32} {s t : State} {b : Nat}
    (hf : FrameOk P fr lim s) (hb : b ≤ fr.height) (hsp : t.sp = s.sp)
    (ha : AboveSame s.sp s t) : Below fr b s t := by
  have hfit := hf.fits
  intro h hh
  obtain ⟨hk8, hklr, hlrs⟩ := fr.opAt_bounds (k := h) (by omega)
  refine ⟨?_, ?_⟩ <;>
    exact load32_above ha (by rw [toNat_add_ofNat (by omega)]; omega)
      (by rw [toNat_add_ofNat (by omega)]; omega)

/-- The relation after a pop to the stack `vs`, whose values lie in the slots that they had, from
a state whose memory from SP up and whose SP are those of `ms`. -/
theorem Inv.pop_above {E : Env} {σs σ' : List ValueType} {sl : Locals} {ms t : State}
    {vs : List Value} (hinv : Inv P E σs sl ms)
    (hsuf : ∀ (h : Nat) (v : Value), vs.reverse[h]? = some v → sl.values.reverse[h]? = some v)
    (hlen : vs.length ≤ sl.values.length) (hty : Typed σ' vs) (hsp : t.sp = ms.sp)
    (ha : AboveSame ms.sp ms t) : Inv P E σ' { sl with values := vs } t := by
  have hh := hinv.height
  have hfit := hinv.frame.fits
  refine ⟨by simp only; omega, fun h v hv => ?_, hinv.count, fun i v o hv ho => ?_, hinv.ltypes,
    hinv.frame.congr hsp, hty⟩
  · have hl := getElem?_reverse_lt hv
    obtain ⟨hk8, hklr, hlrs⟩ := E.frame.opAt_bounds (k := h) (by simp only at hl; omega)
    exact (hinv.stack h v (hsuf h v hv)).of_above hsp ha (by omega)
  · obtain ⟨ho8, hob, -, -⟩ := Frame.localOff_bounds ho
    exact (hinv.locals i v o hv ho).of_above hsp ha (by omega)

/-- A word store into the area keeps every byte from SP up. -/
theorem aboveSame_store2 {s t : State} {lim c w0 w1 : UInt32} {x : Nat}
    (hl : lim.toNat ≤ s.sp.toNat) (hb : c.toNat + x + 8 ≤ lim.toNat)
    (hmem : t.mem = store32 (store32 s.mem (c + UInt32.ofNat x) w0)
      (c + UInt32.ofNat (x + 4)) w1) : AboveSame s.sp s t := by
  have hlim := toNat_lt32 lim
  intro d hd
  rw [hmem, store32_low (by rw [toNat_add_ofNat (by omega)]; omega),
    store32_low (by rw [toNat_add_ofNat (by omega)]; omega)]

/-! ## Loads and stores of a pair at r2 -/

/-- Two loads at r2 plus `o` and plus `o + 4` into r0 and r1. -/
theorem run_ldr2 {o : Nat} {h0 : o < 4096} {h1 : o + 4 < 4096} {s : State} {b : UInt32}
    (hb : s.r 2 = b) (hc : CodeAt code s.pc [.ldr 0 2 ⟨o, h0⟩, .ldr 1 2 ⟨o + 4, h1⟩])
    (hw0 : WordOk P (b + UInt32.ofNat o)) (hw1 : WordOk P (b + UInt32.ofNat (o + 4))) :
    ∃ t, Reach P σ code s t ∧ t.pc = s.pc + 8 ∧ Keeps s t ∧
      t.r 0 = load32 s.mem (b + UInt32.ofNat o) ∧
      t.r 1 = load32 s.mem (b + UInt32.ofNat (o + 4)) := by
  obtain ⟨u1, hu1⟩ : ∃ u : State,
      u = { s.setR 0 (load32 s.mem (s.r 2 + UInt32.ofNat o)) with pc := s.pc + 4 } := ⟨_, rfl⟩
  have e0 : exec P σ (.ldr 0 2 ⟨o, h0⟩) s = some u1 := by
    rw [hu1]; exact exec_ldr (by rw [hb]; exact hw0)
  obtain ⟨r1, c1, p1⟩ := reach_falls hc rfl e0
  have k1 : Keeps s u1 := by rw [hu1]; exact ((Keeps.refl s).setR _ _).withPc _
  have u1r2 : u1.r 2 = b := by rw [hu1, State.r_withPc, State.r_setR_ne _ _ (by decide), hb]
  obtain ⟨u2, hu2⟩ : ∃ u : State,
      u = { u1.setR 1 (load32 u1.mem (u1.r 2 + UInt32.ofNat (o + 4))) with pc := u1.pc + 4 } :=
    ⟨_, rfl⟩
  have e1 : exec P σ (.ldr 1 2 ⟨o + 4, h1⟩) u1 = some u2 := by
    rw [hu2]; exact exec_ldr (by rw [u1r2]; exact hw1)
  obtain ⟨r2, -, p2⟩ := reach_falls c1 rfl e1
  have k2 : Keeps u1 u2 := by rw [hu2]; exact ((Keeps.refl u1).setR _ _).withPc _
  refine ⟨u2, r1.trans r2, by rw [p2, p1]; addr_eq, k1.trans k2, ?_, ?_⟩
  · rw [hu2, State.r_withPc, State.r_setR_ne _ _ (by decide), hu1, State.r_withPc,
      State.r_setR_same, hb]
  · rw [hu2, State.r_withPc, State.r_setR_same, u1r2, k1.mem]

/-- Two stores of r0 and r1 at r2 plus `o` and plus `o + 4`. -/
theorem run_str2 {o : Nat} {h0 : o < 4096} {h1 : o + 4 < 4096} {s : State} {b : UInt32}
    (hb : s.r 2 = b) (hc : CodeAt code s.pc [.str 0 2 ⟨o, h0⟩, .str 1 2 ⟨o + 4, h1⟩])
    (hw0 : WordOk P (b + UInt32.ofNat o)) (hw1 : WordOk P (b + UInt32.ofNat (o + 4))) :
    ∃ t, Reach P σ code s t ∧ t.pc = s.pc + 8 ∧ t.sp = s.sp ∧ t.lr = s.lr ∧
      t.trace = s.trace ∧ t.reads = s.reads ∧
      t.mem = store32 (store32 s.mem (b + UInt32.ofNat o) (s.r 0))
        (b + UInt32.ofNat (o + 4)) (s.r 1) := by
  obtain ⟨u1, hu1⟩ : ∃ u : State,
      u = { s with
        mem := store32 s.mem (s.r 2 + UInt32.ofNat o) (s.r 0), pc := s.pc + 4 } := ⟨_, rfl⟩
  have e0 : exec P σ (.str 0 2 ⟨o, h0⟩) s = some u1 := by
    rw [hu1]; exact exec_str (by rw [hb]; exact hw0)
  obtain ⟨r1, c1, p1⟩ := reach_falls hc rfl e0
  have u1r : ∀ i, u1.r i = s.r i := fun i => by rw [hu1]; rfl
  obtain ⟨u2, hu2⟩ : ∃ u : State,
      u = { u1 with
        mem := store32 u1.mem (u1.r 2 + UInt32.ofNat (o + 4)) (u1.r 1), pc := u1.pc + 4 } :=
    ⟨_, rfl⟩
  have e1 : exec P σ (.str 1 2 ⟨o + 4, h1⟩) u1 = some u2 := by
    rw [hu2]; exact exec_str (by rw [u1r, hb]; exact hw1)
  obtain ⟨r2, -, p2⟩ := reach_falls c1 rfl e1
  refine ⟨u2, r1.trans r2, by rw [p2, p1]; addr_eq, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hu2, hu1]
  · rw [hu2, hu1]
  · rw [hu2, hu1]
  · rw [hu2, hu1]
  · rw [hu2]
    show store32 u1.mem (u1.r 2 + UInt32.ofNat (o + 4)) (u1.r 1) = _
    rw [u1r, u1r, hb, hu1]
    show store32 (store32 s.mem (s.r 2 + UInt32.ofNat o) (s.r 0)) _ _ = _
    rw [hb]

/-- The stores of r0 and r1 into the slot at the offset `x` from SP. -/
theorem run_stPair {x : Nat} {h0 : x < 4096} {h1 : x + 4 < 4096} {s : State}
    (hc : CodeAt code s.pc [.strSp 0 ⟨x, h0⟩, .strSp 1 ⟨x + 4, h1⟩])
    (hw0 : WordOk P (s.sp + UInt32.ofNat x)) (hw1 : WordOk P (s.sp + UInt32.ofNat (x + 4))) :
    ∃ t, Reach P σ code s t ∧ t.pc = s.pc + 8 ∧ t.sp = s.sp ∧ t.lr = s.lr ∧
      t.trace = s.trace ∧ t.reads = s.reads ∧
      t.mem = store32 (store32 s.mem (s.sp + UInt32.ofNat x) (s.r 0))
        (s.sp + UInt32.ofNat (x + 4)) (s.r 1) := by
  have hok : SlotsOk P s.sp [.strSp 0 ⟨x, h0⟩, .strSp 1 ⟨x + 4, h1⟩] :=
    slotsOk_st hw0 (slotsOk_st hw1 (slotsOk_nil _))
  obtain ⟨r, p, sp, lr, tr, rd, -⟩ := run_slots (σ := σ) hok hc
  exact ⟨_, r, by rw [p]; rfl, sp, lr, tr, rd, slotRun_st2 s 0 1 x h0 h1⟩

/-! ## `wrapI64` -/

theorem gen_wrapI64 {E : Env} {ctl : List Ctl} {σs : List ValueType} {a : UInt32}
    {is : List Instr} {fin : Option (List ValueType)}
    (hg : genInstr E ctl σs a .wrapI64 = .ok (is, fin)) :
    curBase ctl + 1 ≤ σs.length ∧ σs.length - 1 < E.frame.height ∧ ∃ h1,
      is = [.movImm 0 0, .strSp 0 ⟨E.frame.opAt (σs.length - 1) + 4, h1⟩] ∧
      fin = some (.i32 :: σs.tail) := by
  unfold genInstr at hg
  by_cases hc : σs.length < curBase ctl + 1
  · simp only [hc, ↓reduceIte, except_bind_ok] at hg
    obtain ⟨_, h, -⟩ := hg
    exact absurd h except_throw_ok
  · simp only [hc, ↓reduceIte, except_bind_ok, except_pure_ok, Prod.mk.injEq] at hg
    obtain ⟨x, hx, c, hcc, rfl, rfl⟩ := hg
    obtain ⟨hlt, rfl⟩ := Env.op_ok hx
    obtain ⟨h1, rfl⟩ := imm_ok hcc
    exact ⟨by omega, hlt, h1, rfl, rfl⟩

theorem sim_wrapI64 (F : Nat) : InstrSim P σ code F .wrapI64 := by
  intro E ctl σs a is fin hgen hcode _ _ hb _ α m st sl ms hinv hsr hpc _ need D _ _ _
  obtain ⟨hb1, hlt, h1, rfl, rfl⟩ := gen_wrapI64 hgen
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f =>
      have hh := hinv.len
      by_cases hshape : ∃ x vs, sl.values = .i64 x :: vs
      · obtain ⟨x, vs, hv⟩ := hshape
        simp only [execOne.eq_def, hv]
        have hvl : vs.length = σs.length - 1 := by rw [hv] at hh; simp at hh; omega
        have htop := hinv.stack vs.length (.i64 x) (by
          rw [hv, List.reverse_cons, List.getElem?_append_right (by simp), List.length_reverse,
            Nat.sub_self, List.getElem?_cons_zero])
        rw [hvl] at htop
        obtain ⟨hx0, -⟩ := htop
        obtain ⟨hk8, hklr, hlrs⟩ := E.frame.opAt_bounds hlt
        have hok : SlotsOk P ms.sp
            [.movImm 0 0, .strSp 0 ⟨E.frame.opAt (σs.length - 1) + 4, h1⟩] :=
          slotsOk_cons rfl (fun o ho => by cases ho)
            (slotsOk_st (hinv.frame.word (by omega) (by omega)) (slotsOk_nil _))
        refine outcome_write
          (w0 := load32 ms.mem (ms.sp + UInt32.ofNat (E.frame.opAt (σs.length - 1))))
          (w1 := 0) hinv hsr hpc hcode hok ?_ hlt (by omega) hvl (fun h v hv' => ?_) ?_
          (Typed.cons trivial ?_)
        · rw [store32_load32]
          rfl
        · have hl := getElem?_reverse_lt hv'
          exact hinv.stack h v (by rw [hv, getElem?_reverse_cons hl]; exact hv')
        · refine ⟨?_, rfl⟩
          rw [hx0]
          apply UInt32.toNat_inj.mp
          rw [UInt64.toNat_toUInt32, UInt32.toNat_ofNat']
          simp only [Nat.reducePow, Nat.mod_mod]
        · have := hinv.types.tail
          rw [hv] at this
          exact this
      · simp only [execOne.eq_def]
        split
        · rename_i x vs hv
          exact absurd ⟨x, vs, hv⟩ hshape
        · trivial

/-! ## `load64` -/

theorem gen_load64 {E : Env} {ctl : List Ctl} {σs : List ValueType} {a : UInt32} {off : UInt32}
    {is : List Instr} {fin : Option (List ValueType)}
    (hg : genInstr E ctl σs a (.load64 off) = .ok (is, fin)) :
    ∃ A, E.area = some A ∧ curBase ctl + 1 ≤ σs.length ∧
      (σs.head? = some .i32 ∨ σs.head? = some .i64) ∧ off.toNat ≤ 4088 ∧
      σs.length - 1 < E.frame.height ∧ ∃ bs h0 h1 h2 h3,
        boundsCode A.trapBounds (E.frame.opAt (σs.length - 1)) off.toNat a = .ok bs ∧
        is = bs ++ [.ldr 0 2 ⟨off.toNat, h0⟩, .ldr 1 2 ⟨off.toNat + 4, h1⟩,
          .strSp 0 ⟨E.frame.opAt (σs.length - 1), h2⟩,
          .strSp 1 ⟨E.frame.opAt (σs.length - 1) + 4, h3⟩] ∧
        fin = some (.i64 :: σs.tail) := by
  unfold genInstr at hg
  split at hg
  · exact absurd hg except_throw_ok
  · rename_i A hA
    by_cases hc : σs.length < curBase ctl + 1 ∨ ¬ (σs.head? = some .i32 ∨ σs.head? = some .i64)
    · simp only [hc, ↓reduceIte, except_bind_ok] at hg
      obtain ⟨_, h, -⟩ := hg
      exact absurd h except_throw_ok
    · simp only [hc, ↓reduceIte] at hg
      by_cases ho : 4088 < off.toNat
      · simp only [ho, ↓reduceIte, except_bind_ok] at hg
        obtain ⟨_, h, -⟩ := hg
        exact absurd h except_throw_ok
      · simp only [ho, ↓reduceIte, except_bind_ok, except_pure_ok, Prod.mk.injEq] at hg
        obtain ⟨x, hx, bs, hbs, i0, hi0, i1, hi1, l, hl, rfl, rfl⟩ := hg
        obtain ⟨hlt, rfl⟩ := Env.op_ok hx
        obtain ⟨h0, rfl⟩ := imm_ok hi0
        obtain ⟨h1, rfl⟩ := imm_ok hi1
        obtain ⟨h2, h3, rfl⟩ := stPair_ok hl
        simp only [not_or, Nat.not_lt] at hc
        exact ⟨A, hA, by omega, Classical.byContradiction fun hn => hc.2 (not_or.mp hn), by omega, hlt, bs, h0,
          h1, h2, h3, hbs, by simp, rfl⟩

/-- The outcome of a `load64` inside memory from an address whose slot holds the words `lo` and
0. -/
theorem load_outcome {E : Env} {ctl : List Ctl} {σs : List ValueType} {a : UInt32}
    {off : UInt32} {α : Type} {st : Store α} {sl : Locals} {ms : State} {A : AreaShared}
    {bs : List Instr} {h0 : off.toNat < 4096} {h1 : off.toNat + 4 < 4096}
    {h2 : E.frame.opAt (σs.length - 1) < 4096} {h3 : E.frame.opAt (σs.length - 1) + 4 < 4096}
    {vs : List Value} {lo : UInt32} (hA : E.area = some A) (hb1 : curBase ctl + 1 ≤ σs.length)
    (hoff : off.toNat ≤ 4088) (hlt : σs.length - 1 < E.frame.height)
    (hbs : boundsCode A.trapBounds (E.frame.opAt (σs.length - 1)) off.toNat a = .ok bs)
    (hcode : CodeAt code a (bs ++ [.ldr 0 2 ⟨off.toNat, h0⟩, .ldr 1 2 ⟨off.toNat + 4, h1⟩,
      .strSp 0 ⟨E.frame.opAt (σs.length - 1), h2⟩,
      .strSp 1 ⟨E.frame.opAt (σs.length - 1) + 4, h3⟩]))
    (hinv : Inv P E σs sl ms) (hsr : StoreOk P E.toShared st ms) (hpc : ms.pc = a)
    (hvl : vs.length = σs.length - 1)
    (hbelow : ∀ h v, vs.reverse[h]? = some v → ValAt ms (E.frame.opAt h) v)
    (hty : Typed σs.tail vs)
    (hlo : load32 ms.mem (ms.sp + UInt32.ofNat (E.frame.opAt (σs.length - 1))) = lo)
    (hhi : load32 ms.mem (ms.sp + UInt32.ofNat (E.frame.opAt (σs.length - 1) + 4)) = 0)
    (hin : lo.toNat + off.toNat + 8 ≤ st.mem.pages * 65536)
    (hal : (lo.toNat + off.toNat) % 8 = 0) :
    Outcome P σ code E ctl (some (.i64 :: σs.tail))
      (after a (bs ++ [Instr.ldr 0 2 ⟨off.toNat, h0⟩, Instr.ldr 1 2 ⟨off.toNat + 4, h1⟩,
        Instr.strSp 0 ⟨E.frame.opAt (σs.length - 1), h2⟩,
        Instr.strSp 1 ⟨E.frame.opAt (σs.length - 1) + 4, h3⟩]).length)
      (.Fallthrough st { sl with values := .i64 (st.mem.read64 (lo + off)) :: vs }) ms := by
  have hsrA := hsr A hA
  obtain ⟨hsz, hp1, hp2⟩ := hsrA.size_toNat
  have hlim := hinv.frame.limit
  obtain ⟨hk8, hklr, hlrs⟩ := E.frame.opAt_bounds hlt
  have hfit := hinv.frame.fits
  -- the bounds test and the loads
  obtain ⟨hw, hbl⟩ := gen_bounds_wide hbs
  obtain ⟨cB, cL⟩ := hcode.split_wide hw
  rw [hbl] at cL
  have cL' : CodeAt code (after a 14) ([Instr.ldr 0 2 ⟨off.toNat, h0⟩,
      .ldr 1 2 ⟨off.toNat + 4, h1⟩] ++ [.strSp 0 ⟨E.frame.opAt (σs.length - 1), h2⟩,
      .strSp 1 ⟨E.frame.opAt (σs.length - 1) + 4, h3⟩]) := cL
  obtain ⟨cL1, cL2⟩ := cL'.split_wide rfl
  have hwh : WordOk P areaHeader := by
    simpa using hsrA.word areaHeader_mod4 (o := 0) (by decide)
      (by unfold areaSize areaPages; omega)
  have hl0 : WordOk P (areaMemory + lo + UInt32.ofNat off.toNat) := by
    rw [memAddr (by omega)]
    exact hsrA.word areaHeader_mod4 (by omega) (by unfold areaSize areaPages; omega)
  have hl1 : WordOk P (areaMemory + lo + UInt32.ofNat (off.toNat + 4)) := by
    rw [memAddr (by omega)]
    exact hsrA.word areaHeader_mod4 (by omega) (by unfold areaSize areaPages; omega)
  obtain ⟨t, rt, pt, kt, r2t⟩ := run_bounds (P := P) (σ := σ) hbs cB hpc
    (hinv.frame.word (by omega) (by omega)) (hinv.frame.word (by omega) (by omega)) hwh
    (by omega) hhi (by rw [hlo, hsz]; omega)
  rw [hlo] at r2t
  rw [← pt] at cL1
  obtain ⟨u, ru, pu, ku, u0, u1⟩ := run_ldr2 (P := P) (σ := σ) r2t cL1 hl0 hl1
  have hupc : u.pc = after (after a 14) 2 := by rw [pu, pt]; addr_after
  rw [show ([Instr.ldr 0 2 ⟨off.toNat, h0⟩, Instr.ldr 1 2 ⟨off.toNat + 4, h1⟩] : List Instr).length
    = 2 from rfl, ← hupc] at cL2
  obtain ⟨v, rv, pv, spv, -, trv, rdv, memv⟩ := run_stPair (P := P) (σ := σ) cL2
    (by rw [ku.sp, kt.sp]; exact hinv.frame.word (by omega) (by omega))
    (by rw [ku.sp, kt.sp]; exact hinv.frame.word (by omega) (by omega))
  -- the words that Talos reads
  obtain ⟨e0, e1⟩ := hsrA.load (y := lo.toNat + off.toNat) hin
  have hy : UInt32.ofNat (lo.toNat + off.toNat) = lo + off := by
    rw [UInt32.ofNat_add, UInt32.ofNat_toNat, UInt32.ofNat_toNat]
  rw [hy] at e0 e1
  have ha0 : load32 ms.mem (areaMemory + lo + UInt32.ofNat off.toNat) =
      (st.mem.read64 (lo + off)).toUInt32 := by
    rw [memAddr (by omega)]; exact e0
  have ha1 : load32 ms.mem (areaMemory + lo + UInt32.ofNat (off.toNat + 4)) =
      (st.mem.read64 (lo + off) >>> 32).toUInt32 := by
    rw [memAddr (by omega), show 4096 + (lo.toNat + (off.toNat + 4)) =
      4096 + (lo.toNat + off.toNat) + 4 by omega]
    exact e1
  refine outcome_store (z := v) hinv hsr (rt.trans (ru.trans rv)) ?_ (by rw [spv, ku.sp, kt.sp])
    (by rw [trv, ku.trace, kt.trace]) (by rw [rdv, ku.reads, kt.reads]) ?_ hlt (by omega) hvl
    hbelow ⟨rfl, rfl⟩ (Typed.cons trivial hty)
  · rw [pv, hupc, List.length_append, hbl]
    simp only [List.length_cons, List.length_nil]
    addr_after
  · rw [memv, ku.mem, kt.mem, ku.sp, kt.sp, u0, u1, kt.mem, ha0, ha1]

theorem sim_load64 (F : Nat) (off : UInt32) : InstrSim P σ code F (.load64 off) := by
  intro E ctl σs a is fin hgen hcode _ _ hb _ α m st sl ms hinv hsr hpc hal need D _ _ _
  obtain ⟨A, hA, hb1, hhead, hoff, hlt, bs, h0, h1, h2, h3, hbs, rfl, rfl⟩ := gen_load64 hgen
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f =>
      have hali := alignedOne_load64 (hal (by rw [hA]; rfl)).2
      have hh := hinv.len
      obtain ⟨w, vs, hv⟩ : ∃ w vs, sl.values = w :: vs := by
        cases hvs : sl.values with
        | nil => rw [hvs] at hh; simp at hh; omega
        | cons w vs => exact ⟨w, vs, rfl⟩
      have hvl : vs.length = σs.length - 1 := by rw [hv] at hh; simp at hh; omega
      have htop := hinv.stack vs.length w (by
        rw [hv, List.reverse_cons, List.getElem?_append_right (by simp), List.length_reverse,
          Nat.sub_self, List.getElem?_cons_zero])
      rw [hvl] at htop
      have hty := hinv.types
      rw [hv] at hty
      have hbelow : ∀ h v, vs.reverse[h]? = some v → ValAt ms (E.frame.opAt h) v :=
        fun h v hv' => hinv.stack h v (by
          rw [hv, getElem?_reverse_cons (getElem?_reverse_lt hv')]; exact hv')
      obtain ⟨-, hp1, hp2⟩ := (hsr A hA).size_toNat
      cases w
      case i32 x =>
        simp only [execOne.eq_def, hv]
        split
        · trivial
        · rename_i hnot
          have hin : x.toNat + off.toNat + 8 ≤ st.mem.pages * 65536 := by omega
          exact load_outcome hA hb1 hoff hlt hbs hcode hinv hsr hpc hvl hbelow hty.tail htop.1
            htop.2 hin (hali.1 x vs hv hin)
      case i64 x =>
        simp only [execOne.eq_def, hv]
        split
        · trivial
        · rename_i hnot
          have hin : x.toNat + off.toNat + 8 ≤ st.mem.pages * 65536 := by omega
          have hxl : x.toUInt32.toNat = x.toNat := by
            rw [UInt64.toNat_toUInt32]; simp only [Nat.reducePow]; omega
          have hhi : (x >>> 32).toUInt32 = 0 := by
            apply UInt32.toNat_inj.mp
            rw [toNat_hi64]
            show x.toNat / 4294967296 % 4294967296 = 0
            rw [Nat.div_eq_of_lt (by omega)]
          exact load_outcome hA hb1 hoff hlt hbs hcode hinv hsr hpc hvl hbelow hty.tail htop.1
            (by rw [htop.2, hhi]) (by rw [hxl]; exact hin) (hali.2 x vs hv hin)
      all_goals (simp only [execOne.eq_def, hv]; trivial)

/-! ## `store64` -/

theorem gen_store64 {E : Env} {ctl : List Ctl} {σs : List ValueType} {a : UInt32} {off : UInt32}
    {is : List Instr} {fin : Option (List ValueType)}
    (hg : genInstr E ctl σs a (.store64 off) = .ok (is, fin)) :
    ∃ A, E.area = some A ∧ curBase ctl + 2 ≤ σs.length ∧ σs.head? = some .i64 ∧
      (σs[1]? = some .i32 ∨ σs[1]? = some .i64) ∧ off.toNat ≤ 4088 ∧
      σs.length - 1 < E.frame.height ∧ ∃ bs h0 h1 h2 h3,
        boundsCode A.trapBounds (E.frame.opAt (σs.length - 2)) off.toNat a = .ok bs ∧
        is = bs ++ [.ldrSp 0 ⟨E.frame.opAt (σs.length - 1), h0⟩,
          .ldrSp 1 ⟨E.frame.opAt (σs.length - 1) + 4, h1⟩, .str 0 2 ⟨off.toNat, h2⟩,
          .str 1 2 ⟨off.toNat + 4, h3⟩] ∧
        fin = some (σs.drop 2) := by
  unfold genInstr at hg
  split at hg
  · exact absurd hg except_throw_ok
  · rename_i A hA
    by_cases hc : σs.length < curBase ctl + 2 ∨ σs.head? ≠ some .i64 ∨
        ¬ (σs[1]? = some .i32 ∨ σs[1]? = some .i64)
    · simp only [hc, ↓reduceIte, except_bind_ok] at hg
      obtain ⟨_, h, -⟩ := hg
      exact absurd h except_throw_ok
    · simp only [hc, ↓reduceIte] at hg
      by_cases ho : 4088 < off.toNat
      · simp only [ho, ↓reduceIte, except_bind_ok] at hg
        obtain ⟨_, h, -⟩ := hg
        exact absurd h except_throw_ok
      · simp only [ho, ↓reduceIte, except_bind_ok, except_pure_ok, Prod.mk.injEq] at hg
        obtain ⟨x, hx, y, hy, bs, hbs, l, hl, i0, hi0, i1, hi1, rfl, rfl⟩ := hg
        obtain ⟨-, rfl⟩ := Env.op_ok hx
        obtain ⟨hlt, rfl⟩ := Env.op_ok hy
        obtain ⟨h0, h1, rfl⟩ := ldPair_ok hl
        obtain ⟨h2, rfl⟩ := imm_ok hi0
        obtain ⟨h3, rfl⟩ := imm_ok hi1
        simp only [not_or, Ne, Decidable.not_not, Nat.not_lt] at hc
        exact ⟨A, hA, by omega, hc.2.1, Classical.byContradiction fun hn => hc.2.2 (not_or.mp hn), by omega,
          hlt, bs, h0, h1, h2, h3, hbs, by simp, rfl⟩

/-- The outcome of a `store64` of `val` inside memory at an address whose slot holds the words `lo`
and 0. -/
theorem store_outcome {E : Env} {ctl : List Ctl} {σs : List ValueType} {a : UInt32}
    {off : UInt32} {α : Type} {st : Store α} {sl : Locals} {ms : State} {A : AreaShared}
    {bs : List Instr} {h0 : E.frame.opAt (σs.length - 1) < 4096}
    {h1 : E.frame.opAt (σs.length - 1) + 4 < 4096} {h2 : off.toNat < 4096}
    {h3 : off.toNat + 4 < 4096} {vs : List Value} {val : UInt64} {lo : UInt32} {adr : Value}
    (hA : E.area = some A) (hb2 : curBase ctl + 2 ≤ σs.length) (hoff : off.toNat ≤ 4088)
    (hlt : σs.length - 1 < E.frame.height)
    (hbs : boundsCode A.trapBounds (E.frame.opAt (σs.length - 2)) off.toNat a = .ok bs)
    (hcode : CodeAt code a (bs ++ [.ldrSp 0 ⟨E.frame.opAt (σs.length - 1), h0⟩,
      .ldrSp 1 ⟨E.frame.opAt (σs.length - 1) + 4, h1⟩, .str 0 2 ⟨off.toNat, h2⟩,
      .str 1 2 ⟨off.toNat + 4, h3⟩]))
    (hinv : Inv P E σs sl ms) (hsr : StoreOk P E.toShared st ms) (hpc : ms.pc = a)
    (hv : sl.values = .i64 val :: adr :: vs) (hb : curBase ctl ≤ σs.length - 2)
    (hlo : load32 ms.mem (ms.sp + UInt32.ofNat (E.frame.opAt (σs.length - 2))) = lo)
    (hhi : load32 ms.mem (ms.sp + UInt32.ofNat (E.frame.opAt (σs.length - 2) + 4)) = 0)
    (hin : lo.toNat + off.toNat + 8 ≤ st.mem.pages * 65536)
    (hal : (lo.toNat + off.toNat) % 8 = 0) :
    Outcome P σ code E ctl (some (σs.drop 2))
      (after a (bs ++ [Instr.ldrSp 0 ⟨E.frame.opAt (σs.length - 1), h0⟩,
        Instr.ldrSp 1 ⟨E.frame.opAt (σs.length - 1) + 4, h1⟩, Instr.str 0 2 ⟨off.toNat, h2⟩,
        Instr.str 1 2 ⟨off.toNat + 4, h3⟩]).length)
      (.Fallthrough { st with mem := st.mem.write64 (lo + off) val }
        { sl with values := vs }) ms := by
  have hsrA := hsr A hA
  obtain ⟨hsz, hp1, hp2⟩ := hsrA.size_toNat
  have hlim := hinv.frame.limit
  have hh := hinv.len
  have hvl : vs.length = σs.length - 2 := by rw [hv] at hh; simp at hh; omega
  obtain ⟨hk8, hklr, hlrs⟩ := E.frame.opAt_bounds hlt
  obtain ⟨hj8, hjlr, -⟩ := E.frame.opAt_bounds (k := σs.length - 2) (by omega)
  have hfit := hinv.frame.fits
  have hbelow := hsrA.below
  rw [areaHeader_toNat] at hbelow
  unfold areaSize areaPages at hbelow
  -- the bounds test, the loads of the value, and its stores
  obtain ⟨hw, hbl⟩ := gen_bounds_wide hbs
  obtain ⟨cB, cL⟩ := hcode.split_wide hw
  rw [hbl] at cL
  have cL' : CodeAt code (after a 14) ([Instr.ldrSp 0 ⟨E.frame.opAt (σs.length - 1), h0⟩,
      .ldrSp 1 ⟨E.frame.opAt (σs.length - 1) + 4, h1⟩] ++ [.str 0 2 ⟨off.toNat, h2⟩,
      .str 1 2 ⟨off.toNat + 4, h3⟩]) := cL
  obtain ⟨cL1, cL2⟩ := cL'.split_wide rfl
  have hwh : WordOk P areaHeader := by
    simpa using hsrA.word areaHeader_mod4 (o := 0) (by decide)
      (by unfold areaSize areaPages; omega)
  have hl0 : WordOk P (areaMemory + lo + UInt32.ofNat off.toNat) := by
    rw [memAddr (by omega)]
    exact hsrA.word areaHeader_mod4 (by omega) (by unfold areaSize areaPages; omega)
  have hl1 : WordOk P (areaMemory + lo + UInt32.ofNat (off.toNat + 4)) := by
    rw [memAddr (by omega)]
    exact hsrA.word areaHeader_mod4 (by omega) (by unfold areaSize areaPages; omega)
  obtain ⟨t, rt, pt, kt, r2t⟩ := run_bounds (P := P) (σ := σ) hbs cB hpc
    (hinv.frame.word (by omega) (by omega)) (hinv.frame.word (by omega) (by omega)) hwh
    (by omega) hhi (by rw [hlo, hsz]; omega)
  rw [hlo] at r2t
  rw [← pt] at cL1
  have hokL : SlotsOk P t.sp [Instr.ldrSp 0 ⟨E.frame.opAt (σs.length - 1), h0⟩,
      .ldrSp 1 ⟨E.frame.opAt (σs.length - 1) + 4, h1⟩] := by
    rw [kt.sp]
    exact slotsOk_ld (hinv.frame.word (by omega) (by omega))
      (slotsOk_ld (hinv.frame.word (by omega) (by omega)) (slotsOk_nil _))
  obtain ⟨ru, pu, spu, lru, tru, rdu, hiu⟩ := run_slots (σ := σ) hokL cL1
  generalize hu : slotRun P σ [Instr.ldrSp 0 ⟨E.frame.opAt (σs.length - 1), h0⟩,
    .ldrSp 1 ⟨E.frame.opAt (σs.length - 1) + 4, h1⟩] t = u at ru pu spu lru tru rdu hiu
  have hum : u.mem = t.mem := by rw [← hu]; rfl
  have hu0 : u.r 0 = load32 ms.mem (ms.sp + UInt32.ofNat (E.frame.opAt (σs.length - 1))) := by
    rw [← hu]
    show load32 t.mem (t.sp + _) = _
    rw [kt.mem, kt.sp]
  have hu1 : u.r 1 =
      load32 ms.mem (ms.sp + UInt32.ofNat (E.frame.opAt (σs.length - 1) + 4)) := by
    rw [← hu]
    show load32 t.mem (t.sp + _) = _
    rw [kt.mem, kt.sp]
  have hu2 : u.r 2 = areaMemory + lo := by
    rw [← hu]
    show t.r 2 = _
    exact r2t
  have hupc : u.pc = after (after a 14) 2 := by
    rw [pu, pt]; simp only [List.length_cons, List.length_nil]; addr_after
  rw [show ([Instr.ldrSp 0 ⟨E.frame.opAt (σs.length - 1), h0⟩,
    Instr.ldrSp 1 ⟨E.frame.opAt (σs.length - 1) + 4, h1⟩] : List Instr).length = 2 from rfl,
    ← hupc] at cL2
  obtain ⟨v, rv, pv, spv, -, trv, rdv, memv⟩ := run_str2 (P := P) (σ := σ) hu2 cL2 hl0 hl1
  -- the value's words and Talos's store
  have htop := hinv.stack (σs.length - 1) (.i64 val) (by
    rw [hv, List.reverse_cons, List.getElem?_append_right (by simp; omega), List.length_reverse]
    simp only [List.length_cons]
    rw [show σs.length - 1 - (vs.length + 1) = 0 by omega, List.getElem?_cons_zero])
  obtain ⟨hv0, hv1⟩ := htop
  have hy : UInt32.ofNat (lo.toNat + off.toNat) = lo + off := by
    rw [UInt32.ofNat_add, UInt32.ofNat_toNat, UInt32.ofNat_toNat]
  have hmv : v.mem = store32 (store32 ms.mem
      (areaHeader + UInt32.ofNat (4096 + (lo.toNat + off.toNat))) val.toUInt32)
      (areaHeader + UInt32.ofNat (4096 + (lo.toNat + off.toNat) + 4)) (val >>> 32).toUInt32 := by
    rw [memv, hum, kt.mem, hu0, hu1, hv0, hv1, memAddr (by omega), memAddr (by omega),
      show 4096 + (lo.toNat + (off.toNat + 4)) = 4096 + (lo.toNat + off.toNat) + 4 by omega]
  have hab : AboveSame ms.sp ms v := by
    refine aboveSame_store2 (lim := E.limit) hlim.2 ?_ hmv
    rw [areaHeader_toNat]
    omega
  have hvsp : v.sp = ms.sp := by rw [spv, spu, kt.sp]
  refine ⟨σs.drop 2, rfl, v, rt.trans (ru.trans rv), ?_, hvsp,
    by rw [trv, tru, kt.trace], by rw [rdv, rdu, kt.reads],
    BodyKeeps.of_above hinv.frame hab,
    Below.of_above hinv.frame (by have := hinv.height; have := hinv.len; omega) hvsp hab,
    Inv.pop_above hinv (fun h w hw => by
      have hl := getElem?_reverse_lt hw
      rw [hv, getElem?_reverse_cons (show h < (adr :: vs).length by simp; omega),
        getElem?_reverse_cons hl]
      exact hw)
      (by rw [hv]; simp only [List.length_cons]; omega)
      (by have := hinv.types.drop 2; rw [hv] at this; simpa using this) hvsp hab,
      fun A' hA' => ?_⟩
  · rw [pv, hupc, List.length_append, hbl]
    simp only [List.length_cons, List.length_nil]
    addr_after
  · rw [hA] at hA'
    cases hA'
    rw [← hy]
    exact hsrA.write hin hmv

theorem sim_store64 (F : Nat) (off : UInt32) : InstrSim P σ code F (.store64 off) := by
  intro E ctl σs a is fin hgen hcode _ _ hb _ α m st sl ms hinv hsr hpc hal need D _ _ _
  obtain ⟨A, hA, hb2, hhead, hsnd, hoff, hlt, bs, h0, h1, h2, h3, hbs, rfl, rfl⟩ :=
    gen_store64 hgen
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f =>
      have hali := alignedOne_store64 (hal (by rw [hA]; rfl)).2
      have hh := hinv.len
      obtain ⟨-, hp1, hp2⟩ := (hsr A hA).size_toNat
      by_cases hshape : ∃ val w vs, sl.values = .i64 val :: w :: vs
      · obtain ⟨val, w, vs, hv⟩ := hshape
        have hvl : vs.length = σs.length - 2 := by rw [hv] at hh; simp at hh; omega
        have haddr := hinv.stack vs.length w (by
          rw [hv, List.reverse_cons, List.reverse_cons, List.append_assoc,
            List.getElem?_append_right (by simp), List.length_reverse, Nat.sub_self]
          rfl)
        rw [hvl] at haddr
        cases w
        case i32 x =>
          simp only [execOne.eq_def, hv]
          split
          · trivial
          · rename_i hnot
            have hin : x.toNat + off.toNat + 8 ≤ st.mem.pages * 65536 := by omega
            exact store_outcome hA hb2 hoff hlt hbs hcode hinv hsr hpc hv (by omega) haddr.1
              haddr.2 hin (hali.1 val x vs hv hin)
        case i64 x =>
          simp only [execOne.eq_def, hv]
          split
          · trivial
          · rename_i hnot
            have hin : x.toNat + off.toNat + 8 ≤ st.mem.pages * 65536 := by omega
            have hxl : x.toUInt32.toNat = x.toNat := by
              rw [UInt64.toNat_toUInt32]; simp only [Nat.reducePow]; omega
            have hhi : (x >>> 32).toUInt32 = 0 := by
              apply UInt32.toNat_inj.mp
              rw [toNat_hi64]
              show x.toNat / 4294967296 % 4294967296 = 0
              rw [Nat.div_eq_of_lt (by omega)]
            exact store_outcome hA hb2 hoff hlt hbs hcode hinv hsr hpc hv (by omega) haddr.1
              (by rw [haddr.2, hhi]) (by rw [hxl]; exact hin) (hali.2 val x vs hv hin)
        all_goals (simp only [execOne.eq_def, hv]; trivial)
      · simp only [execOne.eq_def]
        split
        · rename_i val x vs hv
          exact absurd ⟨val, .i32 x, vs, hv⟩ hshape
        · rename_i val x vs hv
          exact absurd ⟨val, .i64 x, vs, hv⟩ hshape
        · trivial

/-! ## Globals -/

theorem gen_globalGet {E : Env} {ctl : List Ctl} {σs : List ValueType} {a : UInt32} {i : Nat}
    {is : List Instr} {fin : Option (List ValueType)}
    (hg : genInstr E ctl σs a (.globalGet i) = .ok (is, fin)) :
    ∃ A t, E.area = some A ∧ A.globals[i]? = some t ∧ σs.length < E.frame.height ∧
      ∃ h0 h1 h2 h3, is = movWord 2 areaHeader ++ [.ldr 0 2 ⟨8 * (i + 1), h0⟩,
        .ldr 1 2 ⟨8 * (i + 1) + 4, h1⟩, .strSp 0 ⟨E.frame.opAt σs.length, h2⟩,
        .strSp 1 ⟨E.frame.opAt σs.length + 4, h3⟩] ∧ fin = some (t :: σs) := by
  unfold genInstr at hg
  split at hg
  · exact absurd hg except_throw_ok
  · rename_i A hA
    split at hg
    · rename_i t ht
      simp only [except_bind_ok, except_pure_ok, Prod.mk.injEq] at hg
      obtain ⟨i0, hi0, i1, hi1, x, hx, l, hl, rfl, rfl⟩ := hg
      obtain ⟨h0, rfl⟩ := imm_ok hi0
      obtain ⟨h1, rfl⟩ := imm_ok hi1
      obtain ⟨hlt, rfl⟩ := Env.op_ok hx
      obtain ⟨h2, h3, rfl⟩ := stPair_ok hl
      exact ⟨A, t, hA, ht, hlt, h0, h1, h2, h3, by simp, rfl⟩
    · exact absurd hg except_throw_ok

theorem sim_globalGet (F i : Nat) : InstrSim P σ code F (.globalGet i) := by
  intro E ctl σs a is fin hgen hcode _ _ hb _ α m st sl ms hinv hsr hpc _ need D _ _ _
  obtain ⟨A, t, hA, ht, hlt, h0, h1, h2, h3, rfl, rfl⟩ := gen_globalGet hgen
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f =>
      have hsrA := hsr A hA
      have hgl := hsrA.types.length
      have hglen := hsrA.glen
      have hi : i < A.globals.length := (List.getElem?_eq_some_iff.mp ht).1
      have hi' : i < st.globals.globals.length := by omega
      simp only [execOne.eq_def, List.getElem?_eq_getElem hi']
      have hh := hinv.len
      obtain ⟨hk8, hklr, hlrs⟩ := E.frame.opAt_bounds hlt
      have hfit := hinv.frame.fits
      have hc : CodeAt code a (movWord 2 areaHeader ++ [Instr.ldr 0 2 ⟨8 * (i + 1), h0⟩,
          .ldr 1 2 ⟨8 * (i + 1) + 4, h1⟩] ++ [.strSp 0 ⟨E.frame.opAt σs.length, h2⟩,
          .strSp 1 ⟨E.frame.opAt σs.length + 4, h3⟩]) := hcode
      obtain ⟨c12, c3⟩ := hc.split_wide rfl
      obtain ⟨c1, c2⟩ := c12.split_wide rfl
      rw [← hpc] at c1
      obtain ⟨r1, p1, sp1, lr1, tr1, rd1, -⟩ := run_slots (σ := σ) (slotsOk_reg rfl _) c1
      obtain ⟨hm1, -, -⟩ := slotRun_reg (P := P) (σ := σ) (movWord_regForm 2 areaHeader) ms
      generalize hu1 : slotRun P σ (movWord 2 areaHeader) ms = u1 at r1 p1 sp1 lr1 tr1 rd1 hm1
      have hr2 : u1.r 2 = areaHeader := by rw [← hu1]; exact (slotRun_movWord 2 areaHeader ms).1
      have hp1' : u1.pc = after a 2 := by
        rw [p1, hpc]; simp only [movWord, List.length_cons, List.length_nil]; addr_after
      rw [show (movWord 2 areaHeader).length = 2 from rfl, ← hp1'] at c2
      obtain ⟨u2, r2, p2, k2, u20, u21⟩ := run_ldr2 (P := P) (σ := σ) hr2 c2
        (hsrA.word areaHeader_mod4 (by omega) (by unfold areaSize; omega))
        (hsrA.word areaHeader_mod4 (by omega) (by unfold areaSize; omega))
      have hp2' : u2.pc = after (after a 2) 2 := by rw [p2, hp1']; addr_after
      rw [show (movWord 2 areaHeader ++ [Instr.ldr 0 2 ⟨8 * (i + 1), h0⟩,
        .ldr 1 2 ⟨8 * (i + 1) + 4, h1⟩]).length = 4 from rfl,
        show after a 4 = after (after a 2) 2 by rw [after_after], ← hp2'] at c3
      obtain ⟨v, rv, pv, spv, -, trv, rdv, memv⟩ := run_stPair (P := P) (σ := σ) c3
        (by rw [k2.sp, sp1]; exact hinv.frame.word (by omega) (by omega))
        (by rw [k2.sp, sp1]; exact hinv.frame.word (by omega) (by omega))
      refine outcome_store (z := v) hinv hsr (r1.trans (r2.trans rv)) ?_
        (by rw [spv, k2.sp, sp1]) (by rw [trv, k2.trace, tr1]) (by rw [rdv, k2.reads, rd1]) ?_ hlt
        hb (by rw [hh]) hinv.stack (hsrA.globals i hi') (Typed.cons ?_ hinv.types)
      · rw [pv, hp2']
        simp only [movWord, List.length_append, List.length_cons, List.length_nil]
        addr_after
      · rw [memv, k2.sp, sp1, k2.mem, hm1, u20, u21, hm1]
      · have := hsrA.types.getElem hi
        rw [List.getElem?_eq_getElem hi, Option.some.injEq] at ht
        rw [← ht]
        exact this

theorem gen_globalSet {E : Env} {ctl : List Ctl} {σs : List ValueType} {a : UInt32} {i : Nat}
    {is : List Instr} {fin : Option (List ValueType)}
    (hg : genInstr E ctl σs a (.globalSet i) = .ok (is, fin)) :
    ∃ A, E.area = some A ∧ curBase ctl + 1 ≤ σs.length ∧ σs.head? = A.globals[i]? ∧
      σs.length - 1 < E.frame.height ∧ ∃ h0 h1 h2 h3,
        is = [.ldrSp 0 ⟨E.frame.opAt (σs.length - 1), h0⟩,
          .ldrSp 1 ⟨E.frame.opAt (σs.length - 1) + 4, h1⟩] ++ movWord 2 areaHeader ++
          [.str 0 2 ⟨8 * (i + 1), h2⟩, .str 1 2 ⟨8 * (i + 1) + 4, h3⟩] ∧
        fin = some σs.tail := by
  unfold genInstr at hg
  split at hg
  · exact absurd hg except_throw_ok
  · rename_i A hA
    by_cases hc : σs.length < curBase ctl + 1 ∨ σs.head? ≠ A.globals[i]?
    · simp only [hc, ↓reduceIte, except_bind_ok] at hg
      obtain ⟨_, h, -⟩ := hg
      exact absurd h except_throw_ok
    · simp only [hc, ↓reduceIte, except_bind_ok, except_pure_ok, Prod.mk.injEq] at hg
      obtain ⟨x, hx, l, hl, i0, hi0, i1, hi1, rfl, rfl⟩ := hg
      obtain ⟨hlt, rfl⟩ := Env.op_ok hx
      obtain ⟨h0, h1, rfl⟩ := ldPair_ok hl
      obtain ⟨h2, rfl⟩ := imm_ok hi0
      obtain ⟨h3, rfl⟩ := imm_ok hi1
      simp only [not_or, Ne, Decidable.not_not, Nat.not_lt] at hc
      exact ⟨A, hA, by omega, hc.2, hlt, h0, h1, h2, h3, rfl, rfl⟩

theorem sim_globalSet (F i : Nat) : InstrSim P σ code F (.globalSet i) := by
  intro E ctl σs a is fin hgen hcode _ _ hb _ α m st sl ms hinv hsr hpc _ need D _ _ _
  obtain ⟨A, hA, hb1, hhead, hlt, h0, h1, h2, h3, rfl, rfl⟩ := gen_globalSet hgen
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f =>
      have hsrA := hsr A hA
      have hgl := hsrA.types.length
      have hglen := hsrA.glen
      have hh := hinv.len
      obtain ⟨v, vs, hv⟩ : ∃ v vs, sl.values = v :: vs := by
        cases hvs : sl.values with
        | nil => rw [hvs] at hh; simp at hh; omega
        | cons v vs => exact ⟨v, vs, rfl⟩
      have hvl : vs.length = σs.length - 1 := by rw [hv] at hh; simp at hh; omega
      obtain ⟨t, ht⟩ : ∃ t, A.globals[i]? = some t := by
        rw [← hhead]
        cases σs with
        | nil => simp at hb1
        | cons t _ => exact ⟨t, rfl⟩
      have hi : i < A.globals.length := (List.getElem?_eq_some_iff.mp ht).1
      have hi' : i < st.globals.globals.length := by omega
      simp only [execOne.eq_def, hv, List.getElem?_eq_getElem hi']
      have htop := hinv.stack vs.length v (by
        rw [hv, List.reverse_cons, List.getElem?_append_right (by simp), List.length_reverse,
          Nat.sub_self, List.getElem?_cons_zero])
      rw [hvl] at htop
      have hty := hinv.types
      rw [hv] at hty
      have hvt : HasType A.globals[i] v := by
        have := hty.head_cons (hhead.trans ht)
        rw [List.getElem?_eq_getElem hi, Option.some.injEq] at ht
        rw [ht]
        exact this
      obtain ⟨hk8, hklr, hlrs⟩ := E.frame.opAt_bounds hlt
      have hfit := hinv.frame.fits
      have hlim := hinv.frame.limit
      have hbelow := hsrA.below
      rw [areaHeader_toNat] at hbelow
      unfold areaSize areaPages at hbelow
      have hc : CodeAt code a (([Instr.ldrSp 0 ⟨E.frame.opAt (σs.length - 1), h0⟩,
          .ldrSp 1 ⟨E.frame.opAt (σs.length - 1) + 4, h1⟩] ++ movWord 2 areaHeader) ++
          [.str 0 2 ⟨8 * (i + 1), h2⟩, .str 1 2 ⟨8 * (i + 1) + 4, h3⟩]) := hcode
      obtain ⟨c1, c2⟩ := hc.split_wide rfl
      rw [← hpc] at c1
      have hok : SlotsOk P ms.sp ([Instr.ldrSp 0 ⟨E.frame.opAt (σs.length - 1), h0⟩,
          .ldrSp 1 ⟨E.frame.opAt (σs.length - 1) + 4, h1⟩] ++ movWord 2 areaHeader) :=
        slotsOk_ld (hinv.frame.word (by omega) (by omega))
          (slotsOk_ld (hinv.frame.word (by omega) (by omega)) (slotsOk_reg rfl _))
      obtain ⟨r1, p1, sp1, lr1, tr1, rd1, -⟩ := run_slots (σ := σ) hok c1
      generalize hu1 : slotRun P σ ([Instr.ldrSp 0 ⟨E.frame.opAt (σs.length - 1), h0⟩,
        .ldrSp 1 ⟨E.frame.opAt (σs.length - 1) + 4, h1⟩] ++ movWord 2 areaHeader) ms = u1
        at r1 p1 sp1 lr1 tr1 rd1
      have hm1 : u1.mem = ms.mem := by rw [← hu1]; rfl
      have hu1r : u1.r 0 = load32 ms.mem (ms.sp + UInt32.ofNat (E.frame.opAt (σs.length - 1))) ∧
          u1.r 1 = load32 ms.mem (ms.sp + UInt32.ofNat (E.frame.opAt (σs.length - 1) + 4)) ∧
          u1.r 2 = areaHeader := by
        rw [← hu1, slotRun_append]
        obtain ⟨e2, e⟩ := slotRun_movWord (P := P) (σ := σ) 2 areaHeader
          (slotRun P σ [Instr.ldrSp 0 ⟨E.frame.opAt (σs.length - 1), h0⟩,
            .ldrSp 1 ⟨E.frame.opAt (σs.length - 1) + 4, h1⟩] ms)
        refine ⟨?_, ?_, e2⟩
        · rw [e 0 (by decide)]
          simp only [slotRun_cons, slotRun_nil, slotStep]
          state_simp
          try rfl
        · rw [e 1 (by decide)]
          simp only [slotRun_cons, slotRun_nil, slotStep]
          state_simp
          try rfl
      have hp1' : u1.pc = after a 4 := by
        rw [p1, hpc]
        simp only [movWord, List.length_append, List.length_cons, List.length_nil]
        addr_after
      rw [show ([Instr.ldrSp 0 ⟨E.frame.opAt (σs.length - 1), h0⟩,
        .ldrSp 1 ⟨E.frame.opAt (σs.length - 1) + 4, h1⟩] ++ movWord 2 areaHeader).length = 4
        from rfl, ← hp1'] at c2
      obtain ⟨w, rw', pw, spw, -, trw, rdw, memw⟩ := run_str2 (P := P) (σ := σ) hu1r.2.2 c2
        (hsrA.word areaHeader_mod4 (by omega) (by unfold areaSize; omega))
        (hsrA.word areaHeader_mod4 (by omega) (by unfold areaSize; omega))
      have hmw : w.mem = store32 (store32 ms.mem (areaHeader + UInt32.ofNat (8 * (i + 1)))
          (load32 ms.mem (ms.sp + UInt32.ofNat (E.frame.opAt (σs.length - 1)))))
          (areaHeader + UInt32.ofNat (8 * (i + 1) + 4))
          (load32 ms.mem (ms.sp + UInt32.ofNat (E.frame.opAt (σs.length - 1) + 4))) := by
        rw [memw, hm1, hu1r.1, hu1r.2.1]
      have hab : AboveSame ms.sp ms w := by
        refine aboveSame_store2 (lim := E.limit) hlim.2 ?_ hmw
        rw [areaHeader_toNat]
        omega
      have hwsp : w.sp = ms.sp := by rw [spw, sp1]
      refine ⟨σs.tail, rfl, w, r1.trans rw', ?_, hwsp, by rw [trw, tr1], by rw [rdw, rd1],
        BodyKeeps.of_above hinv.frame hab,
        Below.of_above hinv.frame (by have := hinv.height; have := hinv.len; omega) hwsp hab,
        Inv.pop_above hinv (fun h u hu => by
          rw [hv, getElem?_reverse_cons (getElem?_reverse_lt hu)]; exact hu)
          (by rw [hv]; simp only [List.length_cons]; omega) hty.tail hwsp hab,
          fun A' hA' => ?_⟩
      · rw [pw, hp1']
        simp only [movWord, List.length_append, List.length_cons, List.length_nil]
        addr_after
      · rw [hA] at hA'
        cases hA'
        exact hsrA.setGlobal hi htop hvt hmw

end LeanExe.M7
