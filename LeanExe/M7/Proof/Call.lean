import LeanExe.M7.Proof.Branch

/-!
The simulation of a call.  The caller copies the arguments from the operand slots of their
heights into its outgoing area, branches with `BL`, and copies the results from the outgoing area
into the operand slots of their heights.  `run_copies` runs a list of slot copies whose sources no
copy overwrites: afterwards each destination holds the words of its source, and every byte outside
the destinations keeps its value.  The callee's `FunSim` from `CallsOk` gives the return with the
results in the outgoing area and every byte from the caller's SP plus the area up unchanged, which
keeps the caller's other slots.
-/

namespace LeanExe.M7

open Wasm LeanExe.ProofKit LeanExe.CallGraph

variable {P : Platform} {σ : Nat → UInt32} {code : UInt32 → Option UInt16}

/-! ## Bytes and slots -/

/-- The byte at `b` lies outside the slot at the offset `x` from `sp`. -/
def Outside (sp : UInt32) (x : Nat) (b : UInt32) : Prop := 8 ≤ (b - (sp + UInt32.ofNat x)).toNat

theorem store2_outside {m : UInt32 → UInt8} {sp w0 w1 b : UInt32} {x : Nat}
    (h : Outside sp x b) :
    store32 (store32 m (sp + UInt32.ofNat x) w0) (sp + UInt32.ofNat (x + 4)) w1 b = m b := by
  unfold Outside at h
  have e : (b - (sp + UInt32.ofNat (x + 4))).toNat = (b - (sp + UInt32.ofNat x)).toNat - 4 := by
    rw [UInt32.toNat_sub, UInt32.toNat_sub, UInt32.toNat_add, UInt32.toNat_add,
      UInt32.toNat_ofNat', UInt32.toNat_ofNat'] at *
    have := toNat_lt32 sp
    have := toNat_lt32 b
    simp only [Nat.reducePow] at *
    omega
  rw [store32_far, store32_far]
  · rw [UInt32.lt_iff_toNat_lt, show (4 : UInt32).toNat = 4 from rfl]; omega
  · rw [UInt32.lt_iff_toNat_lt, show (4 : UInt32).toNat = 4 from rfl, e]; omega

/-- The bytes of the slot at the offset `o` lie outside the slot at `x` when the slots do not
overlap. -/
theorem outside_of_disjoint {sp : UInt32} {o x : Nat} (hd : o + 8 ≤ x ∨ x + 8 ≤ o)
    (ho : o + 8 ≤ 4294967296) (hx : x + 8 ≤ 4294967296) {k : Nat} (hk : k < 8) :
    Outside sp x (sp + UInt32.ofNat (o + k)) := by
  unfold Outside
  rw [toNat_sub_offsets sp (by omega) (by omega)]
  omega

/-- The two words of the slot at the offset `o` from SP. -/
def slotWords (s : State) (o : Nat) : UInt32 × UInt32 :=
  (load32 s.mem (s.sp + UInt32.ofNat o), load32 s.mem (s.sp + UInt32.ofNat (o + 4)))

theorem load32_congr {m m' : UInt32 → UInt8} {a : UInt32}
    (h : ∀ k < 4, m' (a + UInt32.ofNat k) = m (a + UInt32.ofNat k)) : load32 m' a = load32 m a := by
  have h0 := h 0 (by decide)
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  rw [show UInt32.ofNat 0 = 0 from rfl, UInt32.add_zero] at h0
  rw [show UInt32.ofNat 1 = 1 from rfl] at h1
  rw [show UInt32.ofNat 2 = 2 from rfl] at h2
  rw [show UInt32.ofNat 3 = 3 from rfl] at h3
  unfold load32
  rw [h0, h1, h2, h3]

/-- A slot whose bytes keep their values keeps its words. -/
theorem slotWords_congr {s t : State} {o : Nat} (hsp : t.sp = s.sp)
    (h : ∀ k < 8, t.mem (s.sp + UInt32.ofNat (o + k)) = s.mem (s.sp + UInt32.ofNat (o + k))) :
    slotWords t o = slotWords s o := by
  unfold slotWords
  rw [hsp]
  congr 1
  · exact load32_congr fun k hk => by rw [add_ofNat_add]; exact h k (by omega)
  · exact load32_congr fun k hk => by
      rw [add_ofNat_add, show o + 4 + k = o + (4 + k) by omega]; exact h (4 + k) (by omega)

theorem slotSame_of_words {s t : State} {o : Nat} (h : slotWords t o = slotWords s o)
    (hsp : t.sp = s.sp) : SlotSame s t o := by
  unfold slotWords at h
  rw [hsp] at h
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

/-! ## Copies -/

/-- `c` copies the slot at the offset `x` from SP to the slot at `y` through r0 and r1. -/
def CopyCode (c : List Instr) (x y : Nat) : Prop :=
  ∃ h0 h1 h2 h3, c = [.ldrSp 0 ⟨x, h0⟩, .ldrSp 1 ⟨x + 4, h1⟩, .strSp 0 ⟨y, h2⟩, .strSp 1 ⟨y + 4, h3⟩]

/-- Placed copies whose sources lie apart from every destination and whose destinations lie apart
from each other, all within `Ram` words of a region that the checks accept. -/
theorem run_copies {s : State} :
    ∀ {codes : List (List Instr)} {src dst : Nat → Nat},
      (∀ i (hi : i < codes.length), CopyCode codes[i] (src i) (dst i)) →
      (∀ i < codes.length, WordOk P (s.sp + UInt32.ofNat (src i)) ∧
        WordOk P (s.sp + UInt32.ofNat (src i + 4)) ∧ WordOk P (s.sp + UInt32.ofNat (dst i)) ∧
        WordOk P (s.sp + UInt32.ofNat (dst i + 4))) →
      (∀ i < codes.length, ∀ j < codes.length, src i + 8 ≤ dst j ∨ dst j + 8 ≤ src i) →
      (∀ i < codes.length, ∀ j < codes.length, i ≠ j → dst i + 8 ≤ dst j ∨ dst j + 8 ≤ dst i) →
      (∀ i < codes.length, src i + 8 ≤ 4294967296 ∧ dst i + 8 ≤ 4294967296) →
      CodeAt code s.pc codes.flatten →
      ∃ t, Reach P σ code s t ∧ t.pc = s.pc + UInt32.ofNat (16 * codes.length) ∧ t.sp = s.sp ∧
        t.lr = s.lr ∧ t.trace = s.trace ∧ t.reads = s.reads ∧
        (∀ i < codes.length, slotWords t (dst i) = slotWords s (src i)) ∧
        (∀ b, (∀ i < codes.length, Outside s.sp (dst i) b) → t.mem b = s.mem b)
  | [], _, _, _, _, _, _, _, _ =>
      ⟨s, .refl _, by simp, rfl, rfl, rfl, rfl, fun i hi => absurd hi (by simp), fun _ _ => rfl⟩
  | c :: cs, src, dst, hcp, hw, hsd, hdd, hb, hc => by
      obtain ⟨h0, h1, h2, h3, rfl⟩ := hcp 0 (by simp)
      obtain ⟨w0, w1, w2, w3⟩ := hw 0 (by simp)
      have hok : SlotsOk P s.sp [.ldrSp 0 ⟨src 0, h0⟩, .ldrSp 1 ⟨src 0 + 4, h1⟩,
          .strSp 0 ⟨dst 0, h2⟩, .strSp 1 ⟨dst 0 + 4, h3⟩] :=
        slotsOk_ld w0 (slotsOk_ld w1 (slotsOk_st w2 (slotsOk_st w3 (slotsOk_nil _))))
      rw [List.flatten_cons] at hc
      obtain ⟨hc1, hc2⟩ := CodeAt.append.mp hc
      obtain ⟨r1, p1, sp1, lr1, tr1, rd1, -⟩ := run_slots (σ := σ) hok hc1
      have hm1 : (slotRun P σ [.ldrSp 0 ⟨src 0, h0⟩, .ldrSp 1 ⟨src 0 + 4, h1⟩,
          .strSp 0 ⟨dst 0, h2⟩, .strSp 1 ⟨dst 0 + 4, h3⟩] s).mem =
          store32 (store32 s.mem (s.sp + UInt32.ofNat (dst 0))
          (load32 s.mem (s.sp + UInt32.ofNat (src 0)))) (s.sp + UInt32.ofNat (dst 0 + 4))
          (load32 s.mem (s.sp + UInt32.ofNat (src 0 + 4))) := rfl
      rw [show s.pc + UInt32.ofNat (codeSize [Instr.ldrSp 0 ⟨src 0, h0⟩,
          .ldrSp 1 ⟨src 0 + 4, h1⟩, .strSp 0 ⟨dst 0, h2⟩, .strSp 1 ⟨dst 0 + 4, h3⟩]) =
          (slotRun P σ [.ldrSp 0 ⟨src 0, h0⟩, .ldrSp 1 ⟨src 0 + 4, h1⟩,
          .strSp 0 ⟨dst 0, h2⟩, .strSp 1 ⟨dst 0 + 4, h3⟩] s).pc by
        rw [p1]; rfl] at hc2
      generalize slotRun P σ [.ldrSp 0 ⟨src 0, h0⟩, .ldrSp 1 ⟨src 0 + 4, h1⟩,
          .strSp 0 ⟨dst 0, h2⟩, .strSp 1 ⟨dst 0 + 4, h3⟩] s = s1 at r1 p1 sp1 lr1 tr1 rd1 hm1 hc2
      have hb0 := hb 0 (by simp)
      -- the copies after the first read the memory of `s1`, whose sources are those of `s`
      have hsrc : ∀ i < cs.length, slotWords s1 (src (i + 1)) = slotWords s (src (i + 1)) :=
        fun i hi => slotWords_congr sp1 fun k hk => by
          rw [hm1]
          exact store2_outside (outside_of_disjoint (hsd (i + 1) (by simp; omega) 0 (by simp))
            (hb (i + 1) (by simp; omega)).1 hb0.2 hk)
      obtain ⟨t, rt, pt, spt, lrt, trt, rdt, hwt, hmt⟩ :=
        run_copies (s := s1) (codes := cs) (src := fun i => src (i + 1))
          (dst := fun i => dst (i + 1)) (fun i hi => hcp (i + 1) (by simp; omega))
          (fun i hi => by rw [sp1]; exact hw (i + 1) (by simp; omega))
          (fun i hi j hj => hsd (i + 1) (by simp; omega) (j + 1) (by simp; omega))
          (fun i hi j hj hij => hdd (i + 1) (by simp; omega) (j + 1) (by simp; omega)
            (by omega))
          (fun i hi => hb (i + 1) (by simp; omega)) hc2
      refine ⟨t, r1.trans rt, ?_, spt.trans sp1, lrt.trans lr1, trt.trans tr1, rdt.trans rd1,
        fun i hi => ?_, fun b hbo => ?_⟩
      · rw [pt, p1]
        simp only [List.length_cons, List.length_nil]
        addr_eq
      · cases i with
        | zero =>
            have e1 : slotWords t (dst 0) = slotWords s1 (dst 0) :=
              slotWords_congr spt fun k hk => hmt _ fun j hj => by
                rw [sp1]
                exact outside_of_disjoint
                  (hdd 0 (by simp) (j + 1) (by simp; omega) (by omega)) hb0.2
                  (hb (j + 1) (by simp; omega)).2 hk
            rw [e1]
            unfold slotWords
            rw [hm1, sp1, load32_store32, load32_store32_off (by omega) (by omega) (by omega),
              load32_store32]
        | succ i =>
            rw [hwt i (by simp at hi; omega)]
            exact hsrc i (by simp at hi; omega)
      · rw [hmt b fun j hj => by rw [sp1]; exact hbo (j + 1) (by simp; omega), hm1]
        exact store2_outside (hbo 0 (by simp))

theorem length_copies : ∀ {codes : List (List Instr)} {src dst : Nat → Nat},
    (∀ i (hi : i < codes.length), CopyCode codes[i] (src i) (dst i)) →
    codes.flatten.length = 4 * codes.length
  | [], _, _, _ => rfl
  | c :: cs, src, dst, h => by
      obtain ⟨h0, h1, h2, h3, rfl⟩ := h 0 (by simp)
      rw [List.flatten_cons, List.length_append,
        length_copies (src := fun i => src (i + 1)) (dst := fun i => dst (i + 1))
          fun i hi => h (i + 1) (by simp; omega)]
      simp only [List.length_cons, List.length_nil]
      omega

theorem drop_reverse_getElem? {β : Type} {l : List β} {p j : Nat} (hj : j < l.length - p) :
    (l.drop p).reverse[j]? = l.reverse[j]? := by
  rw [List.getElem?_reverse (by simp; omega), List.getElem?_reverse (by omega),
    List.getElem?_drop]
  simp only [List.length_drop]
  congr 1
  omega

theorem outside_above {sp b : UInt32} {x : Nat} (h : sp.toNat + x + 8 ≤ b.toNat) :
    Outside sp x b := by
  unfold Outside
  rw [UInt32.toNat_sub, UInt32.toNat_add, UInt32.toNat_ofNat']
  have := toNat_lt32 b
  have := toNat_lt32 sp
  simp only [Nat.reducePow]
  omega

theorem codeSize_copies : ∀ {codes : List (List Instr)} {src dst : Nat → Nat},
    (∀ i (hi : i < codes.length), CopyCode codes[i] (src i) (dst i)) →
    codeSize codes.flatten = 16 * codes.length
  | [], _, _, _ => rfl
  | c :: cs, src, dst, h => by
      obtain ⟨h0, h1, h2, h3, rfl⟩ := h 0 (by simp)
      rw [List.flatten_cons, codeSize_append,
        codeSize_copies (src := fun i => src (i + 1)) (dst := fun i => dst (i + 1))
          fun i hi => h (i + 1) (by simp; omega)]
      simp only [codeSize, List.map, Instr.size, List.sum_cons, List.sum_nil, List.length_cons]
      omega

theorem mapM_ok {β γ : Type} {f : β → Except String γ} :
    ∀ {l : List β} {r : List γ}, l.mapM f = .ok r →
      r.length = l.length ∧ ∀ i (hi : i < l.length) (hr : i < r.length), f l[i] = .ok r[i]
  | [], r, h => by
      simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ⟨rfl, fun i hi => absurd hi (by simp)⟩
  | x :: xs, r, h => by
      rw [List.mapM_cons] at h
      simp only [except_bind_ok, except_pure_ok] at h
      obtain ⟨y, hy, ys, hys, rfl⟩ := h
      obtain ⟨hl, hf⟩ := mapM_ok hys
      refine ⟨by simp [hl], fun i hi hr => ?_⟩
      cases i with
      | zero => exact hy
      | succ i => exact hf i (by simp at hi; omega) (by simp at hr; omega)

theorem gen_call {E : Env} {ctl : List Ctl} {σs : List ValueType} {a : UInt32} {k : Nat}
    {is : List Instr} {fin : Option (List ValueType)}
    (hg : genInstr E ctl σs a (.call k) = .ok (is, fin)) :
    ∃ target ps rs, E.callee k = some (target, ps, rs) ∧ curBase ctl + ps.length ≤ σs.length ∧
      max ps.length rs.length ≤ E.frame.out ∧ σs.take ps.length = ps.reverse ∧
      ∃ (args res : List (List Instr)) (off : Int), args.length = ps.length ∧
        (∀ i (hi : i < args.length),
          CopyCode args[i] (E.frame.opAt (σs.length - ps.length + i)) (8 * i)) ∧
        (∀ i < ps.length, σs.length - ps.length + i < E.frame.height) ∧
        res.length = rs.length ∧
        (∀ j (hj : j < res.length),
          CopyCode res[j] (8 * j) (E.frame.opAt (σs.length - ps.length + j))) ∧
        (∀ j < rs.length, σs.length - ps.length + j < E.frame.height) ∧
        off % 2 = 0 ∧ -16777216 ≤ off ∧ off < 16777216 ∧
        after a (4 * ps.length) + 4 + UInt32.ofInt off = target ∧
        is = args.flatten ++ [Instr.blTo off] ++ res.flatten ∧
        fin = some (rs.reverse ++ σs.drop ps.length) := by
  unfold genInstr at hg
  split at hg
  · exact absurd hg except_throw_ok
  · rename_i target ps rs hk
    by_cases hc : σs.length < curBase ctl + ps.length ∨ E.frame.out < max ps.length rs.length ∨
        σs.take ps.length ≠ ps.reverse
    · simp only [hc, ↓reduceIte, except_bind_ok] at hg
      obtain ⟨_, h, -⟩ := hg
      exact absurd h except_throw_ok
    · simp only [hc, ↓reduceIte, except_bind_ok, except_pure_ok, Prod.mk.injEq] at hg
      obtain ⟨args, hargs, res, hres, bl, hbl, rfl, rfl⟩ := hg
      simp only [not_or, Ne, Decidable.not_not, Nat.not_lt] at hc
      obtain ⟨hal, hai⟩ := mapM_ok hargs
      obtain ⟨hrl, hri⟩ := mapM_ok hres
      simp only [List.length_range] at hal hrl
      obtain ⟨off, rfl, o1, o2, o3, o4⟩ := blAt_ok hbl
      have hargc : ∀ i (hi : i < args.length),
          CopyCode args[i] (E.frame.opAt (σs.length - ps.length + i)) (8 * i) ∧
            σs.length - ps.length + i < E.frame.height := fun i hi => by
        have h := hai i (by simp; omega) hi
        simp only [List.getElem_range, except_bind_ok] at h
        obtain ⟨o, ho, hcp⟩ := h
        obtain ⟨hlt, rfl⟩ := Env.op_ok ho
        exact ⟨copySlot_ok hcp, hlt⟩
      have hresc : ∀ j (hj : j < res.length),
          CopyCode res[j] (8 * j) (E.frame.opAt (σs.length - ps.length + j)) ∧
            σs.length - ps.length + j < E.frame.height := fun j hj => by
        have h := hri j (by simp; omega) hj
        simp only [List.getElem_range, except_bind_ok] at h
        obtain ⟨o, ho, hcp⟩ := h
        obtain ⟨hlt, rfl⟩ := Env.op_ok ho
        exact ⟨copySlot_ok hcp, hlt⟩
      exact ⟨target, ps, rs, hk, by omega, hc.2.1, hc.2.2, args, res, off, hal,
        fun i hi => (hargc i hi).1, fun i hi => (hargc i (by omega)).2, hrl,
        fun j hj => (hresc j hj).1, fun j hj => (hresc j (by omega)).2, o1, o2, o3, o4, rfl, rfl⟩

theorem take_reverse_getElem? {β : Type} {l : List β} {p i : Nat} (hp : p ≤ l.length)
    (hi : i < p) : (l.take p).reverse[i]? = l.reverse[l.length - p + i]? := by
  rw [List.getElem?_reverse (by simp; omega), List.getElem?_reverse (by omega),
    List.getElem?_take]
  simp only [List.length_take, Nat.min_eq_left hp, show p - 1 - i < p by omega, ↓reduceIte]
  congr 1
  omega

/-- The simulation of a call of function `k`: the copies of the arguments into the outgoing
area, `BL`, the callee's `FunSim` from `CallsOk`, and the copies of the results. -/
theorem sim_call (f k : Nat) : InstrSim P σ code (f + 1) (.call k) := by
  intro E ctl σs a is fin hgen hcode hev _ hb α m st sl ms hinv hpc need D hcl hD hroom
  obtain ⟨target, ps, rs, hk, hbp, hout, htake, args, res, off, hal, hargs, hah, hrl, hres, hrh,
    o1, o2, o3, o4, rfl, rfl⟩ := gen_call hgen
  have hfun : FunSim P σ code m E.toShared need f k (target, ps, rs) :=
    hcl k (target, ps, rs) hk f (by omega)
  have hh := hinv.len
  have hfit := hinv.frame.fits
  have hsz := E.frame.size_eq
  have hlr := E.frame.lrOff_eq
  have hop : ∀ j, E.frame.opAt j = 8 * (E.frame.out + E.frame.named.length + j) := fun _ => rfl
  generalize hp : ps.length = p at *
  generalize hr : rs.length = r at *
  generalize hhd : σs.length = h at *
  -- the copies of the arguments
  have hc0 := hcode
  rw [← hpc] at hc0
  obtain ⟨hc12, hcR⟩ := CodeAt.append.mp hc0
  obtain ⟨hcA, hcB⟩ := CodeAt.append.mp hc12
  have hwA : ∀ i < args.length,
      WordOk P (ms.sp + UInt32.ofNat (E.frame.opAt (h - p + i))) ∧
      WordOk P (ms.sp + UInt32.ofNat (E.frame.opAt (h - p + i) + 4)) ∧
      WordOk P (ms.sp + UInt32.ofNat (8 * i)) ∧ WordOk P (ms.sp + UInt32.ofNat (8 * i + 4)) :=
    fun i hi => by
      have := hah i (by omega)
      have := hop (h - p + i)
      exact ⟨hinv.frame.word (by omega) (by omega), hinv.frame.word (by omega) (by omega),
        hinv.frame.word (by omega) (by omega), hinv.frame.word (by omega) (by omega)⟩
  obtain ⟨t1, r1, p1, sp1, lr1, tr1, rd1, hw1, hm1⟩ := run_copies (P := P) (σ := σ)
    (src := fun i => E.frame.opAt (h - p + i)) (dst := fun i => 8 * i) hargs hwA
    (fun i hi j hj => by have := hah i (by omega); have := hop (h - p + i); omega)
    (fun i hi j hj hij => by omega)
    (fun i hi => by have := hah i (by omega); have := hop (h - p + i); omega) hcA
  -- the branch with link
  have hcsA := codeSize_copies hargs
  have ht1pc : t1.pc = after a (4 * p) := by
    rw [p1, hpc, hal]; addr_after
  rw [hcsA, hal, show ms.pc + UInt32.ofNat (16 * p) = t1.pc by rw [ht1pc, hpc]; addr_after] at hcB
  have eBL := exec_blTo (P := P) (σ := σ) o1 o2 o3 t1
  obtain ⟨w, hwd⟩ : ∃ w : State,
      w = { t1 with lr := (t1.pc + 4) ||| 1, pc := t1.pc + 4 + UInt32.ofInt off } := ⟨_, rfl⟩
  rw [← hwd] at eBL
  have hwpc : w.pc = target := by rw [hwd, State.pc_withLrPc, ht1pc]; exact o4
  have hwsp : w.sp = ms.sp := by rw [hwd, State.sp_withLrPc]; exact sp1
  have hwmem : w.mem = t1.mem := by rw [hwd, State.mem_withLrPc]
  -- the callee's simulation
  have hpv : p ≤ sl.values.length := by omega
  have hst : StackOk P E.limit (max p r) (need k) w := by
    refine ⟨by rw [hwsp]; exact hinv.frame.aligned, fun j hj => ?_, by rw [hwsp]; omega,
      by rw [hwsp]; exact hinv.frame.limit, by rw [hwsp]; exact hinv.frame.below,
      by rw [hwsp]; have := hD k (by simp [callsOf]); unfold room at hroom; omega⟩
    rw [hwsp]
    exact hinv.frame.ram j (by omega)
  have hargsW : ArgsAt w (sl.values.take p) := fun i v hv => by
    have hi : i < p := by
      have := (List.getElem?_eq_some_iff.mp hv).1; simp at this; omega
    rw [take_reverse_getElem? hpv hi, hh] at hv
    have hv0 := hinv.stack (h - p + i) v hv
    unfold ValAt at hv0 ⊢
    have e := hw1 i (by omega)
    unfold slotWords at e
    rw [hwmem, hwsp, ← sp1]
    rw [Prod.mk.injEq] at e
    rw [e.1, e.2]
    exact hv0
  have hres0 := hfun st sl.values w (by simp only; omega)
    (by have := hinv.types.take p; rw [htake] at this; simpa [hp] using this) hwpc
    (by rw [hwd, State.lr_withLrPc]; exact or1_odd _) (by simpa [hp, hr] using hst)
    (by simpa [hp] using hargsW)
  simp only [execOne.eq_def]
  revert hres0
  cases hR : Wasm.run f m k st sl.values with
  | Trap _ _ => intro _; trivial
  | Invalid _ => intro _; trivial
  | OutOfFuel => intro _; trivial
  | Thrown _ _ _ => intro h; exact h.elim
  | Success vs' st' =>
      intro hres0
      obtain ⟨ms', r2, p2, sp2, lr2, tr2, rd2, hm2, hl2, hd2, hargs2, hty2⟩ := hres0
      simp only [hp, hr] at hm2 hl2 hd2 hargs2 hty2
      -- the copies of the results
      have hms'sp : ms'.sp = ms.sp := sp2.trans hwsp
      have hwR : ∀ j < res.length,
          WordOk P (ms'.sp + UInt32.ofNat (8 * j)) ∧ WordOk P (ms'.sp + UInt32.ofNat (8 * j + 4)) ∧
          WordOk P (ms'.sp + UInt32.ofNat (E.frame.opAt (h - p + j))) ∧
          WordOk P (ms'.sp + UInt32.ofNat (E.frame.opAt (h - p + j) + 4)) := fun j hj => by
        have := hrh j (by omega)
        have := hop (h - p + j)
        rw [hms'sp]
        exact ⟨hinv.frame.word (by omega) (by omega), hinv.frame.word (by omega) (by omega),
          hinv.frame.word (by omega) (by omega), hinv.frame.word (by omega) (by omega)⟩
      have hpc2 : ms'.pc = after a (4 * p + 1) := by
        rw [p2, hwd, State.lr_withLrPc]
        have hev1 : (t1.pc + 4).toNat % 2 = 0 := by
          rw [ht1pc, show after a (4 * p) + 4 = after a (4 * p + 1) by addr_after]
          exact even_after hev _
        rw [or1_and _ hev1, ht1pc]
        addr_after
      have hcsB : codeSize (args.flatten ++ [Instr.blTo off]) = 16 * p + 4 := by
        rw [codeSize_append, hcsA, hal]; rfl
      rw [hcsB, show ms.pc + UInt32.ofNat (16 * p + 4) = ms'.pc by rw [hpc2, hpc]; addr_after] at hcR
      obtain ⟨t2, r3, p3, sp3, lr3, tr3, rd3, hw3, hm3⟩ := run_copies (P := P) (σ := σ)
        (src := fun j => 8 * j) (dst := fun j => E.frame.opAt (h - p + j)) hres hwR
        (fun i hi j hj => by have := hrh j (by omega); have := hop (h - p + j); omega)
        (fun i hi j hj hij => by
          have := hrh i (by omega); have := hrh j (by omega)
          have := hop (h - p + i); have := hop (h - p + j); omega)
        (fun j hj => by have := hrh j (by omega); have := hop (h - p + j); omega) hcR
      have ht2sp : t2.sp = ms.sp := sp3.trans hms'sp
      -- the bytes outside the outgoing area and the results' slots keep their values
      have hkeep : ∀ b : UInt32, ms.sp.toNat + 8 * E.frame.out ≤ b.toNat →
          (∀ j < r, Outside ms.sp (E.frame.opAt (h - p + j)) b) → t2.mem b = ms.mem b := by
        intro b hb1 hb2
        rw [hm3 b (fun j hj => by rw [hms'sp]; exact hb2 j (by omega)),
          hm2 b (by rw [hwsp]; omega), hwmem]
        refine hm1 b fun i hi => ?_
        unfold Outside
        rw [UInt32.toNat_sub, UInt32.toNat_add, UInt32.toNat_ofNat']
        have := toNat_lt32 b
        have := toNat_lt32 ms.sp
        simp only [Nat.reducePow]
        omega
      have hslot : ∀ o, 8 * E.frame.out ≤ o → o + 8 ≤ E.frame.size + 8 * E.frame.params →
          (∀ j < r, o + 8 ≤ E.frame.opAt (h - p + j) ∨ E.frame.opAt (h - p + j) + 8 ≤ o) →
          SlotSame ms t2 o := fun o ho1 ho2 ho3 =>
        slotSame_of_words (slotWords_congr ht2sp fun k hk => hkeep _ (by
          rw [UInt32.toNat_add, UInt32.toNat_ofNat']
          have := toNat_lt32 ms.sp
          simp only [Nat.reducePow]
          omega) fun j hj => outside_of_disjoint (ho3 j hj) (by omega)
            (by have := hrh j (by omega); have := hop (h - p + j); omega) hk) ht2sp
      have hvs' : vs' = vs'.take r ++ sl.values.drop p := by
        rw [← hd2, List.take_append_drop]
      have hvs' : vs' = vs'.take r ++ sl.values.drop p := by
        rw [← hd2, List.take_append_drop]
      have hhp : h - p + r ≤ E.frame.height := by
        rcases Nat.eq_zero_or_pos r with hr0 | hr0
        · have := hinv.height; omega
        · have := hrh (r - 1) (by omega); omega
      refine ⟨_, rfl, t2, r1.trans (reach_exec hcB eBL (r2.trans r3)), ?_, ht2sp,
        tr3.trans (tr2.trans (by rw [hwd, State.trace_withLrPc]; exact tr1)),
        rd3.trans (rd2.trans (by rw [hwd, State.reads_withLrPc]; exact rd1)),
        ⟨(hslot E.frame.lrOff (by omega) (by omega) fun j hj => by
            have := hrh j (by omega); have := hop (h - p + j); omega).1,
          fun b hb => hkeep b (by omega) fun j hj => outside_above (by
            have := hrh j (by omega); have := hop (h - p + j); omega)⟩,
        fun j hj => hslot _ (by have := hop j; omega) (by have := hop j; omega) fun j' hj' => by
          have := hop j; have := hop (h - p + j'); omega, ?_⟩
      · rw [p3, hpc2, hrl, List.length_append, List.length_append, length_copies hargs,
          length_copies hres, hal, hrl]
        simp only [List.length_cons, List.length_nil]
        addr_after
      · refine ⟨by rw [hl2]; omega, fun j v hv => ?_, hinv.count, fun i v o hv ho => ?_,
          hinv.ltypes, hinv.frame.congr ht2sp, ?_⟩
        · change vs'.reverse[j]? = some v at hv
          rw [hvs', List.reverse_append] at hv
          by_cases hj : j < h - p
          · rw [List.getElem?_append_left (by simp; omega), drop_reverse_getElem? (by omega)]
              at hv
            exact (hinv.stack j v hv).congr ht2sp (hslot _ (by have := hop j; omega)
              (by have := hop j; omega) fun j' hj' => by
                have := hop j; have := hop (h - p + j'); omega)
          · rw [List.getElem?_append_right (by simp; omega)] at hv
            simp only [List.length_reverse, List.length_drop, hh] at hv
            have hv2 := hargs2 (j - (h - p)) v hv
            have e := hw3 (j - (h - p)) (by
              have := (List.getElem?_eq_some_iff.mp hv).1; simp at this; omega)
            rw [show h - p + (j - (h - p)) = j by omega] at e
            unfold ValAt at hv2 ⊢
            unfold slotWords at e
            rw [Prod.mk.injEq] at e
            rw [e.1, e.2]
            exact hv2
        · obtain ⟨ho8, hob, -, hop'⟩ := Frame.localOff_bounds ho
          have hlo : 8 * E.frame.out ≤ o := by
            rcases Frame.localOff_eq ho with ⟨-, rfl⟩ | ⟨j, -, -, rfl⟩ <;> omega
          exact (hinv.locals i v o hv ho).congr ht2sp (hslot o hlo hob fun j hj =>
            (hop' (h - p + j) (by omega)))
        · show Typed _ vs'
          rw [hvs']
          exact hty2.append (hinv.types.drop p)

end LeanExe.M7
