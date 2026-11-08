import LeanExe.M7.Setup
import LeanExe.M7.Proof.Store
import LeanExe.M7.Proof.Init

/-!
The run of the setup of `LeanExe/M7/Setup.lean`.  `run_clearLoop` runs `clearLoop` by induction
on the number of words from r0 to r1, as A64's `run_clearLoop` does: each pass compares r0 with r1
as unsigned numbers, stores the zero of r2 at r0, and adds the 4 of r3 to r0, so the loop leaves
when r0 reaches r1, with every byte from r0's first value below r1 zero.  `run_storeWords` runs
the stores of the prefix's nonzero words by induction on the words: the bytes that `store32`
writes for a word are the bytes from which `wordsOf` formed it, and a zero word's bytes are the
zeros that the loop left.  `setup_run` joins the two: after the setup, every byte of the area
holds `areaByte` of the module's initial store, the prefix's bytes by `areaPrefixBytes_getElem`
and the others by `areaByte_tail`.

`setup_boot` runs an image whose layout `Boot.setup` gives, from reset to the initialization's
start, where the machine holds the module's initial store in the area by `storeRel_init`.
`setupBoot_run` continues the run through the initialization, which keeps memory, and `main_run`
of `LeanExe/M7/Proof/Main.lean`, whose windows carry the store in the area from the initial store
on.
-/

namespace LeanExe.M7

open Wasm LeanExe.ProofKit LeanExe.CallGraph LeanExe.Pipeline LeanExe.Requests

variable {P : Platform} {σ : Nat → UInt32} {code : UInt32 → Option UInt16}

/-! ## Addresses and bytes -/

theorem ofNat_add_ne {a : UInt32} {x y : Nat} (hx : a.toNat + x < 4294967296)
    (hy : a.toNat + y < 4294967296) (hne : x ≠ y) :
    a + UInt32.ofNat x ≠ a + UInt32.ofNat y := by
  intro h
  have := congrArg UInt32.toNat h
  rw [toNat_add_ofNat hx, toNat_add_ofNat hy] at this
  omega

theorem add_ofNat_congr (a : UInt32) {x y : Nat} (h : x = y) :
    a + UInt32.ofNat x = a + UInt32.ofNat y := by
  rw [h]

/-- A word store at `a` gives the bytes from `a` those of the word. -/
theorem store32_in {m : UInt32 → UInt8} {a v : UInt32} {j : Nat} (hj : j < 4) :
    store32 m a v (a + UInt32.ofNat j) = (v >>> (UInt32.ofNat j * 8)).toUInt8 := by
  have e : a + UInt32.ofNat j - a = UInt32.ofNat j := by
    rw [UInt32.add_comm, UInt32.add_sub_cancel]
  have hlt : UInt32.ofNat j < 4 := by
    rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_ofNat', show (4 : UInt32).toNat = 4 from rfl]
    omega
  simp only [store32, e, hlt, ↓reduceIte]

/-- A word store at `a` leaves every byte outside its four. -/
theorem store32_out {m : UInt32 → UInt8} {a v b : UInt32}
    (h : ∀ j < 4, b ≠ a + UInt32.ofNat j) : store32 m a v b = m b := by
  apply store32_far
  intro hlt
  have hj : (b - a).toNat < 4 := by
    rw [UInt32.lt_iff_toNat_lt] at hlt
    exact hlt
  apply h _ hj
  rw [UInt32.ofNat_toNat, UInt32.add_comm, UInt32.sub_add_cancel]

theorem zero_byte (x : UInt32) : ((0 : UInt32) >>> x).toUInt8 = 0 := by
  apply UInt8.toNat_inj.mp
  rw [UInt32.toNat_toUInt8, UInt32.toNat_shiftRight]
  simp

/-- Byte `k` of a word, as `store32` writes it, as a number. -/
theorem toNat_wordByte (v : UInt32) {k : Nat} (hk : k < 4) :
    ((v >>> (UInt32.ofNat k * 8)).toUInt8).toNat = v.toNat / 2 ^ (8 * k) % 256 := by
  have := toNat_byte v (UInt32.ofNat k) k (by rw [UInt32.toNat_ofNat']; omega) hk
  rwa [UInt8.toNat_toUInt32] at this

theorem length_wordsOf : ∀ bs : List UInt8, (wordsOf bs).length = bs.length / 4
  | [] => rfl
  | [_] => by simp [wordsOf]
  | [_, _] => by simp [wordsOf]
  | [_, _, _] => by simp [wordsOf]
  | _ :: _ :: _ :: _ :: rest => by
      simp only [wordsOf, List.length_cons, length_wordsOf rest]
      omega

/-- Byte `j` of the bytes `bs` is byte `j % 4` of word `j / 4` of `wordsOf bs`. -/
theorem wordsOf_byte : ∀ (bs : List UInt8) (j : Nat) {w : UInt32}, (wordsOf bs)[j / 4]? = some w →
    bs[j]? = some (w >>> (UInt32.ofNat (j % 4) * 8)).toUInt8
  | [], _, _, h => by
      rw [show wordsOf [] = [] from rfl, List.getElem?_nil] at h; cases h
  | [a], _, _, h => by
      rw [show wordsOf [a] = [] from rfl, List.getElem?_nil] at h; cases h
  | [a, b], _, _, h => by
      rw [show wordsOf [a, b] = [] from rfl, List.getElem?_nil] at h; cases h
  | [a, b, c], _, _, h => by
      rw [show wordsOf [a, b, c] = [] from rfl, List.getElem?_nil] at h; cases h
  | b0 :: b1 :: b2 :: b3 :: rest, j, w, h => by
      have e : wordsOf (b0 :: b1 :: b2 :: b3 :: rest) =
          (b0.toUInt32 ||| b1.toUInt32 <<< 8 ||| b2.toUInt32 <<< 16 ||| b3.toUInt32 <<< 24) ::
            wordsOf rest := rfl
      rw [e] at h
      by_cases hj : j < 4
      · rw [show j / 4 = 0 by omega, List.getElem?_cons_zero, Option.some.injEq] at h
        have hw : w.toNat = b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat := by
          rw [← h]
          exact toNat_bytes32 _ _ _ _
        have hb := toNat_wordByte w (k := j % 4) (Nat.mod_lt _ (by decide))
        rw [hw] at hb
        have h0 := b0.toNat_lt
        have h1 := b1.toNat_lt
        have h2 := b2.toNat_lt
        have h3 := b3.toNat_lt
        simp only [Nat.reducePow] at h0 h1 h2 h3
        rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
        all_goals
          first
            | show some b0 = some _
            | show some b1 = some _
            | show some b2 = some _
            | show some b3 = some _
          congr 1
          apply UInt8.toNat_inj.mp
          rw [hb]
          simp only [Nat.reduceMod, Nat.reduceMul, Nat.reducePow]
          omega
      · obtain ⟨k, rfl⟩ : ∃ k, j = k + 4 := ⟨j - 4, by omega⟩
        rw [show (k + 4) / 4 = k / 4 + 1 by omega, List.getElem?_cons_succ] at h
        have ih := wordsOf_byte rest k h
        rw [show (k + 4) % 4 = k % 4 by omega, show k + 4 = k + 1 + 1 + 1 + 1 from rfl,
          List.getElem?_cons_succ, List.getElem?_cons_succ, List.getElem?_cons_succ,
          List.getElem?_cons_succ]
        exact ih

/-! ## Single instructions -/

theorem exec_str_ram {s : State} {t n : Fin 8} {o : Fin 4096}
    (h : WordOk P (s.r n + UInt32.ofNat o.val)) :
    exec P σ (.str t n o) s =
      some { s with
        mem := store32 s.mem (s.r n + UInt32.ofNat o.val) (s.r t)
        pc := s.pc + 4 } := by
  obtain ⟨h4, hd, hm⟩ := h
  simp only [exec, storeWord, h4, hd, hm, ne_eq, not_true_eq_false, ↓reduceIte, Bool.false_eq_true,
    Option.map_some]

/-- A store that changes the memory and the program counter keeps SP, LR, the registers, the
trace, and the read count. -/
theorem withMem_keeps (s : State) (m : UInt32 → UInt8) (p : UInt32) :
    ({ s with mem := m, pc := p } : State).sp = s.sp ∧
      ({ s with mem := m, pc := p } : State).lr = s.lr ∧
      ({ s with mem := m, pc := p } : State).regs = s.regs ∧
      ({ s with mem := m, pc := p } : State).trace = s.trace ∧
      ({ s with mem := m, pc := p } : State).reads = s.reads := by
  cases s; exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `movConst d w` sets register `d` to `w` and keeps the other registers, SP, LR, the memory,
the trace, and the read count. -/
theorem run_movConst {s : State} {d : Fin 8} {w : Nat} {rest : List Instr} (hw : w < 4294967296)
    (hc : CodeAt code s.pc (movConst d w ++ rest)) :
    ∃ t, Reach P σ code s t ∧ CodeAt code t.pc rest ∧
      t.pc = s.pc + UInt32.ofNat (4 * (movConst d w).length) ∧ t.sp = s.sp ∧ t.lr = s.lr ∧
      t.mem = s.mem ∧ t.trace = s.trace ∧ t.reads = s.reads ∧ t.r d = UInt32.ofNat w ∧
      ∀ e, e ≠ d → t.r e = s.r e := by
  obtain ⟨c1, c2⟩ := CodeAt.append.mp hc
  obtain ⟨r, p, sp, lr, tr, rd, -⟩ :=
    run_slots (P := P) (σ := σ) (slotsOk_reg (movConst_regForm d w) s.sp) c1
  obtain ⟨hm, -, -⟩ := slotRun_reg (P := P) (σ := σ) (movConst_regForm d w) s
  obtain ⟨hd, he⟩ := slotRun_movConst (P := P) (σ := σ) d hw s
  refine ⟨_, r, ?_, p, sp, lr, hm, tr, rd, hd, he⟩
  rw [p, ← codeSize_of_wide (movConst_wide d w)]
  exact c2

/-! ## The clearing loop -/

/-- The comparison and the conditional branch of `clearLoop` at `a`: the machine reaches the
instruction after the loop when r1 is at or below r0 and the `STR` otherwise, and it keeps the
registers. -/
theorem run_clearCheck {a : UInt32} {s : State} (hc : CodeAt code a clearLoop) (hpc : s.pc = a) :
    ∃ u, Reach P σ code s u ∧ Keeps s u ∧ u.regs = s.regs ∧
      u.pc = if (s.r 1).toNat ≤ (s.r 0).toNat then a + 20 else a + 8 := by
  rw [show clearLoop = ([.cmpReg 0 1] ++ [Instr.bcondTo condCS 12]) ++
    [.str 2 0 0, .addReg 0 0 0 3 0 0, .bTo (-20)] from rfl] at hc
  obtain ⟨c1, -⟩ := CodeAt.append.mp hc
  rw [← hpc] at c1
  obtain ⟨u, r, k, g, p⟩ := run_branch (P := P) (σ := σ) (t := _) (a + 20) (a + 8) rfl rfl c1 rfl
    (by decide) (by decide) (by decide) (by rw [hpc]; addr_eq) (by rw [hpc]; addr_eq)
  refine ⟨u, r, k, g, ?_⟩
  rw [p, condCS, condHolds_cs, State.cFlag_withPc, State.cFlag_setNZCV', carry_cmp]
  by_cases h : (s.r 1).toNat ≤ (s.r 0).toNat
  · rw [decide_eq_true h, if_pos h]; rfl
  · rw [decide_eq_false h, if_neg h]; rfl

/-- A pass of `clearLoop` at `a`, with r0 below r1 and the word at r0 Normal memory: the machine
stores r2 at r0, adds r3 to r0, and returns to `a`. -/
theorem run_clearPass {a : UInt32} {s : State} (hc : CodeAt code a clearLoop) (hpc : s.pc = a)
    (hlt : ¬ (s.r 1).toNat ≤ (s.r 0).toNat) (hw : WordOk P (s.r 0)) :
    ∃ u, Reach P σ code s u ∧ u.pc = a ∧ u.r 0 = s.r 0 + s.r 3 ∧ (∀ e, e ≠ 0 → u.r e = s.r e) ∧
      u.sp = s.sp ∧ u.lr = s.lr ∧ u.trace = s.trace ∧ u.reads = s.reads ∧
      u.mem = store32 s.mem (s.r 0) (s.r 2) := by
  obtain ⟨u1, r1, k1, g1, p1⟩ := run_clearCheck (P := P) (σ := σ) hc hpc
  rw [if_neg hlt] at p1
  rw [show clearLoop = [.cmpReg 0 1, Instr.bcondTo condCS 12] ++
    [.str 2 0 0, .addReg 0 0 0 3 0 0, .bTo (-20)] from rfl] at hc
  obtain ⟨-, c2⟩ := CodeAt.append.mp hc
  have c2' : CodeAt code u1.pc [.str 2 0 0, .addReg 0 0 0 3 0 0, .bTo (-20)] :=
    c2.at_eq (by rw [p1]; addr_eq)
  have e0 : u1.r 0 = s.r 0 := State.r_of_regs g1 0
  have hw' : WordOk P (u1.r 0 + UInt32.ofNat (0 : Fin 4096).val) := by
    rw [e0, show UInt32.ofNat (0 : Fin 4096).val = 0 from rfl, UInt32.add_zero]
    exact hw
  obtain ⟨r2, c3, p2⟩ := reach_falls (P := P) (σ := σ) c2' rfl (exec_str_ram (t := 2) hw')
  obtain ⟨sp2, lr2, g2, tr2, rd2⟩ := withMem_keeps u1
    (store32 u1.mem (u1.r 0 + UInt32.ofNat (0 : Fin 4096).val) (u1.r 2)) (u1.pc + 4)
  generalize hu2 : ({ u1 with
    mem := (store32 u1.mem (u1.r 0 + UInt32.ofNat (0 : Fin 4096).val) (u1.r 2))
    pc := u1.pc + 4 } : State) = u2 at r2 c3 p2 sp2 lr2 g2 tr2 rd2
  have m2 : u2.mem = store32 s.mem (s.r 0) (s.r 2) := by
    rw [← hu2, State.mem_withMem, k1.mem, e0, State.r_of_regs g1 2,
      show UInt32.ofNat (0 : Fin 4096).val = 0 from rfl, UInt32.add_zero]
  obtain ⟨r3, c4, p3, k3⟩ := run_reg (P := P) (σ := σ) c3 rfl rfl
    (show exec P σ (.addReg 0 0 0 3 0 0) u2 = some { u2.result 0 0
      (addWithCarry (u2.r 0) (shl (u2.r 3) (4 * (0 : Fin 8).val + (0 : Fin 4).val)) false) with
        pc := u2.pc + 4 } from rfl)
  generalize hu3 : ({ u2.result 0 0 (addWithCarry (u2.r 0)
    (shl (u2.r 3) (4 * (0 : Fin 8).val + (0 : Fin 4).val)) false) with pc := u2.pc + 4 } : State)
    = u3 at r3 c4 p3 k3
  have e3 : ∀ e : Fin 8, u3.r e =
      if e = 0 then (addWithCarry (u2.r 0) (shl (u2.r 3) 0) false).1 else u2.r e := by
    intro e
    rw [← hu3, State.r_withPc, State.r_result_zero]
    by_cases he : e = 0
    · subst he; rw [State.r_setR_same, if_pos rfl]; rfl
    · rw [State.r_setR_ne _ _ he, if_neg he]
  have eb := exec_bTo (P := P) (σ := σ) (off := -20) (by decide) (by decide) (by decide) u3
  have r4 : Reach P σ code u3 { u3 with pc := u3.pc + 4 + UInt32.ofInt (-20) } :=
    reach_exec (CodeAt.cons.mp c4).1 eb (.refl _)
  have hregs : ∀ e : Fin 8, e ≠ 0 → u2.r e = s.r e := fun e _ => by
    rw [State.r_of_regs g2, State.r_of_regs g1]
  refine ⟨_, r1.trans (r2.trans (r3.trans r4)), ?_, ?_, fun e he => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show u3.pc + 4 + UInt32.ofInt (-20) = a
    rw [p3, p2, p1]
    have := toNat_lt32 a
    addr_eq
  · rw [State.r_withPc, e3 0, if_pos rfl, shl_zero, add_addWithCarry,
      State.r_of_regs g2 0, e0, hregs 3 (by decide)]
  · rw [State.r_withPc, e3 e, if_neg he, hregs e he]
  · show u3.sp = s.sp
    rw [k3.sp, sp2, k1.sp]
  · show u3.lr = s.lr
    rw [k3.lr, lr2, k1.lr]
  · show u3.trace = s.trace
    rw [k3.trace, tr2, k1.trace]
  · show u3.reads = s.reads
    rw [k3.reads, rd2, k1.reads]
  · show u3.mem = _
    rw [k3.mem, m2]

/-- The run of `clearLoop` at `a` with `lo` in r0, `hi` in r1, 0 in r2, and 4 in r3, where `lo` is
a multiple of 4 at or below `hi`, `hi - lo` is a multiple of 4, and every byte from `lo` below `hi`
is `Ram`: the machine reaches the instruction after the loop with every byte from `lo` below `hi`
zero and every other byte kept. -/
theorem run_clearLoop {a lo hi : UInt32} {s : State} (hc : CodeAt code a clearLoop)
    (hpc : s.pc = a) (h0 : s.r 0 = lo) (h1 : s.r 1 = hi) (h2 : s.r 2 = 0) (h3 : s.r 3 = 4)
    (hle : lo.toNat ≤ hi.toNat) (h4 : (hi.toNat - lo.toNat) % 4 = 0) (hal : lo % 4 = 0)
    (hram : ∀ j < hi.toNat - lo.toNat, Ram P (lo + UInt32.ofNat j)) :
    ∃ t, Reach P σ code s t ∧ t.pc = a + 20 ∧
      (∀ j < hi.toNat - lo.toNat, t.mem (lo + UInt32.ofNat j) = 0) ∧
      (∀ b, (∀ j < hi.toNat - lo.toNat, b ≠ lo + UInt32.ofNat j) → t.mem b = s.mem b) ∧
      t.sp = s.sp ∧ t.lr = s.lr ∧ t.trace = s.trace ∧ t.reads = s.reads := by
  obtain ⟨n, hn⟩ : ∃ n, hi.toNat = lo.toNat + 4 * n := ⟨(hi.toNat - lo.toNat) / 4, by omega⟩
  clear hle h4
  have hhi := toNat_lt32 hi
  induction n generalizing s lo with
  | zero =>
      obtain ⟨u, r, k, -, p⟩ := run_clearCheck (P := P) (σ := σ) hc hpc
      rw [h0, h1, if_pos (by omega)] at p
      exact ⟨u, r, p, fun j hj => by omega, fun b _ => by rw [k.mem], k.sp, k.lr, k.trace,
        k.reads⟩
  | succ n ih =>
      have hlt : ¬ (s.r 1).toNat ≤ (s.r 0).toNat := by rw [h0, h1]; omega
      have hw : WordOk P (s.r 0) := by
        have := wordOk_of_ram (P := P) (sp := lo) (n := 4) (o := 0)
          (fun j hj => hram j (by omega)) hal rfl (by omega)
        rwa [show UInt32.ofNat 0 = 0 from rfl, UInt32.add_zero, ← h0] at this
      obtain ⟨u, r, p, u0, ue, usp, ulr, utr, urd, umem⟩ :=
        run_clearPass (P := P) (σ := σ) hc hpc hlt hw
      have hlo : (lo + UInt32.ofNat 4).toNat = lo.toNat + 4 := toNat_add_ofNat (by omega)
      obtain ⟨t, r', p', hz, hk, tsp, tlr, ttr, trd⟩ := ih (s := u) (lo := lo + UInt32.ofNat 4) p
        (by rw [u0, h0, h3]; rfl) (by rw [ue 1 (by decide), h1]) (by rw [ue 2 (by decide), h2])
        (by rw [ue 3 (by decide), h3]) (mod4_add hal rfl)
        (fun j hj => by rw [add_ofNat_add]; exact hram (4 + j) (by omega)) (by omega)
      have hne : ∀ j < 4, ∀ j' < hi.toNat - (lo + UInt32.ofNat 4).toNat,
          lo + UInt32.ofNat j ≠ lo + UInt32.ofNat 4 + UInt32.ofNat j' := fun j hj j' hj' => by
        rw [add_ofNat_add]
        exact ofNat_add_ne (by omega) (by omega) (by omega)
      refine ⟨t, r.trans r', p', fun j hj => ?_, fun b hb => ?_, by rw [tsp, usp],
        by rw [tlr, ulr], by rw [ttr, utr], by rw [trd, urd]⟩
      · by_cases hj4 : j < 4
        · rw [hk _ (hne j hj4), umem, h0, h2, store32_in hj4, zero_byte]
        · have := hz (j - 4) (by omega)
          rwa [add_ofNat_add, show 4 + (j - 4) = j by omega] at this
      · rw [hk b fun j' hj' => by
            rw [add_ofNat_add]
            exact hb (4 + j') (by omega),
          umem, h0, store32_out fun j hj => hb j (by omega)]

/-! ## The stores of the prefix -/

theorem storeWords_wide (area : Nat) : ∀ (i : Nat) (cur : Option Nat) (ws : List UInt32),
    (storeWords area i cur ws).all Instr.wide = true
  | _, _, [] => rfl
  | i, cur, w :: ws => by
      rw [storeWords]
      split
      · exact storeWords_wide area _ _ ws
      · have hb : (if cur = some (i / 1024) then []
            else movConst 1 (area + 4096 * (i / 1024))).all Instr.wide = true := by
          split
          · rfl
          · exact movConst_wide _ _
        rw [List.all_append, List.all_append, List.all_append, hb, movConst_wide,
          storeWords_wide area _ _ ws]
        rfl

/-- The base register of the stores of a word: after the `movConst 1` that `storeWords` emits
when r1 does not hold the address of the word's 4 KiB block, r1 holds that address. -/
theorem run_base {s : State} {area q : Nat} {cur : Option Nat} {rest : List Instr}
    (hq : area + 4096 * q < 4294967296)
    (hcur : ∀ q', cur = some q' → s.r 1 = UInt32.ofNat area + UInt32.ofNat (4096 * q'))
    (hc : CodeAt code s.pc ((if cur = some q then [] else movConst 1 (area + 4096 * q)) ++ rest)) :
    ∃ t, Reach P σ code s t ∧ CodeAt code t.pc rest ∧
      t.pc = s.pc + UInt32.ofNat
        (4 * (if cur = some q then [] else movConst 1 (area + 4096 * q)).length) ∧
      t.sp = s.sp ∧ t.lr = s.lr ∧ t.mem = s.mem ∧ t.trace = s.trace ∧ t.reads = s.reads ∧
      t.r 1 = UInt32.ofNat area + UInt32.ofNat (4096 * q) := by
  by_cases h : cur = some q
  · rw [if_pos h] at hc ⊢
    refine ⟨s, .refl _, hc, ?_, rfl, rfl, rfl, rfl, rfl, hcur q h⟩
    rw [List.length_nil, Nat.mul_zero]
    exact (UInt32.add_zero _).symm
  · rw [if_neg h] at hc ⊢
    obtain ⟨t, r, c, p, sp, lr, m, tr, rd, h1, -⟩ := run_movConst (P := P) (σ := σ) hq hc
    exact ⟨t, r, c, p, sp, lr, m, tr, rd, by rw [h1, UInt32.ofNat_add]⟩

theorem getElem?_cons_div {α : Type} {w : α} {ws : List α} {j : Nat} {x : α} (hj : j < 4)
    (h : (w :: ws)[j / 4]? = some x) : x = w := by
  rw [show j / 4 = 0 by omega, List.getElem?_cons_zero, Option.some.injEq] at h
  exact h.symm

theorem getElem?_cons_div' {α : Type} {w : α} {ws : List α} {j : Nat} (hj : 4 ≤ j) :
    (w :: ws)[j / 4]? = ws[(j - 4) / 4]? := by
  rw [show j / 4 = (j - 4) / 4 + 1 by omega, List.getElem?_cons_succ]

/-- The stores of the nonzero words `ws` from word `i` of the area at `area`, where every byte of
those words is `Ram` and 0 before the stores: each byte of the words then holds its byte of its
word, as `store32` writes it, and every other byte is kept. -/
theorem run_storeWords {area : UInt32} (hal : area % 4 = 0) :
    ∀ (ws : List UInt32) (i : Nat) (cur : Option Nat) (s : State) (rest : List Instr),
    CodeAt code s.pc (storeWords area.toNat i cur ws ++ rest) →
    (∀ q, cur = some q → s.r 1 = area + UInt32.ofNat (4096 * q)) →
    area.toNat + 4 * (i + ws.length) < 4294967296 →
    (∀ j < 4 * ws.length, Ram P (area + UInt32.ofNat (4 * i + j))) →
    (∀ j < 4 * ws.length, s.mem (area + UInt32.ofNat (4 * i + j)) = 0) →
    ∃ t, Reach P σ code s t ∧ CodeAt code t.pc rest ∧
      t.pc = s.pc + UInt32.ofNat (4 * (storeWords area.toNat i cur ws).length) ∧
      t.sp = s.sp ∧ t.lr = s.lr ∧ t.trace = s.trace ∧ t.reads = s.reads ∧
      (∀ j < 4 * ws.length, ∀ w, ws[j / 4]? = some w →
        t.mem (area + UInt32.ofNat (4 * i + j)) = (w >>> (UInt32.ofNat (j % 4) * 8)).toUInt8) ∧
      (∀ b, (∀ j < 4 * ws.length, b ≠ area + UInt32.ofNat (4 * i + j)) → t.mem b = s.mem b)
  | [], i, cur, s, rest, hc, _, _, _, _ => by
      have e : storeWords area.toNat i cur [] = [] := rfl
      rw [e] at hc ⊢
      refine ⟨s, .refl _, hc, ?_, rfl, rfl, rfl, rfl, fun j hj => by simp at hj, fun _ _ => rfl⟩
      rw [List.length_nil, Nat.mul_zero]
      exact (UInt32.add_zero _).symm
  | w :: ws, i, cur, s, rest, hc, hcur, hfit, hram, hzero => by
      simp only [List.length_cons] at hfit hram hzero ⊢
      have hne : ∀ j < 4, ∀ j' < 4 * ws.length,
          area + UInt32.ofNat (4 * i + j) ≠ area + UInt32.ofNat (4 * (i + 1) + j') :=
        fun j hj j' hj' => ofNat_add_ne (by omega) (by omega) (by omega)
      by_cases hw0 : w = 0
      · have hsw : storeWords area.toNat i cur (w :: ws) = storeWords area.toNat (i + 1) cur ws :=
          by simp only [storeWords, if_pos hw0]
        have hc' : CodeAt code s.pc (storeWords area.toNat (i + 1) cur ws ++ rest) := by
          rw [hsw] at hc
          exact hc
        obtain ⟨t, r, c, p, sp, lr, tr, rd, hm, hk⟩ := run_storeWords hal ws (i + 1) cur s rest hc'
          hcur (by omega) (fun j hj => by
            rw [show 4 * (i + 1) + j = 4 * i + (4 + j) by omega]
            exact hram _ (by omega))
          (fun j hj => by
            rw [show 4 * (i + 1) + j = 4 * i + (4 + j) by omega]
            exact hzero _ (by omega))
        refine ⟨t, r, c, by rw [p, hsw], sp, lr, tr, rd, fun j hj x hx => ?_,
          fun b hb => hk b fun j' hj' => by
            rw [show 4 * (i + 1) + j' = 4 * i + (4 + j') by omega]
            exact hb _ (by omega)⟩
        by_cases hj4 : j < 4
        · rw [getElem?_cons_div hj4 hx, hw0, zero_byte, hk _ (hne j hj4)]
          exact hzero j (by omega)
        · rw [getElem?_cons_div' (by omega)] at hx
          have := hm (j - 4) (by omega) x hx
          rwa [show 4 * (i + 1) + (j - 4) = 4 * i + j by omega,
            show (j - 4) % 4 = j % 4 by omega] at this
      · have hcode : storeWords area.toNat i cur (w :: ws) =
            (if cur = some (i / 1024) then [] else movConst 1 (area.toNat + 4096 * (i / 1024))) ++
              (movConst 0 w.toNat ++ (.str 0 1 (field 4096 (4 * (i % 1024))) ::
                storeWords area.toNat (i + 1) (some (i / 1024)) ws)) := by
          simp only [storeWords, if_neg hw0, List.append_assoc, List.cons_append, List.nil_append]
        rw [hcode] at hc
        simp only [List.append_assoc, List.cons_append] at hc
        have hcur' : ∀ q', cur = some q' →
            s.r 1 = UInt32.ofNat area.toNat + UInt32.ofNat (4096 * q') := fun q' hq' => by
          rw [UInt32.ofNat_toNat]; exact hcur q' hq'
        obtain ⟨u1, r1, c1, p1, sp1, lr1, m1, tr1, rd1, b1⟩ :=
          run_base (P := P) (σ := σ) (q := i / 1024) (by omega) hcur' hc
        rw [UInt32.ofNat_toNat] at b1
        obtain ⟨u2, r2, c2, p2, sp2, lr2, m2, tr2, rd2, w2, k2⟩ :=
          run_movConst (P := P) (σ := σ) (d := 0) (w := w.toNat) (toNat_lt32 w) c1
        rw [UInt32.ofNat_toNat] at w2
        have hb2 : u2.r 1 = area + UInt32.ofNat (4096 * (i / 1024)) := by
          rw [k2 1 (by decide), b1]
        have haddr : u2.r 1 + UInt32.ofNat (field 4096 (4 * (i % 1024))).val =
            area + UInt32.ofNat (4 * i) := by
          rw [hb2, field_val, add_ofNat_add]
          exact add_ofNat_congr _ (by omega)
        have hwo : WordOk P (u2.r 1 + UInt32.ofNat (field 4096 (4 * (i % 1024))).val) := by
          rw [haddr]
          have := wordOk_of_ram (P := P) (sp := area + UInt32.ofNat (4 * i)) (n := 4) (o := 0)
            (fun j hj => by rw [add_ofNat_add]; exact hram j (by omega)) (mod4_add hal (by omega))
            rfl (by omega)
          rwa [show UInt32.ofNat 0 = 0 from rfl, UInt32.add_zero] at this
        obtain ⟨r3, c3, p3⟩ := reach_falls (P := P) (σ := σ) c2 rfl (exec_str_ram (t := 0) hwo)
        obtain ⟨sp3, lr3, g3, tr3, rd3⟩ := withMem_keeps u2
          (store32 u2.mem (u2.r 1 + UInt32.ofNat (field 4096 (4 * (i % 1024))).val) (u2.r 0))
          (u2.pc + 4)
        generalize hu3 : ({ u2 with
          mem := (store32 u2.mem (u2.r 1 + UInt32.ofNat (field 4096 (4 * (i % 1024))).val)
            (u2.r 0))
          pc := u2.pc + 4 } : State) = u3 at r3 c3 p3 sp3 lr3 g3 tr3 rd3
        have m3 : u3.mem = store32 s.mem (area + UInt32.ofNat (4 * i)) w := by
          rw [← hu3, State.mem_withMem, haddr, w2, m2, m1]
        obtain ⟨t, r, c, p, sp, lr, tr, rd, hm, hk⟩ := run_storeWords hal ws (i + 1)
          (some (i / 1024)) u3 rest c3
          (fun q hq => by
            cases hq
            rw [State.r_of_regs g3, hb2])
          (by omega)
          (fun j hj => by
            rw [show 4 * (i + 1) + j = 4 * i + (4 + j) by omega]
            exact hram _ (by omega))
          (fun j hj => by
            rw [m3, store32_out (a := area + UInt32.ofNat (4 * i))
                (b := area + UInt32.ofNat (4 * (i + 1) + j)) fun j' hj' => by
                rw [add_ofNat_add]
                exact (hne j' hj' j hj).symm,
              show 4 * (i + 1) + j = 4 * i + (4 + j) by omega]
            exact hzero _ (by omega))
        refine ⟨t, r1.trans (r2.trans (r3.trans r)), c, ?_, ?_, ?_, ?_, ?_, fun j hj x hx => ?_,
          fun b hb => ?_⟩
        · rw [p, p3, p2, p1, hcode]
          simp only [List.length_append, List.length_cons, add_ofNat_add]
          rw [show (4 : UInt32) = UInt32.ofNat 4 from rfl, add_ofNat_add, add_ofNat_add]
          exact add_ofNat_congr _ (by omega)
        · rw [sp, sp3, sp2, sp1]
        · rw [lr, lr3, lr2, lr1]
        · rw [tr, tr3, tr2, tr1]
        · rw [rd, rd3, rd2, rd1]
        · by_cases hj4 : j < 4
          · rw [getElem?_cons_div hj4 hx, hk _ (hne j hj4), m3, ← add_ofNat_add, store32_in hj4,
              Nat.mod_eq_of_lt hj4]
          · rw [getElem?_cons_div' (by omega)] at hx
            have := hm (j - 4) (by omega) x hx
            rwa [show 4 * (i + 1) + (j - 4) = 4 * i + j by omega,
              show (j - 4) % 4 = j % 4 by omega] at this
        · rw [hk b fun j' hj' => by
              rw [show 4 * (i + 1) + j' = 4 * i + (4 + j') by omega]
              exact hb _ (by omega),
            m3, store32_out (a := area + UInt32.ofNat (4 * i)) (b := b) fun j hj => by
              rw [add_ofNat_add]
              exact hb j (by omega)]

/-! ## The setup -/

theorem setupCode_wide (area : UInt32) (cap : Nat) (m : Module) :
    (setupCode area cap m).all Instr.wide = true := by
  rw [setupCode, List.all_append, List.all_append, List.all_append, List.all_append,
    movConst_wide, movConst_wide, storeWords_wide]
  rfl

theorem of_setupOk {m : Module} {cap : Nat} (h : setupOk m cap = true) :
    areaOk m cap = true ∧ areaPrefix m ≤ areaSize cap ∧ ∃ gts, globalTypesOf m = some gts ∧
      gts.length ≤ 511 ∧ gts.all intType = true := by
  unfold setupOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, ?_⟩
  cases hg : globalTypesOf m with
  | none => rw [hg] at h3; cases h3
  | some gts =>
      rw [hg] at h3
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h3
      exact ⟨gts, rfl, h3.1, h3.2⟩

/-- The setup of the area at `area` for the store of `m` with a memory of `cap` pages, placed at
the program counter and followed by `rest`: the area lies below 2^32 at a multiple of 4 and its
bytes are `Ram`, and the machine reaches `rest` with every byte of the area holding `areaByte` of
the module's initial store and SP, LR, the trace, and the read count unchanged. -/
theorem setup_run {area : UInt32} {cap : Nat} {m : Module} {s : State} {rest : List Instr}
    (hok : setupOk m cap = true) (hal : area % 4 = 0)
    (hfit : area.toNat + areaSize cap < 4294967296)
    (hram : ∀ j < areaSize cap, Ram P (area + UInt32.ofNat j))
    (hc : CodeAt code s.pc (setupCode area cap m ++ rest)) :
    ∃ t, Reach P σ code s t ∧ CodeAt code t.pc rest ∧
      t.pc = s.pc + UInt32.ofNat (4 * (setupCode area cap m).length) ∧ t.sp = s.sp ∧
      t.lr = s.lr ∧ t.trace = s.trace ∧ t.reads = s.reads ∧
      ∀ j < areaSize cap, t.mem (area + UInt32.ofNat j) = areaByte m.initialStore j := by
  obtain ⟨-, hpre, -⟩ := of_setupOk hok
  have hcode : setupCode area cap m ++ rest =
      movConst 0 area.toNat ++ (movConst 1 (area.toNat + areaSize cap) ++ (.movImm 2 0 ::
        .movImm 3 4 :: (clearLoop ++ (storeWords area.toNat 0 none
          (wordsOf (areaPrefixBytes m)) ++ rest)))) := by
    simp only [setupCode, List.append_assoc, List.cons_append, List.nil_append]
  rw [hcode] at hc
  obtain ⟨t1, r1, c1, p1, sp1, lr1, m1, tr1, rd1, a1, -⟩ :=
    run_movConst (P := P) (σ := σ) (toNat_lt32 area) hc
  obtain ⟨t2, r2, c2, p2, sp2, lr2, m2, tr2, rd2, a2, k2⟩ :=
    run_movConst (P := P) (σ := σ) (d := 1) (w := area.toNat + areaSize cap) hfit c1
  obtain ⟨r3, c3, p3, k3⟩ := run_reg (P := P) (σ := σ) c2 rfl rfl
    (show exec P σ (.movImm 2 0) t2 = some { t2.setR 2 (UInt32.ofNat (0 : Fin 256).val) with
      pc := t2.pc + 4 } from rfl)
  generalize hu3 : ({ t2.setR 2 (UInt32.ofNat (0 : Fin 256).val) with pc := t2.pc + 4 } : State)
    = t3 at r3 c3 p3 k3
  obtain ⟨r4, c4, p4, k4⟩ := run_reg (P := P) (σ := σ) c3 rfl rfl
    (show exec P σ (.movImm 3 4) t3 = some { t3.setR 3 (UInt32.ofNat (4 : Fin 256).val) with
      pc := t3.pc + 4 } from rfl)
  generalize hu4 : ({ t3.setR 3 (UInt32.ofNat (4 : Fin 256).val) with pc := t3.pc + 4 } : State)
    = t4 at r4 c4 p4 k4
  have e3 : ∀ e : Fin 8, e ≠ 2 → t3.r e = t2.r e := fun e he => by
    rw [← hu3, State.r_withPc, State.r_setR_ne _ _ he]
  have e4 : ∀ e : Fin 8, e ≠ 3 → t4.r e = t3.r e := fun e he => by
    rw [← hu4, State.r_withPc, State.r_setR_ne _ _ he]
  obtain ⟨cl, cs⟩ := CodeAt.append.mp c4
  have hL : (UInt32.ofNat (area.toNat + areaSize cap)).toNat = area.toNat + areaSize cap := by
    rw [UInt32.toNat_ofNat']; omega
  have hsz : areaSize cap % 4 = 0 := by unfold areaSize; omega
  obtain ⟨t5, r5, p5, z5, k5, sp5, lr5, tr5, rd5⟩ := run_clearLoop (P := P) (σ := σ)
    (lo := area) (hi := UInt32.ofNat (area.toNat + areaSize cap)) cl rfl
    (by rw [e4 0 (by decide), e3 0 (by decide), k2 0 (by decide), a1, UInt32.ofNat_toNat])
    (by rw [e4 1 (by decide), e3 1 (by decide), a2])
    (by rw [e4 2 (by decide), ← hu3, State.r_withPc, State.r_setR_same]; rfl)
    (by rw [← hu4, State.r_withPc, State.r_setR_same]; rfl)
    (by rw [hL]; omega) (by rw [hL]; omega) hal (fun j hj => hram j (by rw [hL] at hj; omega))
  rw [hL, Nat.add_sub_cancel_left] at z5 k5
  have cs' : CodeAt code t5.pc (storeWords area.toNat 0 none (wordsOf (areaPrefixBytes m)) ++
      rest) := cs.at_eq (by rw [p5]; rfl)
  have hlen : 4 * (wordsOf (areaPrefixBytes m)).length = areaPrefix m := by
    rw [length_wordsOf, areaPrefixBytes_length]
    have := roundUp_dvd (4096 + dataEnd m) 8
    unfold areaPrefix
    omega
  obtain ⟨t6, r6, c6, p6, sp6, lr6, tr6, rd6, hm6, hk6⟩ := run_storeWords (P := P) (σ := σ) hal
    (wordsOf (areaPrefixBytes m)) 0 none t5 rest cs' (fun q hq => by cases hq) (by omega)
    (fun j hj => by rw [Nat.mul_zero, Nat.zero_add]; exact hram j (by omega))
    (fun j hj => by rw [Nat.mul_zero, Nat.zero_add]; exact z5 j (by omega))
  refine ⟨t6, r1.trans (r2.trans (r3.trans (r4.trans (r5.trans r6)))), c6, ?_, ?_, ?_, ?_, ?_,
    fun j hj => ?_⟩
  · rw [p6, p5, p4, p3, p2, p1]
    simp only [setupCode, List.length_append, List.length_cons, List.length_nil]
    rw [show (4 : UInt32) = UInt32.ofNat 4 from rfl, show (20 : UInt32) = UInt32.ofNat 20 from rfl,
      add_ofNat_add, add_ofNat_add, add_ofNat_add, add_ofNat_add, add_ofNat_add]
    exact add_ofNat_congr _ (by simp only [clearLoop, List.length_cons, List.length_nil]; omega)
  · rw [sp6, sp5, k4.sp, k3.sp, sp2, sp1]
  · rw [lr6, lr5, k4.lr, k3.lr, lr2, lr1]
  · rw [tr6, tr5, k4.trace, k3.trace, tr2, tr1]
  · rw [rd6, rd5, k4.reads, k3.reads, rd2, rd1]
  · by_cases hjp : j < areaPrefix m
    · obtain ⟨w, hw⟩ : ∃ w, (wordsOf (areaPrefixBytes m))[j / 4]? = some w :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have hb := wordsOf_byte _ j hw
      rw [areaPrefixBytes_getElem m j hjp, Option.some.injEq] at hb
      have := hm6 j (by omega) w hw
      rw [Nat.mul_zero, Nat.zero_add] at this
      rw [this, hb]
    · rw [hk6 _ fun j' hj' => by
          rw [Nat.mul_zero, Nat.zero_add]
          exact ofNat_add_ne (by omega) (by omega) (by omega),
        z5 j hj, areaByte_tail m j (by omega)]

/-! ## From reset -/

/-- An image whose layout `B.setup` gives the setup of the area at `area` for the store of `am`
with a memory of `cap` pages, whose bytes the kernel's check `hk` finds in the code map, run from
reset to the initialization's start: SP holds the table's initial SP, LR 0xFFFFFFFF, the trace is
empty, and the machine holds the store in which `am` starts in the area, below the stack's limit
`lim`.  The area lies at a multiple of 4 and its bytes are `Ram`. -/
theorem setup_boot {B : Boot} {am m : Module} {cap : Nat} {gts : List ValueType}
    {area lim : UInt32} {k : Nat} {s0 : List UInt64} {limit dev : UInt32} {n len : Nat}
    (hok : setupOk am cap = true) (hgt : globalTypesOf am = some gts) (hal : area % 4 = 0)
    (hram : ∀ j < areaSize cap, Ram P (area + UInt32.ofNat j))
    (hbelow : area.toNat + areaSize cap ≤ lim.toNat) (hent : 2 ≤ B.entries)
    (hw : B.init.all Instr.wide = true)
    (hk : bootFileOk (B.setup (setupCode area cap am))
      (bootProgram (B.setup (setupCode area cap am)) m k s0 limit dev) n len = true)
    (hf : FileAt code n len B.org) (hsp : B.sp.toNat % 4 = 0) (horg : B.org.toNat % 4 = 0)
    (b : State) (hb : Reset code B.org b) :
    ∃ t, Reach P σ code b t ∧ t.pc = after B.reset (setupCode area cap am).length ∧
      CodeAt code t.pc B.init ∧ t.sp = B.sp ∧ t.lr = 0xFFFFFFFF ∧ t.trace = [] ∧ t.reads = 0 ∧
      StoreRel P area lim cap gts (initStore am cap) t := by
  obtain ⟨hao, -, gts', hgt', hgl, hint⟩ := of_setupOk hok
  rw [hgt] at hgt'
  cases hgt'
  have hw' : (B.setup (setupCode area cap am)).init.all Instr.wide = true := by
    show (setupCode area cap am ++ B.init).all Instr.wide = true
    rw [List.all_append, setupCode_wide, hw]
    rfl
  obtain ⟨-, -, -, hci, hw0, hw1⟩ := boot_image (code := code)
    (B := B.setup (setupCode area cap am)) hent hw' hk hf
  have hw0' : codeWord code B.org = some B.sp := hw0
  have hw1' : codeWord code (B.org + 4) = some (B.reset ||| 1) := hw1
  obtain ⟨w0, e0, hbsp⟩ := hb.sp
  obtain ⟨w1, e1, -, hbpc⟩ := hb.pc
  rw [hw0', Option.some.injEq] at e0
  rw [hw1', Option.some.injEq] at e1
  subst e0 e1
  have hev : (B.reset).toNat % 2 = 0 := by
    rw [Boot.reset]
    exact even_after (by omega) _
  rw [or1_and _ hev] at hbpc
  rw [and_align hsp] at hbsp
  have hci' : CodeAt code b.pc (setupCode area cap am ++ B.init) := by
    rw [hbpc]
    exact hci
  have hlim := toNat_lt32 lim
  obtain ⟨t, r, c, p, sp, lr, tr, rd, harea⟩ := setup_run (P := P) (σ := σ) hok hal (by omega)
    hram hci'
  refine ⟨t, r, ?_, c, by rw [sp, hbsp], by rw [lr, hb.lr], by rw [tr, hb.trace],
    by rw [rd, hb.reads], storeRel_init hao hgt hgl hint harea hram hbelow⟩
  rw [p, hbpc, after_eq]

/-- The image of step `k` of `m`, whose program has an area, in a layout `B.setup` with the setup
of the generator's area for the store of `m`, whose bytes the kernel's check `hk` finds in the code
map, run from reset: the setup leaves the store in which `m` starts in the area, the
initialization keeps it and appends `t0 σ` to the trace with its `r` reads, and `main` reaches the
loop's head after `N` windows with their accesses appended, the windows reading `σ` from `σ r` on.
The step's call keeps the invariant `J`, which holds of the initial store with the heap `heap`.
The area's bytes are `Ram` below the stack's limit `lim`, the table lies at a multiple of 4, its
initial SP is a multiple of 4 above the outgoing area, and every state whose SP lies at the
outgoing area has the stack that `StackOk` states. -/
theorem setupBoot_run {G : Type} {m : Module} {k : Nat} {s0 : List UInt64} {lim dev : UInt32}
    {B : Boot} {n len : Nat} {words : G → List UInt64} (hlen : ∀ g, (words g).length = s0.length)
    {tick : G → UInt64 → G × UInt64} {J : Heap → Store Unit → Prop}
    (hcall : StepCall m k words tick J) (hm : m.imports = []) (hcov : reachCovered m k = true)
    (hok : setupOk m areaPages = true)
    (hram : ∀ j < areaSize areaPages, Ram P (areaHeader + UInt32.ofNat j))
    (hbelow : areaHeader.toNat + areaSize areaPages ≤ lim.toNat) (hdev : DevWindow P dev)
    {heap : Heap} (hat : heap.At (initStore m areaPages)) (hJ : J heap (initStore m areaPages))
    (hent : 2 ≤ B.entries) (hw : B.init.all Instr.wide = true)
    (hk : bootFileOk (B.setup (setupCode areaHeader areaPages m))
      (bootProgram (B.setup (setupCode areaHeader areaPages m)) m k s0 lim dev) n len = true)
    (hf : FileAt code n len B.org) (horg : B.org.toNat % 4 = 0)
    {t0 : (Nat → UInt32) → List Access} {r : Nat} (hinit : InitRuns P σ code B.init t0 r)
    (hsp : B.sp.toNat % 4 = 0) (hfit : 8 * (s0.length + 1) ≤ B.sp.toNat)
    (hstk : ∀ s : State, s.sp = B.sp - UInt32.ofNat (8 * (s0.length + 1)) →
      StackOk P lim (s0.length + 1) (stackBound m k) s)
    (g0 : G) (hs0 : words g0 = s0) (b : State) (hb : Reset code B.org b) (N : Nat) :
    ∃ t, Reach P σ code b t ∧
      t.pc = after (B.setup (setupCode areaHeader areaPages m)).base (mainStart s0) ∧
      t.trace = t0 σ ++ windows (reqTrace (devBus dev) tick g0 (fun j => σ (j + r))) N := by
  obtain ⟨-, -, gts, hgt, -, -⟩ := of_setupOk hok
  have hw' : (B.setup (setupCode areaHeader areaPages m)).init.all Instr.wide = true := by
    show (setupCode areaHeader areaPages m ++ B.init).all Instr.wide = true
    rw [List.all_append, setupCode_wide, hw]
    rfl
  obtain ⟨prog, hprog, hcp, -, -, -⟩ := boot_image (code := code)
    (B := B.setup (setupCode areaHeader areaPages m)) hent hw' hk hf
  obtain ⟨t, rt, pt, ct, spt, -, trt, rdt, hsr⟩ := setup_boot (P := P) (σ := σ) hok hgt
    (by decide) hram hbelow hent hw hk hf hsp horg b hb
  obtain ⟨t1, r1, p1, sp1, tr1, rd1, mm1⟩ := hinit t ct
  have hp1 : t1.pc = (B.setup (setupCode areaHeader areaPages m)).base := by
    rw [p1, pt, Boot.base, Boot.reset]
    show _ = after B.org (B.entries + 1 + (setupCode areaHeader areaPages m ++ B.init).length)
    rw [List.length_append]
    addr_after
  have hsp1 : t1.sp = B.sp := sp1.trans spt
  obtain ⟨t2, r2, p2, tr2⟩ := main_run (P := P) (σ := σ) (code := code)
    (fun g _ _ _ h => by rw [h.1]; exact hlen g) hcall.rep hm hprog hcp
    (by rw [Boot.base]; exact even_after (a := B.org) (by omega) _) hcov hdev hat
    (by show areaPages ≤ 65535; decide) g0 ⟨hs0.symm, hJ⟩ t1 hp1
    (by rw [hsp1]; exact hsp) (by rw [hsp1]; exact hfit) (hstk _ (by rw [← hsp1]))
    (fun _ => ⟨gts, hgt, hsr.congr (KeepsBelow.of_mem mm1)⟩) N
  refine ⟨t2, rt.trans (r1.trans r2), p2, ?_⟩
  rw [tr2, tr1, rd1, trt, rdt, List.nil_append, Nat.zero_add]
  rfl

end LeanExe.M7
