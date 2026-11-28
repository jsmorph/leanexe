module

public import Verified.ShimA64.Handles
public import Verified.ShimA64.OpenHow
public import Verified.ShimA64.Utf8
public import LeanExe.A64.Proof.WasiOpen
public import LeanExe.A64.Proof.WasiUtf8

@[expose] public section

/-!
The stub of `path_open` against the shim's host environment: `openStub_sim` proves that the stub
of `LeanExe/A64/WasiFiles.lean` meets `Machine.StubSim` for `openInvoke` on `shimMachine`.  From
the stub's entry, `run_openHead` reaches the trap stub when the path or the result's four bytes
lie outside the memory, and `run_openBody` makes the checks of `openCheck` in its order.  A check
that fails returns its errno, and when every check passes the run reaches the first `openat2` with
the path and its zero in the scratch's path buffer and the bytes of `openHowBytes` in its
`open_how` record.  The path's bytes in the process's memory are the store's (`readList_bytes`),
`utf8Scan_iff` turns the stub's decision of UTF-8 into the condition that `openCheck` tests, and
`held_byte` turns the test of the directory's byte into membership in `openNumbers`.

`run_openLoop` follows the `openat2` calls in the process as `openLoop` makes them, by induction on
the calls that remain.  Each call has the event `openEvent` and keeps the memory
(`sysCall_openEvent`, from `step_openat2`), and a result of `-EAGAIN` after fewer than four calls
repeats the call.  `run_openResult` handles the last result: a descriptor below 1,024 sets its
byte in the scratch and is stored at the result's pointer, a negated error number returns its
errno, and any other result reaches the trap stub, as `openReply` and `placeReply` state.
`ScratchHolds` holds after the path and the record, which lie above the descriptors' bytes
(`ScratchHolds.congrLow`), after each `-EAGAIN` (`ScratchHolds.again`), and after the last call,
with the descriptor's byte set (`ScratchHolds.opened`) or kept.
-/

namespace Verified.ShimA64

open Wasm LeanExe LeanExe.A64 LeanExe.Wasi Verified.Wasi Verified.Shim

/-! ## The checks and the reply -/

theorem openCheck_lt (opened : List UInt64) (dir oflags : UInt64) (path : Bytes)
    (fdflags : UInt64) : (openCheck opened dir oflags path fdflags).toNat < 2 ^ 32 := by
  unfold openCheck
  repeat' split
  all_goals decide

/-- A request that passes the checks has a path without a zero byte and of fewer than 4,096
bytes. -/
theorem openCheck_zero {opened : List UInt64} {dir oflags fdflags : UInt64} {path : Bytes}
    (h : openCheck opened dir oflags path fdflags = 0) :
    (0 : UInt8) ∉ path.data.data.toList ∧ path.data.size < 4096 := by
  unfold openCheck at h
  repeat' split at h
  all_goals first
    | exact absurd h (by decide)
    | exact ⟨by assumption, by omega⟩

theorem openReply_small {r : UInt64} (h : r ≤ 1023) :
    openReply r = .returned 0 [leBytes 4 r.toNat] := by
  have hr : r.toNat < descriptorLimit := by
    rw [UInt64.le_iff_toNat_le] at h
    unfold descriptorLimit
    simp only [UInt64.reduceToNat] at h
    omega
  unfold openReply
  rw [ite_eq_left hr]

theorem openReply_error {r : UInt64} (h1 : 1023 < r) (h2 : 0 - r ≤ 4095) :
    openReply r = .returned (errnoOf (0 - r)) [zeros 4] := by
  have hr : ¬ r.toNat < descriptorLimit := by
    rw [UInt64.lt_iff_toNat_lt] at h1
    unfold descriptorLimit
    simp only [UInt64.reduceToNat] at h1
    omega
  unfold openReply
  rw [ite_eq_right hr, ite_eq_left ((isError_iff (c := 1023) (by decide) h1).mpr h2)]

theorem openReply_trap {r : UInt64} (h1 : 1023 < r) (h2 : 4095 < 0 - r) :
    openReply r = .trapped shimTrap [zeros 4] := by
  have hr : ¬ r.toNat < descriptorLimit := by
    rw [UInt64.lt_iff_toNat_lt] at h1
    unfold descriptorLimit
    simp only [UInt64.reduceToNat] at h1
    omega
  unfold openReply
  rw [ite_eq_right hr, ite_eq_right fun h =>
    absurd ((isError_iff (c := 1023) (by decide) h1).mp h) (UInt64.not_le.mpr h2)]

theorem placeReply_word (mem : Mem) (result : UInt32) (b : Bytes) :
    placeReply mem (fun outputs => [(result, outputs.headD Bytes.empty)]) (.returned 0 [b]) =
      mem.writeBytes result.toNat b.data.data.toList := by
  simp [placeReply, placeAll]

theorem placeReply_errno (mem : Mem) (place : List Bytes → List (UInt32 × Bytes)) {e : UInt64}
    (outputs : List Bytes) (h : e ≠ 0) : placeReply mem place (.returned e outputs) = mem := by
  simp only [placeReply]
  exact ite_eq_right h

/-- The memory's size, 8 plus the area's first word, lies below a word exactly when the store's
memory holds fewer bytes than the word's value. -/
theorem StoreRel.size_lt {P : Platform} {cap : Nat} {gts : List ValueType} {α : Type}
    {st : Store α} {s : State} (h : StoreRel P cap gts st s) (x : UInt64) :
    load64 s.mem (s.x 17) + 8 < x ↔ st.mem.pages * 65536 < x.toNat := by
  have hpg := h.pages
  have hcap := h.cap_lt
  have hle : st.mem.pages * 65536 ≤ 65535 * 65536 := Nat.mul_le_mul_right _ (by omega)
  rw [UInt64.lt_iff_toNat_lt, h.size, UInt64.toNat_add, UInt64.toNat_ofNat']
  simp only [UInt64.reduceToNat, Nat.reducePow]
  constructor <;> intro hx <;> omega

theorem typed_open {args : List Value} (hlen : args.length = 9)
    (hty : Typed [.i32, .i32, .i32, .i32, .i32, .i64, .i64, .i32, .i32] args) :
    ∃ (a0 a1 a2 a3 a4 : UInt32) (a5 a6 : UInt64) (a7 a8 : UInt32),
      args = [.i32 a0, .i32 a1, .i32 a2, .i32 a3, .i32 a4, .i64 a5, .i64 a6, .i32 a7,
        .i32 a8] := by
  match args, hlen, hty with
  | [v0, v1, v2, v3, v4, v5, v6, v7, v8], _, ⟨t0, t1, t2, t3, t4, t5, t6, t7, t8, _⟩ =>
    obtain ⟨a0, rfl⟩ : ∃ a, v0 = .i32 a := by
      cases v0 <;> first | exact ⟨_, rfl⟩ | exact t0.elim
    obtain ⟨a1, rfl⟩ : ∃ a, v1 = .i32 a := by
      cases v1 <;> first | exact ⟨_, rfl⟩ | exact t1.elim
    obtain ⟨a2, rfl⟩ : ∃ a, v2 = .i32 a := by
      cases v2 <;> first | exact ⟨_, rfl⟩ | exact t2.elim
    obtain ⟨a3, rfl⟩ : ∃ a, v3 = .i32 a := by
      cases v3 <;> first | exact ⟨_, rfl⟩ | exact t3.elim
    obtain ⟨a4, rfl⟩ : ∃ a, v4 = .i32 a := by
      cases v4 <;> first | exact ⟨_, rfl⟩ | exact t4.elim
    obtain ⟨a5, rfl⟩ : ∃ a, v5 = .i64 a := by
      cases v5 <;> first | exact ⟨_, rfl⟩ | exact t5.elim
    obtain ⟨a6, rfl⟩ : ∃ a, v6 = .i64 a := by
      cases v6 <;> first | exact ⟨_, rfl⟩ | exact t6.elim
    obtain ⟨a7, rfl⟩ : ∃ a, v7 = .i32 a := by
      cases v7 <;> first | exact ⟨_, rfl⟩ | exact t7.elim
    obtain ⟨a8, rfl⟩ : ∃ a, v8 = .i32 a := by
      cases v8 <;> first | exact ⟨_, rfl⟩ | exact t8.elim
    exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, rfl⟩

theorem sysFn_open (F : OpenFlags) (L : ShimLayout) (I : Launch) (replies : Linux.Replies)
    (st : Store (Observed LinuxWorld)) (args : List Value) :
    (sysFn F L I replies Call.pathOpen).invoke st args = openInvoke F L I replies st args := by
  simp (config := { decide := true }) only [sysFn, sysInvoke, ↓reduceIte]

/-! ## The scratch -/

/-- Bytes written in the scratch keep every byte outside it. -/
theorem ScratchOnly.writeList {G : Scratch} (m : UInt64 → UInt8) {j : Nat} (bs : List UInt8)
    (hj : j + bs.length ≤ scratchSize) (hG : G.base.toNat + scratchSize < 2 ^ 64) :
    ScratchOnly G m (LeanExe.A64.writeList m (G.base + UInt64.ofNat j) bs) := by
  intro a ha
  apply writeList_other
  rw [UInt64.toNat_sub, UInt64.toNat_add, UInt64.toNat_ofNat']
  have := a.toNat_lt
  unfold scratchSize at hj hG ha
  simp only [Nat.reducePow] at *
  omega

/-- Bytes written in the scratch from offset 1,040 on keep the scratch's first 1,040 bytes, which
`ScratchHolds` reads, and every byte from `2^32` up. -/
theorem writeList_scratchHigh {G : Scratch} (m : UInt64 → UInt8) {i : Nat} (bs : List UInt8)
    (hi : 1040 ≤ i) (hb : i + bs.length ≤ scratchSize)
    (hlow : G.base.toNat + scratchSize ≤ 2 ^ 32) :
    (∀ j < 1040, LeanExe.A64.writeList m (G.base + UInt64.ofNat i) bs (G.base + UInt64.ofNat j) =
        m (G.base + UInt64.ofNat j)) ∧
      ∀ a : UInt64, 2 ^ 32 ≤ a.toNat →
        LeanExe.A64.writeList m (G.base + UInt64.ofNat i) bs a = m a := by
  unfold scratchSize at hb hlow
  have ei : (G.base + UInt64.ofNat i).toNat = G.base.toNat + i := by
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.reducePow]
    omega
  refine ⟨fun j hj => writeList_other m bs _ _ ?_,
    fun a ha => writeList_below (lim := a) (by omega) (Nat.le_refl _)⟩
  have ej : (G.base + UInt64.ofNat j).toNat = G.base.toNat + j := by
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.reducePow]
    omega
  rw [UInt64.toNat_sub, ei, ej]
  simp only [Nat.reducePow]
  omega

/-- A memory that keeps the scratch's first 1,040 bytes and every byte from `2^32` up keeps the
scratch's relation. -/
theorem ScratchHolds.congrLow {G : Scratch} {I : Launch} {sp₀ top : UInt64}
    {events : List Linux.Event} {m m' : UInt64 → UInt8} (h : ScratchHolds G I sp₀ top events m)
    (hlow : ∀ j < 1040, m' (G.base + UInt64.ofNat j) = m (G.base + UInt64.ofNat j))
    (hhigh : ∀ a : UInt64, 2 ^ 32 ≤ a.toNat → m' a = m a) :
    ScratchHolds G I sp₀ top events m' := by
  refine ⟨?_, h.stack.congr hhigh, ?_, fun d hd => ?_⟩
  · rw [← h.saved]
    exact load64_congr fun k hk => hlow k (by omega)
  · rw [← h.preopen]
    exact hlow 8 (by decide)
  · rw [← h.held d hd]
    unfold descriptorLimit at hd
    exact hlow (16 + d) (by omega)

/-- Calls of `openat2` that return `-EAGAIN` keep the scratch's relation. -/
theorem ScratchHolds.again {G : Scratch} {I : Launch} {sp₀ top : UInt64} {mem : UInt64 → UInt8}
    (L : ShimLayout) (dir : UInt64) (path how : List UInt8) :
    ∀ (pre : List Linux.Reply) (events : List Linux.Event), (∀ r ∈ pre, r.ret = 0 - 11) →
      ScratchHolds G I sp₀ top events mem →
      ScratchHolds G I sp₀ top (events ++ pre.map (openEvent L dir path how)) mem
  | [], events, _, h => by simpa using h
  | r :: pre, events, hpre, h => by
    have h1 : ScratchHolds G I sp₀ top (events ++ [openEvent L dir path how r]) mem :=
      h.quiet (fun hc => by
        have hlt := hc.2
        rw [show (openEvent L dir path how r).ret = r.ret from rfl,
          hpre r List.mem_cons_self] at hlt
        exact absurd hlt (by decide))
        (show Linux.openat2Call ≠ Linux.closeCall by decide)
    have := ScratchHolds.again L dir path how pre _
      (fun r' hr' => hpre r' (List.mem_cons_of_mem _ hr')) h1
    simpa [List.append_assoc] using this

/-- An event that opens a descriptor below `descriptorLimit` keeps the scratch's relation when the
memory sets the descriptor's byte to 1 and keeps the scratch's other first 1,040 bytes and every
byte from `2^32` up. -/
theorem ScratchHolds.opened {G : Scratch} {I : Launch} {sp₀ top : UInt64}
    {events : List Linux.Event} {m m' : UInt64 → UInt8} {e : Linux.Event}
    (h : ScratchHolds G I sp₀ top events m) (hopen : e.call.opens = true)
    (hsmall : e.ret.toNat < descriptorLimit) (hset : m' (G.held e.ret.toNat) = 1)
    (hlow : ∀ j < 1040, j ≠ 16 + e.ret.toNat →
      m' (G.base + UInt64.ofNat j) = m (G.base + UInt64.ofNat j))
    (hhigh : ∀ a : UInt64, 2 ^ 32 ≤ a.toNat → m' a = m a) :
    ScratchHolds G I sp₀ top (events ++ [e]) m' := by
  obtain ⟨hn, hp⟩ := openNumbers_append_open I events hopen hsmall
  unfold descriptorLimit at hsmall
  refine ⟨?_, h.stack.congr hhigh, ?_, fun d hd => ?_⟩
  · rw [← h.saved]
    exact load64_congr fun k hk => hlow k (by omega) (by omega)
  · rw [hp, ← h.preopen]
    exact hlow 8 (by decide) (by omega)
  · unfold descriptorLimit at hd
    by_cases hde : d = e.ret.toNat
    · subst hde
      rw [hset, UInt64.ofNat_toNat]
      simp [hn]
    · have hne : UInt64.ofNat d ≠ e.ret := fun same => hde (by
        rw [← same, UInt64.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le hd (by decide))])
      have hb := h.held d (by unfold descriptorLimit; omega)
      show m' (G.base + UInt64.ofNat (16 + d)) = _
      rw [hlow (16 + d) (by omega) (by omega),
        show G.base + UInt64.ofNat (16 + d) = G.held d from rfl, hb]
      simp only [hn, hne, false_or]

/-! ## Reads after writes -/

theorem readList_writeList (m : UInt64 → UInt8) (a : UInt64) (bs : List UInt8) {n : Nat}
    (hn : n = bs.length) (h : bs.length < 2 ^ 64) :
    readList (LeanExe.A64.writeList m a bs) a n = bs := by
  subst hn
  exact readList_eq _ a bs fun j hj => by
    rw [writeList_at m bs a j hj h]

theorem readList_writeList_apart (m : UInt64 → UInt8) (a b : UInt64) (bs : List UInt8) (n : Nat)
    (h : ∀ j < n, ¬ (b + UInt64.ofNat j - a).toNat < bs.length) :
    readList (LeanExe.A64.writeList m a bs) b n = readList m b n :=
  readList_congr n b fun j hj => writeList_other m bs a _ (h j hj)

/-! ## The checks in the program's model -/

section Runs

variable (P : Platform) (code : UInt64 → Option UInt32)

/-- The stub of `path_open` from the check of UTF-8 at `after a 17`, with the scratch's address in
X20, the path's guest address and length in X2 and X3, and the directory, the `oflags`, and the
`fdflags` in X0, X4, and X7.  The memory holds the path's bytes `path`, and the directory lies in
`opened` exactly when its byte in the scratch is set.  When `openCheck` fails, the run returns to
X30 with its errno and keeps the memory.  Otherwise it reaches the first `openat2` call's
arguments at `after a 192` with X22 at the directory, X23 at 0, the path and its zero in the
scratch's path buffer, and the record of `openHowBytes` in the scratch's `open_how`.  SP, the
UART's state, X17, and X18 keep their values. -/
theorem run_openBody {a svc tr en : UInt64} {sc : Nat} {is : List Instr}
    (hg : openStub a svc tr en sc = .ok is) (hcode : CodeAt code a is) {s : State}
    (hpc : s.pc = after a 17) {opened : List UInt64} {path : Bytes}
    (hpath : readList s.mem (s.x 17 + UInt64.ofNat 4096 + s.x 2) (s.x 3).toNat =
      path.data.data.toList)
    (hheld : (s.x 0 ≤ 1023 ∧ s.mem (s.x 20 + s.x 0 + 16) ≠ 0) ↔ s.x 0 ∈ opened)
    (hsrc : ∀ k < (s.x 3).toNat,
      P.normal (s.x 17 + UInt64.ofNat 4096 + s.x 2 + UInt64.ofNat k) = true)
    (hbyte : s.x 0 ≤ 1023 → P.normal (s.x 20 + s.x 0 + 16) = true)
    (hscr : ∀ k < 4120, P.normal (s.x 20 + UInt64.ofNat (1056 + k)) = true)
    (hsep : (s.x 17 + UInt64.ofNat 4096 + s.x 2).toNat + (s.x 3).toNat ≤ (s.x 20).toNat)
    (hwrap : (s.x 20).toNat + 5176 ≤ 2 ^ 64) (hU : P.normal P.uart = false) :
    ∃ t, Reach P code s t ∧ t.sp = s.sp ∧ t.io = s.io ∧ t.x 17 = s.x 17 ∧ t.x 18 = s.x 18 ∧
      if openCheck opened (s.x 0) (s.x 4) path (s.x 7) = 0 then
        t.pc = after a 192 ∧ t.x 20 = s.x 20 ∧ t.x 19 = s.x 19 ∧ t.x 21 = s.x 21 ∧
          t.x 22 = s.x 0 ∧ t.x 23 = 0 ∧
          t.mem = LeanExe.A64.writeList (LeanExe.A64.writeList s.mem
            (s.x 20 + UInt64.ofNat 1080) (path.data.data.toList ++ [0]))
            (s.x 20 + UInt64.ofNat 1056)
            (openHowBytes arm64Flags (s.x 1) (s.x 4) (s.x 5) (s.x 7))
      else t.pc = s.x 30 ∧ t.x 0 = openCheck opened (s.x 0) (s.x 4) path (s.x 7) ∧
        t.mem = s.mem := by
  obtain ⟨_, _, _, held, _, _, _, _, _, _, _, _, _, -, -, hu, hh, hz, hc, hw, hl, -, -, -, -, -,
    -, -, -, -, -, -, cU, cH, -, cZ, -, cC, cW, cL, -, e25, e8, -, e28, -⟩ :=
    openStub_code code hg hcode
  obtain ⟨e1, e4, he1, he4, rfl⟩ := heldTest_ok hh
  -- UTF-8
  obtain ⟨u1, r1, p1, k1, sp1, m1, io1⟩ := run_utf8Check P code hu cU hpc hsrc
  rw [hpath] at p1
  by_cases hv : path.data.IsValidUTF8
  swap
  · have hs : utf8Scan path.data.data.toList = false := by
      cases h : utf8Scan path.data.data.toList with
      | false => rfl
      | true => exact absurd ((utf8Scan_iff path.data).mp h) hv
    rw [hs, ite_eq_right (show ¬ (false = true) by decide)] at p1
    obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := run_movzRet P code e25 p1
    have hcheck : openCheck opened (s.x 0) (s.x 4) path (s.x 7) = 25 := by
      unfold openCheck
      rw [ite_eq_left hv]
    refine ⟨u2, r1.trans r2, by rw [sp2, sp1], by rw [io2, io1],
      by simp (disch := decide) only [k2, k1], by simp (disch := decide) only [k2, k1], ?_⟩
    rw [hcheck, ite_eq_right (show (25 : UInt64) ≠ 0 by decide)]
    exact ⟨by rw [p2]; simp (disch := decide) only [k1], x2.trans rfl, by rw [m2, m1]⟩
  have hs : utf8Scan path.data.data.toList = true := (utf8Scan_iff path.data).mpr hv
  rw [hs, ite_eq_left rfl, after_after] at p1
  have hv' : ¬ ¬ path.data.IsValidUTF8 := fun h => h hv
  -- the directory
  obtain ⟨u2, r2, p2, k2, sp2, m2, io2⟩ := run_heldTest P code (r := 0) (by decide) cH he1 he4 p1
    (fun h => by simp (disch := decide) only [k1] at h ⊢; exact hbyte h)
  simp (disch := decide) only [k1, m1] at p2
  by_cases hd : s.x 0 ∈ opened
  swap
  · rw [ite_eq_right fun h => hd (hheld.mp h)] at p2
    obtain ⟨u3, r3, p3, x3, k3, sp3, m3, io3⟩ := run_movzRet P code e8 p2
    have hcheck : openCheck opened (s.x 0) (s.x 4) path (s.x 7) = 8 := by
      unfold openCheck
      rw [ite_eq_right hv', ite_eq_left hd]
    refine ⟨u3, r1.trans (r2.trans r3), by rw [sp3, sp2, sp1], by rw [io3, io2, io1],
      by simp (disch := decide) only [k3, k2, k1], by simp (disch := decide) only [k3, k2, k1],
      ?_⟩
    rw [hcheck, ite_eq_right (show (8 : UInt64) ≠ 0 by decide)]
    exact ⟨by rw [p3]; simp (disch := decide) only [k2, k1], x3.trans rfl,
      by rw [m3, m2, m1]⟩
  rw [ite_eq_left (hheld.mpr hd), after_after] at p2
  have hd' : ¬ s.x 0 ∉ opened := fun h => h hd
  -- the flags
  obtain ⟨u3, r3, k3, sp3, m3, io3, hc3⟩ := run_openFlags P code hg hcode p2
  simp (disch := decide) only [k2, k1] at hc3
  by_cases hf : s.x 7 &&& 0x1A ≠ 0
  · rw [ite_eq_left hf] at hc3
    obtain ⟨p3, x3⟩ := hc3
    have hcheck : openCheck opened (s.x 0) (s.x 4) path (s.x 7) = 58 := by
      unfold openCheck
      rw [ite_eq_right hv', ite_eq_right hd', ite_eq_left hf]
    refine ⟨u3, r1.trans (r2.trans r3), by rw [sp3, sp2, sp1], by rw [io3, io2, io1],
      by simp (disch := decide) only [k3, k2, k1], by simp (disch := decide) only [k3, k2, k1],
      ?_⟩
    rw [hcheck, ite_eq_right (show (58 : UInt64) ≠ 0 by decide)]
    exact ⟨p3, x3, by rw [m3, m2, m1]⟩
  rw [ite_eq_right hf] at hc3
  by_cases ho : s.x 4 &&& 2 ≠ 0 ∧ s.x 4 &&& 0xD ≠ 0
  · rw [ite_eq_left ho] at hc3
    obtain ⟨p3, x3⟩ := hc3
    have hcheck : openCheck opened (s.x 0) (s.x 4) path (s.x 7) = 28 := by
      unfold openCheck
      rw [ite_eq_right hv', ite_eq_right hd', ite_eq_right hf, ite_eq_left ho]
    refine ⟨u3, r1.trans (r2.trans r3), by rw [sp3, sp2, sp1], by rw [io3, io2, io1],
      by simp (disch := decide) only [k3, k2, k1], by simp (disch := decide) only [k3, k2, k1],
      ?_⟩
    rw [hcheck, ite_eq_right (show (28 : UInt64) ≠ 0 by decide)]
    exact ⟨p3, x3, by rw [m3, m2, m1]⟩
  rw [ite_eq_right ho] at hc3
  obtain ⟨p3, x03⟩ := hc3
  -- the zero bytes
  obtain ⟨u4, r4, p4, k4, sp4, m4, io4⟩ := run_zeroScan P code hz cZ p3
    (fun k hk => by simp (disch := decide) only [k3, k2, k1] at hk ⊢; exact hsrc k hk)
  simp (disch := decide) only [k3, k2, k1, m3, m2, m1, hpath, after_after] at p4
  by_cases hz0 : (0 : UInt8) ∈ path.data.data.toList
  · rw [ite_eq_left hz0] at p4
    obtain ⟨u5, r5, p5, x5, k5, sp5, m5, io5⟩ := run_movzRet P code e28 p4
    have hcheck : openCheck opened (s.x 0) (s.x 4) path (s.x 7) = 28 := by
      unfold openCheck
      rw [ite_eq_right hv', ite_eq_right hd', ite_eq_right hf, ite_eq_right ho, ite_eq_left hz0]
    refine ⟨u5, r1.trans (r2.trans (r3.trans (r4.trans r5))), by rw [sp5, sp4, sp3, sp2, sp1],
      by rw [io5, io4, io3, io2, io1], by simp (disch := decide) only [k5, k4, k3, k2, k1],
      by simp (disch := decide) only [k5, k4, k3, k2, k1], ?_⟩
    rw [hcheck, ite_eq_right (show (28 : UInt64) ≠ 0 by decide)]
    exact ⟨by rw [p5]; simp (disch := decide) only [k4, k3, k2, k1], x5.trans rfl,
      by rw [m5, m4, m3, m2, m1]⟩
  rw [ite_eq_right hz0] at p4
  -- the length
  obtain ⟨u5, r5, k5, sp5, m5, io5, hc5⟩ := run_openLength P code hg hcode p4
  simp (disch := decide) only [k4, k3, k2, k1] at hc5
  have hsize : path.data.size = (s.x 3).toNat := by
    have := congrArg List.length hpath
    rw [readList_length] at this
    rw [this]
    simp only [Array.length_toList, ByteArray.size]
  have hlen : 4095 < s.x 3 ↔ 4096 ≤ path.data.size := by
    rw [hsize, UInt64.lt_iff_toNat_lt]
    simp only [UInt64.reduceToNat]
    constructor <;> intro h <;> omega
  by_cases hlong : 4095 < s.x 3
  · rw [ite_eq_left hlong] at hc5
    obtain ⟨p5, x5⟩ := hc5
    have hcheck : openCheck opened (s.x 0) (s.x 4) path (s.x 7) = 37 := by
      unfold openCheck
      rw [ite_eq_right hv', ite_eq_right hd', ite_eq_right hf, ite_eq_right ho,
        ite_eq_right hz0, ite_eq_left (hlen.mp hlong)]
    refine ⟨u5, r1.trans (r2.trans (r3.trans (r4.trans r5))), by rw [sp5, sp4, sp3, sp2, sp1],
      by rw [io5, io4, io3, io2, io1], by simp (disch := decide) only [k5, k4, k3, k2, k1],
      by simp (disch := decide) only [k5, k4, k3, k2, k1], ?_⟩
    rw [hcheck, ite_eq_right (show (37 : UInt64) ≠ 0 by decide)]
    exact ⟨p5, x5, by rw [m5, m4, m3, m2, m1]⟩
  rw [ite_eq_right hlong] at hc5
  obtain ⟨p5, x05⟩ := hc5
  have hc0 : openCheck opened (s.x 0) (s.x 4) path (s.x 7) = 0 := by
    unfold openCheck
    rw [ite_eq_right hv', ite_eq_right hd', ite_eq_right hf, ite_eq_right ho, ite_eq_right hz0,
      ite_eq_right fun h => hlong (hlen.mpr h)]
  have h3 : (s.x 3).toNat < 4096 := by
    have := UInt64.not_lt.mp hlong
    rw [UInt64.le_iff_toNat_le] at this
    simp only [UInt64.reduceToNat] at this
    omega
  -- the copy of the path
  have e2 : u5.x 2 = s.x 2 := by simp (disch := decide) only [k5, k4, k3, k2, k1]
  have e3 : u5.x 3 = s.x 3 := by simp (disch := decide) only [k5, k4, k3, k2, k1]
  have e20 : u5.x 20 = s.x 20 := by simp (disch := decide) only [k5, k4, k3, k2, k1]
  have e17 : u5.x 17 = s.x 17 := by simp (disch := decide) only [k5, k4, k3, k2, k1]
  have e1080 : (s.x 20 + UInt64.ofNat 1080).toNat = (s.x 20).toNat + 1080 := by
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.reducePow]
    omega
  obtain ⟨u6, r6, p6, k6, sp6, io6, m6⟩ := run_pathCopy P code hc cC p5
    (by rw [e3]; exact h3)
    (fun k hk => by rw [e17, e2]; rw [e3] at hk; exact hsrc k hk)
    (fun k hk => by
      rw [e20]
      rw [e3] at hk
      have := hscr (24 + k) (by omega)
      rwa [show 1056 + (24 + k) = 1080 + k by omega] at this)
    hU (by rw [e17, e2, e3, e20, e1080]; omega) (by rw [e20, e1080]; omega)
  -- the record
  obtain ⟨u7, r7, p7, k7, sp7, io7, m7⟩ := run_openHow P code hw cW (by rw [p6, after_after])
    (fun k hk => by
      rw [k6 20 (by decide) (by decide) (by decide) (by decide), e20]
      exact hscr k (by omega))
  -- the first call's setup
  obtain ⟨u8, r8, p8, x22_8, x23_8, k8, sp8, m8, io8⟩ := run_openStart P code hl cL
    (by rw [p7, after_after])
  refine ⟨u8, r1.trans (r2.trans (r3.trans (r4.trans (r5.trans (r6.trans (r7.trans r8)))))),
    by rw [sp8, sp7, sp6, sp5, sp4, sp3, sp2, sp1], by rw [io8, io7, io6, io5, io4, io3, io2, io1],
    by simp (disch := decide) only [k8, k7, k6, k5, k4, k3, k2, k1],
    by simp (disch := decide) only [k8, k7, k6, k5, k4, k3, k2, k1], ?_⟩
  rw [ite_eq_left hc0]
  refine ⟨by rw [p8, after_after], by simp (disch := decide) only [k8, k7, k6, k5, k4, k3, k2, k1],
    by simp (disch := decide) only [k8, k7, k6, k5, k4, k3, k2, k1],
    by simp (disch := decide) only [k8, k7, k6, k5, k4, k3, k2, k1], ?_, x23_8, ?_⟩
  · rw [x22_8]
    simp (disch := decide) only [k7, k6, x05, x03]
  · rw [m8, m7, m6]
    simp (disch := decide) only [k6, k5, k4, k3, k2, k1, m5, m4, m3, m2, m1, hpath]

end Runs

/-! ## The calls of `openat2` -/

theorem table_openat2 :
    Linux.table.find? (fun c => c.arm64 == 437) = some Linux.openat2Call := rfl

/-- `openat2` of the path buffer and the `open_how` record of the layout `L`, which hold the path
`path` with its zero and the record `how`, gives `openEvent` and keeps the memory. -/
theorem sysCall_openEvent {R : Linux.Replies} {P : Platform} {p : Proc} (L : ShimLayout)
    (path how : List UInt8) (h1 : p.core.x 1 = L.path) (h2 : p.core.x 2 = L.openHow)
    (h3 : p.core.x 3 = 24) (short : path.length < 4096) (nonzero : 0 ∉ path)
    (named : readList p.core.mem L.path (path.length + 1) = path ++ [0])
    (record : readList p.core.mem L.openHow 24 = how)
    (mappedPath : P.mapped L.path (path.length + 1) = true)
    (mappedHow : P.mapped L.openHow 24 = true) :
    sysCall R P Linux.openat2Call p = some (p.ret (R p.trace.length).ret p.core.mem
      (.sys (openEvent L (p.core.x 0) path how (R p.trace.length)))) := by
  unfold sysCall
  rw [argWords_four (show Linux.openat2Call.words = 4 from rfl), h1, h2, h3,
    step_openat2 (a64Memory P) p.core.mem L (p.core.x 0) path how _ short nonzero
      (by rw [readBytes_a64]; exact named) (by rw [readBytes_a64]; exact record) mappedPath
      mappedHow]
  rfl

theorem openLoop_again {L : ShimLayout} {rs : Linux.Replies} {dir : UInt64}
    {path how : List UInt8} {c k : Nat} (h : (rs k).ret = 0 - 11 ∧ c < 3) :
    openLoop L rs dir path how c k =
      (openEvent L dir path how (rs k) :: (openLoop L rs dir path how (c + 1) (k + 1)).1,
        (openLoop L rs dir path how (c + 1) (k + 1)).2) := by
  rw [openLoop.eq_1 L rs dir path how c k, dite_eq_left h]

theorem openLoop_stop {L : ShimLayout} {rs : Linux.Replies} {dir : UInt64}
    {path how : List UInt8} {c k : Nat} (h : ¬((rs k).ret = 0 - 11 ∧ c < 3)) :
    openLoop L rs dir path how c k =
      ([openEvent L dir path how (rs k)], openReply (rs k).ret) := by
  rw [openLoop.eq_1 L rs dir path how c k, dite_eq_right h]

/-- One `openat2` call, from the call's arguments at `after a 2` of `openCalls` at `a` to the test
of its result at `after a 8`, with the path buffer and the `open_how` record of the layout `L`
1,080 and 1,056 bytes above X20.  The call leaves the reply's result in X0, appends `openEvent` of
the directory in X22 to the trace, and keeps the memory. -/
theorem run_openCall {R : Linux.Replies} {P : Platform} {code : UInt64 → Option UInt32}
    (hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55) {a svc : UInt64} {is : List Instr}
    (hg : openCalls a svc = .ok is) (hcode : CodeAt code a is)
    (hsvc : OpsAt code svc [.svc, .ins (.ret 30)]) (L : ShimLayout) (path how : List UInt8)
    (short : path.length < 4096) (nonzero : 0 ∉ path)
    (mappedPath : P.mapped L.path (path.length + 1) = true)
    (mappedHow : P.mapped L.openHow 24 = true) {p : Proc} (hpc : p.core.pc = after a 2)
    (hpath : p.core.x 20 + UInt64.ofNat 1080 = L.path)
    (hhow : p.core.x 20 + UInt64.ofNat 1056 = L.openHow)
    (named : readList p.core.mem L.path (path.length + 1) = path ++ [0])
    (record : readList p.core.mem L.openHow 24 = how) (hf : p.fpcr = fpcrValue) :
    ∃ q, ProcRunWith Linux.table R P code p q ∧ q.core.pc = after a 8 ∧
      q.core.x 0 = (R p.trace.length).ret ∧
      (∀ r : Fin 32, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 8 → r ≠ 30 →
        q.core.x r = p.core.x r) ∧
      q.core.sp = p.core.sp ∧ q.core.mem = p.core.mem ∧ q.core.io = p.core.io ∧
      q.fpcr = p.fpcr ∧
      q.trace = p.trace ++ [.sys (openEvent L (p.core.x 22) path how (R p.trace.length))] := by
  obtain ⟨u, ru, pu, x0u, x1u, x2u, x3u, x8u, ku, spu, mu, iou⟩ :=
    run_openArgs P code hg hcode (s := p.core) hpc
  obtain ⟨g7, _, _, _, hg7, -, -, -, rfl⟩ := openCalls_ok hg
  have cbl := hcode 7 (by simp)
  have c8 := hcode 8 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at cbl c8
  have hnext : (after (after a 7) 1).toNat < 2 ^ 55 := by
    rw [after_after]
    exact hdom _ _ c8
  have hT : Linux.table.find? (fun c => c.arm64 == ({ p with core := u } : Proc).core.x 8) =
      some Linux.openat2Call := by
    show Linux.table.find? (fun c => c.arm64 == u.x 8) = _
    rw [x8u]
    exact table_openat2
  have e0 : (({ p with core := u } : Proc).call (after a 7) svc).core.x 0 = p.core.x 22 := by
    rw [Proc.call_x _ _ _ (by decide)]
    exact x0u
  obtain ⟨q, rq, pq, x0q, -, kq, spq, mq, ioq, fq, trq⟩ :=
    run_callSvc (T := Linux.table) (R := R) (P := P) (code := code) hsvc cbl hg7 hdom hnext
      (p := { p with core := u }) pu hT rfl
      (sysCall_openEvent L path how
        (by rw [Proc.call_x _ _ _ (by decide)]; exact x1u.trans hpath)
        (by rw [Proc.call_x _ _ _ (by decide)]; exact x2u.trans hhow)
        (by rw [Proc.call_x _ _ _ (by decide)]; exact x3u) short nonzero
        (by rw [Proc.call_mem]; show readList u.mem _ _ = _; rw [mu]; exact named)
        (by rw [Proc.call_mem]; show readList u.mem _ _ = _; rw [mu]; exact record)
        mappedPath mappedHow)
  refine ⟨q, ProcRunWith.trans hdom (ProcRunWith.ofReach hf ru)
      (ProcRunWith.ofWith rq (by rw [fq]; exact hf)), by rw [pq, after_after], x0q,
    fun r h0 h1 h2 h3 h8 h30 => (kq r h0 h30).trans (ku r h0 h1 h2 h3 h8), spq.trans spu,
    by rw [mq, Proc.call_mem]; exact mu, ioq.trans iou, fq, ?_⟩
  rw [trq, e0]
  rfl

/-- One `openat2` call and the test of its result, from `after a 2` of `openCalls` at `a` with the
number `c` of calls made before, at most 3, in X23.  After `-EAGAIN` with `c` below 3 the run
returns to `after a 2` with X23 at `c + 1`, and otherwise it reaches `after a 14`. -/
theorem run_openStep {R : Linux.Replies} {P : Platform} {code : UInt64 → Option UInt32}
    (hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55) {a svc : UInt64} {is : List Instr}
    (hg : openCalls a svc = .ok is) (hcode : CodeAt code a is)
    (hsvc : OpsAt code svc [.svc, .ins (.ret 30)]) (L : ShimLayout) (path how : List UInt8)
    (short : path.length < 4096) (nonzero : 0 ∉ path)
    (mappedPath : P.mapped L.path (path.length + 1) = true)
    (mappedHow : P.mapped L.openHow 24 = true) {p : Proc} {c : Nat} (hpc : p.core.pc = after a 2)
    (h23 : p.core.x 23 = UInt64.ofNat c) (hc : c ≤ 3)
    (hpath : p.core.x 20 + UInt64.ofNat 1080 = L.path)
    (hhow : p.core.x 20 + UInt64.ofNat 1056 = L.openHow)
    (named : readList p.core.mem L.path (path.length + 1) = path ++ [0])
    (record : readList p.core.mem L.openHow 24 = how) (hf : p.fpcr = fpcrValue) :
    ∃ q, ProcRunWith Linux.table R P code p q ∧
      (∀ r : Fin 32, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 8 → r ≠ 9 → r ≠ 23 → r ≠ 30 →
        q.core.x r = p.core.x r) ∧
      q.core.sp = p.core.sp ∧ q.core.mem = p.core.mem ∧ q.core.io = p.core.io ∧
      q.fpcr = p.fpcr ∧
      q.trace = p.trace ++ [.sys (openEvent L (p.core.x 22) path how (R p.trace.length))] ∧
      q.core.x 0 = (R p.trace.length).ret ∧
      if (R p.trace.length).ret = 0 - 11 ∧ c < 3 then
        q.core.pc = after a 2 ∧ q.core.x 23 = UInt64.ofNat (c + 1)
      else q.core.pc = after a 14 := by
  obtain ⟨q1, rq1, p1, x01, k1, sp1, m1, io1, f1, tr1⟩ :=
    run_openCall (R := R) hdom hg hcode hsvc L path how short nonzero mappedPath mappedHow hpc
      hpath hhow named record hf
  obtain ⟨t, rt, ht, kt, spt, mt, iot⟩ := run_openRetry P code hg hcode (s := q1.core) p1
  have h23' : q1.core.x 23 = UInt64.ofNat c :=
    (k1 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h23
  rw [x01, h23'] at ht
  have hle : UInt64.ofNat c ≤ 2 ↔ c < 3 := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt hc (by decide))]
    simp only [UInt64.reduceToNat]
    constructor <;> intro h <;> omega
  refine ⟨{ q1 with core := t }, ProcRunWith.trans hdom rq1 (ProcRunWith.ofReach (f1.trans hf) rt),
    fun r h0 h1 h2 h3 h8 h9 h23 h30 => (kt r h9 h23).trans (k1 r h0 h1 h2 h3 h8 h30),
    spt.trans sp1, mt.trans m1, iot.trans io1, f1, tr1,
    (kt 0 (by decide) (by decide)).trans x01, ?_⟩
  by_cases hag : (R p.trace.length).ret = 0 - 11 ∧ c < 3
  · rw [ite_eq_left ⟨hag.1, hle.mpr hag.2⟩] at ht
    rw [ite_eq_left hag]
    exact ⟨ht.1, ht.2.trans (UInt64.ofNat_add c 1).symm⟩
  · rw [ite_eq_right fun h => hag ⟨h.1, hle.mp h.2⟩] at ht
    rw [ite_eq_right hag]
    exact ht.1

/-- The `openat2` calls of the stub of `path_open`, from the call's arguments at `after a 2` of
`openCalls` at `a` with the number `c` of calls made before in X23 and the replies `rs` from call
`k` on.  The run appends the events of `openLoop` to the trace, which are `openEvent`s whose
results before the last are `-EAGAIN`, and leaves the last result in X0, whose `openReply` is the
loop's reply. -/
theorem run_openLoop {R : Linux.Replies} {P : Platform} {code : UInt64 → Option UInt32}
    (hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55) {a svc : UInt64} {is : List Instr}
    (hg : openCalls a svc = .ok is) (hcode : CodeAt code a is)
    (hsvc : OpsAt code svc [.svc, .ins (.ret 30)]) (L : ShimLayout) (rs : Linux.Replies)
    (n : Nat) (hrs : ∀ j, rs j = R (n + j)) (dir : UInt64) (path how : List UInt8)
    (short : path.length < 4096) (nonzero : 0 ∉ path)
    (mappedPath : P.mapped L.path (path.length + 1) = true)
    (mappedHow : P.mapped L.openHow 24 = true) :
    ∀ (m c k : Nat) (p : Proc), 3 - c = m → c ≤ 3 → p.core.pc = after a 2 →
      p.core.x 22 = dir → p.core.x 23 = UInt64.ofNat c →
      p.core.x 20 + UInt64.ofNat 1080 = L.path → p.core.x 20 + UInt64.ofNat 1056 = L.openHow →
      readList p.core.mem L.path (path.length + 1) = path ++ [0] →
      readList p.core.mem L.openHow 24 = how → p.fpcr = fpcrValue → p.trace.length = n + k →
      ∃ q, ProcRunWith Linux.table R P code p q ∧ q.core.pc = after a 14 ∧
        (∀ r : Fin 32, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 8 → r ≠ 9 → r ≠ 23 → r ≠ 30 →
          q.core.x r = p.core.x r) ∧
        q.core.sp = p.core.sp ∧ q.core.mem = p.core.mem ∧ q.core.io = p.core.io ∧
        q.fpcr = p.fpcr ∧
        q.trace = p.trace ++ (openLoop L rs dir path how c k).1.map A64.Event.sys ∧
        ∃ (pre : List Linux.Reply) (r : Linux.Reply), (openLoop L rs dir path how c k).1 =
            pre.map (openEvent L dir path how) ++ [openEvent L dir path how r] ∧
          (∀ r' ∈ pre, r'.ret = 0 - 11) ∧
          (openLoop L rs dir path how c k).2 = openReply r.ret ∧ q.core.x 0 = r.ret := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro c k p hm hc hpc h22 h23 h1080 h1056 named record hf hk
  obtain ⟨q1, rq1, k1, sp1, m1, io1, f1, tr1, x01, hc1⟩ :=
    run_openStep (R := R) hdom hg hcode hsvc L path how short nonzero mappedPath mappedHow hpc
      h23 hc h1080 h1056 named record hf
  have hR : R p.trace.length = rs k := by rw [hk, hrs]
  rw [hR, h22] at tr1
  rw [hR] at x01 hc1
  by_cases hag : (rs k).ret = 0 - 11 ∧ c < 3
  · rw [ite_eq_left hag] at hc1
    have hc3 := hag.2
    obtain ⟨q, rq, pq, kq, spq, mq, ioq, fq, trq, pre, r, hpre, hret, hrep, hx0⟩ :=
      ih (3 - (c + 1)) (by omega) (c + 1) (k + 1) q1 rfl (by omega) hc1.1
        (by
          rw [k1 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide), h22])
        hc1.2
        (by
          rw [k1 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide)]
          exact h1080)
        (by
          rw [k1 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide)]
          exact h1056)
        (by rw [m1]; exact named) (by rw [m1]; exact record) (by rw [f1]; exact hf)
        (by rw [tr1, List.length_append, List.length_singleton, hk, Nat.add_assoc])
    rw [openLoop_again hag]
    refine ⟨q, ProcRunWith.trans hdom rq1 rq, pq,
      fun r h0 h1 h2 h3 h8 h9 h23 h30 =>
        (kq r h0 h1 h2 h3 h8 h9 h23 h30).trans (k1 r h0 h1 h2 h3 h8 h9 h23 h30),
      spq.trans sp1, mq.trans m1, ioq.trans io1, fq.trans f1, ?_, rs k :: pre, r, ?_, ?_, hrep,
      hx0⟩
    · rw [trq, tr1]
      simp
    · rw [hpre]
      rfl
    · intro r' hr'
      rcases List.mem_cons.mp hr' with rfl | hr'
      · exact hag.1
      · exact hret r' hr'
  · rw [ite_eq_right hag] at hc1
    rw [openLoop_stop hag]
    exact ⟨q1, rq1, hc1, k1, sp1, m1, io1, f1, tr1.trans rfl, [], rs k, rfl,
      fun _ h => absurd h List.not_mem_nil, rfl, x01⟩

/-! ## The stub -/

variable {R : Linux.Replies} {L : ElfLayout} {G : Scratch} {I : Launch} {sp₀ top : UInt64}
  {l₀ : List Linux.Event} {calls : List LeanExe.Wasi.Call} {code : UInt64 → Option UInt32}
  {hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55}
  {hk : ∀ a w i, code a = some w → decode w = some i → i.keepsX17 = true}
  {hk18 : ∀ a w i, code a = some w → decode w = some i → i.keepsX18 = true}
  {hL : L.area.toNat + L.dataMem ≤ 2 ^ 32} {hG : G.base.toNat + scratchSize < 2 ^ 64}
  {base : UInt64} {size : Nat}

/-- The stub of `path_open` stands for the shim's `path_open`. -/
theorem openStub_sim (S : Shared) (n : Nat) {op svc en : UInt64} {is : List Instr}
    (hg : openStub op svc S.trapUnreachable en (areaSize S.cap) = .ok is)
    (hcode : CodeAt code op is) (hsvc : OpsAt code svc [.svc, .ins (.ret 30)])
    (hen : CodeAt code en errnoRoutine)
    (hGb : G.base = L.area + UInt64.ofNat (areaSize S.cap))
    (hdata : areaSize S.cap + scratchSize ≤ L.dataMem)
    (hU' : (modulePlatform L G).normal (modulePlatform L G).uart = false) :
    (shimMachine R L G I sp₀ top l₀ calls code hdom hk hk18 hL hG base size).StubSim S n
      [.i32, .i32, .i32, .i32, .i32, .i64, .i64, .i32, .i32] [.i32]
      (sysFn arm64Flags (shimLayout L.area G) I (fun j => R (l₀.length + j)) Call.pathOpen)
      op := by
  intro st args q hlen hty hpc hstk hsr hregs
  change Proc at q
  change q.core.pc = op at hpc
  change StackOk (modulePlatform L G) q.core at hstk
  obtain ⟨dir, dirflags, ptr, len, oflags, rights, _, fdflags, result, rfl⟩ :=
    typed_open hlen hty
  have x0 : q.core.x 0 = dir.toUInt64 := hregs 0 (by simp)
  have x1 : q.core.x 1 = dirflags.toUInt64 := hregs 1 (by simp)
  have x2 : q.core.x 2 = ptr.toUInt64 := hregs 2 (by simp)
  have x3 : q.core.x 3 = len.toUInt64 := hregs 3 (by simp)
  have x4 : q.core.x 4 = oflags.toUInt64 := hregs 4 (by simp)
  have x5 : q.core.x 5 = rights := hregs 5 (by simp)
  have x7 : q.core.x 7 = fdflags.toUInt64 := hregs 7 (by simp)
  have x8 : q.core.x 8 = result.toUInt64 := hregs 8 (by simp)
  obtain ⟨hst, hf, h17, hgap, htr, hK⟩ := hsr
  rw [sysFn_open]
  simp only [openInvoke]
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, -, -, -, -, -, -, -, hl, hr, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, cL, cR, -⟩ := openStub_code code hg hcode
  have hGnat := scratch_toNat hL hGb hdata
  have hlow : G.base.toNat + scratchSize ≤ 2 ^ 32 := by rw [hGnat]; omega
  have hU := wasiPlatform_uart (top := top)
    (elfPlatform_uart hU' (scratch_pos hL hGb hdata)) hK.stack.above
  have hscrP := scratch_wasi (sp := sp₀) (top := top) hL hGb hdata
  have hbase : q.core.x 17 + UInt64.ofNat (areaSize S.cap) = G.base := by rw [h17, hGb]
  have hmapP : ∀ j < areaSize S.cap,
      (wasiPlatform L sp₀ top).normal (q.core.x 17 + UInt64.ofNat j) = true :=
    fun j hj => (modulePlatform_le_wasi L G sp₀ top).normal _ (hst.mapped j hj)
  have h17nat : (q.core.x 17).toNat = L.area.toNat := by rw [h17]
  have hlim := hst.below
  have hpg := hst.pages
  have hcap := hst.cap_lt
  have hP32 : st.mem.pages * 65536 < 2 ^ 32 := by
    have : st.mem.pages * 65536 ≤ 65535 * 65536 := Nat.mul_le_mul_right _ (by omega)
    omega
  have hoff : ∀ k ≤ scratchSize, (G.base + UInt64.ofNat k).toNat = G.base.toNat + k := by
    intro k hk
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.reducePow]
    unfold scratchSize at hk hG
    omega
  -- the head
  obtain ⟨u1, r1, p1, x20_1, x19_1, x21_1, k1, sp1, m1, io1⟩ :=
    run_openHead (wasiPlatform L sp₀ top) code hg hcode hpc
      (fun k hk => hmapP k (by unfold areaSize; omega))
  have e12 : (ptr.toUInt64 + len.toUInt64).toNat = ptr.toNat + len.toNat := by
    rw [UInt64.toNat_add, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64]
    have := ptr.toNat_lt
    have := len.toNat_lt
    simp only [Nat.reducePow] at *
    omega
  have e84 : (result.toUInt64 + 4).toNat = result.toNat + 4 := by
    rw [UInt64.toNat_add, UInt32.toNat_toUInt64]
    have := result.toNat_lt
    simp only [UInt64.reduceToNat, Nat.reducePow] at *
    omega
  simp only [x2, x3, x8, StoreRel.size_lt hst, e12, e84] at p1
  by_cases hok : ptr.toNat + len.toNat ≤ st.mem.pages * 65536 ∧
      ptr.toNat + len.toNat ≤ 2 ^ 32 ∧ result.toNat + 4 ≤ st.mem.pages * 65536 ∧
      result.toNat + 4 < 2 ^ 32
  swap
  · rw [ite_eq_right hok]
    rw [ite_eq_left (by omega)] at p1
    exact shim_trap (ProcRunWith.ofReach hf r1) io1 p1 hf htr
  rw [ite_eq_left hok]
  rw [ite_eq_right (by omega)] at p1
  have hlenle : ptr.toNat + len.toNat ≤ S.cap * 65536 :=
    Nat.le_trans hok.1 (Nat.mul_le_mul_right _ hpg.2)
  have hresle : result.toNat + 4 ≤ S.cap * 65536 :=
    Nat.le_trans hok.2.2.1 (Nat.mul_le_mul_right _ hpg.2)
  obtain ⟨path, hpdef⟩ : ∃ path : Bytes,
      path = bytesOfList (st.mem.readBytes ptr.toNat len.toNat) := ⟨_, rfl⟩
  rw [← hpdef]
  have hdata : path.data.data.toList = st.mem.readBytes ptr.toNat len.toNat := by
    rw [hpdef]
    simp [bytesOfList]
  -- the checks, the copy of the path, and the record
  have hpath : readList u1.mem (u1.x 17 + UInt64.ofNat 4096 + u1.x 2) (u1.x 3).toNat =
      path.data.data.toList := by
    simp (disch := decide) only [k1, m1, x2, x3, UInt32.toNat_toUInt64]
    rw [guest_addr, readList_bytes (modulePlatform L G) hst len.toNat ptr.toNat hlenle,
      memBytes_readBytes, hdata]
  have hheld : (u1.x 0 ≤ 1023 ∧ u1.mem (u1.x 20 + u1.x 0 + 16) ≠ 0) ↔
      u1.x 0 ∈ openNumbers I st.host.world.events := by
    simp (disch := decide) only [k1, m1, x0]
    rw [x20_1, hbase]
    exact held_byte hK _
  have hsrc : ∀ k < (u1.x 3).toNat, (wasiPlatform L sp₀ top).normal
      (u1.x 17 + UInt64.ofNat 4096 + u1.x 2 + UInt64.ofNat k) = true := by
    intro k hk
    simp (disch := decide) only [k1, x2, x3, UInt32.toNat_toUInt64] at hk ⊢
    rw [guest_addr, add_ofNat_add]
    exact hmapP _ (by unfold areaSize; omega)
  have hbyte : u1.x 0 ≤ 1023 →
      (wasiPlatform L sp₀ top).normal (u1.x 20 + u1.x 0 + 16) = true := by
    intro hle
    simp (disch := decide) only [k1, x0] at hle ⊢
    rw [x20_1, hbase, ← held_addr G dir.toUInt64]
    refine hscrP _ ?_
    rw [UInt64.le_iff_toNat_le] at hle
    simp only [UInt64.reduceToNat] at hle
    unfold scratchSize
    omega
  have hscr' : ∀ k < 4120,
      (wasiPlatform L sp₀ top).normal (u1.x 20 + UInt64.ofNat (1056 + k)) = true := by
    intro k hk
    rw [x20_1, hbase]
    exact hscrP _ (by unfold scratchSize; omega)
  have hsep : (u1.x 17 + UInt64.ofNat 4096 + u1.x 2).toNat + (u1.x 3).toNat ≤
      (u1.x 20).toNat := by
    simp (disch := decide) only [k1, x2, x3, UInt32.toNat_toUInt64]
    rw [guest_addr, x20_1, hbase, hst.toNat_addr (j := 4096 + ptr.toNat)
      (by unfold areaSize; omega), hGnat]
    unfold areaSize
    omega
  have hwrap : (u1.x 20).toNat + 5176 ≤ 2 ^ 64 := by
    rw [x20_1, hbase]
    unfold scratchSize at hG
    omega
  obtain ⟨t2, r2, sp2, io2, x17_2, x18_2, hc2⟩ :=
    run_openBody (wasiPlatform L sp₀ top) code hg hcode p1
      (opened := openNumbers I st.host.world.events) hpath hheld hsrc hbyte hscr' hsep hwrap hU
  simp (disch := decide) only [k1, x0, x1, x4, x5, x7, m1] at hc2
  rw [x20_1, hbase, x19_1, x21_1, x8] at hc2
  have u1x17 : u1.x 17 = q.core.x 17 :=
    k1 17 (by decide) (by decide) (by decide) (by decide) (by decide)
  have u1x18 : u1.x 18 = q.core.x 18 :=
    k1 18 (by decide) (by decide) (by decide) (by decide) (by decide)
  by_cases hc0 : openCheck (openNumbers I st.host.world.events) dir.toUInt64 oflags.toUInt64
    path fdflags.toUInt64 = 0
  swap
  · rw [ite_eq_right hc0] at hc2 ⊢
    obtain ⟨p2, x02, m2⟩ := hc2
    exact shim_errno ⟨hst, hf, h17, hgap, htr, hK⟩ (r1.trans r2) p2 (sp2.trans sp1) m2
      (io2.trans io1) (x17_2.trans u1x17) (x18_2.trans u1x18) x02 (openCheck_lt _ _ _ _ _)
  rw [ite_eq_left hc0] at hc2 ⊢
  obtain ⟨p2, x20_2, x19_2, x21_2, x22_2, x23_2, m2⟩ := hc2
  obtain ⟨hz0, hshort⟩ := openCheck_zero hc0
  have hhl : (openHowBytes arm64Flags dirflags.toUInt64 oflags.toUInt64 rights
      fdflags.toUInt64).length = 24 := by
    simp [openHowBytes]
  generalize openHowBytes arm64Flags dirflags.toUInt64 oflags.toUInt64 rights
    fdflags.toUInt64 = how at m2 hhl ⊢
  have hpl : path.data.data.toList.length = len.toNat := by
    have := congrArg List.length hpath
    rw [readList_length] at this
    simp (disch := decide) only [k1, x3, UInt32.toNat_toUInt64] at this
    exact this.symm
  have hshortL : path.data.data.toList.length < 4096 := by
    have : path.data.size = path.data.data.toList.length := by
      simp only [Array.length_toList, ByteArray.size]
    omega
  -- the memory before the calls
  have eP : (shimLayout L.area G).path = G.base + UInt64.ofNat 1080 := rfl
  have eH : (shimLayout L.area G).openHow = G.base + UInt64.ofNat 1056 := rfl
  have named : readList t2.mem (shimLayout L.area G).path (path.data.data.toList.length + 1) =
      path.data.data.toList ++ [0] := by
    rw [m2, eP, readList_writeList_apart _ _ _ _ _ fun j hj => ?_]
    · exact readList_writeList _ _ _ (by simp) (by simp; omega)
    · rw [add_ofNat_add, UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
        rw [hoff _ (by unfold scratchSize; omega), hoff _ (by unfold scratchSize; omega)]
        omega)), hoff _ (by unfold scratchSize; omega), hoff _ (by unfold scratchSize; omega),
        hhl]
      omega
  have record : readList t2.mem (shimLayout L.area G).openHow 24 = how := by
    rw [m2, eH]
    exact readList_writeList _ _ _ hhl.symm (by omega)
  have mappedPath : (wasiPlatform L sp₀ top).mapped (shimLayout L.area G).path
      (path.data.data.toList.length + 1) = true := by
    rw [eP]
    unfold Platform.mapped
    rw [List.all_eq_true]
    intro i hi
    rw [List.mem_range] at hi
    rw [add_ofNat_add]
    exact hscrP _ (by unfold scratchSize; omega)
  have mappedHow : (wasiPlatform L sp₀ top).mapped (shimLayout L.area G).openHow 24 = true := by
    rw [eH]
    unfold Platform.mapped
    rw [List.all_eq_true]
    intro i hi
    rw [List.mem_range] at hi
    rw [add_ofNat_add]
    exact hscrP _ (by unfold scratchSize; omega)
  -- the calls
  have hlen0 : ({ q with core := t2 } : Proc).trace.length =
      l₀.length + st.host.world.events.length := by
    show q.trace.length = _
    rw [htr.1, List.length_map, List.length_append]
  obtain ⟨q3, rq3, p3, k3, sp3, m3, io3, f3, tr3, pre, rl, hpre, hret, hrep, x03⟩ :=
    run_openLoop (R := R) (P := wasiPlatform L sp₀ top) hdom hl cL hsvc (shimLayout L.area G)
      (fun j => R (l₀.length + j)) l₀.length (fun _ => rfl) dir.toUInt64 path.data.data.toList
      how hshortL hz0 mappedPath mappedHow 3 0 st.host.world.events.length
      { q with core := t2 } rfl (by decide) (by show t2.pc = _; rw [p2, after_after])
      x22_2 x23_2 (by show t2.x 20 + _ = _; rw [x20_2]; rfl)
      (by show t2.x 20 + _ = _; rw [x20_2]; rfl) named record hf hlen0
  generalize openLoop (shimLayout L.area G) (fun j => R (l₀.length + j)) dir.toUInt64
    path.data.data.toList how 0 st.host.world.events.length = lp at tr3 hpre hrep ⊢
  have q3x : ∀ r : Fin 32, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 8 → r ≠ 9 → r ≠ 23 → r ≠ 30 →
      q3.core.x r = t2.x r := k3
  have q3x20 : q3.core.x 20 = G.base := (q3x 20 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)).trans x20_2
  have q3x17 : q3.core.x 17 = q.core.x 17 := (q3x 17 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)).trans (x17_2.trans u1x17)
  have q3x18 : q3.core.x 18 = q.core.x 18 := (q3x 18 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)).trans (x18_2.trans u1x18)
  have q3x19 : q3.core.x 19 = q.core.x 30 := (q3x 19 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)).trans x19_2
  have q3x21 : q3.core.x 21 = result.toUInt64 := (q3x 21 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)).trans x21_2
  have q3mem : q3.core.mem = t2.mem := m3
  have hf3 : q3.fpcr = fpcrValue := f3.trans hf
  -- the result
  obtain ⟨t4, r4, sp4, io4, x17_4, x18_4, hc4⟩ :=
    run_openResult (wasiPlatform L sp₀ top) code hr cR hen (s := q3.core)
      (by rw [p3, after_after])
      (fun hle => by
        rw [q3x20, ← held_addr G]
        refine hscrP _ ?_
        rw [UInt64.le_iff_toNat_le] at hle
        simp only [UInt64.reduceToNat] at hle
        unfold scratchSize
        omega)
      (fun _ k hk => by
        rw [q3x17, q3x21, guest_addr, add_ofNat_add]
        exact hmapP _ (by unfold areaSize; omega)) hU
  rw [q3x20, q3x17, q3x19, q3x21, q3mem, x03] at hc4
  have hrch : (shimMachine R L G I sp₀ top l₀ calls code hdom hk hk18 hL hG base size).Rch q
      { q3 with core := t4 } :=
    ProcRunWith.trans hdom (ProcRunWith.ofReach hf (r1.trans r2))
      (ProcRunWith.trans hdom rq3 (ProcRunWith.ofReach hf3 r4))
  have hsp4 : t4.sp = q.core.sp := by
    rw [sp4, sp3]
    show t2.sp = _
    rw [sp2, sp1]
  have hio4 : t4.io = q.core.io := by
    rw [io4, io3]
    show t2.io = _
    rw [io2, io1]
  have h174 : t4.x 17 = L.area := by rw [x17_4, q3x17, h17]
  have h184 : t4.x 18 = q.core.x 18 := by rw [x18_4, q3x18]
  have hgap4 : L.area.toNat + areaSize S.cap + scratchSize ≤ (t4.x 18).toNat := by
    rw [h184]
    exact hgap
  have htrace : ({ q3 with core := t4 } : Proc).trace =
      (l₀ ++ (st.host.world.events ++ lp.1)).map A64.Event.sys := by
    show q3.trace = _
    rw [tr3]
    show q.trace ++ _ = _
    rw [htr.1]
    simp only [List.map_append, List.append_assoc]
  have hopenW : ∀ r, WritesNative (shimLayout L.area G) size
      (openEvent (shimLayout L.area G) dir.toUInt64 path.data.data.toList how r) :=
    fun r => .inl fun g hg => by
      change g ∈ Linux.outputRegions [dir.toUInt64, (shimLayout L.area G).path,
        (shimLayout L.area G).openHow, 24] 0 Linux.openat2Call.params at hg
      rw [(Linux.regions_openat2 (a64Memory (wasiPlatform L sp₀ top)) q.core.mem dir.toUInt64
        _ _ 24).2] at hg
      cases hg
  have hwithin : ∀ e ∈ st.host.world.events ++ lp.1,
      WritesNative (shimLayout L.area G) size e := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact htr.2 e he
    · rw [hpre] at he
      rcases List.mem_append.mp he with he | he
      · obtain ⟨r, -, rfl⟩ := List.mem_map.mp he
        exact hopenW r
      · rw [List.mem_singleton] at he
        subst he
        exact hopenW rl
  -- the scratch before the result
  obtain ⟨hw1a, hw1b⟩ := writeList_scratchHigh (G := G) q.core.mem (i := 1080)
    (path.data.data.toList ++ [0]) (by decide)
    (by rw [List.length_append, List.length_singleton]; unfold scratchSize; omega) hlow
  obtain ⟨hw2a, hw2b⟩ := writeList_scratchHigh (G := G)
    (LeanExe.A64.writeList q.core.mem (G.base + UInt64.ofNat 1080)
      (path.data.data.toList ++ [0])) (i := 1056) how (by decide)
    (by rw [hhl]; decide) hlow
  have hK2 : ScratchHolds G I sp₀ top st.host.world.events t2.mem := by
    rw [m2]
    exact (hK.congrLow hw1a hw1b).congrLow hw2a hw2b
  have hK3 := ScratchHolds.again (shimLayout L.area G) dir.toUInt64 path.data.data.toList how pre
    _ hret hK2
  have hso2 : ScratchOnly G q.core.mem t2.mem := by
    rw [m2]
    exact (ScratchOnly.writeList _ _
      (by rw [List.length_append, List.length_singleton]; unfold scratchSize; omega) hG).trans
      (ScratchOnly.writeList _ _ (by rw [hhl]; decide) hG)
  have hGlim : G.base.toNat + scratchSize ≤ (q.core.x 18).toNat := by rw [hGnat]; exact hgap
  have hgu : (q.core.x 17 + UInt64.ofNat (4096 + result.toNat)).toNat =
      (q.core.x 17).toNat + (4096 + result.toNat) :=
    hst.toNat_addr (by unfold areaSize; omega)
  rcases hc4 with ⟨hle, p4, x04, m4⟩ | ⟨hgt, h4095, p4, x04, m4⟩ | ⟨hgt, hbig, p4, m4⟩
  · -- a descriptor
    have hsmall : rl.ret.toNat < 1024 := by
      rw [UInt64.le_iff_toNat_le] at hle
      simp only [UInt64.reduceToNat] at hle
      omega
    rw [hrep, openReply_small hle, placeReply_word]
    simp only [sysAnswer, sysResult]
    rw [guest_addr, ← leBytes_word, ← held_addr G rl.ret] at m4
    have hbl : (leBytes 4 rl.ret.toNat).data.data.toList.length = 4 := by
      rw [show (leBytes 4 rl.ret.toNat).data.data.toList.length =
        (leBytes 4 rl.ret.toNat).data.size by simp only [Array.length_toList, ByteArray.size],
        leBytes_size]
    have hso3 : ScratchOnly G q.core.mem (store8 t2.mem (G.held rl.ret.toNat) 1) :=
      hso2.trans (ScratchOnly.store8 (G := G) t2.mem (j := 16 + rl.ret.toNat) 1
        (by unfold scratchSize; omega) hG)
    have hmid : StoreRel (modulePlatform L G) S.cap S.globalTypes st
        { t4 with mem := store8 t2.mem (G.held rl.ret.toNat) 1 } :=
      ScratchOnly.storeRel hst hbase.symm (by show t4.x 17 = _; rw [h174, h17]) h184 hso3
    have hst4 := hmid.ofWriteList (modulePlatform L G) (leBytes 4 rl.ret.toNat).data.data.toList
      (s' := t4) (p := result.toNat) (by rw [hbl]; exact hok.2.2.1) rfl rfl
      (by
        rw [m4]
        show _ = LeanExe.A64.writeList _ (t4.x 17 + _) _
        rw [h174, h17])
    refine shim_return hrch (by show t4.pc = _; exact p4) hsp4 h184 hio4 (fun a ha => ?_)
      (x04.trans rfl) ⟨StoreRel.withHost hst4 _, hf3, h174, hgap4, ⟨htrace, hwithin⟩, ?_⟩
    · show t4.mem a = q.core.mem a
      have := hstk.limit
      rw [m4, writeList_below (lim := q.core.x 18)
        (by rw [hgu, hbl]; unfold areaSize at hlim; omega) (by omega)]
      exact hso3.high hGlim (by omega)
    · show ScratchHolds G I sp₀ top (st.host.world.events ++ lp.1) t4.mem
      rw [hpre, ← List.append_assoc]
      refine hK3.opened (e := openEvent (shimLayout L.area G) dir.toUInt64 path.data.data.toList
        how rl) rfl (by show rl.ret.toNat < descriptorLimit; unfold descriptorLimit; exact hsmall)
        ?_ ?_ ?_
      · show t4.mem (G.held rl.ret.toNat) = 1
        rw [m4, writeList_below (lim := G.held rl.ret.toNat) (by
          show _ ≤ (G.base + UInt64.ofNat (16 + rl.ret.toNat)).toNat
          rw [hgu, hbl, hoff _ (by unfold scratchSize; omega), hGnat]
          unfold areaSize
          omega) (Nat.le_refl _)]
        simp [store8]
      · intro j hj hjr
        rw [m4, writeList_below (lim := G.base + UInt64.ofNat j) (by
          rw [hgu, hbl, hoff _ (by unfold scratchSize; omega), hGnat]
          unfold areaSize
          omega) (Nat.le_refl _)]
        exact store8_other _ _ _ _
          (scratch_ne (by unfold scratchSize; omega) (by unfold scratchSize; omega) hjr)
      · intro a ha
        rw [m4, writeList_below (lim := a) (by
          rw [hgu, hbl]
          rw [hGnat] at hlow
          unfold areaSize at hlow
          omega) (Nat.le_refl _)]
        refine store8_other _ _ _ _ fun same => ?_
        rw [same] at ha
        change 2 ^ 32 ≤ (G.base + UInt64.ofNat (16 + rl.ret.toNat)).toNat at ha
        rw [hoff _ (by unfold scratchSize; omega)] at ha
        unfold scratchSize at hlow
        omega
  · -- an error
    rw [hrep, openReply_error hgt h4095, placeReply_errno _ _ _ (errnoOf_valid _).2]
    simp only [sysAnswer, sysResult]
    have hso4 : ScratchOnly G q.core.mem t4.mem := by rw [m4]; exact hso2
    refine shim_return hrch (by show t4.pc = _; exact p4) hsp4 h184 hio4 (fun a ha => ?_)
      (by show t4.x 0 = _; rw [x04, errno_toUInt64, errnoOf_lookup])
      ⟨StoreRel.withHost (ScratchOnly.storeRel hst hbase.symm
        (by show t4.x 17 = _; rw [h174, h17]) h184 hso4) _, hf3, h174,
        hgap4, ⟨htrace, hwithin⟩, ?_⟩
    · show t4.mem a = q.core.mem a
      have := hstk.limit
      exact hso4.high hGlim (by omega)
    · show ScratchHolds G I sp₀ top (st.host.world.events ++ lp.1) t4.mem
      rw [hpre, ← List.append_assoc, m4]
      refine hK3.quiet (fun h => ?_) (show Linux.openat2Call ≠ Linux.closeCall by decide)
      have h2 := h.2
      change rl.ret.toNat < 2 ^ 31 at h2
      rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub] at h4095
      rw [UInt64.lt_iff_toNat_lt] at hgt
      simp only [UInt64.reduceToNat, Nat.reducePow] at h4095 h2 hgt
      omega
  · -- a trap
    rw [hrep, openReply_trap hgt hbig]
    simp only [sysAnswer, sysResult]
    exact shim_trap hrch hio4 p4 hf3 ⟨htrace, hwithin⟩

end Verified.ShimA64
