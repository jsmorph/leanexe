import Verified.ShimA64.Strings
import LeanExe.A64.Proof.WasiPreopen

/-!
The stubs of the preopened directory against the shim's host environment: `prestatStub_sim` and
`dirNameStub_sim` prove that the stubs of `fd_prestat_get` and `fd_prestat_dir_name` meet
`Machine.StubSim` for their functions of `linuxEnv` on `shimMachine`.  The stubs read the
scratch, which lies outside `modulePlatform`, so their runs lie on the process's platform,
`wasiPlatform`.  A request whose region exceeds the memory reaches the trap stub with the store
unchanged.  Every other request returns with the errno of the specification's function: the stubs
read the preopen flag and the byte of the descriptor, which the machine's `ScratchHolds` relates
to `preopened` and `openNumbers` of the world's events.  They make no call, write only the area,
and leave the world's events as they were, so `ScratchHolds` and the trace's relation hold at the
return (`stub_returned`).  `prestat_placed` states the record that `prestatInvoke` writes for
descriptor 3 while it is the preopened directory as Talos's `write64` of `2^32`, the word that the
stub stores.
-/

namespace Verified.ShimA64

open Wasm LeanExe LeanExe.A64 LeanExe.Wasi Verified.Wasi Verified.Shim

/-- Talos's `write64` as the write of its eight bytes, the lowest first. -/
theorem write64_writeBytes (m : Mem) (y : UInt32) (v : UInt64) :
    m.write64 y v = m.writeBytes y.toNat [(v &&& 0xFF).toUInt8, ((v >>> 8) &&& 0xFF).toUInt8,
      ((v >>> 16) &&& 0xFF).toUInt8, ((v >>> 24) &&& 0xFF).toUInt8, ((v >>> 32) &&& 0xFF).toUInt8,
      ((v >>> 40) &&& 0xFF).toUInt8, ((v >>> 48) &&& 0xFF).toUInt8,
      ((v >>> 56) &&& 0xFF).toUInt8] := by
  cases m with
  | mk pages bytes =>
    simp only [Mem.write64, Mem.writeBytes, List.length_cons, List.length_nil]
    congr 1
    funext i
    by_cases h : y.toNat ≤ i ∧ i < y.toNat + 8
    · rw [dif_pos h]
      obtain ⟨k, hk, rfl⟩ : ∃ k, k < 8 ∧ i = y.toNat + k := ⟨i - y.toNat, by omega, by omega⟩
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 by omega) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · rw [dif_neg h, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- The record that `fd_prestat_get` writes for descriptor 3 while it is the preopened directory:
the word `2^32`. -/
theorem prestat_placed (m : Mem) (p : UInt32) :
    placeReply m (fun outputs => [(p, outputs.headD Bytes.empty)]) (prestatReply true 3) =
      m.write64 p (2 ^ 32) := by
  rw [write64_writeBytes]
  simp only [prestatReply, and_self, ↓reduceIte, placeReply, placeAll, List.headD_cons]
  rfl

/-- Three values of type `i32` from their typing. -/
theorem typed_i32x3 {args : List Value} (hlen : args.length = 3)
    (hty : Typed [.i32, .i32, .i32] args) :
    ∃ a0 a1 a2 : UInt32, args = [.i32 a0, .i32 a1, .i32 a2] := by
  match args, hlen, hty with
  | [v0, v1, v2], _, ⟨t0, t1, t2, _⟩ =>
    obtain ⟨a0, rfl⟩ : ∃ a, v0 = .i32 a := by
      cases v0 <;> first | exact ⟨_, rfl⟩ | exact t0.elim
    obtain ⟨a1, rfl⟩ : ∃ a, v1 = .i32 a := by
      cases v1 <;> first | exact ⟨_, rfl⟩ | exact t1.elim
    obtain ⟨a2, rfl⟩ : ∃ a, v2 = .i32 a := by
      cases v2 <;> first | exact ⟨_, rfl⟩ | exact t2.elim
    exact ⟨a0, a1, a2, rfl⟩

/-- A store of the eight bytes from `a`, all of them Normal memory of `P`, keeps every byte outside
`P`'s Normal memory. -/
theorem store64_outside {P : Platform} {m : UInt64 → UInt8} {a v : UInt64}
    (h : ∀ k < 8, P.normal (a + UInt64.ofNat k) = true) {b : UInt64} (hb : P.normal b = false) :
    store64 m a v b = m b := by
  have hn : ¬ b - a < 8 := by
    intro hlt
    have hk : (b - a).toNat < 8 := by
      rw [UInt64.lt_iff_toNat_lt] at hlt
      exact hlt
    have e : a + UInt64.ofNat (b - a).toNat = b := by
      rw [UInt64.ofNat_toNat, UInt64.add_sub_cancel_left]
    rw [← e, h _ hk] at hb
    cases hb
  simp only [store64, hn, ↓reduceIte]

/-- The store of a byte of Normal memory of `P` keeps every byte outside `P`'s Normal memory. -/
theorem store8_outside {P : Platform} {m : UInt64 → UInt8} {a : UInt64} {v : UInt8}
    (h : P.normal a = true) {b : UInt64} (hb : P.normal b = false) : store8 m a v b = m b := by
  have hne : b ≠ a := fun e => by rw [e, h] at hb; cases hb
  simp only [store8, hne, ↓reduceIte]

/-- The scratch's bytes are Normal memory of the process's platform when the scratch lies in the
data segment, which ends below `2^32`. -/
theorem scratch_wasi {L : ElfLayout} {G : Scratch} {cap : Nat} {sp top : UInt64}
    (hL : L.area.toNat + L.dataMem ≤ 2 ^ 32) (hGb : G.base = L.area + UInt64.ofNat (areaSize cap))
    (hdata : areaSize cap + scratchSize ≤ L.dataMem) :
    ∀ j < scratchSize, (wasiPlatform L sp top).normal (G.base + UInt64.ofNat j) = true := by
  intro j hj
  have e : (G.base + UInt64.ofNat j).toNat = L.area.toNat + areaSize cap + j := by
    rw [hGb, add_ofNat_add, UInt64.toNat_add, UInt64.toNat_ofNat']
    simp only [Nat.reducePow] at *
    omega
  refine (elfPlatform_le_wasi L sp top).normal _ ?_
  simp only [elfPlatform, decide_eq_true_eq, UInt64.le_iff_toNat_le, e]
  omega

variable {R : Linux.Replies} {L : ElfLayout} {G : Scratch} {I : Launch} {sp₀ top : UInt64}
  {l₀ : List Linux.Event} {calls : List LeanExe.Wasi.Call} {code : UInt64 → Option UInt32}
  {hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55}
  {hk : ∀ a w i, code a = some w → decode w = some i → i.keepsX17 = true}
  {hk18 : ∀ a w i, code a = some w → decode w = some i → i.keepsX18 = true}
  {hL : L.area.toNat + L.dataMem ≤ 2 ^ 32} {hG : G.base.toNat + scratchSize < 2 ^ 64}
  {base : UInt64} {size : Nat}

/-- A run on the process's platform from a state that holds the store `st` to the return address
with the errno `errno` in X0, SP, X17, X18, and the UART's state kept, and a memory that differs
from the state's only in the area and below SP, is a return of a stub that answered without a call
with the memory `mem` and the WASI event `e`. -/
theorem stub_returned {S : Shared} {n : Nat} {st : Store (Observed LinuxWorld)} {q : Proc}
    (hsr : (shimMachine R L G I sp₀ top l₀ calls code hdom hk hk18 hL hG base size).SR S.cap
      S.globalTypes st q)
    {t : State} (rt : Reach (wasiPlatform L sp₀ top) code q.core t) (pt : t.pc = q.core.x 30)
    (spt : t.sp = q.core.sp) (iot : t.io = q.core.io) (x17t : t.x 17 = q.core.x 17)
    (x18t : t.x 18 = q.core.x 18) {errno : UInt64} (xt0 : t.x 0 = errno)
    (herr : errno.toNat < 2 ^ 32)
    (hsp : ∀ b : UInt64, q.core.sp.toNat ≤ b.toNat → t.mem b = q.core.mem b)
    (hout : ∀ b, (modulePlatform L G).normal b = false → t.mem b = q.core.mem b) {mem : Mem}
    (hst : StoreRel (modulePlatform L G) S.cap S.globalTypes { st with mem } t) (e : Wasi.Event) :
    ∃ q', (shimMachine R L G I sp₀ top l₀ calls code hdom hk hk18 hL hG base size).Rch q q' ∧
      Returned [.i32] [.i32 errno.toUInt32]
        ((shimMachine R L G I sp₀ top l₀ calls code hdom hk hk18 hL hG base size).core q)
        ((shimMachine R L G I sp₀ top l₀ calls code hdom hk hk18 hL hG base size).core q') ∧
      (shimMachine R L G I sp₀ top l₀ calls code hdom hk hk18 hL hG base size).SR S.cap
        S.globalTypes (answered st mem [] e) q' := by
  obtain ⟨-, hf, h17, hgap, htr, hK⟩ := hsr
  have hev : (st.host.world.answer [] e).events = st.host.world.events := by
    simp [LinuxWorld.answer]
  refine ⟨{ q with core := t }, ProcRunWith.ofReach hf rt,
    ⟨pt, spt, x18t, iot, fun b hb => hsp b (by simpa using hb), by simp,
      ⟨by simp, fun k hk => ?_⟩, by simp [Typed, HasType]⟩,
    StoreRel.withHost hst _, hf, by show t.x 17 = _; rw [x17t]; exact h17,
    by show _ ≤ (t.x 18).toNat; rw [x18t]; exact hgap, ⟨?_, ?_⟩, ?_⟩
  · simp only [List.take_succ_cons, List.take_zero, List.length_cons, List.length_nil] at hk
    obtain rfl : k = 0 := by omega
    show t.x 0 = errno.toUInt32.toUInt64
    rw [xt0]
    apply UInt64.toNat_inj.mp
    rw [UInt32.toNat_toUInt64, UInt64.toNat_toUInt32]
    omega
  · show q.trace = _
    rw [htr.1]
    simp [answered, hev]
  · intro x hx
    simp only [answered, hev] at hx
    exact htr.2 x hx
  · show ScratchHolds G I sp₀ top (answered st mem [] e).host.world.events t.mem
    simp only [answered, hev]
    exact hK.frame hL hG hout

/-- The stub of `fd_prestat_get` stands for the shim's `fd_prestat_get`. -/
theorem prestatStub_sim (S : Shared) (n : Nat) {a : UInt64} {is : List Instr}
    (hg : prestatStub a S.trapUnreachable (areaSize S.cap) = .ok is) (hcode : CodeAt code a is)
    (hGa : G.base = L.area + UInt64.ofNat (areaSize S.cap))
    (hscr : ∀ j < scratchSize,
      (wasiPlatform L sp₀ top).normal (G.base + UInt64.ofNat j) = true) :
    (shimMachine R L G I sp₀ top l₀ calls code hdom hk hk18 hL hG base size).StubSim S n
      [.i32, .i32] [.i32]
      (sysFn arm64Flags (shimLayout L.area G) I (fun j => R (l₀.length + j)) Call.fdPrestatGet)
      a := by
  intro st args q hlen hty hpc hstk hsr hregs
  change Proc at q
  change q.core.pc = a at hpc
  change StackOk (modulePlatform L G) q.core at hstk
  obtain ⟨a0, a1, rfl⟩ := typed_i32x2 hlen hty
  have x0 : q.core.x 0 = a0.toUInt64 := hregs 0 (by simp)
  have x1 : q.core.x 1 = a1.toUInt64 := hregs 1 (by simp)
  have hsr' := hsr
  obtain ⟨hst, hf, h17, hgap, htr, hK⟩ := hsr
  refine .inr ?_
  have hPP := modulePlatform_le_wasi L G sp₀ top
  have hinv : (sysFn arm64Flags (shimLayout L.area G) I (fun j => R (l₀.length + j))
      Call.fdPrestatGet).invoke st [.i32 a0, .i32 a1] = prestatInvoke I st [.i32 a0, .i32 a1] := by
    simp (config := { decide := true }) only [sysFn, sysInvoke, ↓reduceIte]
  rw [hinv]
  have hpg := hst.pages
  have hcap := hst.cap_lt
  have hlim := hst.below
  have hstk2 := hstk.limit
  have hG17 : q.core.x 17 + UInt64.ofNat (areaSize S.cap) = G.base := by rw [h17, hGa]
  have hsize8 : ∀ k < 8, (wasiPlatform L sp₀ top).normal (q.core.x 17 + UInt64.ofNat k) = true :=
    fun k hk => hPP.normal _ (hst.mapped k (by unfold areaSize; omega))
  have hflagN : (wasiPlatform L sp₀ top).normal
      (q.core.x 17 + UInt64.ofNat (areaSize S.cap) + 8) = true := by
    rw [hG17]
    exact hscr 8 (by decide)
  have hsz : load64 q.core.mem (q.core.x 17) + 8 = UInt64.ofNat (st.mem.pages * 65536) := by
    rw [hst.size]
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.reducePow, UInt64.reduceToNat]
    omega
  have hend : q.core.x 1 + 8 = UInt64.ofNat (a1.toNat + 8) := by
    rw [x1]
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat', UInt32.toNat_toUInt64, Nat.reducePow,
      UInt64.reduceToNat]
    omega
  have htrapIff : load64 q.core.mem (q.core.x 17) + 8 < q.core.x 1 + 8 ↔
      st.mem.pages * 65536 < a1.toNat + 8 := by
    rw [hsz, hend, UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat', UInt64.toNat_ofNat']
    have := a1.toNat_lt
    simp only [Nat.reducePow] at *
    omega
  have haddr : ∀ k < 8, q.core.x 17 + q.core.x 1 + UInt64.ofNat (8 * 512 + k) =
      q.core.x 17 + UInt64.ofNat (4096 + (a1.toNat + k)) := fun k _ => by
    rw [x1, UInt64.add_assoc]
    congr 1
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat', UInt32.toNat_toUInt64, Nat.reducePow]
    omega
  have hrecN : ¬ load64 q.core.mem (q.core.x 17) + 8 < q.core.x 1 + 8 → ∀ k < 8,
      (wasiPlatform L sp₀ top).normal (q.core.x 17 + q.core.x 1 + UInt64.ofNat (8 * 512 + k)) =
        true := fun h k hk => by
    rw [haddr k hk]
    refine hPP.normal _ (hst.mapped _ ?_)
    rw [htrapIff] at h
    unfold areaSize
    have := Nat.mul_le_mul_right 65536 hpg.2
    omega
  obtain ⟨t, rt, spt, iot, x17t, x18t, ht⟩ := run_prestatStub (wasiPlatform L sp₀ top) code hg
    hcode hpc hsize8 hflagN hrecN
  simp only [prestatInvoke]
  by_cases htrap : load64 q.core.mem (q.core.x 17) + 8 < q.core.x 1 + 8
  · rw [if_pos htrap] at ht
    rw [if_neg (fun h => by have := htrapIff.mp htrap; omega)]
    exact ⟨{ q with core := t }, ProcRunWith.ofReach hf rt, iot, .inr (.inr (.inr ⟨rfl, ht⟩)),
      hf, htr⟩
  rw [if_neg htrap] at ht
  obtain ⟨pt, hret⟩ := ht
  have hin : a1.toNat + 8 ≤ st.mem.pages * 65536 ∧ a1.toNat + 8 < 2 ^ 32 := by
    have := htrapIff.not.mp htrap
    have := Nat.mul_le_mul_right 65536 hpg.2
    omega
  rw [if_pos hin]
  have hflag : q.core.mem (q.core.x 17 + UInt64.ofNat (areaSize S.cap) + 8) =
      if preopened I st.host.world.events then 1 else 0 := by
    rw [hG17]
    exact hK.preopen
  have hfit : (q.core.x 17 + UInt64.ofNat (4096 + a1.toNat)).toNat + 8 ≤ (q.core.x 18).toNat := by
    rw [hst.toNat_addr (j := 4096 + a1.toNat) (by unfold areaSize; omega)]
    unfold areaSize at hlim
    have := Nat.mul_le_mul_right 65536 hpg.2
    omega
  by_cases hgr : a0.toUInt64 = 3 ∧ preopened I st.host.world.events = true
  · have hc : q.core.x 0 = 3 ∧ q.core.mem (q.core.x 17 + UInt64.ofNat (areaSize S.cap) + 8) ≠ 0 :=
      ⟨by rw [x0]; exact hgr.1, by rw [hflag, if_pos hgr.2]; decide⟩
    rw [if_pos hc] at hret
    obtain ⟨xt0, mt⟩ := hret
    have hrep : prestatReply (preopened I st.host.world.events) a0.toUInt64 =
        prestatReply true 3 := by rw [hgr.1, hgr.2]
    rw [hrep, prestat_placed,
      show prestatReply true 3 = .returned 0 [bytesOfList [0, 0, 0, 0, 1, 0, 0, 0]] from rfl]
    simp only [sysAnswer, sysResult]
    have hmt : t.mem = store64 q.core.mem (q.core.x 17 + UInt64.ofNat (4096 + a1.toNat))
        (2 ^ 32) := by
      rw [mt, ← haddr 0 (by decide)]
      rfl
    exact stub_returned hsr' rt pt spt iot x17t x18t xt0 (by decide)
      (fun b hb => by
        rw [hmt]
        exact store64_other _ _ _ _ (not_within8 (.inr (by omega)) (by omega)))
      (fun b hb => by
        rw [hmt]
        refine store64_outside (fun k hk => ?_) hb
        rw [add_ofNat_add]
        refine hst.mapped _ ?_
        unfold areaSize
        have := Nat.mul_le_mul_right 65536 hpg.2
        omega)
      (hst.write (modulePlatform L G) (y := a1) (v := 2 ^ 32) hin.1 x17t x18t hmt) _
  · have hc : ¬ (q.core.x 0 = 3 ∧
        q.core.mem (q.core.x 17 + UInt64.ofNat (areaSize S.cap) + 8) ≠ 0) := by
      rw [x0, hflag]
      intro h
      apply hgr
      refine ⟨h.1, ?_⟩
      cases hp : preopened I st.host.world.events
      · rw [hp] at h
        exact absurd rfl h.2
      · rfl
    rw [if_neg hc] at hret
    obtain ⟨xt0, mt⟩ := hret
    have hrep : prestatReply (preopened I st.host.world.events) a0.toUInt64 =
        .returned 8 [zeros 8] := by
      simp only [prestatReply]
      rw [if_neg hgr]
    rw [hrep]
    simp only [sysAnswer, sysResult, placeReply, show (8 : UInt64) ≠ 0 by decide, ↓reduceIte]
    exact stub_returned hsr' rt pt spt iot x17t x18t xt0 (by decide)
      (fun b _ => by rw [mt]) (fun b _ => by rw [mt]) (StoreRel.regs hst x17t x18t mt) _


/-- A number that the shim holds lies below `descriptorLimit`. -/
theorem openNumbers_lt {I : Launch} {events : List Linux.Event} {x : UInt64}
    (h : x ∈ openNumbers I events) : x.toNat < descriptorLimit := by
  unfold openNumbers at h
  have := (List.mem_filter.mp h).2
  simpa using this

/-- The stub of `fd_prestat_dir_name` stands for the shim's `fd_prestat_dir_name`. -/
theorem dirNameStub_sim (S : Shared) (n : Nat) {a : UInt64} {is : List Instr}
    (hg : dirNameStub a S.trapUnreachable (areaSize S.cap) = .ok is) (hcode : CodeAt code a is)
    (hGa : G.base = L.area + UInt64.ofNat (areaSize S.cap))
    (hscr : ∀ j < scratchSize,
      (wasiPlatform L sp₀ top).normal (G.base + UInt64.ofNat j) = true) :
    (shimMachine R L G I sp₀ top l₀ calls code hdom hk hk18 hL hG base size).StubSim S n
      [.i32, .i32, .i32] [.i32]
      (sysFn arm64Flags (shimLayout L.area G) I (fun j => R (l₀.length + j))
        Call.fdPrestatDirName) a := by
  intro st args q hlen hty hpc hstk hsr hregs
  change Proc at q
  change q.core.pc = a at hpc
  change StackOk (modulePlatform L G) q.core at hstk
  obtain ⟨a0, a1, a2, rfl⟩ := typed_i32x3 hlen hty
  have x0 : q.core.x 0 = a0.toUInt64 := hregs 0 (by simp)
  have x1 : q.core.x 1 = a1.toUInt64 := hregs 1 (by simp)
  have x2 : q.core.x 2 = a2.toUInt64 := hregs 2 (by simp)
  have hsr' := hsr
  obtain ⟨hst, hf, h17, hgap, htr, hK⟩ := hsr
  refine .inr ?_
  have hPP := modulePlatform_le_wasi L G sp₀ top
  have hinv : (sysFn arm64Flags (shimLayout L.area G) I (fun j => R (l₀.length + j))
      Call.fdPrestatDirName).invoke st [.i32 a0, .i32 a1, .i32 a2] =
      dirNameInvoke I st [.i32 a0, .i32 a1, .i32 a2] := by
    simp (config := { decide := true }) only [sysFn, sysInvoke, ↓reduceIte]
  rw [hinv]
  have hpg := hst.pages
  have hcap := hst.cap_lt
  have hlim := hst.below
  have hstk2 := hstk.limit
  have hsz8 := Nat.mul_le_mul_right 65536 hpg.2
  have hG17 : q.core.x 17 + UInt64.ofNat (areaSize S.cap) = G.base := by rw [h17, hGa]
  have hsize8 : ∀ k < 8, (wasiPlatform L sp₀ top).normal (q.core.x 17 + UInt64.ofNat k) = true :=
    fun k hk => hPP.normal _ (hst.mapped k (by unfold areaSize; omega))
  have hflagN : (wasiPlatform L sp₀ top).normal
      (q.core.x 17 + UInt64.ofNat (areaSize S.cap) + 8) = true := by
    rw [hG17]
    exact hscr 8 (by decide)
  have hheldA : ∀ d : Nat, d < 2 ^ 32 →
      q.core.x 17 + UInt64.ofNat (areaSize S.cap) + UInt64.ofNat d + 16 =
        G.base + UInt64.ofNat (16 + d) := fun d _ => by
    rw [hG17, UInt64.add_assoc]
    congr 1
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.reducePow, UInt64.reduceToNat]
    omega
  have ha0 : a0.toUInt64 = UInt64.ofNat a0.toNat := by
    apply UInt64.toNat_inj.mp
    rw [UInt32.toNat_toUInt64, UInt64.toNat_ofNat']
    have := a0.toNat_lt
    simp only [Nat.reducePow] at *
    omega
  have hle1023 : a0.toUInt64 ≤ 1023 ↔ a0.toNat ≤ 1023 := by
    rw [UInt64.le_iff_toNat_le, UInt32.toNat_toUInt64]
    rfl
  have hheldN : q.core.x 0 ≤ 1023 → (wasiPlatform L sp₀ top).normal
      (q.core.x 17 + UInt64.ofNat (areaSize S.cap) + q.core.x 0 + 16) = true := fun h => by
    rw [x0] at h ⊢
    rw [ha0, hheldA a0.toNat a0.toNat_lt]
    exact hscr _ (by unfold scratchSize; have := hle1023.mp h; omega)
  have hsz : load64 q.core.mem (q.core.x 17) + 8 = UInt64.ofNat (st.mem.pages * 65536) := by
    rw [hst.size]
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.reducePow, UInt64.reduceToNat]
    omega
  have hend : q.core.x 1 + q.core.x 2 = UInt64.ofNat (a1.toNat + a2.toNat) := by
    rw [x1, x2]
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat', UInt32.toNat_toUInt64, Nat.reducePow]
    have := a1.toNat_lt
    have := a2.toNat_lt
    simp only [Nat.reducePow] at *
    omega
  have htrapIff : load64 q.core.mem (q.core.x 17) + 8 < q.core.x 1 + q.core.x 2 ↔
      st.mem.pages * 65536 < a1.toNat + a2.toNat := by
    rw [hsz, hend, UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat', UInt64.toNat_ofNat']
    have := a1.toNat_lt
    have := a2.toNat_lt
    simp only [Nat.reducePow] at *
    omega
  have hbufA : q.core.x 17 + q.core.x 1 + 1 + 4095 = q.core.x 17 + UInt64.ofNat (4096 + a1.toNat) := by
    rw [x1, UInt64.add_assoc, UInt64.add_assoc]
    congr 1
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat', UInt32.toNat_toUInt64, Nat.reducePow,
      UInt64.reduceToNat]
    omega
  have hbufN : ¬ load64 q.core.mem (q.core.x 17) + 8 < q.core.x 1 + q.core.x 2 →
      q.core.x 2 ≠ 0 → (wasiPlatform L sp₀ top).normal (q.core.x 17 + q.core.x 1 + 1 + 4095) =
        true := fun h h2 => by
    rw [hbufA]
    refine hPP.normal _ (hst.mapped _ ?_)
    rw [htrapIff] at h
    unfold areaSize
    have : a1.toNat < a1.toNat + a2.toNat := by
      rw [x2] at h2
      have : a2.toNat ≠ 0 := fun e => h2 (by
        apply UInt64.toNat_inj.mp
        rw [UInt32.toNat_toUInt64, e]
        rfl)
      omega
    omega
  have hbufU : ¬ load64 q.core.mem (q.core.x 17) + 8 < q.core.x 1 + q.core.x 2 →
      q.core.x 2 ≠ 0 → q.core.x 17 + q.core.x 1 + 1 + 4095 ≠ (wasiPlatform L sp₀ top).uart :=
    fun h _ e => by
      rw [hbufA] at e
      have := congrArg UInt64.toNat e
      rw [hst.toNat_addr (j := 4096 + a1.toNat) (by
        rw [htrapIff] at h
        unfold areaSize
        omega)] at this
      have hu : (wasiPlatform L sp₀ top).uart = 0 := rfl
      rw [hu] at this
      simp only [UInt64.toNat_zero] at this
      omega
  obtain ⟨t, rt, spt, iot, x17t, x18t, ht⟩ := run_dirNameStub (wasiPlatform L sp₀ top) code hg
    hcode hpc hsize8 hflagN hheldN hbufN hbufU
  simp only [dirNameInvoke]
  by_cases htrap : load64 q.core.mem (q.core.x 17) + 8 < q.core.x 1 + q.core.x 2
  · rw [if_pos htrap] at ht
    rw [if_neg (fun h => by have := htrapIff.mp htrap; omega)]
    exact ⟨{ q with core := t }, ProcRunWith.ofReach hf rt, iot, .inr (.inr (.inr ⟨rfl, ht⟩)),
      hf, htr⟩
  rw [if_neg htrap] at ht
  obtain ⟨pt, hret⟩ := ht
  have hin : a1.toNat + a2.toNat ≤ st.mem.pages * 65536 ∧ a1.toNat + a2.toNat < 2 ^ 32 := by
    have := htrapIff.not.mp htrap
    omega
  rw [if_pos hin]
  have hflag : q.core.mem (q.core.x 17 + UInt64.ofNat (areaSize S.cap) + 8) =
      if preopened I st.host.world.events then 1 else 0 := by
    rw [hG17]
    exact hK.preopen
  have hcode0 : ∀ v : UInt64, v.toNat < 2 ^ 32 → v.toUInt32.toUInt64 = v := fun v hv => by
    apply UInt64.toNat_inj.mp
    rw [UInt32.toNat_toUInt64, UInt64.toNat_toUInt32]
    omega
  have hmem0 : ∀ m : Mem, placeReply m (fun _ => []) (.returned 0 []) = m := fun _ => rfl
  by_cases hgr : a0.toUInt64 = 3 ∧ preopened I st.host.world.events = true
  · have hc : q.core.x 0 = 3 ∧
        q.core.mem (q.core.x 17 + UInt64.ofNat (areaSize S.cap) + 8) ≠ 0 :=
      ⟨by rw [x0]; exact hgr.1, by rw [hflag, if_pos hgr.2]; decide⟩
    rw [if_pos hc] at hret
    rw [if_pos hgr]
    by_cases h2 : q.core.x 2 = 0
    · rw [if_pos h2] at hret
      obtain ⟨xt0, mt⟩ := hret
      have hn : ¬ 1 ≤ a2.toNat := by
        rw [x2] at h2
        have := congrArg UInt64.toNat h2
        rw [UInt32.toNat_toUInt64] at this
        simp only [UInt64.reduceToNat] at this
        omega
      rw [if_neg hn]
      simp only [sysAnswer, sysResult]
      exact stub_returned hsr' rt pt spt iot x17t x18t xt0 (by decide)
        (fun b _ => by rw [mt]) (fun b _ => by rw [mt]) (StoreRel.regs hst x17t x18t mt) _
    · rw [if_neg h2] at hret
      obtain ⟨xt0, mt⟩ := hret
      have hn : 1 ≤ a2.toNat := by
        rw [x2] at h2
        refine Nat.one_le_iff_ne_zero.mpr fun e => h2 ?_
        apply UInt64.toNat_inj.mp
        rw [UInt32.toNat_toUInt64, e]
        rfl
      rw [if_pos hn]
      simp only [sysAnswer, sysResult]
      have hmt : t.mem = writeList q.core.mem (q.core.x 17 + UInt64.ofNat (4096 + a1.toNat))
          [46] := by
        rw [mt, hbufA]
        rfl
      have hbyte : a1.toNat < areaSize S.cap := by unfold areaSize; omega
      exact stub_returned hsr' rt pt spt iot x17t x18t xt0 (by decide)
        (fun b hb => by
          rw [hmt]
          refine writeList_below (lim := q.core.x 18) ?_ (by omega)
          rw [hst.toNat_addr (j := 4096 + a1.toNat) (by unfold areaSize; omega)]
          unfold areaSize at hlim
          simp only [List.length_cons, List.length_nil]
          omega)
        (fun b hb => by
          rw [hmt]
          exact store8_outside (hst.mapped _ (by unfold areaSize; omega)) hb)
        (hst.ofWriteList (modulePlatform L G) [46] (p := a1.toNat)
          (by simp only [List.length_cons, List.length_nil]; omega) x17t x18t hmt) _
  · have hc : ¬ (q.core.x 0 = 3 ∧
        q.core.mem (q.core.x 17 + UInt64.ofNat (areaSize S.cap) + 8) ≠ 0) := by
      rw [x0, hflag]
      intro h
      apply hgr
      refine ⟨h.1, ?_⟩
      cases hp : preopened I st.host.world.events
      · rw [hp] at h
        exact absurd rfl h.2
      · rfl
    rw [if_neg hc] at hret
    rw [if_neg hgr]
    have hlo : q.core.x 0 < 3 ↔ a0.toNat < 3 := by
      rw [x0, UInt64.lt_iff_toNat_lt, UInt32.toNat_toUInt64]
      rfl
    have hheld : (q.core.x 0 ≤ 1023 ∧ q.core.mem
        (q.core.x 17 + UInt64.ofNat (areaSize S.cap) + q.core.x 0 + 16) ≠ 0) ↔
        a0.toUInt64 ∈ openNumbers I st.host.world.events := by
      rw [x0]
      constructor
      · rintro ⟨hle, hb⟩
        have hd := hle1023.mp hle
        rw [ha0, hheldA a0.toNat a0.toNat_lt, hK.held a0.toNat (by unfold descriptorLimit; omega)]
          at hb
        rw [ha0]
        by_contra hm
        exact hb (by rw [if_neg hm])
      · intro hm
        have hd := openNumbers_lt hm
        rw [UInt32.toNat_toUInt64] at hd
        unfold descriptorLimit at hd
        refine ⟨hle1023.mpr (by omega), ?_⟩
        rw [ha0, hheldA a0.toNat a0.toNat_lt, hK.held a0.toNat (by unfold descriptorLimit; omega)]
        rw [ha0] at hm
        rw [if_pos hm]
        decide
    by_cases h54 : a0.toNat < 3 ∨ a0.toUInt64 ∈ openNumbers I st.host.world.events
    · rw [if_pos (by
        rcases h54 with h | h
        · exact .inl (hlo.mpr h)
        · exact .inr (hheld.mpr h))] at hret
      obtain ⟨xt0, mt⟩ := hret
      rw [if_pos (by simpa using h54)]
      simp only [sysAnswer, sysResult]
      exact stub_returned hsr' rt pt spt iot x17t x18t xt0 (by decide)
        (fun b _ => by rw [mt]) (fun b _ => by rw [mt]) (StoreRel.regs hst x17t x18t mt) _
    · rw [if_neg (fun h => h54 (h.elim (fun h => .inl (hlo.mp h)) (fun h => .inr (hheld.mp h))))]
        at hret
      obtain ⟨xt0, mt⟩ := hret
      rw [if_neg (by simpa using h54)]
      simp only [sysAnswer, sysResult]
      exact stub_returned hsr' rt pt spt iot x17t x18t xt0 (by decide)
        (fun b _ => by rw [mt]) (fun b _ => by rw [mt]) (StoreRel.regs hst x17t x18t mt) _

/-- The flat call of `shimCalls` whose name is that of a prestat function. -/
theorem shimCall_preopen {c : Call} (hc : c ∈ shimCalls) :
    (c.name = "fd_prestat_get" → c = Call.fdPrestatGet) ∧
      (c.name = "fd_prestat_dir_name" → c = Call.fdPrestatDirName) := by
  revert c
  decide

/-- The code of a stub of `preopenStubs` at `a`, generated with the trap stub and the scratch
`areaSize S.cap` bytes above the area, stands for the shim's function of the call `c` of
`shimCalls` whose import is the stub's, when the scratch lies at the area's end and in the data
segment.  `flatStub_sim` takes its cases for these stubs from here. -/
theorem preopenStub_sim {s : FlatStub} (hs : s ∈ preopenStubs) {c : Call} (hc : c ∈ shimCalls)
    (hd : ABI.callImport c = s.decl) (S : Shared) (n : Nat) {a svc en : UInt64}
    {is : List Instr} (hg : s.gen a svc S.trapUnreachable en (areaSize S.cap) = .ok is)
    (hcode : CodeAt code a is) (hGb : G.base = L.area + UInt64.ofNat (areaSize S.cap))
    (hdata : areaSize S.cap + scratchSize ≤ L.dataMem) :
    (shimMachine R L G I sp₀ top l₀ calls code hdom hk hk18 hL hG base size).StubSim S n
      s.decl.params s.decl.results
      (sysFn arm64Flags (shimLayout L.area G) I (fun j => R (l₀.length + j)) c) a := by
  have hn : c.name = s.decl.name := congrArg ImportDecl.name hd
  have hscr := scratch_wasi (sp := sp₀) (top := top) hL hGb hdata
  obtain ⟨n1, n2⟩ := shimCall_preopen hc
  simp only [preopenStubs, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · obtain rfl := n1 hn
    exact prestatStub_sim S n hg hcode hGb hscr
  · obtain rfl := n2 hn
    exact dirNameStub_sim S n hg hcode hGb hscr

end Verified.ShimA64
