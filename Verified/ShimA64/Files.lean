import Verified.ShimA64.Stubs
import LeanExe.A64.Proof.WasiFiles

/-!
The stubs of `fd_close` and of `fd_read` and `fd_write` on a handle against the shim's host
environment: each stub of `LeanExe/A64/WasiFiles.lean` meets `Machine.StubSim` for its function of
`linuxEnv` on `shimMachine`.  The stubs read and write the shim's scratch, which lies outside the
module's platform, so their runs lie on the process's platform `wasiPlatform`, and each statement
takes the scratch's place, `areaSize` bytes above the area, and its bytes' being Normal memory
there.  The byte of a descriptor number in the scratch is nonzero exactly when the shim holds the
number (`held_byte`), so a stub's test of the byte decides membership in `openNumbers`.  A request
that the specification's function refuses reaches the trap stub with the store unchanged, or
returns errno 8 for a number that the shim does not hold.  An accepted one reaches `SVC #0` with
the call whose event the specification's function records, and the result reaches the return
with the WASI reply or the trap stub.  At a return the scratch's bytes follow `openNumbers` and
`preopened` of the world's new events: a `close` clears the number's byte, and the preopen flag
for descriptor 3, whatever its result (`ScratchHolds.close`), and a `read` or `write` changes
neither (`ScratchHolds.quiet`).
-/

namespace Verified.ShimA64

open Wasm LeanExe LeanExe.A64 LeanExe.Wasi Verified.Wasi Verified.Shim

/-! ## The scratch's bytes -/

theorem mem_openNumbers_lt {I : Launch} {events : List Linux.Event} {x : UInt64}
    (h : x ∈ openNumbers I events) : x.toNat < descriptorLimit := by
  unfold openNumbers at h
  simpa using (List.mem_filter.mp h).2

/-- The address of the byte of descriptor number `d`. -/
theorem held_addr (G : Scratch) (d : UInt64) :
    G.held d.toNat = G.base + d + 16 := by
  unfold Scratch.held
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.reduceToNat, Nat.reducePow]
  omega

/-- The shim holds the number `d` exactly when it lies at most 1,023 and its byte in the scratch
is nonzero. -/
theorem held_byte {G : Scratch} {I : Launch} {sp₀ top : UInt64} {events : List Linux.Event}
    {mem : UInt64 → UInt8} (h : ScratchHolds G I sp₀ top events mem) (d : UInt64) :
    (d ≤ 1023 ∧ mem (G.base + d + 16) ≠ 0) ↔ d ∈ openNumbers I events := by
  by_cases hlo : d ≤ 1023
  · have hlt : d.toNat < descriptorLimit := by
      rw [UInt64.le_iff_toNat_le] at hlo
      unfold descriptorLimit
      simp only [UInt64.reduceToNat] at hlo
      omega
    have hb := h.held d.toNat hlt
    rw [held_addr G d, UInt64.ofNat_toNat] at hb
    rw [hb]
    by_cases hm : d ∈ openNumbers I events
    · simp [hm, hlo]
    · simp [hm]
  · refine ⟨fun h' => absurd h'.1 hlo, fun hm => absurd ?_ hlo⟩
    have := mem_openNumbers_lt hm
    unfold descriptorLimit at this
    rw [UInt64.le_iff_toNat_le]
    simp only [UInt64.reduceToNat]
    omega

/-- Two bytes of the scratch at different offsets have different addresses. -/
theorem scratch_ne {G : Scratch} {i j : Nat}
    (hi : i < scratchSize) (hj : j < scratchSize) (hij : i ≠ j) :
    G.base + UInt64.ofNat i ≠ G.base + UInt64.ofNat j := by
  intro same
  apply hij
  have := congrArg UInt64.toNat same
  unfold scratchSize at hi hj
  simp only [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.reducePow] at this
  omega

/-- A `close` of a number that the shim holds keeps the scratch's relation to the shim's
descriptor state when the memory clears the number's byte, and the preopen flag for descriptor 3,
and keeps every other byte. -/
theorem ScratchHolds.close {G : Scratch} {I : Launch} {sp₀ top : UInt64}
    {events : List Linux.Event} {mem mem' : UInt64 → UInt8} {e : Linux.Event} {d : UInt64}
    (h : ScratchHolds G I sp₀ top events mem) (hclose : e.call = Linux.closeCall)
    (harg : Linux.arg e.args 0 = d) (hd : d.toNat < descriptorLimit)
    (hlow : G.base.toNat + scratchSize ≤ 2 ^ 32)
    (hmem : mem' = if d = 3 then store8 (store8 mem (G.held d.toNat) 0) G.preopen 0
      else store8 mem (G.held d.toNat) 0) :
    ScratchHolds G I sp₀ top (events ++ [e]) mem' := by
  unfold descriptorLimit at hd
  obtain ⟨hn, hp⟩ := openNumbers_append_close I events hclose harg (by omega)
  have hG : G.base.toNat + scratchSize ≤ 2 ^ 64 := by omega
  -- the bytes that the close keeps
  have keep : ∀ a, a ≠ G.held d.toNat → a ≠ G.preopen → mem' a = mem a := by
    intro a h1 h2
    rw [hmem]
    split
    · rw [store8_other _ _ _ _ h2, store8_other _ _ _ _ h1]
    · rw [store8_other _ _ _ _ h1]
  have offset : ∀ j < scratchSize, (G.base + UInt64.ofNat j).toNat = G.base.toNat + j := by
    intro j hj
    unfold scratchSize at hj hG
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.reducePow] at hG ⊢
    omega
  have heldNe : ∀ j < 1040, j ≠ 16 + d.toNat → G.base + UInt64.ofNat j ≠ G.held d.toNat :=
    fun j hj hjd => scratch_ne (by unfold scratchSize; omega) (by unfold scratchSize; omega) hjd
  have flagNe : ∀ j < 1040, j ≠ 8 → G.base + UInt64.ofNat j ≠ G.preopen :=
    fun j hj hj8 => scratch_ne (by unfold scratchSize; omega) (by unfold scratchSize; decide)
      hj8
  refine ⟨?_, h.stack.congr fun a ha => keep a ?_ ?_, ?_, fun j hj => ?_⟩
  · rw [← h.saved]
    apply load64_congr
    intro k hk
    exact keep _ (heldNe k (by omega) (by omega)) (flagNe k (by omega) (by omega))
  · intro same
    rw [same, Scratch.held, offset _ (by unfold scratchSize; omega)] at ha
    unfold scratchSize at hlow
    omega
  · intro same
    rw [same, Scratch.preopen, show (8 : UInt64) = UInt64.ofNat 8 from rfl,
      offset _ (by unfold scratchSize; decide)] at ha
    unfold scratchSize at hlow
    omega
  · rw [hp]
    by_cases h3 : d = 3
    · rw [hmem, ite_eq_left h3]
      simp [store8, h3]
    · have hne : G.preopen ≠ G.held d.toNat := heldNe 8 (by decide) (by omega)
      rw [hmem, ite_eq_right h3, store8_other _ _ _ _ hne, h.preopen]
      simp [h3]
  · by_cases hj' : j = d.toNat
    · subst hj'
      have hz : mem' (G.held d.toNat) = 0 := by
        rw [hmem]
        split
        · have hne : G.held d.toNat ≠ G.preopen := flagNe (16 + d.toNat) (by omega) (by omega)
          simp [store8, hne]
        · simp [store8]
      have hnot : d ∉ openNumbers I (events ++ [e]) := fun h' => ((hn d).mp h').1 rfl
      rw [hz, UInt64.ofNat_toNat]
      simp [hnot]
    · unfold descriptorLimit at hj
      have hk := keep (G.held j) (heldNe (16 + j) (by omega) (by omega))
        (flagNe (16 + j) (by omega) (by omega))
      rw [hk, h.held j (by unfold descriptorLimit; omega)]
      have hjd : UInt64.ofNat j ≠ d := fun same => hj' (by
        rw [← same, UInt64.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (show j < 1024 by omega)
          (by decide))])
      simp only [hn, ne_eq, hjd, not_false_eq_true, true_and]

/-! ## Memory outside the area -/

/-- The store relation holds after code that keeps X17, X18, and the area's bytes. -/
theorem StoreRel.congrArea {P : Platform} {cap : Nat} {gts : List ValueType} {α : Type}
    {st : Store α} {s s' : State} (h : StoreRel P cap gts st s) (h17 : s'.x 17 = s.x 17)
    (h18 : s'.x 18 = s.x 18)
    (hmem : ∀ j < areaSize cap, s'.mem (s.x 17 + UInt64.ofNat j) = s.mem (s.x 17 + UInt64.ofNat j)) :
    StoreRel P cap gts st s' := by
  have hgl := h.types.length
  have hg := h.glen
  refine ⟨h.caps, h.cap_lt, h.glen, h.pages, ?_, h.types, ?_, ?_, ?_, ?_⟩
  · rw [h17, load64_congr (m := s'.mem) (m' := s.mem) fun k hk =>
      hmem k (by unfold areaSize; omega)]
    exact h.size
  · intro i hi
    rw [h17, load64_congr (m := s'.mem) (m' := s.mem) fun k hk => by
      rw [add_ofNat_add]
      exact hmem _ (by unfold areaSize; omega)]
    exact h.globals i hi
  · intro j hj
    rw [h17, hmem _ (by unfold areaSize; omega)]
    exact h.bytes j hj
  · intro j hj
    rw [h17]
    exact h.mapped j hj
  · rw [h17, h18]
    exact h.below

/-- `m'` keeps every byte of `m` outside the scratch `G`. -/
def ScratchOnly (G : Scratch) (m m' : UInt64 → UInt8) : Prop :=
  ∀ a : UInt64, (a.toNat < G.base.toNat ∨ G.base.toNat + scratchSize ≤ a.toNat) → m' a = m a

theorem ScratchOnly.refl (G : Scratch) (m : UInt64 → UInt8) : ScratchOnly G m m :=
  fun _ _ => rfl

theorem ScratchOnly.trans {G : Scratch} {m m' m'' : UInt64 → UInt8} (h : ScratchOnly G m m')
    (h' : ScratchOnly G m' m'') : ScratchOnly G m m'' :=
  fun a ha => (h' a ha).trans (h a ha)

theorem ScratchOnly.store8 {G : Scratch} (m : UInt64 → UInt8) {j : Nat} (v : UInt8)
    (hj : j < scratchSize) (hG : G.base.toNat + scratchSize < 2 ^ 64) :
    ScratchOnly G m (store8 m (G.base + UInt64.ofNat j) v) := by
  intro a ha
  have e : (G.base + UInt64.ofNat j).toNat = G.base.toNat + j := by
    unfold scratchSize at hj hG
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.reducePow] at hG ⊢
    omega
  refine store8_other _ _ _ _ fun same => ?_
  rw [same, e] at ha
  omega

/-- A memory that differs from the process's only in the scratch, which follows the area, keeps the
store relation and every byte from the stack's limit up. -/
theorem ScratchOnly.storeRel {P : Platform} {cap : Nat} {gts : List ValueType} {α : Type}
    {st : Store α} {s s' : State} {G : Scratch} (h : StoreRel P cap gts st s)
    (hGb : G.base = s.x 17 + UInt64.ofNat (areaSize cap)) (h17 : s'.x 17 = s.x 17)
    (h18 : s'.x 18 = s.x 18) (hm : ScratchOnly G s.mem s'.mem) : StoreRel P cap gts st s' := by
  have hb := h.below
  have h18lt := (s.x 18).toNat_lt
  refine StoreRel.congrArea h h17 h18 fun j hj => hm _ (.inl ?_)
  have e1 := h.toNat_addr (Nat.le_of_lt hj)
  have e2 := h.toNat_addr (j := areaSize cap) (Nat.le_refl _)
  rw [hGb]
  omega

theorem ScratchOnly.high {G : Scratch} {m m' : UInt64 → UInt8} (hm : ScratchOnly G m m')
    {lim : UInt64} (hlim : G.base.toNat + scratchSize ≤ lim.toNat) {a : UInt64}
    (ha : lim.toNat ≤ a.toNat) : m' a = m a :=
  hm a (.inr (by omega))

/-! ## A stub's end -/

variable {R : Linux.Replies} {L : ElfLayout} {G : Scratch} {I : Launch} {sp₀ top : UInt64}
  {l₀ : List Linux.Event} {calls : List LeanExe.Wasi.Call} {code : UInt64 → Option UInt32}
  {hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55}
  {hk : ∀ a w i, code a = some w → decode w = some i → i.keepsX17 = true}
  {hk18 : ∀ a w i, code a = some w → decode w = some i → i.keepsX18 = true}
  {hL : L.area.toNat + L.dataMem ≤ 2 ^ 32} {hG : G.base.toNat + scratchSize < 2 ^ 64}
  {base : UInt64} {size : Nat}

/-- A run of the process to the return address with an `i32` in X0, SP, X18, and the UART's state
kept, and the memory kept from SP up, ends the stub with that value and a store that the final
state holds. -/
theorem shim_return {S : Shared} {n : Nat} {st' : Store (Observed LinuxWorld)} {q q' : Proc}
    {v : UInt32}
    (hr : ProcRunWith Linux.table R (wasiPlatform L sp₀ top) code q q')
    (hpc : q'.core.pc = q.core.x 30) (hsp : q'.core.sp = q.core.sp)
    (h18 : q'.core.x 18 = q.core.x 18) (hio : q'.core.io = q.core.io)
    (hmem : ∀ a : UInt64, q.core.sp.toNat ≤ a.toNat → q'.core.mem a = q.core.mem a)
    (hx0 : q'.core.x 0 = v.toUInt64)
    (hsr : (shimMachine R L G I sp₀ top l₀ calls code hdom hk hk18 hL hG base size).SR S.cap
      S.globalTypes st' q') :
    (shimMachine R L G I sp₀ top l₀ calls code hdom hk hk18 hL hG base size).StubResult S n [.i32]
      (.Return [.i32 v] st') q := by
  refine .inr ⟨q', hr, ⟨hpc, hsp, h18, hio, fun a ha => hmem a (by
    have h' := ha
    simp only [Nat.mul_zero, Nat.add_zero] at h'
    exact h'), by simp,
    ⟨by simp, fun k hk => ?_⟩, by simp [Typed, HasType]⟩, hsr⟩
  simp only [List.take_succ_cons, List.take_zero, List.length_cons, List.length_nil] at hk
  have hk0 : k = 0 := by omega
  subst hk0
  exact hx0

/-- A run of the process to the trap stub with FPCR at `fpcrValue` and the UART's state kept ends
the stub in a trap of the shim with a store whose events the trace holds. -/
theorem shim_trap {S : Shared} {n : Nat} {rs : List ValueType} {st' : Store (Observed LinuxWorld)}
    {q q' : Proc}
    (hr : ProcRunWith Linux.table R (wasiPlatform L sp₀ top) code q q')
    (hio : q'.core.io = q.core.io) (hpc : q'.core.pc = S.trapUnreachable)
    (hf : q'.fpcr = fpcrValue) (htr : TraceRel l₀ (shimLayout L.area G) size st'.host q'.trace) :
    (shimMachine R L G I sp₀ top l₀ calls code hdom hk hk18 hL hG base size).StubResult S n rs
      (.Trap st' shimTrap) q :=
  .inr ⟨q', hr, hio, .inr (.inr (.inr ⟨rfl, hpc⟩)), hf, htr⟩

/-- The scratch's address as a number, when the data segment holds the area and the scratch and
ends below `2^32`. -/
theorem scratch_toNat {G : Scratch} {cap : Nat} (hL : L.area.toNat + L.dataMem ≤ 2 ^ 32)
    (hGb : G.base = L.area + UInt64.ofNat (areaSize cap))
    (hdata : areaSize cap + scratchSize ≤ L.dataMem) :
    G.base.toNat = L.area.toNat + areaSize cap := by
  rw [hGb]
  simp only [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.reducePow]
  unfold scratchSize at hdata
  omega

/-- The scratch's bytes are Normal memory of the data segment, which ends below `2^32`. -/
theorem scratch_normal {G : Scratch} {cap : Nat} (hL : L.area.toNat + L.dataMem ≤ 2 ^ 32)
    (hGb : G.base = L.area + UInt64.ofNat (areaSize cap))
    (hdata : areaSize cap + scratchSize ≤ L.dataMem) :
    ∀ j < scratchSize, (elfPlatform L).normal (G.base + UInt64.ofNat j) = true := by
  intro j hj
  have e := scratch_toNat hL hGb hdata
  have e' : (G.base + UInt64.ofNat j).toNat = G.base.toNat + j := by
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.reducePow]
    unfold scratchSize at hj hdata
    omega
  simp only [elfPlatform, decide_eq_true_eq, UInt64.le_iff_toNat_le, e']
  unfold scratchSize at hj hdata
  omega

/-- The UART of the process's platform is no Normal memory when the module's is not, the scratch
follows the area, and the initial stack lies from `2^32` up. -/
theorem wasiPlatform_uart {G : Scratch} {cap : Nat}
    (hU : (modulePlatform L G).normal (modulePlatform L G).uart = false)
    (hGb : G.base = L.area + UInt64.ofNat (areaSize cap))
    (hsp : 2 ^ 32 ≤ sp₀.toNat) :
    (wasiPlatform L sp₀ top).normal (wasiPlatform L sp₀ top).uart = false := by
  have hm : (modulePlatform L G).normal 0 = false := hU
  have he : (elfPlatform L).normal 0 = false := by
    cases hE : (elfPlatform L).normal 0 with
    | false => rfl
    | true =>
      exfalso
      have hin : decide (G.base ≤ 0 ∧ (0 : UInt64).toNat < G.base.toNat + scratchSize) =
          true := by
        simp only [modulePlatform, hE, Bool.true_and, Bool.not_eq_false'] at hm
        exact hm
      simp only [elfPlatform, decide_eq_true_eq, UInt64.le_iff_toNat_le] at hE
      simp only [decide_eq_true_eq, UInt64.le_iff_toNat_le] at hin
      have hb := congrArg UInt64.toNat hGb
      simp only [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.reducePow] at hb
      unfold areaSize at hb
      simp only [UInt64.reduceToNat] at hE hin
      omega
  show ((elfPlatform L).normal 0 || decide (sp₀ ≤ 0 ∧ (0 : UInt64) < top)) = false
  rw [he, Bool.false_or, decide_eq_false_iff_not]
  intro h
  have := h.1
  rw [UInt64.le_iff_toNat_le] at this
  simp only [UInt64.reduceToNat] at this
  omega

/-! ## `fd_close` -/

theorem sysFn_close (F : OpenFlags) (L : ShimLayout) (I : Launch) (replies : Linux.Replies)
    (st : Store (Observed LinuxWorld)) (args : List Value) :
    (sysFn F L I replies Call.fdClose).invoke st args = closeInvoke I replies st args := by
  simp (config := { decide := true }) only [sysFn, sysInvoke, ↓reduceIte]

/-- The stub of `fd_close` stands for the shim's `fd_close`. -/
theorem closeStub_sim (S : Shared) (n : Nat) {cl svc en : UInt64} {is : List Instr}
    (hg : closeStub cl svc S.trapUnreachable en (areaSize S.cap) = .ok is)
    (hcode : CodeAt code cl is) (hsvc : OpsAt code svc [.svc, .ins (.ret 30)])
    (hen : CodeAt code en errnoRoutine)
    (hGb : G.base = L.area + UInt64.ofNat (areaSize S.cap))
    (hdata : areaSize S.cap + scratchSize ≤ L.dataMem)
    (hU' : (modulePlatform L G).normal (modulePlatform L G).uart = false) :
    (shimMachine R L G I sp₀ top l₀ calls code hdom hk hk18 hL hG base size).StubSim S n [.i32]
      [.i32] (sysFn arm64Flags (shimLayout L.area G) I (fun j => R (l₀.length + j)) Call.fdClose)
      cl := by
  intro st args q hlen hty hpc hstk hsr hregs
  change Proc at q
  change q.core.pc = cl at hpc
  change StackOk (modulePlatform L G) q.core at hstk
  obtain ⟨fd, rfl⟩ : ∃ fd : UInt32, args = [.i32 fd] := by
    match args, hlen, hty with
    | [v], _, ⟨t, _⟩ => cases v <;> first | exact ⟨_, rfl⟩ | exact t.elim
  have x0 : q.core.x 0 = fd.toUInt64 := hregs 0 (by simp)
  have hsr' := hsr
  obtain ⟨hst, hf, h17, hgap, htr, hK⟩ := hsr
  rw [sysFn_close]
  have hscr := scratch_normal hL hGb hdata
  have hlow : G.base.toNat + scratchSize ≤ 2 ^ 32 := by
    rw [scratch_toNat hL hGb hdata]
    omega
  have hU := wasiPlatform_uart (sp₀ := sp₀) (top := top) hU' hGb hK.stack.above
  have hPP := elfPlatform_le_wasi L sp₀ top
  have hscrP : ∀ j < scratchSize, (wasiPlatform L sp₀ top).normal (G.base + UInt64.ofNat j) =
      true := fun j hj => hPP.normal _ (hscr j hj)
  have hbase : q.core.x 17 + UInt64.ofNat (areaSize S.cap) = G.base := by rw [h17, hGb]
  obtain ⟨u1, r1, sp1, m1, io1, x17_1, x18_1, hc1⟩ :=
    run_closeFront (wasiPlatform L sp₀ top) code hg hcode hpc (fun hle => by
      rw [x0] at hle
      rw [hbase, x0, ← held_addr G fd.toUInt64]
      refine hscrP _ ?_
      rw [UInt64.le_iff_toNat_le] at hle
      simp only [UInt64.reduceToNat] at hle
      unfold scratchSize
      omega)
  rw [hbase, x0] at hc1
  simp only [closeInvoke]
  by_cases hheld : fd.toUInt64 ∈ openNumbers I st.host.world.events
  swap
  · rw [ite_eq_right (mt (held_byte hK _).mp hheld)] at hc1
    rw [ite_eq_right hheld]
    obtain ⟨p1, x01⟩ := hc1
    simp only [sysAnswer, sysResult]
    refine shim_return (ProcRunWith.ofReach hf r1) p1 sp1 x18_1 io1 (fun a _ => by
      show u1.mem a = q.core.mem a
      rw [m1]) (by rw [x01]; rfl) ⟨StoreRel.withHost (hst.regs x17_1 x18_1 m1) _, hf, ?_, ?_,
        ⟨?_, ?_⟩, ?_⟩
    · show u1.x 17 = L.area
      rw [x17_1, h17]
    · show _ ≤ (u1.x 18).toNat
      rw [x18_1]
      exact hgap
    · show q.trace = _
      rw [htr.1]
      simp [answered, LinuxWorld.answer]
    · intro e he
      simp only [answered, LinuxWorld.answer, List.append_nil] at he
      exact htr.2 e he
    · show ScratchHolds G I sp₀ top (st.host.world.events ++ []) u1.mem
      rw [List.append_nil, m1]
      exact hK
  rw [ite_eq_left ((held_byte hK _).mpr hheld)] at hc1
  rw [ite_eq_left hheld]
  obtain ⟨p1, x01, x81, x161, x191, x211, x301⟩ := hc1
  have hd : fd.toUInt64.toNat < descriptorLimit := mem_openNumbers_lt hheld
  -- the call
  obtain ⟨held, tail, g13, g17, g19, hh, ht, h13, h17', h19, his⟩ := closeStub_ok hg
  obtain ⟨e1, e4, he1, he4, rfl⟩ := heldTest_ok hh
  obtain ⟨t2, t4, ht2, ht4, rfl⟩ := errnoTail_ok ht
  have cbl : code (after cl 13) = some (encode (.bl g13)) := by
    have := hcode 13 (by rw [his]; simp [scratchAddr, movImm])
    simpa [his, scratchAddr, movImm] using this
  obtain ⟨w14, cnext⟩ : ∃ w, code (after cl 14) = some w :=
    ⟨_, hcode 14 (by rw [his]; simp [scratchAddr, movImm])⟩
  have hnext : (after (after cl 13) 1).toNat < 2 ^ 55 := by
    rw [after_after]
    exact hdom _ _ cnext
  have hT : Linux.table.find? (fun c => c.arm64 == ({ q with core := u1 } : Proc).core.x 8) =
      some Linux.closeCall := by
    show Linux.table.find? (fun c => c.arm64 == u1.x 8) = _
    rw [x81]
    exact table_close
  obtain ⟨q5, rq5, p5, x05, x305, k5, sp5, m5, io5, f5, tr5⟩ :=
    run_callSvc (T := Linux.table) (R := R) (P := wasiPlatform L sp₀ top) (code := code) hsvc cbl
      h13 hdom hnext (p := { q with core := u1 }) p1 hT rfl sysCall_close
  simp only [Proc.call_trace, Proc.call_mem] at x05 m5 tr5
  rw [Proc.call_x _ _ _ (by decide)] at tr5
  have hlenk : q.trace.length = l₀.length + st.host.world.events.length := by
    rw [htr.1, List.length_map, List.length_append]
  change q5.core.x 0 = (R q.trace.length).ret at x05
  rw [hlenk] at x05 tr5
  generalize hRk : R (l₀.length + st.host.world.events.length) = rk at x05 tr5 ⊢
  change q5.trace = q.trace ++ [A64.Event.sys ⟨Linux.closeCall, [u1.x 0], [], [], rk.ret, []⟩]
    at tr5
  rw [x01] at tr5
  have hev : (⟨Linux.closeCall, [fd.toUInt64], [], [], rk.ret, []⟩ : Linux.Event) =
      closeEvent fd.toUInt64 rk := rfl
  rw [hev] at tr5
  have hf5 : q5.fpcr = fpcrValue := by rw [f5]; exact hf
  -- the result
  have q5x16 : q5.core.x 16 = G.base := by rw [k5 16 (by decide) (by decide)]; exact x161
  have q5x21 : q5.core.x 21 = fd.toUInt64 := by rw [k5 21 (by decide) (by decide)]; exact x211
  have q5x19 : q5.core.x 19 = q.core.x 30 := by rw [k5 19 (by decide) (by decide)]; exact x191
  have hbyteP : (wasiPlatform L sp₀ top).normal (q5.core.x 16 + q5.core.x 21 + 16) = true := by
    rw [q5x16, q5x21, ← held_addr G fd.toUInt64]
    exact hscrP _ (by unfold scratchSize; unfold descriptorLimit at hd; omega)
  have hflagP : (wasiPlatform L sp₀ top).normal (q5.core.x 16 + 8) = true := by
    rw [q5x16]
    exact hscrP 8 (by unfold scratchSize; decide)
  obtain ⟨u6, r6, sp6, io6, x176, x186, m6, hc6⟩ :=
    run_closeBack (wasiPlatform L sp₀ top) code hg hcode hen (s := q5.core)
      (by rw [p5, after_after]) hbyteP hflagP hU
  rw [q5x19, x05] at hc6
  rw [q5x16, q5x21, m5] at m6
  change u6.mem = if fd.toUInt64 = 3 then store8 (store8 u1.mem (G.base + fd.toUInt64 + 16) 0)
    (G.base + 8) 0 else store8 u1.mem (G.base + fd.toUInt64 + 16) 0 at m6
  rw [m1] at m6
  have hrch : (shimMachine R L G I sp₀ top l₀ calls code hdom hk hk18 hL hG base size).Rch q
      { q5 with core := u6 } :=
    ProcRunWith.trans hdom (ProcRunWith.ofReach hf r1)
      (ProcRunWith.trans hdom (ProcRunWith.ofWith rq5 hf5) (ProcRunWith.ofReach hf5 r6))
  have hio6 : u6.io = q.core.io := by rw [io6, io5]; show u1.io = _; exact io1
  have hsp6 : u6.sp = q.core.sp := by rw [sp6, sp5]; show u1.sp = _; exact sp1
  have h176 : u6.x 17 = L.area := by
    rw [x176, k5 17 (by decide) (by decide)]
    show u1.x 17 = _
    rw [x17_1, h17]
  have h186 : u6.x 18 = q.core.x 18 := by
    rw [x186, k5 18 (by decide) (by decide)]
    exact x18_1
  have hm6 : ScratchOnly G q.core.mem u6.mem := by
    rw [m6]
    have s1 := ScratchOnly.store8 (G := G) q.core.mem (j := 16 + fd.toUInt64.toNat) 0
      (by unfold scratchSize; unfold descriptorLimit at hd; omega) hG
    rw [show G.base + UInt64.ofNat (16 + fd.toUInt64.toNat) = G.base + fd.toUInt64 + 16 from
      held_addr G fd.toUInt64] at s1
    split
    · exact s1.trans (ScratchOnly.store8 (G := G) _ (j := 8) 0 (by unfold scratchSize; decide) hG)
    · exact s1
  have htrace : ({ q5 with core := u6 } : Proc).trace =
      (l₀ ++ (st.host.world.events ++ [closeEvent fd.toUInt64 rk])).map A64.Event.sys := by
    show q5.trace = _
    rw [tr5, htr.1]
    simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc]
  have hwithin : ∀ e ∈ st.host.world.events ++ [closeEvent fd.toUInt64 rk],
      WritesNative (shimLayout L.area G) size e := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact htr.2 e he
    · obtain rfl := List.mem_singleton.mp he
      refine .inl fun g hg => ?_
      change g ∈ Linux.outputRegions [fd.toUInt64] 0 Linux.closeCall.params at hg
      rw [(Linux.regions_close (a64Memory (wasiPlatform L sp₀ top)) q.core.mem fd.toUInt64).2]
        at hg
      cases hg
  have hK6 : ScratchHolds G I sp₀ top (st.host.world.events ++ [closeEvent fd.toUInt64 rk])
      u6.mem := by
    refine hK.close (d := fd.toUInt64) rfl rfl hd hlow ?_
    rw [m6, held_addr G fd.toUInt64]
    rfl
  have hbaseNat : G.base.toNat = L.area.toNat + areaSize S.cap := by
    rw [← hbase, hst.toNat_addr (Nat.le_refl _), h17]
  have hst6 : StoreRel (modulePlatform L G) S.cap S.globalTypes st u6 :=
    ScratchOnly.storeRel hst hbase.symm (by rw [h176, h17]) h186 hm6
  have hframe : ∀ a : UInt64, q.core.sp.toNat ≤ a.toNat → u6.mem a = q.core.mem a := fun a ha =>
    hm6.high (lim := q.core.x 18) (by rw [hbaseNat]; exact hgap) (by have := hstk.limit; omega)
  have hgap6 : L.area.toNat + areaSize S.cap + scratchSize ≤ (u6.x 18).toNat := by
    rw [h186]
    exact hgap
  have hsr6 : ∀ ev, (shimMachine R L G I sp₀ top l₀ calls code hdom hk hk18 hL hG base size).SR
      S.cap S.globalTypes (answered st st.mem [closeEvent fd.toUInt64 rk] ev)
      { q5 with core := u6 } :=
    fun ev => ⟨StoreRel.withHost hst6 _, hf5, h176, hgap6, ⟨htrace, hwithin⟩, hK6⟩
  have hret : (closeEvent fd.toUInt64 rk).ret = rk.ret := rfl
  simp only [hret, sysAnswer]
  rcases hc6 with ⟨h0, p6, x06⟩ | ⟨h0, h4095, p6, x06⟩ | ⟨h0, hbig, p6⟩
  · have hrep : closeReply rk.ret = .returned 0 [] := by simp [closeReply, h0]
    rw [hrep]
    exact shim_return hrch p6 hsp6 h186 hio6 hframe (by rw [x06]; rfl) (hsr6 _)
  · have hErr : Linux.isError rk.ret = true :=
      (isError_iff (c := 0) (by decide) (UInt64.pos_iff_ne_zero.mpr h0)).mpr h4095
    have hrep : closeReply rk.ret = .returned (errnoOf (0 - rk.ret)) [] := by
      simp [closeReply, h0, hErr]
    rw [hrep]
    exact shim_return hrch p6 hsp6 h186 hio6 hframe
      (by rw [x06, errno_toUInt64, errnoOf_lookup]) (hsr6 _)
  · have hErr : Linux.isError rk.ret = false := by
      cases h : Linux.isError rk.ret with
      | false => rfl
      | true =>
        exact absurd ((isError_iff (c := 0) (by decide)
          (UInt64.pos_iff_ne_zero.mpr h0)).mp h) (UInt64.not_le.mpr hbig)
    have hrep : closeReply rk.ret = .trapped shimTrap [] := by
      simp [closeReply, h0, hErr]
    rw [hrep]
    exact shim_trap hrch hio6 p6 hf5 ⟨htrace, hwithin⟩

end Verified.ShimA64
