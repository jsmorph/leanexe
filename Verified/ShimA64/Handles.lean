import Verified.ShimA64.Files

/-!
The stub of `fd_read` and `fd_write` on a handle against the shim's host environment:
`handleStub` of `LeanExe/A64/WasiFiles.lean` meets `Machine.StubSim` on `shimMachine` for
`handleReadInvoke` with the call number 63 and for `handleWriteInvoke` with 64.  The stub reads
the scratch's byte of the descriptor, so its runs lie on the process's platform `wasiPlatform`, as
those of the stub of `fd_close` do.  `run_handleChecked` states the stub's run to the call in the
words of the specification: the checks of the iovec count, the iovec, the buffer, and the count's
pointer against the memory's size are those of `handleReadInvoke` (`StoreRel.handleChecks`), and
the iovec's two halves are `read32` of the guest's memory at the iovec and 4 bytes above it
(`StoreRel.iovec`).

A request that fails a check reaches the trap stub with the store unchanged, and a descriptor that
the shim does not hold returns errno 8 with no call and the store's memory unchanged (`shim_errno`).
An accepted request reaches `SVC #0` with the `read` or `write` whose event the specification
records, and a result at most the length is the count, whose four bytes the stub stores as
`placeAll` stores `leBytes 4` of it (`leBytes_word`).  A result above the length returns the
errno of a negated error number or reaches the trap stub, and neither a `read` nor a `write`
changes the scratch's descriptor bytes (`ScratchHolds.quiet`).
-/

namespace Verified.ShimA64

open Wasm LeanExe LeanExe.A64 LeanExe.Wasi Verified.Wasi Verified.Shim

/-! ## The request's checks -/

/-- The memory's size, 8 plus the area's first word, of the store that the area holds, and its
bound below `2^32`. -/
theorem StoreRel.sizeWord {P : Platform} {cap : Nat} {gts : List ValueType} {α : Type}
    {st : Store α} {s : State} (h : StoreRel P cap gts st s) :
    (load64 s.mem (s.x 17) + 8).toNat = st.mem.pages * 65536 ∧
      st.mem.pages * 65536 < 2 ^ 32 := by
  have hpg := h.pages
  have hcap := h.cap_lt
  rw [h.size, UInt64.toNat_add, UInt64.toNat_ofNat']
  simp only [UInt64.reduceToNat, Nat.reducePow]
  exact ⟨by omega, by omega⟩

/-- The address of the byte `k` of the guest's memory above the byte `p`. -/
theorem guest_off (x : UInt64) (p : UInt32) (k : Nat) :
    x + p.toUInt64 + UInt64.ofNat (4096 + k) = x + UInt64.ofNat (4096 + (p.toNat + k)) := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_add, UInt64.toNat_ofNat', UInt32.toNat_toUInt64, Nat.reducePow]
  omega

/-- The iovec's eight bytes at the guest's address `el`, within the memory, hold the buffer's
pointer, `read32` at `el`, in their low half and its length, `read32` at `el + 4`, in their high
half. -/
theorem StoreRel.iovec {P : Platform} {cap : Nat} {gts : List ValueType} {α : Type}
    {st : Store α} {s : State} (h : StoreRel P cap gts st s) {el : UInt32}
    (hel : el.toNat + 8 ≤ st.mem.pages * 65536) :
    (load64 s.mem (s.x 17 + el.toUInt64 + UInt64.ofNat 4096)).toUInt32.toUInt64 =
        (st.mem.read32 el).toUInt64 ∧
      load64 s.mem (s.x 17 + el.toUInt64 + UInt64.ofNat 4096) >>> UInt64.ofNat 32 =
        (st.mem.read32 (el + 4)).toUInt64 := by
  have hpg := h.pages
  have hM := (StoreRel.sizeWord h).2
  have hb : ∀ k < 8, s.mem (s.x 17 + el.toUInt64 + UInt64.ofNat 4096 + UInt64.ofNat k) =
      st.mem.bytes (el.toNat + k) := fun k hk => by
    rw [add_ofNat_add, guest_off]
    exact h.bytes _ (by omega)
  have h4 : (el + 4).toNat = el.toNat + 4 := by
    rw [UInt32.toNat_add]
    simp only [UInt32.reduceToNat, Nat.reducePow] at hM ⊢
    omega
  have b0 := hb 0 (by omega)
  rw [add_ofNat_zero, Nat.add_zero] at b0
  refine ⟨load64_low32 b0 (hb 1 (by omega)) (hb 2 (by omega)) (hb 3 (by omega)),
    load64_shr32 ?_ ?_ ?_ ?_⟩
  · rw [h4]
    exact hb 4 (by omega)
  · rw [h4, show el.toNat + 4 + 1 = el.toNat + 5 by omega]
    exact hb 5 (by omega)
  · rw [h4, show el.toNat + 4 + 2 = el.toNat + 6 by omega]
    exact hb 6 (by omega)
  · rw [h4, show el.toNat + 4 + 3 = el.toNat + 7 by omega]
    exact hb 7 (by omega)

/-- The checks that `run_handleFront` makes, with the iovec's pointer `el`, the iovec count
`cnt`, and the count's pointer `res` in X1 to X3, on a machine that holds the store `st`, are the
checks of `handleReadInvoke` and `handleWriteInvoke`. -/
theorem StoreRel.handleChecks {P : Platform} {cap : Nat} {gts : List ValueType} {α : Type}
    {st : Store α} {s : State} (h : StoreRel P cap gts st s) (el cnt res : UInt32) :
    (cnt.toUInt64 = 1 ∧ ¬ load64 s.mem (s.x 17) + 8 < el.toUInt64 + 8 ∧
        ¬ load64 s.mem (s.x 17) + 8 <
          (load64 s.mem (s.x 17 + el.toUInt64 + UInt64.ofNat 4096)).toUInt32.toUInt64 +
            load64 s.mem (s.x 17 + el.toUInt64 + UInt64.ofNat 4096) >>> UInt64.ofNat 32 ∧
        ¬ load64 s.mem (s.x 17) + 8 < res.toUInt64 + 4) ↔
      (cnt = 1 ∧ el.toNat + 8 ≤ st.mem.pages * 65536 ∧ el.toNat + 8 ≤ 2 ^ 32 ∧
        (st.mem.read32 el).toNat + (st.mem.read32 (el + 4)).toNat ≤ st.mem.pages * 65536 ∧
        (st.mem.read32 el).toNat + (st.mem.read32 (el + 4)).toNat ≤ 2 ^ 32 ∧
        res.toNat + 4 ≤ st.mem.pages * 65536 ∧ res.toNat + 4 < 2 ^ 32) := by
  obtain ⟨hW, hM⟩ := StoreRel.sizeWord h
  have hc : cnt.toUInt64 = 1 ↔ cnt = 1 := ⟨fun e => toUInt64_eq e, fun e => by subst e; rfl⟩
  have he : ¬ load64 s.mem (s.x 17) + 8 < el.toUInt64 + 8 ↔
      el.toNat + 8 ≤ st.mem.pages * 65536 := by
    rw [UInt64.lt_iff_toNat_lt, hW, UInt64.toNat_add, UInt32.toNat_toUInt64, Nat.not_lt]
    simp only [UInt64.reduceToNat]
    have := el.toNat_lt
    constructor <;> intro hh <;> omega
  have hr : ¬ load64 s.mem (s.x 17) + 8 < res.toUInt64 + 4 ↔
      res.toNat + 4 ≤ st.mem.pages * 65536 := by
    rw [UInt64.lt_iff_toNat_lt, hW, UInt64.toNat_add, UInt32.toNat_toUInt64, Nat.not_lt]
    simp only [UInt64.reduceToNat]
    have := res.toNat_lt
    constructor <;> intro hh <;> omega
  have hb : ¬ load64 s.mem (s.x 17) + 8 <
      (st.mem.read32 el).toUInt64 + (st.mem.read32 (el + 4)).toUInt64 ↔
      (st.mem.read32 el).toNat + (st.mem.read32 (el + 4)).toNat ≤ st.mem.pages * 65536 := by
    rw [UInt64.lt_iff_toNat_lt, hW, UInt64.toNat_add, Nat.not_lt]
    simp only [UInt32.toNat_toUInt64]
    have := (st.mem.read32 el).toNat_lt
    have := (st.mem.read32 (el + 4)).toNat_lt
    constructor <;> intro hh <;> omega
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    have hel := he.mp h2
    obtain ⟨lo, hi⟩ := StoreRel.iovec h hel
    rw [lo, hi] at h3
    have hbuf := hb.mp h3
    have hres := hr.mp h4
    exact ⟨hc.mp h1, hel, by omega, hbuf, by omega, hres, by omega⟩
  · rintro ⟨h1, h2, -, h4, -, h6, -⟩
    obtain ⟨lo, hi⟩ := StoreRel.iovec h h2
    refine ⟨hc.mpr h1, he.mpr h2, ?_, hr.mpr h6⟩
    rw [lo, hi]
    exact hb.mpr h4

/-- The four bytes that `wordStore` stores from X0 are `leBytes 4` of its value. -/
theorem leBytes_word (r : UInt64) :
    (leBytes 4 r.toNat).data.data.toList = [r.toUInt8, (r >>> UInt64.ofNat 8).toUInt8,
      (r >>> UInt64.ofNat 16).toUInt8, (r >>> UInt64.ofNat 24).toUInt8] := by
  have b : ∀ k sh, sh = 8 * k → k < 8 →
      (r >>> UInt64.ofNat sh).toUInt8 = Verified.Wasi.byteOf r.toNat k := by
    intro k sh hsh hk
    subst hsh
    apply UInt8.toNat_inj.mp
    rw [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, UInt64.toNat_ofNat',
      Verified.Wasi.byteOf_toNat, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt (show 8 * k < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show 8 * k < 64 by omega)]
  have b0 : r.toUInt8 = Verified.Wasi.byteOf r.toNat 0 := by
    apply UInt8.toNat_inj.mp
    rw [UInt64.toNat_toUInt8, Verified.Wasi.byteOf_toNat]
    simp
  show (List.range 4).map (Verified.Wasi.byteOf r.toNat) = _
  show [Verified.Wasi.byteOf r.toNat 0, Verified.Wasi.byteOf r.toNat 1,
    Verified.Wasi.byteOf r.toNat 2, Verified.Wasi.byteOf r.toNat 3] = _
  rw [b0, b 1 8 rfl (by omega), b 2 16 rfl (by omega), b 3 24 rfl (by omega)]

theorem sysFn_read (F : OpenFlags) (L : ShimLayout) (I : Launch) (replies : Linux.Replies)
    (st : Store (Observed LinuxWorld)) (args : List Value) :
    (sysFn F L I replies Call.fdRead).invoke st args = handleReadInvoke L I replies st args := by
  simp (config := { decide := true }) only [sysFn, sysInvoke, ↓reduceIte]

theorem sysFn_write (F : OpenFlags) (L : ShimLayout) (I : Launch) (replies : Linux.Replies)
    (st : Store (Observed LinuxWorld)) (args : List Value) :
    (sysFn F L I replies Call.fdWrite).invoke st args = handleWriteInvoke L I replies st args := by
  simp (config := { decide := true }) only [sysFn, sysInvoke, ↓reduceIte]

/-! ## The run to the call -/

variable {R : Linux.Replies} {L : ElfLayout} {G : Scratch} {I : Launch} {sp₀ top : UInt64}
  {l₀ : List Linux.Event} {calls : List LeanExe.Wasi.Call} {code : UInt64 → Option UInt32}
  {hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55}
  {hk : ∀ a w i, code a = some w → decode w = some i → i.keepsX17 = true}
  {hk18 : ∀ a w i, code a = some w → decode w = some i → i.keepsX18 = true}
  {hL : L.area.toNat + L.dataMem ≤ 2 ^ 32} {hG : G.base.toNat + scratchSize < 2 ^ 64}
  {base : UInt64} {size : Nat}

/-- The stub of `fd_read` or `fd_write` on a handle from its entry, on the process's platform, for
a request whose descriptor, iovec's pointer, iovec count, and count's pointer lie in X0 to X3 of a
state that holds the store `st` and the shim's descriptors after the layer events `events`: the
trap stub when a check of `handleReadInvoke` fails, the return of errno 8 for a descriptor that
the shim does not hold, and otherwise the call's `BL` at `after a 39` with X1 at the buffer's
address, X2 and X11 at its length, X8 at the call's number, and X19 at the return address.  The
memory, SP, the UART's state, X17, and X18 keep their values. -/
theorem run_handleChecked {nr : Fin 65536} {S : Shared} {a svc en : UInt64} {is : List Instr}
    (hg : handleStub nr a svc S.trapUnreachable en (areaSize S.cap) = .ok is)
    (hcode : CodeAt code a is)
    (hGb : G.base = L.area + UInt64.ofNat (areaSize S.cap))
    (hscr : ∀ j < scratchSize, (wasiPlatform L sp₀ top).normal (G.base + UInt64.ofNat j) = true)
    {α : Type} {st : Store α} {events : List Linux.Event} {s : State}
    (hst : StoreRel (modulePlatform L G) S.cap S.globalTypes st s) (h17 : s.x 17 = L.area)
    (hK : ScratchHolds G I sp₀ top events s.mem) (hpc : s.pc = a)
    {fd el cnt res : UInt32} (x0 : s.x 0 = fd.toUInt64) (x1 : s.x 1 = el.toUInt64)
    (x2 : s.x 2 = cnt.toUInt64) (x3 : s.x 3 = res.toUInt64) :
    ∃ t, Reach (wasiPlatform L sp₀ top) code s t ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io ∧
      t.x 17 = s.x 17 ∧ t.x 18 = s.x 18 ∧
      if cnt = 1 ∧ el.toNat + 8 ≤ st.mem.pages * 65536 ∧ el.toNat + 8 ≤ 2 ^ 32 ∧
          (st.mem.read32 el).toNat + (st.mem.read32 (el + 4)).toNat ≤ st.mem.pages * 65536 ∧
          (st.mem.read32 el).toNat + (st.mem.read32 (el + 4)).toNat ≤ 2 ^ 32 ∧
          res.toNat + 4 ≤ st.mem.pages * 65536 ∧ res.toNat + 4 < 2 ^ 32 then
        if fd.toUInt64 ∈ openNumbers I events then
          t.pc = after a 39 ∧ t.x 0 = fd.toUInt64 ∧
            t.x 1 = L.area + UInt64.ofNat 4096 + (st.mem.read32 el).toUInt64 ∧
            t.x 2 = (st.mem.read32 (el + 4)).toUInt64 ∧ t.x 3 = res.toUInt64 ∧
            t.x 8 = UInt64.ofNat nr.val ∧ t.x 11 = (st.mem.read32 (el + 4)).toUInt64 ∧
            t.x 19 = s.x 30 ∧ t.x 30 = s.x 30
        else t.pc = s.x 30 ∧ t.x 0 = 8
      else t.pc = S.trapUnreachable := by
  have hMP := modulePlatform_le_wasi L G sp₀ top
  have hpg := hst.pages
  have hW := StoreRel.sizeWord hst
  have hbase : s.x 17 + UInt64.ofNat (areaSize S.cap) = G.base := by rw [h17, hGb]
  obtain ⟨t, r, sp, m, io, t17, t18, hc⟩ := run_handleFront (wasiPlatform L sp₀ top) code hg
    hcode hpc (fun k hk => hMP.normal _ (hst.mapped k (by unfold areaSize; omega)))
    (fun hle k hk => by
      rw [x1] at hle ⊢
      rw [UInt64.lt_iff_toNat_lt, hW.1, UInt64.toNat_add, UInt32.toNat_toUInt64] at hle
      have := el.toNat_lt
      simp only [UInt64.reduceToNat, Nat.reducePow] at hle this
      rw [guest_off]
      exact hMP.normal _ (hst.mapped _ (by unfold areaSize; omega)))
    (fun hle => by
      rw [x0] at hle
      rw [hbase, x0, ← held_addr G fd.toUInt64]
      refine hscr _ ?_
      rw [UInt64.le_iff_toNat_le] at hle
      simp only [UInt64.reduceToNat] at hle
      unfold scratchSize
      omega)
  rw [hbase, x0, x1, x2, x3] at hc
  refine ⟨t, r, sp, m, io, t17, t18, ?_⟩
  by_cases hok : cnt = 1 ∧ el.toNat + 8 ≤ st.mem.pages * 65536 ∧ el.toNat + 8 ≤ 2 ^ 32 ∧
      (st.mem.read32 el).toNat + (st.mem.read32 (el + 4)).toNat ≤ st.mem.pages * 65536 ∧
      (st.mem.read32 el).toNat + (st.mem.read32 (el + 4)).toNat ≤ 2 ^ 32 ∧
      res.toNat + 4 ≤ st.mem.pages * 65536 ∧ res.toNat + 4 < 2 ^ 32
  · rw [ite_eq_left ((StoreRel.handleChecks hst el cnt res).mpr hok)] at hc
    rw [ite_eq_left hok]
    obtain ⟨lo, hi⟩ := StoreRel.iovec hst hok.2.1
    by_cases hheld : fd.toUInt64 ∈ openNumbers I events
    · rw [ite_eq_left ((held_byte hK _).mpr hheld)] at hc
      rw [ite_eq_left hheld]
      obtain ⟨p, t0, t1, t2, t3, t8, t11, t19, t30⟩ := hc
      exact ⟨p, t0, by rw [t1, lo, h17], by rw [t2, hi], t3, t8, by rw [t11, hi], t19, t30⟩
    · rw [ite_eq_right (mt (held_byte hK _).mp hheld)] at hc
      rw [ite_eq_right hheld]
      exact hc
  · rw [ite_eq_right (mt (StoreRel.handleChecks hst el cnt res).mp hok)] at hc
    rw [ite_eq_right hok]
    exact hc

/-- A run of the program's model on the process's platform from a state that holds the store `st`
to the return address with the errno `v` in X0, with the memory, SP, the UART's state, X17, and
X18 kept, ends the stub with errno `v` and the store with the WASI event of the reply
`.returned v outputs` and no layer event. -/
theorem shim_errno {S : Shared} {n : Nat} {st : Store (Observed LinuxWorld)} {q : Proc} {t : State}
    {call : LeanExe.Wasi.Call} {request : List LeanExe.Wasi.Arg} {outputs : List LeanExe.Bytes}
    {v : UInt64}
    (hsr : (shimMachine R L G I sp₀ top l₀ calls code hdom hk hk18 hL hG base size).SR S.cap
      S.globalTypes st q)
    (hr : Reach (wasiPlatform L sp₀ top) code q.core t) (hpc : t.pc = q.core.x 30)
    (hsp : t.sp = q.core.sp) (hmem : t.mem = q.core.mem) (hio : t.io = q.core.io)
    (h17 : t.x 17 = q.core.x 17) (h18 : t.x 18 = q.core.x 18) (hx0 : t.x 0 = v)
    (hv : v.toNat < 2 ^ 32) :
    (shimMachine R L G I sp₀ top l₀ calls code hdom hk hk18 hL hG base size).StubResult S n [.i32]
      (sysAnswer st call request st.mem [] (.returned v outputs)) q := by
  obtain ⟨hst, hf, h17', hgap, htr, hK⟩ := hsr
  simp only [sysAnswer, sysResult]
  refine shim_return (ProcRunWith.ofReach hf hr) hpc hsp h18 hio (fun a _ => by
      show t.mem a = q.core.mem a
      rw [hmem]) ?_ ⟨StoreRel.withHost (hst.regs h17 h18 hmem) _, hf, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · show t.x 0 = v.toUInt32.toUInt64
    rw [hx0]
    apply UInt64.toNat_inj.mp
    rw [UInt32.toNat_toUInt64, UInt64.toNat_toUInt32]
    exact (Nat.mod_eq_of_lt hv).symm
  · show t.x 17 = L.area
    rw [h17, h17']
  · show _ ≤ (t.x 18).toNat
    rw [h18]
    exact hgap
  · show q.trace = _
    rw [htr.1]
    simp [answered, LinuxWorld.answer]
  · intro e he
    simp only [answered, LinuxWorld.answer, List.append_nil] at he
    exact htr.2 e he
  · show ScratchHolds G I sp₀ top (st.host.world.events ++ []) t.mem
    rw [List.append_nil, hmem]
    exact hK

/-! ## `fd_read` on a handle -/

/-- The stub of `fd_read` on a handle stands for the shim's `fd_read` on a handle,
`handleReadInvoke`. -/
theorem handleReadStub_sim (S : Shared) (n : Nat) {hr svc en : UInt64} {is : List Instr}
    (hg : handleStub 63 hr svc S.trapUnreachable en (areaSize S.cap) = .ok is)
    (hcode : CodeAt code hr is) (hsvc : OpsAt code svc [.svc, .ins (.ret 30)])
    (hen : CodeAt code en errnoRoutine)
    (hGb : G.base = L.area + UInt64.ofNat (areaSize S.cap))
    (hdata : areaSize S.cap + scratchSize ≤ L.dataMem)
    (hU : (modulePlatform L G).normal (modulePlatform L G).uart = false)
    (hsize : S.cap * 65536 ≤ size) :
    (shimMachine R L G I sp₀ top l₀ calls code hdom hk hk18 hL hG base size).StubSim S n
      [.i32, .i32, .i32, .i32] [.i32]
      (sysFn arm64Flags (shimLayout L.area G) I (fun j => R (l₀.length + j)) Call.fdRead) hr := by
  intro st args q hlen hty hpc hstk hsr hregs
  change Proc at q
  change q.core.pc = hr at hpc
  change StackOk (modulePlatform L G) q.core at hstk
  obtain ⟨fd, el, cnt, res, rfl⟩ := typed_i32x4 hlen hty
  have x0 : q.core.x 0 = fd.toUInt64 := hregs 0 (by simp)
  have x1 : q.core.x 1 = el.toUInt64 := hregs 1 (by simp)
  have x2 : q.core.x 2 = cnt.toUInt64 := hregs 2 (by simp)
  have x3 : q.core.x 3 = res.toUInt64 := hregs 3 (by simp)
  have hsr' := hsr
  obtain ⟨hst, hf, h17, hgap, htr, hK⟩ := hsr
  have hMP := modulePlatform_le_wasi L G sp₀ top
  have hUw := wasiPlatform_uart (top := top)
    (elfPlatform_uart hU (scratch_pos hL hGb hdata)) hK.stack.above
  have hpg := hst.pages
  have hlim := hst.below
  have hstk2 := hstk.limit
  obtain ⟨u1, r1, sp1, m1, io1, x17_1, x18_1, hc1⟩ := run_handleChecked hg hcode hGb
    (scratch_wasi hL hGb hdata) hst h17 hK hpc x0 x1 x2 x3
  rw [sysFn_read]
  simp only [handleReadInvoke]
  split
  swap
  · rename_i hok'
    have hok : ¬ (cnt = 1 ∧ el.toNat + 8 ≤ st.mem.pages * 65536 ∧ el.toNat + 8 ≤ 2 ^ 32 ∧
        (st.mem.read32 el).toNat + (st.mem.read32 (el + 4)).toNat ≤ st.mem.pages * 65536 ∧
        (st.mem.read32 el).toNat + (st.mem.read32 (el + 4)).toNat ≤ 2 ^ 32 ∧
        res.toNat + 4 ≤ st.mem.pages * 65536 ∧ res.toNat + 4 < 2 ^ 32) :=
      fun ⟨c1, c2, c3, c4, c5, c6, c7⟩ =>
        hok' ⟨c1, by omega, by omega, by omega, by omega, by omega, by omega⟩
    rw [ite_eq_right hok] at hc1
    exact shim_trap (ProcRunWith.ofReach hf r1) io1 hc1 hf htr
  rename_i hok'
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hok'
  have hok : cnt = 1 ∧ el.toNat + 8 ≤ st.mem.pages * 65536 ∧ el.toNat + 8 ≤ 2 ^ 32 ∧
      (st.mem.read32 el).toNat + (st.mem.read32 (el + 4)).toNat ≤ st.mem.pages * 65536 ∧
      (st.mem.read32 el).toNat + (st.mem.read32 (el + 4)).toNat ≤ 2 ^ 32 ∧
      res.toNat + 4 ≤ st.mem.pages * 65536 ∧ res.toNat + 4 < 2 ^ 32 :=
    ⟨c1, by omega, by omega, by omega, by omega, by omega, by omega⟩
  rw [ite_eq_left hok] at hc1
  split
  swap
  · rename_i hheld
    rw [ite_eq_right hheld] at hc1
    exact shim_errno hsr' r1 hc1.1 sp1 m1 io1 x17_1 x18_1 hc1.2 (by decide)
  rename_i hheld
  rw [ite_eq_left hheld] at hc1
  obtain ⟨p1, x01, x11, x21, x31, x81, x111, x191, -⟩ := hc1
  generalize st.mem.read32 el = buf at *
  generalize st.mem.read32 (el + 4) = len at *
  obtain ⟨-, -, -, hbl, -, hres, -⟩ := hok
  have hblc : buf.toNat + len.toNat ≤ S.cap * 65536 :=
    Nat.le_trans hbl (Nat.mul_le_mul_right _ hpg.2)
  have hbsize : buf.toNat + len.toNat ≤ size := by omega
  have hbufA : ∀ i < len.toNat, 4096 + buf.toNat + i < areaSize S.cap := fun i hi => by
    unfold areaSize
    omega
  have hresA : ∀ k < 4, 4096 + res.toNat + k < areaSize S.cap := fun k hk => by
    unfold areaSize
    omega
  have hbufN : (q.core.x 17 + UInt64.ofNat (4096 + buf.toNat)).toNat + len.toNat ≤
      (q.core.x 18).toNat := by
    rw [hst.toNat_addr (j := 4096 + buf.toNat) (by unfold areaSize; omega)]
    unfold areaSize at hlim
    omega
  have hresN : (q.core.x 17 + UInt64.ofNat (4096 + res.toNat)).toNat + 4 ≤
      (q.core.x 18).toNat := by
    rw [hst.toNat_addr (j := 4096 + res.toNat) (by unfold areaSize; omega)]
    unfold areaSize at hlim
    omega
  -- the call
  obtain ⟨r1', r2', r3', held, tail, _, g39, hr1, hr2, hr3, hh, ht, _, hg39, his⟩ :=
    handleStub_ok hg
  obtain ⟨_, _, rfl⟩ := rangeCheck_ok hr1
  obtain ⟨_, _, rfl⟩ := rangeCheck_ok hr2
  obtain ⟨_, _, rfl⟩ := rangeCheck_ok hr3
  obtain ⟨_, _, _, _, rfl⟩ := heldTest_ok hh
  rw [his] at hcode
  have cB := CodeAt.split code ((CodeAt.append (code := code)).mp hcode).1 (n := 40)
    (by simp [scratchAddr, movImm])
  have cbl : code (after hr 39) = some (encode (.bl g39)) := by
    have := cB.1 39 (by simp [scratchAddr, movImm])
    simpa [scratchAddr, movImm] using this
  obtain ⟨_, _, _, _, htl⟩ := countTail_ok ht
  have cnext := cB.2 0 (by
    rw [htl]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega)
  rw [after_zero] at cnext
  have hnext : (after (after hr 39) 1).toNat < 2 ^ 55 := by
    rw [after_after]
    exact hdom _ _ cnext
  have hT : Linux.table.find? (fun c => c.arm64 == ({ q with core := u1 } : Proc).core.x 8) =
      some Linux.readCall := by
    show Linux.table.find? (fun c => c.arm64 == u1.x 8) = _
    rw [x81, show UInt64.ofNat (63 : Fin 65536).val = 63 by decide]
    exact table_read
  have hmapR : (wasiPlatform L sp₀ top).mapped
      ((({ q with core := u1 } : Proc).call (after hr 39) svc).core.x 1)
      ((({ q with core := u1 } : Proc).call (after hr 39) svc).core.x 2).toNat = true := by
    rw [Proc.call_x _ _ _ (by decide), Proc.call_x _ _ _ (by decide)]
    show (wasiPlatform L sp₀ top).mapped (u1.x 1) (u1.x 2).toNat = true
    apply hMP.mapped
    rw [x11, x21, guest_addr]
    unfold Platform.mapped
    rw [List.all_eq_true]
    intro i hi
    rw [List.mem_range, UInt32.toNat_toUInt64] at hi
    rw [← h17, add_ofNat_add]
    exact hst.mapped _ (hbufA i hi)
  obtain ⟨q5, rq5, p5, x05, -, k5, sp5, m5, io5, f5, tr5⟩ :=
    run_callSvc (T := Linux.table) (R := R) (P := wasiPlatform L sp₀ top) (code := code) hsvc
      cbl hg39 hdom hnext (p := { q with core := u1 }) p1 hT rfl (sysCall_read hmapR)
  simp only [Proc.call_trace, Proc.call_mem] at x05 m5 tr5
  rw [Proc.call_x _ _ _ (by decide), Proc.call_x _ _ _ (by decide)] at m5 tr5
  have hlenk : q.trace.length = l₀.length + st.host.world.events.length := by
    rw [htr.1, List.length_map, List.length_append]
  change q5.core.mem = writeList u1.mem (u1.x 1) _ at m5
  change q5.core.x 0 = (R q.trace.length).ret at x05
  rw [hlenk] at x05 m5 tr5
  generalize R (l₀.length + st.host.world.events.length) = rk at x05 m5 tr5 ⊢
  have hout : (u1.x 2).toNat = len.toNat := by rw [x21, UInt32.toNat_toUInt64]
  have hrl : readList u1.mem (u1.x 1) len.toNat = st.mem.readBytes buf.toNat len.toNat := by
    rw [x11, guest_addr, m1, ← h17, readList_bytes (modulePlatform L G) hst len.toNat buf.toNat
      hblc, memBytes_readBytes]
  have hev : (⟨Linux.readCall, [u1.x 0, u1.x 1, u1.x 2], [], readList u1.mem (u1.x 1)
      (u1.x 2).toNat, rk.ret, (List.range (u1.x 2).toNat).map rk.bytes⟩ : Linux.Event) =
      readEvent (shimLayout L.area G) st.mem fd.toUInt64 buf len rk := by
    rw [hout, hrl, x01, x11, x21]
    rfl
  change q5.trace = q.trace ++ [A64.Event.sys ⟨Linux.readCall, [u1.x 0, u1.x 1, u1.x 2], [],
    readList u1.mem (u1.x 1) (u1.x 2).toNat, rk.ret, (List.range (u1.x 2).toNat).map rk.bytes⟩]
    at tr5
  rw [hev] at tr5
  change q5.core.mem = writeList u1.mem (u1.x 1) ((List.range (u1.x 2).toNat).map rk.bytes)
    at m5
  rw [hout, x11, guest_addr, m1, ← h17] at m5
  rw [step_read (shimLayout L.area G) st.mem fd.toUInt64 buf len rk hbl]
  dsimp only
  have hret : (readEvent (shimLayout L.area G) st.mem fd.toUInt64 buf len rk).ret = rk.ret := rfl
  have hro : (readEvent (shimLayout L.area G) st.mem fd.toUInt64 buf len rk).output =
      (List.range len.toNat).map rk.bytes := rfl
  -- the result
  have hq5pc : q5.core.pc = after hr 40 := by rw [p5, after_after]
  have q5x17 : q5.core.x 17 = L.area := by
    rw [k5 17 (by decide) (by decide)]
    show u1.x 17 = _
    rw [x17_1, h17]
  have q5x18 : q5.core.x 18 = q.core.x 18 := by
    rw [k5 18 (by decide) (by decide)]
    exact x18_1
  have q5x3 : q5.core.x 3 = res.toUInt64 := by
    rw [k5 3 (by decide) (by decide)]
    exact x31
  have q5x11 : q5.core.x 11 = len.toUInt64 := by
    rw [k5 11 (by decide) (by decide)]
    exact x111
  have q5x19 : q5.core.x 19 = q.core.x 30 := by
    rw [k5 19 (by decide) (by decide)]
    exact x191
  have hmap4 : q5.core.x 0 ≤ q5.core.x 11 → ∀ k < 4, (wasiPlatform L sp₀ top).normal
      (q5.core.x 17 + UInt64.ofNat 4096 + q5.core.x 3 + UInt64.ofNat k) = true := by
    intro _ k hk
    rw [q5x17, q5x3, ← h17, guest_addr, add_ofNat_add]
    exact hMP.normal _ (hst.mapped _ (hresA k hk))
  obtain ⟨u6, r6, sp6, io6, x176, x186, hcases⟩ :=
    run_countTail (wasiPlatform L sp₀ top) code ht cB.2 hen hq5pc hmap4 hUw
  have haddr : q5.core.x 17 + UInt64.ofNat 4096 + q5.core.x 3 =
      q5.core.x 17 + UInt64.ofNat (4096 + res.toNat) := by
    rw [q5x3, guest_addr]
  rw [x05, q5x11, q5x19, haddr] at hcases
  have hf5 : q5.fpcr = fpcrValue := by rw [f5]; exact hf
  have hrch : (shimMachine R L G I sp₀ top l₀ calls code hdom hk hk18 hL hG base size).Rch q
      { q5 with core := u6 } :=
    ProcRunWith.trans hdom (ProcRunWith.ofReach hf r1)
      (ProcRunWith.trans hdom (ProcRunWith.ofWith rq5 hf5) (ProcRunWith.ofReach hf5 r6))
  have hsp6 : u6.sp = q.core.sp := by rw [sp6, sp5]; exact sp1
  have hio6 : u6.io = q.core.io := by rw [io6, io5]; exact io1
  have h176 : u6.x 17 = L.area := by rw [x176, q5x17]
  have h186 : u6.x 18 = q.core.x 18 := by rw [x186, q5x18]
  have hgap6 : L.area.toNat + areaSize S.cap + scratchSize ≤ (u6.x 18).toNat := by
    rw [h186]
    exact hgap
  have hkern : ∀ a : UInt64, q.core.sp.toNat ≤ a.toNat → q5.core.mem a = q.core.mem a :=
    fun a ha => by
      rw [m5]
      exact writeList_below (by rw [List.length_map, List.length_range]; exact hbufN)
        (Nat.le_trans hstk2.2.1 ha)
  have hkernOut : ∀ a, (modulePlatform L G).normal a = false → q5.core.mem a = q.core.mem a := by
    intro a ha
    rw [m5]
    refine writeList_outside _ (fun i hi => ?_) a ha
    rw [add_ofNat_add]
    simp only [List.length_map, List.length_range] at hi
    exact hst.mapped _ (hbufA i hi)
  have hst5 : StoreRel (modulePlatform L G) S.cap S.globalTypes
      { st with mem := st.mem.writeBytes buf.toNat ((List.range len.toNat).map rk.bytes) }
      q5.core :=
    hst.ofWriteList (modulePlatform L G) ((List.range len.toNat).map rk.bytes)
      (by simpa only [List.length_map, List.length_range] using hbl) (by rw [q5x17, h17]) q5x18
      m5
  have htrace : ({ q5 with core := u6 } : Proc).trace =
      (l₀ ++ (st.host.world.events ++
        [readEvent (shimLayout L.area G) st.mem fd.toUInt64 buf len rk])).map A64.Event.sys := by
    show q5.trace = _
    rw [tr5, htr.1]
    simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc]
  have hwithin : ∀ e ∈ st.host.world.events ++
      [readEvent (shimLayout L.area G) st.mem fd.toUInt64 buf len rk],
      WritesNative (shimLayout L.area G) size e := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact htr.2 e he
    · obtain rfl := List.mem_singleton.mp he
      exact .inl (readEvent_writesLinear (shimLayout L.area G) st.mem fd.toUInt64 buf len rk
        hbsize)
  have hquiet : ∀ mem, (∀ a, (modulePlatform L G).normal a = false → mem a = q.core.mem a) →
      ScratchHolds G I sp₀ top
        (st.host.world.events ++ [readEvent (shimLayout L.area G) st.mem fd.toUInt64 buf len rk])
        mem :=
    fun _ hm => (hK.frame hL hG hm).quiet (fun h => Bool.false_ne_true h.1)
      (show Linux.readCall ≠ Linux.closeCall by decide)
  rcases hcases with ⟨hle, p6, x06, m6⟩ | ⟨hgt, h4095, p6, x06, m6⟩ | ⟨hgt, hbig, p6, m6⟩
  · -- a count
    have hret' : rk.ret.toNat ≤ len.toNat := by
      simpa only [UInt64.le_iff_toNat_le, UInt32.toNat_toUInt64] using hle
    have hrep : handleReadReply len.toUInt64 rk.ret ((List.range len.toNat).map rk.bytes) =
        .returned 0 [bytesOfList ((List.range len.toNat).map rk.bytes),
          leBytes 4 rk.ret.toNat] := by
      unfold handleReadReply
      rw [ite_eq_left (by rw [UInt32.toNat_toUInt64]; exact hret')]
    simp only [hret, hro, hrep, placeReply_returned, getD_one, placeAll, sysAnswer, sysResult]
    have hm6 : u6.mem = writeList q5.core.mem (q5.core.x 17 + UInt64.ofNat (4096 + res.toNat))
        (leBytes 4 rk.ret.toNat).data.data.toList := by
      rw [m6, leBytes_word]
    have hcntN : (q5.core.x 17 + UInt64.ofNat (4096 + res.toNat)).toNat +
        (leBytes 4 rk.ret.toNat).data.data.toList.length ≤ (q.core.x 18).toNat := by
      rw [leBytes_word, q5x17, ← h17]
      exact hresN
    refine shim_return hrch p6 hsp6 h186 hio6 (fun a ha => ?_) (by rw [x06]; rfl)
      ⟨StoreRel.withHost (hst5.ofWriteList (modulePlatform L G)
        (leBytes 4 rk.ret.toNat).data.data.toList (p := res.toNat)
        (by rw [leBytes_word]; exact hres) x176 x186 hm6) _, hf5, h176, hgap6,
        ⟨htrace, hwithin⟩, hquiet _ fun a ha => ?_⟩
    · show u6.mem a = q.core.mem a
      rw [hm6, writeList_below hcntN (Nat.le_trans hstk2.2.1 ha)]
      exact hkern a ha
    · show u6.mem a = q.core.mem a
      rw [hm6]
      refine Eq.trans (writeList_outside _ (fun i hi => ?_) a ha) (hkernOut a ha)
      have hi4 : i < 4 := by
        rw [leBytes_word] at hi
        exact hi
      rw [add_ofNat_add, q5x17, ← h17]
      exact hst.mapped _ (hresA i hi4)
  · -- an error
    have hnot : ¬ rk.ret.toNat ≤ (len.toUInt64).toNat :=
      Nat.not_le.mpr (UInt64.lt_iff_toNat_lt.mp hgt)
    have hErr : Linux.isError rk.ret = true :=
      (isError_iff (c := len.toUInt64) (by rw [UInt32.toNat_toUInt64]; exact len.toNat_lt)
        hgt).mpr h4095
    have hrep : handleReadReply len.toUInt64 rk.ret ((List.range len.toNat).map rk.bytes) =
        .returned (errnoOf (0 - rk.ret)) [zeros len.toUInt64.toNat, zeros 4] := by
      unfold handleReadReply
      rw [ite_eq_right hnot, ite_eq_left hErr]
    simp only [hret, hro, hrep, placeReply, (errnoOf_valid (0 - rk.ret)).2, ↓reduceIte,
      sysAnswer, sysResult]
    exact shim_return hrch p6 hsp6 h186 hio6 (fun a ha => by
        show u6.mem a = q.core.mem a
        rw [m6]
        exact hkern a ha) (by rw [x06, errno_toUInt64, errnoOf_lookup])
      ⟨StoreRel.withHost (hst5.regs x176 x186 m6) _, hf5, h176, hgap6, ⟨htrace, hwithin⟩,
        hquiet _ fun a ha => by
          show u6.mem a = q.core.mem a
          rw [m6]
          exact hkernOut a ha⟩
  · -- a trap of the shim
    have hnot : ¬ rk.ret.toNat ≤ (len.toUInt64).toNat :=
      Nat.not_le.mpr (UInt64.lt_iff_toNat_lt.mp hgt)
    have hErr : Linux.isError rk.ret = false := by
      cases h : Linux.isError rk.ret with
      | false => rfl
      | true =>
        exact absurd ((isError_iff (c := len.toUInt64)
          (by rw [UInt32.toNat_toUInt64]; exact len.toNat_lt) hgt).mp h)
          (UInt64.not_le.mpr hbig)
    have hrep : handleReadReply len.toUInt64 rk.ret ((List.range len.toNat).map rk.bytes) =
        .trapped shimTrap [zeros len.toUInt64.toNat, zeros 4] := by
      unfold handleReadReply
      rw [ite_eq_right hnot, ite_eq_right (by rw [hErr]; decide)]
    simp only [hret, hro, hrep, placeReply, sysAnswer, sysResult]
    exact shim_trap hrch hio6 p6 hf5 ⟨htrace, hwithin⟩

/-! ## `fd_write` on a handle -/

/-- The stub of `fd_write` on a handle stands for the shim's `fd_write` on a handle,
`handleWriteInvoke`. -/
theorem handleWriteStub_sim (S : Shared) (n : Nat) {hw svc en : UInt64} {is : List Instr}
    (hg : handleStub 64 hw svc S.trapUnreachable en (areaSize S.cap) = .ok is)
    (hcode : CodeAt code hw is) (hsvc : OpsAt code svc [.svc, .ins (.ret 30)])
    (hen : CodeAt code en errnoRoutine)
    (hGb : G.base = L.area + UInt64.ofNat (areaSize S.cap))
    (hdata : areaSize S.cap + scratchSize ≤ L.dataMem)
    (hU : (modulePlatform L G).normal (modulePlatform L G).uart = false) :
    (shimMachine R L G I sp₀ top l₀ calls code hdom hk hk18 hL hG base size).StubSim S n
      [.i32, .i32, .i32, .i32] [.i32]
      (sysFn arm64Flags (shimLayout L.area G) I (fun j => R (l₀.length + j)) Call.fdWrite) hw := by
  intro st args q hlen hty hpc hstk hsr hregs
  change Proc at q
  change q.core.pc = hw at hpc
  change StackOk (modulePlatform L G) q.core at hstk
  obtain ⟨fd, el, cnt, res, rfl⟩ := typed_i32x4 hlen hty
  have x0 : q.core.x 0 = fd.toUInt64 := hregs 0 (by simp)
  have x1 : q.core.x 1 = el.toUInt64 := hregs 1 (by simp)
  have x2 : q.core.x 2 = cnt.toUInt64 := hregs 2 (by simp)
  have x3 : q.core.x 3 = res.toUInt64 := hregs 3 (by simp)
  have hsr' := hsr
  obtain ⟨hst, hf, h17, hgap, htr, hK⟩ := hsr
  have hMP := modulePlatform_le_wasi L G sp₀ top
  have hUw := wasiPlatform_uart (top := top)
    (elfPlatform_uart hU (scratch_pos hL hGb hdata)) hK.stack.above
  have hpg := hst.pages
  have hlim := hst.below
  have hstk2 := hstk.limit
  obtain ⟨u1, r1, sp1, m1, io1, x17_1, x18_1, hc1⟩ := run_handleChecked hg hcode hGb
    (scratch_wasi hL hGb hdata) hst h17 hK hpc x0 x1 x2 x3
  rw [sysFn_write]
  simp only [handleWriteInvoke]
  split
  swap
  · rename_i hok'
    have hok : ¬ (cnt = 1 ∧ el.toNat + 8 ≤ st.mem.pages * 65536 ∧ el.toNat + 8 ≤ 2 ^ 32 ∧
        (st.mem.read32 el).toNat + (st.mem.read32 (el + 4)).toNat ≤ st.mem.pages * 65536 ∧
        (st.mem.read32 el).toNat + (st.mem.read32 (el + 4)).toNat ≤ 2 ^ 32 ∧
        res.toNat + 4 ≤ st.mem.pages * 65536 ∧ res.toNat + 4 < 2 ^ 32) :=
      fun ⟨c1, c2, c3, c4, c5, c6, c7⟩ =>
        hok' ⟨c1, by omega, by omega, by omega, by omega, by omega, by omega⟩
    rw [ite_eq_right hok] at hc1
    exact shim_trap (ProcRunWith.ofReach hf r1) io1 hc1 hf htr
  rename_i hok'
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hok'
  have hok : cnt = 1 ∧ el.toNat + 8 ≤ st.mem.pages * 65536 ∧ el.toNat + 8 ≤ 2 ^ 32 ∧
      (st.mem.read32 el).toNat + (st.mem.read32 (el + 4)).toNat ≤ st.mem.pages * 65536 ∧
      (st.mem.read32 el).toNat + (st.mem.read32 (el + 4)).toNat ≤ 2 ^ 32 ∧
      res.toNat + 4 ≤ st.mem.pages * 65536 ∧ res.toNat + 4 < 2 ^ 32 :=
    ⟨c1, by omega, by omega, by omega, by omega, by omega, by omega⟩
  rw [ite_eq_left hok] at hc1
  split
  swap
  · rename_i hheld
    rw [ite_eq_right hheld] at hc1
    exact shim_errno hsr' r1 hc1.1 sp1 m1 io1 x17_1 x18_1 hc1.2 (by decide)
  rename_i hheld
  rw [ite_eq_left hheld] at hc1
  obtain ⟨p1, x01, x11, x21, x31, x81, x111, x191, -⟩ := hc1
  generalize st.mem.read32 el = buf at *
  generalize st.mem.read32 (el + 4) = len at *
  obtain ⟨-, -, -, hbl, -, hres, -⟩ := hok
  have hblc : buf.toNat + len.toNat ≤ S.cap * 65536 :=
    Nat.le_trans hbl (Nat.mul_le_mul_right _ hpg.2)
  have hbufA : ∀ i < len.toNat, 4096 + buf.toNat + i < areaSize S.cap := fun i hi => by
    unfold areaSize
    omega
  have hresA : ∀ k < 4, 4096 + res.toNat + k < areaSize S.cap := fun k hk => by
    unfold areaSize
    omega
  have hresN : (q.core.x 17 + UInt64.ofNat (4096 + res.toNat)).toNat + 4 ≤
      (q.core.x 18).toNat := by
    rw [hst.toNat_addr (j := 4096 + res.toNat) (by unfold areaSize; omega)]
    unfold areaSize at hlim
    omega
  -- the call
  obtain ⟨r1', r2', r3', held, tail, _, g39, hr1, hr2, hr3, hh, ht, _, hg39, his⟩ :=
    handleStub_ok hg
  obtain ⟨_, _, rfl⟩ := rangeCheck_ok hr1
  obtain ⟨_, _, rfl⟩ := rangeCheck_ok hr2
  obtain ⟨_, _, rfl⟩ := rangeCheck_ok hr3
  obtain ⟨_, _, _, _, rfl⟩ := heldTest_ok hh
  rw [his] at hcode
  have cB := CodeAt.split code ((CodeAt.append (code := code)).mp hcode).1 (n := 40)
    (by simp [scratchAddr, movImm])
  have cbl : code (after hw 39) = some (encode (.bl g39)) := by
    have := cB.1 39 (by simp [scratchAddr, movImm])
    simpa [scratchAddr, movImm] using this
  obtain ⟨_, _, _, _, htl⟩ := countTail_ok ht
  have cnext := cB.2 0 (by
    rw [htl]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega)
  rw [after_zero] at cnext
  have hnext : (after (after hw 39) 1).toNat < 2 ^ 55 := by
    rw [after_after]
    exact hdom _ _ cnext
  have hT : Linux.table.find? (fun c => c.arm64 == ({ q with core := u1 } : Proc).core.x 8) =
      some Linux.writeCall := by
    show Linux.table.find? (fun c => c.arm64 == u1.x 8) = _
    rw [x81, show UInt64.ofNat (64 : Fin 65536).val = 64 by decide]
    exact table_write
  have hmapW : (wasiPlatform L sp₀ top).mapped
      ((({ q with core := u1 } : Proc).call (after hw 39) svc).core.x 1)
      ((({ q with core := u1 } : Proc).call (after hw 39) svc).core.x 2).toNat = true := by
    rw [Proc.call_x _ _ _ (by decide), Proc.call_x _ _ _ (by decide)]
    show (wasiPlatform L sp₀ top).mapped (u1.x 1) (u1.x 2).toNat = true
    apply hMP.mapped
    rw [x11, x21, guest_addr]
    unfold Platform.mapped
    rw [List.all_eq_true]
    intro i hi
    rw [List.mem_range, UInt32.toNat_toUInt64] at hi
    rw [← h17, add_ofNat_add]
    exact hst.mapped _ (hbufA i hi)
  obtain ⟨q5, rq5, p5, x05, -, k5, sp5, m5, io5, f5, tr5⟩ :=
    run_callSvc (T := Linux.table) (R := R) (P := wasiPlatform L sp₀ top) (code := code) hsvc
      cbl hg39 hdom hnext (p := { q with core := u1 }) p1 hT rfl (sysCall_write hmapW)
  simp only [Proc.call_trace, Proc.call_mem] at x05 m5 tr5
  rw [Proc.call_x _ _ _ (by decide), Proc.call_x _ _ _ (by decide),
    Proc.call_x _ _ _ (by decide)] at tr5
  have hlenk : q.trace.length = l₀.length + st.host.world.events.length := by
    rw [htr.1, List.length_map, List.length_append]
  change q5.core.x 0 = (R q.trace.length).ret at x05
  rw [hlenk] at x05 tr5
  generalize R (l₀.length + st.host.world.events.length) = rk at x05 tr5 ⊢
  have hout : (u1.x 2).toNat = len.toNat := by rw [x21, UInt32.toNat_toUInt64]
  have hrl : readList u1.mem (u1.x 1) len.toNat = st.mem.readBytes buf.toNat len.toNat := by
    rw [x11, guest_addr, m1, ← h17, readList_bytes (modulePlatform L G) hst len.toNat buf.toNat
      hblc, memBytes_readBytes]
  have hev : (⟨Linux.writeCall, [u1.x 0, u1.x 1, u1.x 2],
      [readList u1.mem (u1.x 1) (u1.x 2).toNat], [], rk.ret, []⟩ : Linux.Event) =
      writeEvent (shimLayout L.area G) st.mem fd.toUInt64 buf len rk := by
    rw [hout, hrl, x01, x11, x21]
    rfl
  change q5.trace = q.trace ++ [A64.Event.sys ⟨Linux.writeCall, [u1.x 0, u1.x 1, u1.x 2],
    [readList u1.mem (u1.x 1) (u1.x 2).toNat], [], rk.ret, []⟩] at tr5
  rw [hev] at tr5
  change q5.core.mem = u1.mem at m5
  rw [m1] at m5
  have hret : (writeEvent (shimLayout L.area G) st.mem fd.toUInt64 buf len rk).ret = rk.ret :=
    rfl
  -- the result
  have hq5pc : q5.core.pc = after hw 40 := by rw [p5, after_after]
  have q5x17 : q5.core.x 17 = L.area := by
    rw [k5 17 (by decide) (by decide)]
    show u1.x 17 = _
    rw [x17_1, h17]
  have q5x18 : q5.core.x 18 = q.core.x 18 := by
    rw [k5 18 (by decide) (by decide)]
    exact x18_1
  have q5x3 : q5.core.x 3 = res.toUInt64 := by
    rw [k5 3 (by decide) (by decide)]
    exact x31
  have q5x11 : q5.core.x 11 = len.toUInt64 := by
    rw [k5 11 (by decide) (by decide)]
    exact x111
  have q5x19 : q5.core.x 19 = q.core.x 30 := by
    rw [k5 19 (by decide) (by decide)]
    exact x191
  have hmap4 : q5.core.x 0 ≤ q5.core.x 11 → ∀ k < 4, (wasiPlatform L sp₀ top).normal
      (q5.core.x 17 + UInt64.ofNat 4096 + q5.core.x 3 + UInt64.ofNat k) = true := by
    intro _ k hk
    rw [q5x17, q5x3, ← h17, guest_addr, add_ofNat_add]
    exact hMP.normal _ (hst.mapped _ (hresA k hk))
  obtain ⟨u6, r6, sp6, io6, x176, x186, hcases⟩ :=
    run_countTail (wasiPlatform L sp₀ top) code ht cB.2 hen hq5pc hmap4 hUw
  have haddr : q5.core.x 17 + UInt64.ofNat 4096 + q5.core.x 3 =
      q.core.x 17 + UInt64.ofNat (4096 + res.toNat) := by
    rw [q5x17, q5x3, ← h17, guest_addr]
  rw [x05, q5x11, q5x19, haddr, m5] at hcases
  have hf5 : q5.fpcr = fpcrValue := by rw [f5]; exact hf
  have hrch : (shimMachine R L G I sp₀ top l₀ calls code hdom hk hk18 hL hG base size).Rch q
      { q5 with core := u6 } :=
    ProcRunWith.trans hdom (ProcRunWith.ofReach hf r1)
      (ProcRunWith.trans hdom (ProcRunWith.ofWith rq5 hf5) (ProcRunWith.ofReach hf5 r6))
  have hsp6 : u6.sp = q.core.sp := by rw [sp6, sp5]; exact sp1
  have hio6 : u6.io = q.core.io := by rw [io6, io5]; exact io1
  have h176 : u6.x 17 = L.area := by rw [x176, q5x17]
  have h1717 : u6.x 17 = q.core.x 17 := by rw [h176, h17]
  have h186 : u6.x 18 = q.core.x 18 := by rw [x186, q5x18]
  have hgap6 : L.area.toNat + areaSize S.cap + scratchSize ≤ (u6.x 18).toNat := by
    rw [h186]
    exact hgap
  have htrace : ({ q5 with core := u6 } : Proc).trace =
      (l₀ ++ (st.host.world.events ++
        [writeEvent (shimLayout L.area G) st.mem fd.toUInt64 buf len rk])).map A64.Event.sys := by
    show q5.trace = _
    rw [tr5, htr.1]
    simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc]
  have hwithin : ∀ e ∈ st.host.world.events ++
      [writeEvent (shimLayout L.area G) st.mem fd.toUInt64 buf len rk],
      WritesNative (shimLayout L.area G) size e := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact htr.2 e he
    · obtain rfl := List.mem_singleton.mp he
      exact .inl (writeEvent_writesLinear (shimLayout L.area G) st.mem fd.toUInt64 buf len rk
        size)
  have hquiet : ∀ mem, (∀ a, (modulePlatform L G).normal a = false → mem a = q.core.mem a) →
      ScratchHolds G I sp₀ top
        (st.host.world.events ++ [writeEvent (shimLayout L.area G) st.mem fd.toUInt64 buf len rk])
        mem :=
    fun _ hm => (hK.frame hL hG hm).quiet (fun h => Bool.false_ne_true h.1)
      (show Linux.writeCall ≠ Linux.closeCall by decide)
  rcases hcases with ⟨hle, p6, x06, m6⟩ | ⟨hgt, h4095, p6, x06, m6⟩ | ⟨hgt, hbig, p6, m6⟩
  · -- a count
    have hret' : rk.ret.toNat ≤ len.toNat := by
      simpa only [UInt64.le_iff_toNat_le, UInt32.toNat_toUInt64] using hle
    have hrep : handleWriteReply len.toUInt64 rk.ret = .returned 0 [leBytes 4 rk.ret.toNat] := by
      unfold handleWriteReply
      rw [ite_eq_left (by rw [UInt32.toNat_toUInt64]; exact hret')]
    simp only [hret, hrep, placeReply_returned, List.headD_cons, placeAll, sysAnswer, sysResult]
    have hm6 : u6.mem = writeList q.core.mem (q.core.x 17 + UInt64.ofNat (4096 + res.toNat))
        (leBytes 4 rk.ret.toNat).data.data.toList := by
      rw [m6, leBytes_word]
    have hcntN : (q.core.x 17 + UInt64.ofNat (4096 + res.toNat)).toNat +
        (leBytes 4 rk.ret.toNat).data.data.toList.length ≤ (q.core.x 18).toNat := by
      rw [leBytes_word]
      exact hresN
    refine shim_return hrch p6 hsp6 h186 hio6 (fun a ha => ?_) (by rw [x06]; rfl)
      ⟨StoreRel.withHost (hst.ofWriteList (modulePlatform L G)
        (leBytes 4 rk.ret.toNat).data.data.toList (p := res.toNat)
        (by rw [leBytes_word]; exact hres) h1717 h186 hm6) _, hf5, h176, hgap6,
        ⟨htrace, hwithin⟩, hquiet _ fun a ha => ?_⟩
    · show u6.mem a = q.core.mem a
      rw [hm6]
      exact writeList_below hcntN (Nat.le_trans hstk2.2.1 ha)
    · show u6.mem a = q.core.mem a
      rw [hm6]
      refine writeList_outside _ (fun i hi => ?_) a ha
      have hi4 : i < 4 := by
        rw [leBytes_word] at hi
        exact hi
      rw [add_ofNat_add]
      exact hst.mapped _ (hresA i hi4)
  · -- an error
    have hnot : ¬ rk.ret.toNat ≤ (len.toUInt64).toNat :=
      Nat.not_le.mpr (UInt64.lt_iff_toNat_lt.mp hgt)
    have hErr : Linux.isError rk.ret = true :=
      (isError_iff (c := len.toUInt64) (by rw [UInt32.toNat_toUInt64]; exact len.toNat_lt)
        hgt).mpr h4095
    have hrep : handleWriteReply len.toUInt64 rk.ret =
        .returned (errnoOf (0 - rk.ret)) [zeros 4] := by
      unfold handleWriteReply
      rw [ite_eq_right hnot, ite_eq_left hErr]
    simp only [hret, hrep, placeReply, (errnoOf_valid (0 - rk.ret)).2, ↓reduceIte, sysAnswer,
      sysResult]
    exact shim_return hrch p6 hsp6 h186 hio6 (fun a _ => by
        show u6.mem a = q.core.mem a
        rw [m6]) (by rw [x06, errno_toUInt64, errnoOf_lookup])
      ⟨StoreRel.withHost (hst.regs h1717 h186 m6) _, hf5, h176, hgap6, ⟨htrace, hwithin⟩,
        hquiet _ fun a _ => by
          show u6.mem a = q.core.mem a
          rw [m6]⟩
  · -- a trap of the shim
    have hnot : ¬ rk.ret.toNat ≤ (len.toUInt64).toNat :=
      Nat.not_le.mpr (UInt64.lt_iff_toNat_lt.mp hgt)
    have hErr : Linux.isError rk.ret = false := by
      cases h : Linux.isError rk.ret with
      | false => rfl
      | true =>
        exact absurd ((isError_iff (c := len.toUInt64)
          (by rw [UInt32.toNat_toUInt64]; exact len.toNat_lt) hgt).mp h)
          (UInt64.not_le.mpr hbig)
    have hrep : handleWriteReply len.toUInt64 rk.ret = .trapped shimTrap [zeros 4] := by
      unfold handleWriteReply
      rw [ite_eq_right hnot, ite_eq_right (by rw [hErr]; decide)]
    simp only [hret, hrep, placeReply, sysAnswer, sysResult]
    exact shim_trap hrch hio6 p6 hf5 ⟨htrace, hwithin⟩

end Verified.ShimA64
