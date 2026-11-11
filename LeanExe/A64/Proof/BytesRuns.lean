import LeanExe.A64.Proof.BytesProgram
import LeanExe.A64.Proof.InputRuns
import LeanExe.Pipeline.Bytes
import LeanExe.Pipeline.RuntimeSpec

/-!
The theorems of the programs and images that read a message from the UART and run a function
over bytes on it.  `BytesRuns` is the counterpart of `InputRuns` for a program of
`genBytesProgram`, from `main` on a platform whose UART lies outside Normal memory, with the
receiver at its first read and no poll done.  When the receiver delivers the eight bytes of a
length L of at most `inMax`, the lowest first, and then L bytes, all without an error flag, the
program writes `Out` of the bytes and returns 0, or reaches the exit word with a status that `T`
allows.  When it delivers the eight bytes of a length above `inMax`, the program reaches the exit
word with status 64, and when a byte that the program reads carries an error flag after bytes
without one, with status 65, in both cases with nothing written to the UART.  `bytes_runs` gives
`BytesRuns` from the compiler's theorem of the function, the allocator's specification
`alloc_spec_runs`, and `buffer_of_alloc`, which states that the block that the allocator returns,
with the message's bytes written into it, holds a buffer of those bytes.  `image_bytes_run` joins
`BytesRuns` to the startup, and `image_bytes_run_at` states it at every base.
-/

namespace LeanExe.A64

open Wasm LeanExe.Pipeline LeanExe.ProofKit

/-! ## The buffer of the message -/

/-- A block with element width one that holds `bytes` from its root is a buffer. -/
theorem block_buffer {heap : Heap} {store : Store Unit} {root capacity : UInt64}
    {bytes : LeanExe.Bytes} (h : heap.Block store root capacity 1)
    (hContents : ∀ (i : Nat) (hi : i < bytes.data.size),
      store.mem.bytes (root.toNat + i) = bytes.data[i])
    (hMin : 8 ≤ capacity.toNat) (hCapacity : bytes.data.size ≤ capacity.toNat) :
    heap.Buffer store root bytes := by
  have hRead : capacityAt store root = capacity.toNat := by
    rw [capacityAt, h.fresh.2.2.1]
  obtain ⟨hMagic, hCount, _, hKind, hWidth, hChild⟩ := h.fresh
  refine ⟨⟨h.base, ?_, ?_, ?_⟩, hMagic, hCount, ?_, ?_, hKind, hWidth, hChild, hContents⟩ <;>
    rw [hRead]
  · exact h.address
  · exact h.below
  · exact h.separate
  · exact hMin
  · exact hCapacity

theorem storeBytes_write (st : Store Unit) (p : Nat) (bs : List UInt8)
    (hp : p + bs.length < 2 ^ 32) (c : Nat) (hc : bs.length ≤ c) :
    WritesWithin st (storeBytes st p bs) p c := by
  obtain ⟨hg, hpg, -⟩ := storeBytes_globals st p bs
  refine ⟨hg, hpg, fun a ha => ?_⟩
  rw [storeBytes_bytes st p bs hp a, dif_neg (by omega)]

/-- The block of `allocSize L` bytes that the allocator returns leaves room for L bytes from its
root within the memory. -/
theorem alloc_fit {heap : Heap} {st : Store Unit} (hAt : heap.At st) {L : Nat}
    (hL : L ≤ 4294967296) (hFits : heap.Fits (allocSize (UInt64.ofNat L))) :
    (FixedArrayAllocate.root heap.top (allocSize (UInt64.ofNat L)) heap.free).toNat + L ≤
      (heap.allocateStore st (allocSize (UInt64.ofNat L)) 1).mem.pages * 65536 := by
  have hBlock := hAt.allocate_block 1 hFits
  have hcap := allocated_capacity (allocSize (UInt64.ofNat L)) heap.free
  have hneed : L ≤ (allocSize (UInt64.ofNat L)).toNat := by
    have := le_allocSize (bytes := UInt64.ofNat L)
      (by rw [UInt64.toNat_ofNat']; simp only [Nat.reducePow] at *; omega)
    rwa [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by simp only [Nat.reducePow]; omega)] at this
  have := hBlock.memory
  omega

/-- After the allocation of `allocSize L` bytes for a message `bs` of L bytes and its writes from
the block's root, the heap of the allocation lies at the store, and the block holds a buffer of
the message. -/
theorem buffer_of_alloc {heap : Heap} {st : Store Unit} (hAt : heap.At st) {bs : List UInt8}
    (hlen : bs.length ≤ 4294967296)
    (hFits : heap.Fits (allocSize (UInt64.ofNat bs.length))) :
    let need := allocSize (UInt64.ofNat bs.length)
    let p := FixedArrayAllocate.root heap.top need heap.free
    let st' := storeBytes (heap.allocateStore st need 1) p.toNat bs
    (heap.allocate need).At st' ∧ (heap.allocate need).Buffer st' p ⟨⟨bs.toArray⟩⟩ ∧
      p.toNat + bs.length ≤ (heap.allocateStore st need 1).mem.pages * 65536 := by
  intro need p st'
  have hBlock : (heap.allocate need).Block (heap.allocateStore st need 1) p
      (allocatedCapacity need heap.free) 1 := hAt.allocate_block 1 hFits
  have hcap := allocated_capacity need heap.free
  have hneed : bs.length ≤ need.toNat := by
    have := le_allocSize (bytes := UInt64.ofNat bs.length)
      (by rw [UInt64.toNat_ofNat']; simp only [Nat.reducePow] at *; omega)
    rwa [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by simp only [Nat.reducePow]; omega)] at this
  have hmin : 8 ≤ need.toNat := by
    show 8 ≤ (allocSize _).toNat
    unfold allocSize
    split
    · rfl
    · rename_i h
      rw [UInt64.not_lt, UInt64.le_iff_toNat_le] at h
      exact h
  have haddr := hBlock.address
  have hmem := hBlock.memory
  have hW : WritesWithin (heap.allocateStore st need 1) st' p.toNat
      (allocatedCapacity need heap.free).toNat :=
    storeBytes_write _ p.toNat bs (by omega) _ (by omega)
  have hsz : (⟨bs.toArray⟩ : ByteArray).size = bs.length := by simp [ByteArray.size]
  refine ⟨(hAt.allocate 1 hFits).writesWithin hBlock hW,
    block_buffer (hBlock.writesWithin hW) (fun i hi => ?_) (by omega) (by
      show (⟨bs.toArray⟩ : ByteArray).size ≤ _
      omega),
    by omega⟩
  have hi' : i < bs.length := by simpa [ByteArray.size] using hi
  show (storeBytes _ p.toNat bs).mem.bytes _ = _
  rw [storeBytes_bytes _ p.toNat bs (by omega), dif_pos (by omega)]
  simp [ByteArray.getElem_eq_getElem_data]

/-! ## The receiver's bytes -/

/-- A receiver that delivers the bytes of the word `w` and then `bs` gives the first eight reads
the bytes of `w`, without an error flag. -/
theorem delivers_length {rx : Rx} {w : UInt64} {bs : List UInt8}
    (hd : rx.Delivers (bytesOf w ++ bs)) :
    (∀ j < 8, ¬ rx.Flagged j) ∧ rxSum rx 0 8 = w.toNat := by
  have hb : ∀ t (ht : t < 8), (rx.word t).toNat % 4096 = w.toNat / 2 ^ (8 * t) % 256 :=
    fun t ht => by
      have h := hd t (by simp [bytesOf]; omega)
      rw [List.getElem_append_left (by simp [bytesOf]; omega), bytesOf_digit _ ht] at h
      exact h
  refine ⟨fun j hj => ?_, ?_⟩
  · have := hb j hj
    have : w.toNat / 2 ^ (8 * j) % 256 < 256 := Nat.mod_lt _ (by decide)
    unfold Rx.Flagged
    omega
  · rw [rxSum_digits (rx := rx) (j := 0) (x := w.toNat) 8 fun t ht => by
        have := hb t ht
        have : w.toNat / 2 ^ (8 * t) % 256 < 256 := Nat.mod_lt _ (by decide)
        simp only [Nat.zero_add]
        omega]
    exact Nat.mod_eq_of_lt w.toNat_lt

/-- A receiver that delivers the bytes of the word `w` and then `bs` gives the next reads the
bytes of `bs`, without an error flag. -/
theorem delivers_message {rx : Rx} {w : UInt64} {bs : List UInt8}
    (hd : rx.Delivers (bytesOf w ++ bs)) :
    (∀ t < bs.length, ¬ rx.Flagged (8 + t)) ∧ rxBytes rx 8 bs.length = bs := by
  have hb : ∀ t (ht : t < bs.length), (rx.word (8 + t)).toNat % 4096 = bs[t].toNat :=
    fun t ht => by
      have h := hd (8 + t) (by simp [bytesOf]; omega)
      rw [List.getElem_append_right (by simp [bytesOf])] at h
      simpa [bytesOf] using h
  refine ⟨fun t ht => ?_, ?_⟩
  · have := hb t ht
    have := bs[t].toNat_lt
    unfold Rx.Flagged
    omega
  · have key : ∀ (j : Nat) (cs : List UInt8),
        (∀ t (ht : t < cs.length), (rx.word (j + t)).toNat % 4096 = cs[t].toNat) →
        rxBytes rx j cs.length = cs := by
      intro j cs
      induction cs generalizing j with
      | nil => intro _; rfl
      | cons c cs ih =>
          intro h
          rw [List.length_cons, rxBytes, ih (j + 1) fun t ht => by
            have := h (t + 1) (by simp; omega)
            rwa [show j + (t + 1) = j + 1 + t by omega] at this]
          congr 1
          apply UInt8.toNat_inj.mp
          have := h 0 (by simp)
          have := c.toNat_lt
          simp only [Nat.add_zero, List.getElem_cons_zero] at *
          rw [UInt32.toNat_toUInt8]
          omega
    exact key 8 bs hb

/-! ## The programs at every base -/

theorem readMessage_shift {a err d : UInt64} {δ : Int} {is : List Instr}
    (hg : readMessage a err = .ok is) (ha : MovesFrom d δ a 11) (he : Moves d δ err) :
    readMessage (a + d) (err + d) = .ok is := by
  obtain ⟨done, back, fail, loop, h1, h2, h3, h4, rfl⟩ := readMessage_ok hg
  simp only [readMessage, after_shift, cbField_shift ha.base (ha 11 (by omega)) h1,
    cbField_shift (ha 3 (by omega)) (ha 1 (by omega)) h2, cbField_shift (ha 6 (by omega)) he h3,
    bField_shift (ha 10 (by omega)) ha.base h4, bind, Except.bind, pure, Except.pure]

theorem writeBytes_shift {a d : UInt64} {δ : Int} {is : List Instr}
    (hg : writeBytes a = .ok is) (ha : MovesFrom d δ a 8) : writeBytes (a + d) = .ok is := by
  obtain ⟨done, back, h1, h2, rfl⟩ := writeBytes_ok hg
  simp only [writeBytes, after_shift, cbField_shift (ha 2 (by omega)) (ha 8 (by omega)) h1,
    bField_shift (ha 7 (by omega)) (ha 2 (by omega)) h2, bind, Except.bind, pure, Except.pure]

/-- The entry routine of `genBytesMain` at `a + d`, with the entries of the function and of the
allocator and the exit word shifted by `d`, is the one at `a`, when the shift moves its
addresses, the entries, and the exit word by the same number. -/
theorem genBytesMain_shift {a e a0 inMax uart room base d : UInt64} {δ : Int} {main : List Instr}
    (hg : genBytesMain a e a0 inMax uart room base = .ok main)
    (ha : MovesFrom d δ a bytesMainSize) (he : Moves d δ e) (h0 : Moves d δ a0)
    (hb : Moves d δ base) :
    genBytesMain (a + d) (e + d) (a0 + d) inMax uart room (base + d) = .ok main := by
  obtain ⟨len, ov, ga, msg, gk, out, x65, x64, h1, h2, h3, h4, h5, h6, h7, h8, hm⟩ :=
    gen_bytesMain hg
  have hsz : bytesMainSize = 156 := rfl
  rw [hsz] at ha
  have h1' := readBytes_shift (ha 146 (by omega)) 8 0 h1
    ((ha.drop (m := 16) (by omega)).le (by omega))
  have h4' := readMessage_shift h4 ((ha.drop (m := 114) (by omega)).le (by omega))
    (ha 146 (by omega))
  have h6' := writeBytes_shift h6 ((ha.drop (m := 131) (by omega)).le (by omega))
  rw [← hg]
  simp only [genBytesMain, after_shift, h1, h1', h4, h4', h6, h6',
    cbField_shift (ha 101 (by omega)) (ha 151 (by omega)) h2,
    bField_shift (ha 104 (by omega)) h0 h3, bField_shift (ha 126 (by omega)) he h5,
    bField_shift (by rw [after_after]; exact ha 150 (by omega)) hb h7,
    bField_shift (by rw [after_after]; exact ha 155 (by omega)) hb h8, h2, h3, h5, h7, h8,
    bind, Except.bind, pure, Except.pure]

/-- `genBytesProgram` places the same program at every base where it lies below 2^64. -/
theorem genBytesProgram_shift {m : Module} {k : Nat} {inMax uart base room : UInt64} {cap : Nat}
    {p : List Instr} {d : UInt64}
    (hg : genBytesProgram m k inMax uart base room cap = .ok p)
    (h1 : base.toNat + 4 * p.length < 2 ^ 64) (h2 : (base + d).toNat + 4 * p.length < 2 ^ 64) :
    genBytesProgram m k inMax uart (base + d) room cap = .ok p :=
  genProgramWith_shift hg (fun _ _ hmg => by
      simp only [bind, Except.bind] at hmg
      split at hmg
      · cases hmg
      · split at hmg
        · exact genBytesMain_length hmg
        · cases hmg)
    (fun δ e main hmg ha he hent => by
      simp only [bind, Except.bind] at hmg ⊢
      split at hmg
      · cases hmg
      rename_i fs hfs
      split at hmg
      · rename_i a0 p0 r0 hen0
        have hen0' : entryIn (sigIn (callTargets m k) fs) (after (after (base + d) 1)
            bytesMainSize) fs 0 = some (a0 + d, p0, r0) := by
          rw [after_shift, after_shift, entryIn_shift, hen0]
          rfl
        rw [hen0']
        simp only
        rw [after_shift]
        exact genBytesMain_shift hmg ((ha.drop (m := 1) (by omega)).le (by omega)) he
          (hent fs 0 _ hfs hen0) ha.base
      · cases hmg) h1 h2

theorem genBytesProgram_shiftsBy (m : Module) (k : Nat) (inMax room : UInt64) (cap : Nat)
    (d : UInt64) : ShiftsBy (fun base => genBytesProgram m k inMax uartAddr base room cap) d :=
  fun _ _ hp h1 h2 => genBytesProgram_shift hp h1 h2

/-! ## The theorem's form -/

/-- The form of the theorems of programs of `genBytesProgram`, which read from the UART a length
L of eight bytes, the lowest first, and L bytes, and run function `k` of `m` on them: for every
platform `P` whose UART lies outside Normal memory, exit word `base`, and area `area`, from `main`
with the premises of `InputRuns`, when the receiver delivers the length L of the message `msg`,
at most `inMax`, and `msg`, without an error flag, the program writes `Out msg` and returns 0 or
reaches the exit word with a status that `T msg` allows and writes nothing.  When it delivers a
length above `inMax`, the program reaches the exit word with status 64, and when byte `j` carries
an error flag and no byte before it does, where `j` is one of the first eight or, for a length L
of at most `inMax`, one of the next L, with status 65. -/
def BytesRuns (m : Module) (k : Nat) (inMax room : UInt64) (cap : Nat)
    (Out : List UInt8 → List UInt8) (T : List UInt8 → UInt64 → Prop) : Prop :=
  ∀ (P : Platform) (base area : UInt64) {is : List Instr},
    genBytesProgram m k inMax P.uart base room cap = .ok is → ∀ (ms : State),
    (∀ j (hj : j < (imageBytes is).length),
      ms.mem (after base 1 + UInt64.ofNat j) = (imageBytes is)[j]) →
    ms.pc = after base 1 → ms.sp % 16 = 0 → 4096 ≤ room.toNat → ms.sp.toNat ≤ 2 ^ 63 →
    (∀ j < room.toNat + 16, P.normal (ms.sp - 16 - room + UInt64.ofNat j) = true) →
    ms.x 17 = area →
    (∀ j < areaSize cap, ms.mem (area + UInt64.ofNat j) = areaByte m.initialStore j) →
    (∀ j < areaSize cap, P.normal (area + UInt64.ofNat j) = true) →
    area.toNat + areaSize cap + room.toNat + 16 ≤ ms.sp.toNat →
    P.normal P.uart = false → ms.io.rxNext = 0 → ms.io.rxPolls = 0 →
    (∀ msg : List UInt8, msg.length ≤ inMax.toNat →
      P.rx.Delivers (bytesOf (UInt64.ofNat msg.length) ++ msg) →
      (∃ ms', Reach P (fetchFrom ms.mem (after base 1) is.length) ms ms' ∧ ms'.pc = ms.x 30 ∧
        ms'.x 0 = 0 ∧ ms'.out = ms.out ++ Out msg) ∨
      ∃ ms', Reach P (fetchFrom ms.mem (after base 1) is.length) ms ms' ∧ ms'.pc = base ∧
        T msg (ms'.x 0) ∧ ms'.out = ms.out) ∧
    (∀ len : UInt64, inMax < len → P.rx.Delivers (bytesOf len) →
      ∃ ms', Reach P (fetchFrom ms.mem (after base 1) is.length) ms ms' ∧ ms'.pc = base ∧
        ms'.x 0 = 64 ∧ ms'.out = ms.out) ∧
    (∀ j, (∀ i < j, ¬ P.rx.Flagged i) → P.rx.Flagged j →
      (j < 8 ∨ (rxSum P.rx 0 8 ≤ inMax.toNat ∧ j < 8 + rxSum P.rx 0 8)) →
      ∃ ms', Reach P (fetchFrom ms.mem (after base 1) is.length) ms ms' ∧ ms'.pc = base ∧
        ms'.x 0 = 65 ∧ ms'.out = ms.out)

/-- The facts about function `k` of `m` that a program of `genBytesProgram` needs and its generator
does not check: those of `entryOkWith` for two parameters of type `i64`, and two results of type
`i64`, the root and the length of a buffer. -/
def bytesEntryOk (m : Module) (k : Nat) : Bool :=
  entryOkWith bytesMainSize m k [.i64, .i64] 2 &&
    decide ((m.funcs[k]?).map (·.results) = some [.i64, .i64])

theorem genBytesProgram_length {m : Module} {k : Nat} {inMax uart base room : UInt64}
    {cap : Nat} {is : List Instr} (hg : genBytesProgram m k inMax uart base room cap = .ok is)
    {fs : List (Nat × Function)} (hfs : (reachFrom m k).mapM (funcOf m) = .ok fs) :
    is.length = bytesMainSize +
      (fs.map fun x => functionSize (sigIn (callTargets m k) fs) x.2).sum + 20 :=
  genProgramWith_length hg (fun e main hmg => by
    simp only [bind, Except.bind] at hmg
    split at hmg
    · cases hmg
    · split at hmg
      · exact genBytesMain_length hmg
      · cases hmg) hfs

/-- `BytesRuns` from the compiler's theorem `h` that function `k` of `m` computes `f` over
bytes, for a module whose function 0 is the allocator.  The heap `heap` lies at the module's
initial store, the allocator has room for the block of every length of at most `inMax`, and the
heap after that block's allocation, at the store with the memory's cap, satisfies the theorem's
precondition for every message of at most `inMax` bytes.  The program writes the bytes of
`f` of the message and returns 0, or reaches the exit word with the status 1 of `unreachable`
when `aborts` holds, or with the status 4 of an overflow of the stack when `room` lies below
`stackBound m k`.  The allocator's stack must fit the room. -/
theorem bytes_runs {aborts : Bool} {m : Module} {k : Nat} {f : LeanExe.Bytes → LeanExe.Bytes}
    {Pre : LeanExe.Bytes → Heap → Store Unit → Prop}
    {Post : LeanExe.Bytes → Heap → Store Unit → Heap → Store Unit → Prop}
    (h : ImplementsA aborts m k f Pre Post) {typeIdx : Nat}
    (h0 : m.funcs[0]? = some (LeanExe.Runtime.allocFunction typeIdx))
    {inMax room : UInt64} {cap : Nat} {heap : Heap}
    (hheap : heap.At (m.initialStore : Store Unit)) (hinMax : inMax.toNat ≤ 4294967296)
    (hroomA : ∀ L ≤ inMax.toNat, heap.Room (initStore m cap) m (allocSize (UInt64.ofNat L)))
    (hpre : ∀ (b : LeanExe.Bytes) (st : Store Unit), b.data.size ≤ inMax.toNat →
      st.memoryCap m 0 = cap →
      Pre b (heap.allocate (allocSize (UInt64.ofNat b.data.size))) st)
    (h0room : stackBound m 0 ≤ room.toNat)
    (hok : bytesEntryOk m k = true := by decide +kernel) :
    BytesRuns m k inMax room cap (fun msg => (f ⟨⟨msg.toArray⟩⟩).data.data.toList)
      fun _ c => (aborts = true ∧ c = 1) ∨ (room.toNat < stackBound m k ∧ c = 4) := by
  intro P base area is hg ms himage hpc hal hroom htop hstack h17 harea hamap habove hU hrx hpo
  obtain ⟨-, fs, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hao, -, -, hfs, -⟩ :=
    gen_bytesProgram hg
  have hcap := cap_lt_of_areaOk hao
  have h64 := memIs64_of_areaOk hao
  unfold bytesEntryOk entryOkWith at hok
  rw [hfs] at hok
  simp only [Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨himp, hpar⟩, -⟩, hsize⟩, hres⟩ := hok
  have hn : 4 * is.length < 2 ^ 64 := by
    rw [genBytesProgram_length hg hfs]
    exact hsize
  obtain ⟨fk, hk, hpk, hrk⟩ : ∃ fk, m.funcs[k]? = some fk ∧ fk.params = [.i64, .i64] ∧
      fk.results = [.i64, .i64] := by
    cases hk : m.funcs[k]? with
    | none => rw [hk] at hpar; cases hpar
    | some g =>
        rw [hk] at hpar hres
        exact ⟨g, rfl, Option.some.inj hpar, Option.some.inj hres⟩
  have hrun := fun F => bytesProgram_run P _ hg (codeAt_fetchFrom hn himage) himp hk hpk hrk h0
    h0room F ms hpc hal hroom htop hstack h17 harea hamap habove hU hrx hpo
  have hcap0 : (initStore m cap).memoryCap m 0 ≤ 65535 := by
    have : (initStore m cap).memoryCap m 0 = cap := rfl
    omega
  -- the allocator's run on a length within the limit
  have halloc : ∀ L ≤ inMax.toNat, ∃ N, ∀ fuel ≥ N,
      Wasm.run fuel m 0 (initStore m cap) [.i64 (UInt64.ofNat L)] =
        .Success [.i64 (FixedArrayAllocate.root heap.top (allocSize (UInt64.ofNat L)) heap.free)]
          (heap.allocateStore (initStore m cap) (allocSize (UInt64.ofNat L)) 1) ∧
      heap.Fits (allocSize (UInt64.ofNat L)) := by
    intro L hL
    obtain ⟨N, hN⟩ := alloc_spec_runs false h64 himp h0 {} heap (initStore m cap)
      (UInt64.ofNat L) (heapAt_initStore hheap cap)
      (by rw [UInt64.toNat_ofNat']; simp only [Nat.reducePow] at *; omega) hcap0
      (fun _ => hroomA L hL)
    refine ⟨N, fun fuel hf => ?_⟩
    rcases hN fuel hf with ⟨vs, st, hr, hfit, rfl, rfl⟩ | hab
    · exact ⟨hr, hfit⟩
    · exact hab.elim
  have hAt0 := heapAt_initStore hheap cap
  refine ⟨fun msg hlen hd => ?_, fun len hlt hd => ?_, fun j hpre hf hj => ?_⟩
  rotate_left
  · obtain ⟨hclean, hsum⟩ := delivers_length (bs := []) (by rwa [List.append_nil])
    exact ((hrun 0).2 hclean).1 (by rw [hsum]; exact UInt64.lt_iff_toNat_lt.mp hlt)
  · rcases Nat.lt_or_ge j 8 with h8 | h8
    · exact (hrun 0).1 j h8 hpre hf
    have hclean : ∀ i < 8, ¬ P.rx.Flagged i := fun i hi => hpre i (by omega)
    obtain ⟨hle, hj⟩ : rxSum P.rx 0 8 ≤ inMax.toNat ∧ j < 8 + rxSum P.rx 0 8 := by
      rcases hj with hj | hj
      · omega
      · exact hj
    obtain ⟨N, hN⟩ := halloc _ hle
    obtain ⟨hA, hFits⟩ := hN N (Nat.le_refl _)
    exact (((hrun N).2 hclean).2 hle _ _ hA (alloc_fit hAt0 (by omega) hFits)).1 (j - 8)
      (by omega) (fun i hi => hpre (8 + i) (by omega))
      (by rwa [show 8 + (j - 8) = j by omega])
  -- a message within the limit
  obtain ⟨hclean, hsum⟩ := delivers_length hd
  obtain ⟨hcleanm, hbytes⟩ := delivers_message hd
  have hL : (UInt64.ofNat msg.length).toNat = msg.length := by
    rw [UInt64.toNat_ofNat']
    simp only [Nat.reducePow] at *
    omega
  rw [hL] at hsum
  have hle : rxSum P.rx 0 8 ≤ inMax.toNat := by rw [hsum]; exact hlen
  obtain ⟨N0, hN0⟩ := halloc msg.length hlen
  have hFits := (hN0 N0 (Nat.le_refl _)).2
  obtain ⟨hAt2, hbuf, hfit⟩ := buffer_of_alloc hAt0 (bs := msg) (by omega) hFits
  generalize hneed : allocSize (UInt64.ofNat msg.length) = need at hFits hAt2 hbuf hfit hN0
  generalize hroot : FixedArrayAllocate.root heap.top need heap.free = root at hAt2 hbuf hfit hN0
  generalize hst1 : heap.allocateStore (initStore m cap) need 1 = st1 at hAt2 hbuf hfit hN0
  have hcap2 : (storeBytes st1 root.toNat msg).memoryCap m 0 = cap := by
    unfold Store.memoryCap
    rw [(storeBytes_globals st1 root.toNat msg).2.2, ← hst1, Heap.allocateStore_memoryCaps]
    rfl
  have hrep : Represent.borrowed (heap.allocate need) (storeBytes st1 root.toNat msg)
      [.i64 root, .i64 (UInt64.ofNat msg.length)] (⟨⟨msg.toArray⟩⟩ : LeanExe.Bytes) :=
    ⟨root, UInt64.ofNat msg.length, rfl, ⟨by rw [hL]; simp [ByteArray.size], .inr hbuf⟩⟩
  obtain ⟨N1, hN1⟩ := h {} (storeBytes st1 root.toNat msg) (heap.allocate need)
    [.i64 root, .i64 (UInt64.ofNat msg.length)] ⟨⟨msg.toArray⟩⟩ hAt2
    (by rw [← hneed]; exact hpre _ _ (by simp [ByteArray.size]; omega) hcap2) hrep Separate.nil
    (by rw [hcap2]; omega)
  have hA := (hN0 (max N0 N1) (Nat.le_max_left _ _)).1
  rcases (((hrun (max N0 N1)).2 hclean).2 hle root st1 (by rw [hsum]; exact hA)
      (by rw [hsum]; exact hfit)).2 (by rw [hsum]; exact hcleanm) with
    ⟨ms', r', p', x', o', hlt'⟩ | hres
  · exact .inr ⟨ms', r', p', .inr ⟨hlt', x'⟩, o'⟩
  rw [hsum, hbytes] at hres
  rcases hN1 (max N0 N1) (Nat.le_max_right _ _) with
    ⟨vs, st3, hr3, heap', hAt', hown, -, -, -⟩ | hab
  · rw [show ([Value.i64 root, .i64 (UInt64.ofNat msg.length)]).reverse =
      [.i64 (UInt64.ofNat msg.length), .i64 root] from rfl] at hr3
    rw [hr3] at hres
    obtain ⟨root', len', hvs, hrep'⟩ := hown
    have hvs' : vs = [.i64 len', .i64 root'] := by
      rw [← List.reverse_reverse vs, hvs]
      rfl
    have hsz := hrep'.length_eq
    have hds : ∀ b : ByteArray, b.data.size = b.size := fun _ => rfl
    obtain ⟨ms', r', p', x', o'⟩ := hres root' len' (f ⟨⟨msg.toArray⟩⟩).data.data.toList hvs'
      (by rw [Array.length_toList, hds, hsz])
      (by
        rcases hrep'.buffer with ⟨hr0, h0'⟩ | hb'
        · rw [Array.length_toList, hds, h0', hr0]
          simp
        · have := hb'.object.below
          have := hb'.capacity
          have := hAt'.top
          rw [Array.length_toList, hds]
          omega)
      (fun i hi => by
        rw [Array.length_toList, hds] at hi
        rcases hrep'.buffer with ⟨-, h0'⟩ | hb'
        · rw [h0'] at hi
          omega
        · rw [Array.getElem_toList]
          exact hb'.contents i hi)
    exact .inl ⟨ms', r', p', x', o'⟩
  · cases aborts with
    | false => exact hab.elim
    | true =>
        obtain ⟨st', hr'⟩ := hab
        rw [show ([Value.i64 root, .i64 (UInt64.ofNat msg.length)]).reverse =
          [.i64 (UInt64.ofNat msg.length), .i64 root] from rfl] at hr'
        rw [hr'] at hres
        obtain ⟨ms', r', p', o', hm⟩ := hres
        rcases hm with ⟨-, hx⟩ | ⟨he, -⟩ | ⟨he, -⟩
        · exact .inr ⟨ms', r', p', .inl ⟨rfl, hx⟩, o'⟩
        · exact absurd he (by decide)
        · exact absurd he (by decide)

/-- `bytes_runs` for a theorem without the trap at `unreachable` and a stack whose bound is at
most `room`: no status. -/
theorem bytes_runs_bounded {m : Module} {k : Nat} {f : LeanExe.Bytes → LeanExe.Bytes}
    {Pre : LeanExe.Bytes → Heap → Store Unit → Prop}
    {Post : LeanExe.Bytes → Heap → Store Unit → Heap → Store Unit → Prop}
    (h : ImplementsA false m k f Pre Post) {typeIdx : Nat}
    (h0 : m.funcs[0]? = some (LeanExe.Runtime.allocFunction typeIdx))
    {inMax room : UInt64} {cap : Nat} {heap : Heap}
    (hheap : heap.At (m.initialStore : Store Unit)) (hinMax : inMax.toNat ≤ 4294967296)
    (hroomA : ∀ L ≤ inMax.toNat, heap.Room (initStore m cap) m (allocSize (UInt64.ofNat L)))
    (hpre : ∀ (b : LeanExe.Bytes) (st : Store Unit), b.data.size ≤ inMax.toNat →
      st.memoryCap m 0 = cap →
      Pre b (heap.allocate (allocSize (UInt64.ofNat b.data.size))) st)
    (h0room : stackBound m 0 ≤ room.toNat) (hkroom : stackBound m k ≤ room.toNat)
    (hok : bytesEntryOk m k = true := by decide +kernel) :
    BytesRuns m k inMax room cap (fun msg => (f ⟨⟨msg.toArray⟩⟩).data.data.toList)
      fun _ _ => False := by
  intro P base area _ hg ms himage hpc hal hroom htop hstack h17 harea hamap habove hU hrx hpo
  obtain ⟨h1, h2, h3⟩ := bytes_runs h h0 hheap hinMax hroomA hpre h0room hok P base area hg ms
    himage hpc hal hroom htop hstack h17 harea hamap habove hU hrx hpo
  refine ⟨fun msg hlen hd => ?_, h2, h3⟩
  rcases h1 msg hlen hd with hr | ⟨_, -, -, ⟨hf, -⟩ | ⟨hlt, -⟩, -⟩
  · exact .inl hr
  · cases hf
  · omega

/-- `BytesRuns` for an output `Out'` that agrees with `Out` on every message of at most `inMax`
bytes. -/
theorem BytesRuns.congr {m : Module} {k : Nat} {inMax room : UInt64} {cap : Nat}
    {Out Out' : List UInt8 → List UInt8} {T : List UInt8 → UInt64 → Prop}
    (h : BytesRuns m k inMax room cap Out T)
    (hout : ∀ msg : List UInt8, msg.length ≤ inMax.toNat → Out msg = Out' msg) :
    BytesRuns m k inMax room cap Out' T := by
  intro P base area _ hg ms himage hpc hal hroom htop hstack h17 harea hamap habove hU hrx hpo
  obtain ⟨h1, h2, h3⟩ := h P base area hg ms himage hpc hal hroom htop hstack h17 harea hamap
    habove hU hrx hpo
  refine ⟨fun msg hlen hd => ?_, h2, h3⟩
  rw [← hout msg hlen]
  exact h1 msg hlen hd

/-! ## The images -/

/-- The platform of a ready boot state maps the UART as Device memory, outside Normal memory. -/
theorem platform_uart_apart {h : Hw} {R : UInt64 → Bool} {code : UInt64 → Option UInt32}
    {b : Boot} (hr : Ready h R code b) :
    (b.platform h R).normal (b.platform h R).uart = false := by
  show (!R uartAddr && writableNormal (classify h b.eff b.core.mem uartAddr)) = false
  rw [classify_uart hr.cov hr.tab]
  simp [writableNormal]

/-- The platform of a ready boot state maps the UART's flag register as Device memory, outside
Normal memory, so `exec` stops at every access to it but a 32-bit load. -/
theorem platform_uartFr_apart {h : Hw} {R : UInt64 → Bool} {code : UInt64 → Option UInt32}
    {b : Boot} (hr : Ready h R code b) :
    (b.platform h R).normal ((b.platform h R).uart + 0x18) = false := by
  show (!R (uartAddr + 0x18) &&
    writableNormal (classify h b.eff b.core.mem (uartAddr + 0x18))) = false
  rw [classify_uartFr hr.cov hr.tab]
  simp [writableNormal]

/-- The number of the program's instructions in the image of `genBytesImage` at `image`. -/
def imageBytesProgLength (m : Module) (k : Nat) (inMax room : UInt64) (cap : Nat)
    (image : UInt64) : Nat :=
  match genBytesProgram m k inMax uartAddr (image + UInt64.ofNat (64 + 4 * startupLength)) room
      cap with
  | .ok p => p.length
  | .error _ => 0

/-- The bytes of memory that the image of `genBytesImage` at `image` uses from its start: the size
in its header, which covers the area and the stack. -/
def imageBytesSize (m : Module) (k : Nat) (inMax room : UInt64) (cap : Nat) (image : UInt64) :
    Nat :=
  match genBytesImage m k inMax room cap image with
  | .ok (_, L) => L.size
  | .error _ => 0

/-- The run of an image of `genBytesImage` from its first word to `HVC #0`, given the program's
theorem in the form `BytesRuns`, with the receiver of `h` at its first read and no poll done.
When the receiver delivers the eight bytes of a length L of at most `inMax`, the lowest first,
and L bytes `msg`, all without an error flag, the image's run writes `Out msg` and the byte 0, or
the byte of a status that `T msg` allows.  When it delivers the eight bytes of a length above
`inMax`, the run writes the byte 64 alone, and when a byte that the run reads carries an error
flag after bytes without one, the byte 65 alone.  Each run reaches `HVC #0` with X0 holding PSCI's
`SYSTEM_OFF` and every store to the UART complete.  The code map is that of the image's first
words up to its translation table, and the protected bytes are those below the table's end. -/
theorem image_bytes_run {m : Module} {k : Nat} {inMax room : UInt64} {cap : Nat}
    {image : UInt64} {nb len : Nat} (h : Hw) {b : Boot}
    (hk : bytesOk (genBytesImage m k inMax room cap image) nb len = true)
    (himg : image.toNat % 4096 = 0) (hroom : room.toNat % 16 = 0) (hroom' : 4096 ≤ room.toNat)
    (hm : ∀ j < len, b.core.mem (image + UInt64.ofNat j) = byteAt nb j)
    (hpc : b.core.pc = image) (hoff : b.mmuOff)
    (hio : b.core.io.rxNext = 0 ∧ b.core.io.rxPolls = 0)
    {Out : List UInt8 → List UInt8} {T : List UInt8 → UInt64 → Prop}
    (hprog : BytesRuns m k inMax room cap Out T) :
    (∀ msg : List UInt8, msg.length ≤ inMax.toNat →
      h.rx.Delivers (bytesOf (UInt64.ofNat msg.length) ++ msg) →
      ∃ b', BootReach h (protectedBytes image (imageBytesProgLength m k inMax room cap image))
          (fetchFrom b.core.mem image (codeWords (imageBytesProgLength m k inMax room cap image)))
          b b' ∧
        fetchFrom b.core.mem image (codeWords (imageBytesProgLength m k inMax room cap image))
          b'.core.pc = some (encode .hvc0) ∧
        b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
        (b'.core.out = b.core.out ++ Out msg ++ [0] ∨
          ∃ c, T msg c ∧ b'.core.out = b.core.out ++ [c.toUInt8])) ∧
    (∀ L : UInt64, inMax < L → h.rx.Delivers (bytesOf L) →
      ∃ b', BootReach h (protectedBytes image (imageBytesProgLength m k inMax room cap image))
          (fetchFrom b.core.mem image (codeWords (imageBytesProgLength m k inMax room cap image)))
          b b' ∧
        fetchFrom b.core.mem image (codeWords (imageBytesProgLength m k inMax room cap image))
          b'.core.pc = some (encode .hvc0) ∧
        b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧ b'.core.out = b.core.out ++ [64]) ∧
    (∀ j, (∀ i < j, ¬ h.rx.Flagged i) → h.rx.Flagged j →
      (j < 8 ∨ (rxSum h.rx 0 8 ≤ inMax.toNat ∧ j < 8 + rxSum h.rx 0 8)) →
      ∃ b', BootReach h (protectedBytes image (imageBytesProgLength m k inMax room cap image))
          (fetchFrom b.core.mem image (codeWords (imageBytesProgLength m k inMax room cap image)))
          b b' ∧
        fetchFrom b.core.mem image (codeWords (imageBytesProgLength m k inMax room cap image))
          b'.core.pc = some (encode .hvc0) ∧
        b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧ b'.core.out = b.core.out ++ [65]) := by
  obtain ⟨prog, start, L, hp, hL, hs, cstart, b1, r1, hr1, p1, x30, x17, hal, htop, hstack,
    harea, hamap, habove, himage, hmono, hout1, hud1⟩ :=
    image_main (gp := fun base => genBytesProgram m k inMax uartAddr base room cap) h hk himg
      hroom hm hpc hoff
  have hN : imageBytesProgLength m k inMax room cap image = prog.length := by
    simp only [imageBytesProgLength, hp]
  rw [hN]
  subst hL
  have hbase := layout_base image prog.length m cap room
  have hpr := hprog (b1.platform h (protectedBytes image prog.length)) _ _ hp b1.core himage p1
    hal hroom' htop hstack x17 harea hamap habove (platform_uart_apart hr1)
    (by rw [hout1]; exact hio.1) (by rw [hout1]; exact hio.2)
  refine ⟨fun msg hlen hd => ?_, fun L hlt hd => ?_, fun j hpre hf hj => ?_⟩
  · obtain ⟨b', r2, hc', hx', hu', ho'⟩ := boot_after_main (T := T msg) hs cstart hbase hmono hr1
      (by
        rcases hpr.1 msg hlen hd with ⟨ms, hr, hpc', hx, ho⟩ | ⟨ms, hr, hpc', ht, ho⟩
        · exact .inl ⟨ms, hr, by rw [hpc', x30]; rfl, hx, ho⟩
        · exact .inr ⟨ms, hr, hpc', ht, ho⟩)
    refine ⟨b', r1.trans r2, hc', hx', hu', ?_⟩
    rw [hout1] at ho'
    exact ho'
  · obtain ⟨ms, hr, hpc', hx, ho⟩ := hpr.2.1 L hlt hd
    obtain ⟨b', r2, hc', hx', hu', ho'⟩ := boot_after_exit hs cstart hbase hmono hr1 hr hpc'
    refine ⟨b', r1.trans r2, hc', hx', hu', ?_⟩
    show b'.core.io.out = b.core.io.out ++ [64]
    rw [ho', show ms.io.out = b.core.io.out from ho.trans (congrArg Io.out hout1), hx]
    rfl
  · obtain ⟨ms, hr, hpc', hx, ho⟩ := hpr.2.2 j hpre hf hj
    obtain ⟨b', r2, hc', hx', hu', ho'⟩ := boot_after_exit hs cstart hbase hmono hr1 hr hpc'
    refine ⟨b', r1.trans r2, hc', hx', hu', ?_⟩
    show b'.core.io.out = b.core.io.out ++ [65]
    rw [ho', show ms.io.out = b.core.io.out from ho.trans (congrArg Io.out hout1), hx]
    rfl

/-- The image of `genBytesImage` at `image + d` has as many program instructions as the image at
`image`, under the premises of `genImageWith_shift`. -/
theorem imageBytesProgLength_shift {m : Module} {k : Nat} {inMax room : UInt64} {cap : Nat}
    {image d : UInt64} {bytes : List UInt8} {L : Layout}
    (hg : genBytesImage m k inMax room cap image = .ok (bytes, L))
    (hlo : 0x40000000 ≤ (image + d).toNat) (hhi : (image + d).toNat + L.size ≤ 0x80000000) :
    imageBytesProgLength m k inMax room cap (image + d) =
      imageBytesProgLength m k inMax room cap image := by
  obtain ⟨prog, start, hp, rfl, -, hhi0, -, -, -⟩ := gen_imageWith hg
  have hsz := (layoutOf_fields image prog.length m cap room).2.2.2.2.2.2.2.2
  have hv := vecOff_ge prog.length
  have hao := areaOff_ge prog.length
  unfold tabOff at hao
  have h70 : startupLength = 70 := rfl
  have e1 : (image + UInt64.ofNat (64 + 4 * startupLength)).toNat = image.toNat + 344 := by
    rw [UInt64.toNat_add, toNat_ofNat_lt (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have e2 : (image + d + UInt64.ofNat (64 + 4 * startupLength)).toNat =
      (image + d).toNat + 344 := by
    rw [UInt64.toNat_add, toNat_ofNat_lt (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have hp' := genBytesProgram_shift hp (by rw [e1]; omega) (by rw [← add_right_comm', e2]; omega)
  rw [← add_right_comm'] at hp'
  simp only [imageBytesProgLength, hp, hp']

/-- `image_bytes_run` at every base `B` that is a multiple of 4096 and whose image lies in the RAM
GiB, given the kernel's check of the image at one base `image`. -/
theorem image_bytes_run_at {m : Module} {k : Nat} {inMax room : UInt64} {cap : Nat}
    {image : UInt64} {nb len : Nat} (h : Hw) {B : UInt64} {b : Boot}
    (hk : bytesOk (genBytesImage m k inMax room cap image) nb len = true)
    (hroom : room.toNat % 16 = 0) (hroom' : 4096 ≤ room.toNat) (himg : image.toNat % 4096 = 0)
    (hB : B.toNat % 4096 = 0) (hlo : 0x40000000 ≤ B.toNat)
    (hhi : B.toNat + imageBytesSize m k inMax room cap image ≤ 0x80000000)
    (hm : ∀ j < len, b.core.mem (B + UInt64.ofNat j) = byteAt nb j)
    (hpc : b.core.pc = B) (hoff : b.mmuOff)
    (hio : b.core.io.rxNext = 0 ∧ b.core.io.rxPolls = 0)
    {Out : List UInt8 → List UInt8} {T : List UInt8 → UInt64 → Prop}
    (hprog : BytesRuns m k inMax room cap Out T) :
    (∀ msg : List UInt8, msg.length ≤ inMax.toNat →
      h.rx.Delivers (bytesOf (UInt64.ofNat msg.length) ++ msg) →
      ∃ b', BootReach h (protectedBytes B (imageBytesProgLength m k inMax room cap image))
          (fetchFrom b.core.mem B (codeWords (imageBytesProgLength m k inMax room cap image)))
          b b' ∧
        fetchFrom b.core.mem B (codeWords (imageBytesProgLength m k inMax room cap image))
          b'.core.pc = some (encode .hvc0) ∧
        b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
        (b'.core.out = b.core.out ++ Out msg ++ [0] ∨
          ∃ c, T msg c ∧ b'.core.out = b.core.out ++ [c.toUInt8])) ∧
    (∀ L : UInt64, inMax < L → h.rx.Delivers (bytesOf L) →
      ∃ b', BootReach h (protectedBytes B (imageBytesProgLength m k inMax room cap image))
          (fetchFrom b.core.mem B (codeWords (imageBytesProgLength m k inMax room cap image)))
          b b' ∧
        fetchFrom b.core.mem B (codeWords (imageBytesProgLength m k inMax room cap image))
          b'.core.pc = some (encode .hvc0) ∧
        b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧ b'.core.out = b.core.out ++ [64]) ∧
    (∀ j, (∀ i < j, ¬ h.rx.Flagged i) → h.rx.Flagged j →
      (j < 8 ∨ (rxSum h.rx 0 8 ≤ inMax.toNat ∧ j < 8 + rxSum h.rx 0 8)) →
      ∃ b', BootReach h (protectedBytes B (imageBytesProgLength m k inMax room cap image))
          (fetchFrom b.core.mem B (codeWords (imageBytesProgLength m k inMax room cap image)))
          b b' ∧
        fetchFrom b.core.mem B (codeWords (imageBytesProgLength m k inMax room cap image))
          b'.core.pc = some (encode .hvc0) ∧
        b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧ b'.core.out = b.core.out ++ [65]) := by
  obtain ⟨bytes, L, hg, -, -⟩ := of_bytesOk hk
  have hBd : image + (B - image) = B := by rw [UInt64.add_comm, UInt64.sub_add_cancel]
  have hd : (B - image).toNat % 4096 = 0 := by
    have := image.toNat_lt
    have := B.toNat_lt
    rw [UInt64.toNat_sub]
    omega
  have hsize : imageBytesSize m k inMax room cap image = L.size := by
    simp only [imageBytesSize, hg]
  have hhi' : (image + (B - image)).toNat + L.size ≤ 0x80000000 := by
    rw [hBd, ← hsize]; exact hhi
  have hlo' : 0x40000000 ≤ (image + (B - image)).toNat := by rw [hBd]; exact hlo
  have hk' := bytesOkWith_shift (genBytesProgram_shiftsBy m k inMax room cap _) hk hd hlo'
    (fun bytes' L' hg' => by
      cases hg.symm.trans hg'
      exact hhi')
  have hN := imageBytesProgLength_shift hg hlo' hhi'
  rw [hBd] at hk' hN
  rw [← hN]
  exact image_bytes_run h hk' hB hroom hroom' hm hpc hoff hio hprog

end LeanExe.A64
