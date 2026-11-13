import LeanExe.A64.Proof.LinuxProgram
import LeanExe.A64.Proof.BytesRuns

/-!
The theorems of the programs of Linux executables that run a function over bytes on standard input.
`SysBytesRuns` is the counterpart of `BytesRuns` for a program of `genSysProgram`, from `main` on a
platform whose UART lies outside Normal memory, with `FPCR` at `fpcrValue`, no event in the
process's trace, and a kernel none of whose calls fails.  When standard input holds at most `inMax`
bytes, the process writes `Out` of the input to standard output and returns 0, or reaches the exit
word with a status that `T` allows and writes nothing; when it holds more, the process reaches the
exit word with status 64 and writes nothing.  `sys_bytes_runs` gives `SysBytesRuns` from the
compiler's theorem of the function, the allocator's specification `alloc_spec_runs` at
`inMax + 1` bytes, and `buffer_of_alloc_le`, which states that a block of the allocator holds a
buffer of bytes written into it when they are no more than the bytes allocated.
-/

namespace LeanExe.A64

open Wasm LeanExe.Pipeline LeanExe.ProofKit

/-- The payload of an allocation holds at least 8 bytes. -/
theorem allocSize_ge (x : UInt64) : 8 ≤ (allocSize x).toNat := by
  unfold allocSize
  split
  · rfl
  · rename_i h
    rw [UInt64.not_lt, UInt64.le_iff_toNat_le] at h
    exact h

/-- After the allocation of `need` bytes and the writes of `bs`, at most `need` bytes, from the
block's root, the heap of the allocation lies at the store, and the block holds a buffer of
`bs`. -/
theorem buffer_of_alloc_le {heap : Heap} {st : Store Unit} (hAt : heap.At st) {need : UInt64}
    {bs : List UInt8} (hneed : bs.length ≤ need.toNat) (hmin : 8 ≤ need.toNat)
    (hFits : heap.Fits need) :
    let p := FixedArrayAllocate.root heap.top need heap.free
    let st' := storeBytes (heap.allocateStore st need 1) p.toNat bs
    (heap.allocate need).At st' ∧ (heap.allocate need).Buffer st' p ⟨⟨bs.toArray⟩⟩ ∧
      p.toNat + bs.length ≤ (heap.allocateStore st need 1).mem.pages * 65536 := by
  intro p st'
  have hBlock : (heap.allocate need).Block (heap.allocateStore st need 1) p
      (allocatedCapacity need heap.free) 1 := hAt.allocate_block 1 hFits
  have hcap := allocated_capacity need heap.free
  have haddr := hBlock.address
  have hmem := hBlock.memory
  have hW : WritesWithin (heap.allocateStore st need 1) st' p.toNat
      (allocatedCapacity need heap.free).toNat :=
    storeBytes_write _ p.toNat bs (by omega) _ (by omega)
  refine ⟨(hAt.allocate 1 hFits).writesWithin hBlock hW,
    block_buffer (hBlock.writesWithin hW) (fun i hi => ?_) (by omega) (by
      show (⟨bs.toArray⟩ : ByteArray).size ≤ _
      simp [ByteArray.size]
      omega),
    by omega⟩
  have hi' : i < bs.length := by simpa [ByteArray.size] using hi
  show (storeBytes _ p.toNat bs).mem.bytes _ = _
  rw [storeBytes_bytes _ p.toNat bs (by omega), dif_pos (by omega)]
  simp [ByteArray.getElem_eq_getElem_data]

/-- The form of the theorems of programs of `genSysProgram`, which read standard input to its end
and run function `k` of `m` on its bytes: for every platform `P` whose UART lies outside Normal
memory, kernel `K` none of whose calls fails, code map `code` that holds the program after its exit
word `base`, `sysRead` at `rd`, and `sysWrite` at `wr`, and words only below 2^55, and area `area`,
from `main` with `FPCR` at `fpcrValue`, no event in the trace, and the premises of `BytesRuns` on
the stack and the area: when the input has at most `inMax` bytes, the process writes `Out` of the
input and returns 0, or reaches the exit word with a status that `T` allows and writes nothing;
when it has more, the process reaches the exit word with status 64 and writes nothing.  Every run
leaves the UART's state as it was. -/
def SysBytesRuns (m : Module) (k : Nat) (inMax room : UInt64) (cap : Nat)
    (Out : List UInt8 → List UInt8) (T : List UInt8 → UInt64 → Prop) : Prop :=
  ∀ (P : Platform) (K : Kernel) (code : UInt64 → Option UInt32) (rd wr base area : UInt64)
    {is : List Instr}, genSysProgram m k inMax rd wr base room cap = .ok is →
    CodeAt code (after base 1) is → OpsAt code rd [.ins (.movz 8 63 0), .svc, .ins (.ret 30)] →
    OpsAt code wr [.ins (.movz 8 64 0), .svc, .ins (.ret 30)] →
    (∀ a w, code a = some w → a.toNat < 2 ^ 55) → base.toNat < 2 ^ 55 →
    ∀ p : Proc, p.core.pc = after base 1 → p.fpcr = fpcrValue → p.trace = [] →
    (p.core.x 30).toNat < 2 ^ 55 → p.core.sp % 16 = 0 → 4096 ≤ room.toNat →
    p.core.sp.toNat ≤ 2 ^ 63 →
    (∀ j < room.toNat + 16, P.normal (p.core.sp - 16 - room + UInt64.ofNat j) = true) →
    p.core.x 17 = area →
    (∀ j < areaSize cap, p.core.mem (area + UInt64.ofNat j) = areaByte m.initialStore j) →
    (∀ j < areaSize cap, P.normal (area + UInt64.ofNat j) = true) →
    area.toNat + areaSize cap + room.toNat + 16 ≤ p.core.sp.toNat →
    P.normal P.uart = false → (∀ k, K.fail k = none) →
    (K.input.length ≤ inMax.toNat → ∃ p', ProcReach K P code p p' ∧
      ((p'.core.pc = p.core.x 30 ∧ p'.core.x 0 = 0 ∧ stdoutOf p'.trace = Out K.input) ∨
        (p'.core.pc = base ∧ T K.input (p'.core.x 0) ∧ stdoutOf p'.trace = [])) ∧
      p'.core.io = p.core.io) ∧
    (inMax.toNat < K.input.length → ∃ p', ProcReach K P code p p' ∧ p'.core.pc = base ∧
      p'.core.x 0 = 64 ∧ stdoutOf p'.trace = [] ∧ p'.core.io = p.core.io)

/-- The facts about function `k` of `m` that a program of `genSysProgram` needs and its generator
does not check: those of `entryOkWith` for two parameters of type `i64`, and two results of type
`i64`, the root and the length of a buffer. -/
def sysEntryOk (m : Module) (k : Nat) : Bool :=
  entryOkWith sysMainSize m k [.i64, .i64] 2 &&
    decide ((m.funcs[k]?).map (·.results) = some [.i64, .i64])

theorem genSysProgram_length {m : Module} {k : Nat} {inMax rd wr base room : UInt64}
    {cap : Nat} {is : List Instr} (hg : genSysProgram m k inMax rd wr base room cap = .ok is)
    {fs : List (Nat × Function)} (hfs : (reachFrom m k).mapM (funcOf m) = .ok fs) :
    is.length = sysMainSize +
      (fs.map fun x => functionSize (sigIn (callTargets m k) fs) x.2).sum + 20 :=
  genProgramWith_length hg (fun e main hmg => by
    simp only [bind, Except.bind] at hmg
    split at hmg
    · cases hmg
    · split at hmg
      · exact genSysMain_length hmg
      · cases hmg) hfs

/-- The form of the theorems of programs of `genSysProgram` for every kernel: from `main` with the
premises of `SysBytesRuns` but the one on failures, the process reaches one of five ends, with the
UART's state as it was.  It returns 0 after writing `Out` of the input, which holds at most `inMax`
bytes; it reaches the exit word with a status that `T` allows and nothing written, for such an
input; it reaches the exit word with status 64 and nothing written, for a longer input; in these
three, no call failed.  When a read fails, it reaches the exit word with status 65, nothing
written, and the failure as the trace's last event; when a write fails, it reaches the exit word
with status 66 after writing a prefix of `Out` of the input, with the failure as the trace's last
event.  No other event of a trace is a failure. -/
def SysBytesRunsAny (m : Module) (k : Nat) (inMax room : UInt64) (cap : Nat)
    (Out : List UInt8 → List UInt8) (T : List UInt8 → UInt64 → Prop) : Prop :=
  ∀ (P : Platform) (K : Kernel) (code : UInt64 → Option UInt32) (rd wr base area : UInt64)
    {is : List Instr}, genSysProgram m k inMax rd wr base room cap = .ok is →
    CodeAt code (after base 1) is → OpsAt code rd [.ins (.movz 8 63 0), .svc, .ins (.ret 30)] →
    OpsAt code wr [.ins (.movz 8 64 0), .svc, .ins (.ret 30)] →
    (∀ a w, code a = some w → a.toNat < 2 ^ 55) → base.toNat < 2 ^ 55 →
    ∀ p : Proc, p.core.pc = after base 1 → p.fpcr = fpcrValue → p.trace = [] →
    (p.core.x 30).toNat < 2 ^ 55 → p.core.sp % 16 = 0 → 4096 ≤ room.toNat →
    p.core.sp.toNat ≤ 2 ^ 63 →
    (∀ j < room.toNat + 16, P.normal (p.core.sp - 16 - room + UInt64.ofNat j) = true) →
    p.core.x 17 = area →
    (∀ j < areaSize cap, p.core.mem (area + UInt64.ofNat j) = areaByte m.initialStore j) →
    (∀ j < areaSize cap, P.normal (area + UInt64.ofNat j) = true) →
    area.toNat + areaSize cap + room.toNat + 16 ≤ p.core.sp.toNat →
    P.normal P.uart = false →
    ∃ p', ProcReach K P code p p' ∧ p'.core.io = p.core.io ∧
      ((p'.core.pc = p.core.x 30 ∧ p'.core.x 0 = 0 ∧ K.input.length ≤ inMax.toNat ∧
          stdoutOf p'.trace = Out K.input ∧ ∀ nr e, Event.fail nr e ∉ p'.trace) ∨
        (p'.core.pc = base ∧ K.input.length ≤ inMax.toNat ∧ T K.input (p'.core.x 0) ∧
          stdoutOf p'.trace = [] ∧ ∀ nr e, Event.fail nr e ∉ p'.trace) ∨
        (p'.core.pc = base ∧ p'.core.x 0 = 64 ∧ inMax.toNat < K.input.length ∧
          stdoutOf p'.trace = [] ∧ ∀ nr e, Event.fail nr e ∉ p'.trace) ∨
        (p'.core.pc = base ∧ p'.core.x 0 = 65 ∧ (∃ k e, K.fail k = some e) ∧
          ∃ tr e, p'.trace = tr ++ [.fail 63 e] ∧ stdoutOf tr = [] ∧
            ∀ nr e', Event.fail nr e' ∉ tr) ∨
        (p'.core.pc = base ∧ p'.core.x 0 = 66 ∧ K.input.length ≤ inMax.toNat ∧
          (∃ k e, K.fail k = some e) ∧
          ∃ tr e, p'.trace = tr ++ [.fail 64 e] ∧ stdoutOf tr <+: Out K.input ∧
            ∀ nr e', Event.fail nr e' ∉ tr))

/-- `SysBytesRunsAny` gives `SysBytesRuns`: for a kernel none of whose calls fails, the ends with
a failure do not occur. -/
theorem SysBytesRunsAny.sysBytesRuns {m : Module} {k : Nat} {inMax room : UInt64} {cap : Nat}
    {Out : List UInt8 → List UInt8} {T : List UInt8 → UInt64 → Prop}
    (h : SysBytesRunsAny m k inMax room cap Out T) : SysBytesRuns m k inMax room cap Out T := by
  intro P K code rd wr base area is hg hcode hrd hwr hdom hbase p hpc hf htr h30 hal hroom htop
    hstack h17 harea hamap habove hU hfail
  obtain ⟨p', r', io', out⟩ := h P K code rd wr base area hg hcode hrd hwr hdom hbase p hpc hf
    htr h30 hal hroom htop hstack h17 harea hamap habove hU
  have hno : ∀ k e, K.fail k = some e → False := fun k e he => by rw [hfail k] at he; cases he
  refine ⟨fun hlen => ?_, fun hlong => ?_⟩
  · rcases out with ⟨pc', x', -, o', -⟩ | ⟨pc', -, t', o', -⟩ | ⟨-, -, hl, -, -⟩ |
      ⟨-, -, ⟨k, e, he⟩, -⟩ | ⟨-, -, -, ⟨k, e, he⟩, -⟩
    · exact ⟨p', r', .inl ⟨pc', x', o'⟩, io'⟩
    · exact ⟨p', r', .inr ⟨pc', t', o'⟩, io'⟩
    · omega
    · exact (hno k e he).elim
    · exact (hno k e he).elim
  · rcases out with ⟨-, -, hl, -, -⟩ | ⟨-, hl, -, -, -⟩ | ⟨pc', x', -, o', -⟩ |
      ⟨-, -, ⟨k, e, he⟩, -⟩ | ⟨-, -, -, ⟨k, e, he⟩, -⟩
    · omega
    · omega
    · exact ⟨p', r', pc', x', o', io'⟩
    · exact (hno k e he).elim
    · exact (hno k e he).elim

/-- `SysBytesRunsAny` from the compiler's theorem `h` that function `k` of `m` computes `f` over
bytes, for a module whose function 0 is the allocator.  The heap `heap` lies at the module's
initial store, the allocator has room for a block of `inMax + 1` bytes, and the heap after that
block's allocation, at the store with the memory's cap, satisfies the theorem's precondition for
every input of at most `inMax` bytes.  The program writes the bytes of `f` of the input and returns
0, or reaches the exit word with the status 1 of `unreachable` when `aborts` holds, or with the
status 4 of an overflow of the stack when `room` lies below `stackBound m k`, or with the statuses
of the input's length and of the calls that fail.  The allocator's stack must fit the room. -/
theorem sys_bytes_runs_any {aborts : Bool} {m : Module} {k : Nat}
    {f : LeanExe.Bytes → LeanExe.Bytes}
    {Pre : LeanExe.Bytes → Heap → Store Unit → Prop}
    {Post : LeanExe.Bytes → Heap → Store Unit → Heap → Store Unit → Prop}
    (h : ImplementsA aborts m k f Pre Post) {typeIdx : Nat}
    (h0 : m.funcs[0]? = some (LeanExe.Runtime.allocFunction typeIdx))
    {inMax room : UInt64} {cap : Nat} {heap : Heap}
    (hheap : heap.At (m.initialStore : Store Unit)) (hinMax : inMax.toNat < 4294967296)
    (hroomA : heap.Room (initStore m cap) m (allocSize (inMax + 1)))
    (hpre : ∀ (b : LeanExe.Bytes) (st : Store Unit), b.data.size ≤ inMax.toNat →
      st.memoryCap m 0 = cap → Pre b (heap.allocate (allocSize (inMax + 1))) st)
    (h0room : stackBound m 0 ≤ room.toNat)
    (hok : sysEntryOk m k = true := by decide +kernel) :
    SysBytesRunsAny m k inMax room cap (fun msg => (f ⟨⟨msg.toArray⟩⟩).data.data.toList)
      fun _ c => (aborts = true ∧ c = 1) ∨ (room.toNat < stackBound m k ∧ c = 4) := by
  intro P K code rd wr base area is hg hcode hrd hwr hdom hbase p hpc hf htr h30 hal hroom htop
    hstack h17 harea hamap habove hU
  obtain ⟨-, fs, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hao, -, -, hfs, -⟩ :=
    gen_sysProgram hg
  have hcap := cap_lt_of_areaOk hao
  have h64 := memIs64_of_areaOk hao
  unfold sysEntryOk entryOkWith at hok
  rw [hfs] at hok
  simp only [Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨himp, hpar⟩, -⟩, -⟩, hres⟩ := hok
  obtain ⟨fk, hk, hpk, hrk⟩ : ∃ fk, m.funcs[k]? = some fk ∧ fk.params = [.i64, .i64] ∧
      fk.results = [.i64, .i64] := by
    cases hk : m.funcs[k]? with
    | none => rw [hk] at hpar; cases hpar
    | some g =>
        rw [hk] at hpar hres
        exact ⟨g, rfl, Option.some.inj hpar, Option.some.inj hres⟩
  have hN : (inMax + 1).toNat = inMax.toNat + 1 := by
    rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
    simp only [Nat.reducePow] at *
    omega
  have hcap0 : (initStore m cap).memoryCap m 0 ≤ 65535 := by
    have : (initStore m cap).memoryCap m 0 = cap := rfl
    omega
  -- the allocator's run on `inMax + 1`
  obtain ⟨N0, hN0⟩ : ∃ N, ∀ fuel ≥ N,
      Wasm.run fuel m 0 (initStore m cap) [.i64 (inMax + 1)] =
        .Success [.i64 (FixedArrayAllocate.root heap.top (allocSize (inMax + 1)) heap.free)]
          (heap.allocateStore (initStore m cap) (allocSize (inMax + 1)) 1) ∧
      heap.Fits (allocSize (inMax + 1)) := by
    obtain ⟨N, hN'⟩ := alloc_spec_runs false h64 himp h0 {} heap (initStore m cap)
      (inMax + 1) (heapAt_initStore hheap cap) (by rw [hN]; omega) hcap0 (fun _ => hroomA)
    refine ⟨N, fun fuel hf' => ?_⟩
    rcases hN' fuel hf' with ⟨vs, st, hr, hfit, rfl, rfl⟩ | hab
    · exact ⟨hr, hfit⟩
    · exact hab.elim
  have hFits := (hN0 N0 (Nat.le_refl _)).2
  have hAt0 := heapAt_initStore hheap cap
  have hneedN : inMax.toNat + 1 ≤ (allocSize (inMax + 1)).toNat := by
    have := le_allocSize (bytes := inMax + 1) (by rw [hN]; omega)
    rwa [hN] at this
  have hrun := fun F => sysProgram_run P code (K := K) hg hcode hrd hwr hdom hbase himp hk hpk hrk
    h0 h0room F p hpc hf htr h30 hal hroom htop hstack h17 harea hamap habove hU (by omega)
  -- the block's room for `inMax + 1` bytes
  have hfit : (FixedArrayAllocate.root heap.top (allocSize (inMax + 1)) heap.free).toNat +
      (inMax.toNat + 1) ≤
      (heap.allocateStore (initStore m cap) (allocSize (inMax + 1)) 1).mem.pages * 65536 := by
    have hBlock := hAt0.allocate_block 1 hFits
    have hc := allocated_capacity (allocSize (inMax + 1)) heap.free
    have := hBlock.memory
    omega
  rcases Nat.lt_or_ge inMax.toNat K.input.length with hlong | hlen
  · -- an input longer than the limit, or a failed read
    rcases (hrun N0) _ _ (hN0 N0 (Nat.le_refl _)).1 hfit with
      ⟨p', r', pc', x', io', hk', tr, e, htr', out', nf'⟩ | ⟨h1, -⟩
    · exact ⟨p', r', io', .inr (.inr (.inr (.inl ⟨pc', x', hk', tr, e, htr', out', nf'⟩)))⟩
    · obtain ⟨p', r', pc', x', o', io', nf'⟩ := h1 hlong
      exact ⟨p', r', io', .inr (.inr (.inl ⟨pc', x', hlong, o', nf'⟩))⟩
  -- an input within the limit
  obtain ⟨hAt2, hbuf, -⟩ := buffer_of_alloc_le hAt0 (bs := K.input) (by omega)
    (allocSize_ge _) hFits
  generalize hneed : allocSize (inMax + 1) = need at hFits hAt2 hbuf hN0 hfit
  generalize hroot : FixedArrayAllocate.root heap.top need heap.free = root at hAt2 hbuf hN0 hfit
  generalize hst1 : heap.allocateStore (initStore m cap) need 1 = st1 at hAt2 hbuf hN0 hfit
  have hL : (UInt64.ofNat K.input.length).toNat = K.input.length := by
    rw [UInt64.toNat_ofNat']
    simp only [Nat.reducePow] at *
    omega
  have hcap2 : (storeBytes st1 root.toNat K.input).memoryCap m 0 = cap := by
    unfold Store.memoryCap
    rw [(storeBytes_globals st1 root.toNat K.input).2.2, ← hst1, Heap.allocateStore_memoryCaps]
    rfl
  have hrep : Represent.borrowed (heap.allocate need) (storeBytes st1 root.toNat K.input)
      [.i64 root, .i64 (UInt64.ofNat K.input.length)] (⟨⟨K.input.toArray⟩⟩ : LeanExe.Bytes) :=
    ⟨root, UInt64.ofNat K.input.length, rfl, ⟨by rw [hL]; simp [ByteArray.size], .inr hbuf⟩⟩
  obtain ⟨N1, hN1⟩ := h {} (storeBytes st1 root.toNat K.input) (heap.allocate need)
    [.i64 root, .i64 (UInt64.ofNat K.input.length)] ⟨⟨K.input.toArray⟩⟩ hAt2
    (by rw [← hneed]; exact hpre _ _ (by simp [ByteArray.size]; omega) hcap2) hrep Separate.nil
    (by rw [hcap2]; omega)
  have hA := (hN0 (max N0 N1) (Nat.le_max_left _ _)).1
  rcases (hrun (max N0 N1)) root st1 hA hfit with
    ⟨p', r', pc', x', io', hk', tr, e, htr', out', nf'⟩ | ⟨-, h2⟩
  · exact ⟨p', r', io', .inr (.inr (.inr (.inl ⟨pc', x', hk', tr, e, htr', out', nf'⟩)))⟩
  rcases h2 hlen with ⟨p', r', pc', x', o', io', hlt', nf'⟩ | hres
  · exact ⟨p', r', io', .inr (.inl ⟨pc', hlen, .inr ⟨hlt', x'⟩, o', nf'⟩)⟩
  rcases hN1 (max N0 N1) (Nat.le_max_right _ _) with
    ⟨vs, st3, hr3, heap', hAt', hown, -, -, -⟩ | hab
  · rw [show ([Value.i64 root, .i64 (UInt64.ofNat K.input.length)]).reverse =
      [.i64 (UInt64.ofNat K.input.length), .i64 root] from rfl] at hr3
    rw [hr3] at hres
    obtain ⟨root', len', hvs, hrep'⟩ := hown
    have hvs' : vs = [.i64 len', .i64 root'] := by
      rw [← List.reverse_reverse vs, hvs]
      rfl
    have hsz := hrep'.length_eq
    have hds : ∀ b : ByteArray, b.data.size = b.size := fun _ => rfl
    rcases hres root' len' (f ⟨⟨K.input.toArray⟩⟩).data.data.toList
      hvs' (by rw [Array.length_toList, hds, hsz])
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
          exact hb'.contents i hi) with
      ⟨p', r', pc', x', o', io', nf'⟩ | ⟨p', r', pc', x', io', hk', tr, e, htr', pre', nf'⟩
    · exact ⟨p', r', io', .inl ⟨pc', x', hlen, o', nf'⟩⟩
    · exact ⟨p', r', io',
        .inr (.inr (.inr (.inr ⟨pc', x', hlen, hk', tr, e, htr', pre', nf'⟩)))⟩
  · cases aborts with
    | false => exact hab.elim
    | true =>
        obtain ⟨st', hr'⟩ := hab
        rw [show ([Value.i64 root, .i64 (UInt64.ofNat K.input.length)]).reverse =
          [.i64 (UInt64.ofNat K.input.length), .i64 root] from rfl] at hr'
        rw [hr'] at hres
        obtain ⟨p', r', pc', o', io', nf', hm⟩ := hres
        rcases hm with ⟨-, hx⟩ | ⟨he, -⟩ | ⟨he, -⟩
        · exact ⟨p', r', io', .inr (.inl ⟨pc', hlen, .inl ⟨rfl, hx⟩, o', nf'⟩)⟩
        · exact absurd he (by decide)
        · exact absurd he (by decide)

/-- `SysBytesRuns` from the compiler's theorem `h` that function `k` of `m` computes `f` over
bytes, for a module whose function 0 is the allocator, through `sys_bytes_runs_any`.  The program
writes the bytes of `f` of the input and returns 0, or reaches the exit word with the status 1 of
`unreachable` when `aborts` holds, or with the status 4 of an overflow of the stack when `room`
lies below `stackBound m k`. -/
theorem sys_bytes_runs {aborts : Bool} {m : Module} {k : Nat} {f : LeanExe.Bytes → LeanExe.Bytes}
    {Pre : LeanExe.Bytes → Heap → Store Unit → Prop}
    {Post : LeanExe.Bytes → Heap → Store Unit → Heap → Store Unit → Prop}
    (h : ImplementsA aborts m k f Pre Post) {typeIdx : Nat}
    (h0 : m.funcs[0]? = some (LeanExe.Runtime.allocFunction typeIdx))
    {inMax room : UInt64} {cap : Nat} {heap : Heap}
    (hheap : heap.At (m.initialStore : Store Unit)) (hinMax : inMax.toNat < 4294967296)
    (hroomA : heap.Room (initStore m cap) m (allocSize (inMax + 1)))
    (hpre : ∀ (b : LeanExe.Bytes) (st : Store Unit), b.data.size ≤ inMax.toNat →
      st.memoryCap m 0 = cap → Pre b (heap.allocate (allocSize (inMax + 1))) st)
    (h0room : stackBound m 0 ≤ room.toNat)
    (hok : sysEntryOk m k = true := by decide +kernel) :
    SysBytesRuns m k inMax room cap (fun msg => (f ⟨⟨msg.toArray⟩⟩).data.data.toList)
      fun _ c => (aborts = true ∧ c = 1) ∨ (room.toNat < stackBound m k ∧ c = 4) :=
  (sys_bytes_runs_any h h0 hheap hinMax hroomA hpre h0room hok).sysBytesRuns

/-- `sys_bytes_runs` for a theorem without the trap at `unreachable` and a stack whose bound is at
most `room`: no status. -/
theorem sys_bytes_runs_bounded {m : Module} {k : Nat} {f : LeanExe.Bytes → LeanExe.Bytes}
    {Pre : LeanExe.Bytes → Heap → Store Unit → Prop}
    {Post : LeanExe.Bytes → Heap → Store Unit → Heap → Store Unit → Prop}
    (h : ImplementsA false m k f Pre Post) {typeIdx : Nat}
    (h0 : m.funcs[0]? = some (LeanExe.Runtime.allocFunction typeIdx))
    {inMax room : UInt64} {cap : Nat} {heap : Heap}
    (hheap : heap.At (m.initialStore : Store Unit)) (hinMax : inMax.toNat < 4294967296)
    (hroomA : heap.Room (initStore m cap) m (allocSize (inMax + 1)))
    (hpre : ∀ (b : LeanExe.Bytes) (st : Store Unit), b.data.size ≤ inMax.toNat →
      st.memoryCap m 0 = cap → Pre b (heap.allocate (allocSize (inMax + 1))) st)
    (h0room : stackBound m 0 ≤ room.toNat) (hkroom : stackBound m k ≤ room.toNat)
    (hok : sysEntryOk m k = true := by decide +kernel) :
    SysBytesRuns m k inMax room cap (fun msg => (f ⟨⟨msg.toArray⟩⟩).data.data.toList)
      fun _ _ => False := by
  intro P K code rd wr base area is hg hcode hrd hwr hdom hbase p hpc hf htr h30 hal hroom htop
    hstack h17 harea hamap habove hU hfail
  obtain ⟨h1, h2⟩ := sys_bytes_runs h h0 hheap hinMax hroomA hpre h0room hok P K code rd wr base
    area hg hcode hrd hwr hdom hbase p hpc hf htr h30 hal hroom htop hstack h17 harea hamap habove
    hU hfail
  refine ⟨fun hlen => ?_, h2⟩
  obtain ⟨p', r', out, io'⟩ := h1 hlen
  rcases out with hr | ⟨_, ⟨hf', -⟩ | ⟨hlt, -⟩, -⟩
  · exact ⟨p', r', .inl hr, io'⟩
  · cases hf'
  · omega

/-- `SysBytesRuns` for an output `Out'` that agrees with `Out` on every input of at most `inMax`
bytes. -/
theorem SysBytesRuns.congr {m : Module} {k : Nat} {inMax room : UInt64} {cap : Nat}
    {Out Out' : List UInt8 → List UInt8} {T : List UInt8 → UInt64 → Prop}
    (h : SysBytesRuns m k inMax room cap Out T)
    (hout : ∀ msg : List UInt8, msg.length ≤ inMax.toNat → Out msg = Out' msg) :
    SysBytesRuns m k inMax room cap Out' T := by
  intro P K code rd wr base area is hg hcode hrd hwr hdom hbase p hpc hf htr h30 hal hroom htop
    hstack h17 harea hamap habove hU hfail
  obtain ⟨h1, h2⟩ := h P K code rd wr base area hg hcode hrd hwr hdom hbase p hpc hf htr h30 hal
    hroom htop hstack h17 harea hamap habove hU hfail
  refine ⟨fun hlen => ?_, h2⟩
  rw [← hout K.input hlen]
  exact h1 hlen


/-- `sys_bytes_runs_any` for a theorem without the trap at `unreachable` and a stack whose bound
is at most `room`: no status of `T`. -/
theorem sys_bytes_runs_bounded_any {m : Module} {k : Nat} {f : LeanExe.Bytes → LeanExe.Bytes}
    {Pre : LeanExe.Bytes → Heap → Store Unit → Prop}
    {Post : LeanExe.Bytes → Heap → Store Unit → Heap → Store Unit → Prop}
    (h : ImplementsA false m k f Pre Post) {typeIdx : Nat}
    (h0 : m.funcs[0]? = some (LeanExe.Runtime.allocFunction typeIdx))
    {inMax room : UInt64} {cap : Nat} {heap : Heap}
    (hheap : heap.At (m.initialStore : Store Unit)) (hinMax : inMax.toNat < 4294967296)
    (hroomA : heap.Room (initStore m cap) m (allocSize (inMax + 1)))
    (hpre : ∀ (b : LeanExe.Bytes) (st : Store Unit), b.data.size ≤ inMax.toNat →
      st.memoryCap m 0 = cap → Pre b (heap.allocate (allocSize (inMax + 1))) st)
    (h0room : stackBound m 0 ≤ room.toNat) (hkroom : stackBound m k ≤ room.toNat)
    (hok : sysEntryOk m k = true := by decide +kernel) :
    SysBytesRunsAny m k inMax room cap (fun msg => (f ⟨⟨msg.toArray⟩⟩).data.data.toList)
      fun _ _ => False := by
  intro P K code rd wr base area is hg hcode hrd hwr hdom hbase p hpc hf htr h30 hal hroom htop
    hstack h17 harea hamap habove hU
  obtain ⟨p', r', io', out⟩ := sys_bytes_runs_any h h0 hheap hinMax hroomA hpre h0room hok P K
    code rd wr base area hg hcode hrd hwr hdom hbase p hpc hf htr h30 hal hroom htop hstack h17
    harea hamap habove hU
  refine ⟨p', r', io', ?_⟩
  rcases out with h1 | ⟨-, -, ⟨hf', -⟩ | ⟨hlt, -⟩, -, -⟩ | h3
  · exact .inl h1
  · cases hf'
  · omega
  · exact .inr (.inr h3)

/-- `SysBytesRunsAny` for an output `Out'` that agrees with `Out` on every input of at most
`inMax` bytes. -/
theorem SysBytesRunsAny.congr {m : Module} {k : Nat} {inMax room : UInt64} {cap : Nat}
    {Out Out' : List UInt8 → List UInt8} {T : List UInt8 → UInt64 → Prop}
    (h : SysBytesRunsAny m k inMax room cap Out T)
    (hout : ∀ msg : List UInt8, msg.length ≤ inMax.toNat → Out msg = Out' msg) :
    SysBytesRunsAny m k inMax room cap Out' T := by
  intro P K code rd wr base area is hg hcode hrd hwr hdom hbase p hpc hf htr h30 hal hroom htop
    hstack h17 harea hamap habove hU
  obtain ⟨p', r', io', out⟩ := h P K code rd wr base area hg hcode hrd hwr hdom hbase p hpc hf
    htr h30 hal hroom htop hstack h17 harea hamap habove hU
  refine ⟨p', r', io', ?_⟩
  rcases out with ⟨a, b, hl, o, n⟩ | h2 | h3 | h4 | ⟨a, b, hl, c, tr, e, d, pre, n⟩
  · exact .inl ⟨a, b, hl, by rw [← hout _ hl]; exact o, n⟩
  · exact .inr (.inl h2)
  · exact .inr (.inr (.inl h3))
  · exact .inr (.inr (.inr (.inl h4)))
  · exact .inr (.inr (.inr (.inr
      ⟨a, b, hl, c, tr, e, d, by rw [← hout _ hl]; exact pre, n⟩)))

end LeanExe.A64
