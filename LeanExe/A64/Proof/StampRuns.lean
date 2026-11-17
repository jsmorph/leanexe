import LeanExe.A64.Proof.StampProgram
import LeanExe.A64.Proof.LinuxRuns

/-!
The theorems of programs of `genStampProgram`.  `StampRunsAny` is the form of the theorem of a
stamp program from `main` under the Linux call layer's rule, for every set of replies: the process
returns 0 or reaches the exit word, and the layer's events of its trace are those of
`StampEvents`, with the function's result `Out` and the statuses `Tr` of its traps.
`stamp_runs_any` gives the form from the compiler's theorem of the function and the allocator's
specification at `inMax + 33` bytes.  The block that the reads fill holds the bytes that the
calls returned at its start and, after them, bytes that the last reply wrote.  The buffer that the
function receives is the block's prefix, so the proof needs no statement about the bytes after
it.
-/

namespace LeanExe.A64

open Wasm LeanExe.Pipeline LeanExe.ProofKit
open LeanExe.Linux (Replies)

/-- The form of the theorems of programs of `genStampProgram`, which read the file `pin`, run
function `k` of `m` on the clock's 16 bytes, 16 random bytes, and the file's bytes, and write the
result to the file `pout`: for every platform `P` whose UART lies outside Normal memory, replies
`R`, code map `code` that holds the program after its exit word `base` and the routine
`SVC #0; RET` at `svc`, and words only below 2^55, and area `area`, from `main` with `FPCR` at
`fpcrValue`, no event in the trace, a stack of `room` bytes below the routine's frame, and the
area's premises, the process returns 0 or reaches the exit word, with the UART's state as it was
and the layer's events of `StampEvents`. -/
def StampRunsAny (m : Module) (k : Nat) (inMax room : UInt64) (cap : Nat) (pin pout : List UInt8)
    (Out : List UInt8 → List UInt8) (Tr : List UInt8 → UInt64 → Prop) : Prop :=
  ∀ (P : Platform) (R : Replies) (code : UInt64 → Option UInt32) (svc base area : UInt64)
    {is : List Instr}, genStampProgram m k inMax svc base room cap pin pout = .ok is →
    CodeAt code (after base 1) is → OpsAt code svc [.svc, .ins (.ret 30)] →
    (∀ a w, code a = some w → a.toNat < 2 ^ 55) → base.toNat < 2 ^ 55 →
    ∀ p : Proc, p.core.pc = after base 1 → p.fpcr = fpcrValue → p.trace = [] →
    (p.core.x 30).toNat < 2 ^ 55 → p.core.sp % 16 = 0 → p.core.sp.toNat ≤ 2 ^ 63 →
    (∀ j < room.toNat + stampFrame pin pout,
      P.normal (p.core.sp - UInt64.ofNat (stampFrame pin pout) - room + UInt64.ofNat j) = true) →
    p.core.x 17 = area →
    (∀ j < areaSize cap, p.core.mem (area + UInt64.ofNat j) = areaByte m.initialStore j) →
    (∀ j < areaSize cap, P.normal (area + UInt64.ofNat j) = true) →
    area.toNat + areaSize cap + room.toNat + stampFrame pin pout ≤ p.core.sp.toNat →
    P.normal P.uart = false →
    ∃ p', ProcReachWith LeanExe.Linux.table R P code p p' ∧ p'.core.io = p.core.io ∧
      ((p'.core.pc = p.core.x 30 ∧ p'.core.x 0 = 0 ∧
          StampEvents p.core.sp inMax pin pout Out Tr none (sysEvents p'.trace)) ∨
        (p'.core.pc = base ∧
          StampEvents p.core.sp inMax pin pout Out Tr (some (p'.core.x 0))
            (sysEvents p'.trace)))

/-- The facts about function `k` of `m` that a program of `genStampProgram` needs and its generator
does not check: those of `entryOkWith` for two parameters of type `i64`, and two results of type
`i64`, the root and the length of a buffer. -/
def stampEntryOk (m : Module) (k : Nat) (pin pout : List UInt8) : Bool :=
  entryOkWith (stampMainSize pin pout) m k [.i64, .i64] 2 &&
    decide ((m.funcs[k]?).map (·.results) = some [.i64, .i64])

/-- The payload of an allocation of `bytes` holds at least `bytes` bytes when `bytes + 7` lies
below 2^64. -/
theorem le_allocSize_of_lt {bytes : UInt64} (h : bytes.toNat + 7 < 2 ^ 64) :
    bytes.toNat ≤ (allocSize bytes).toNat := by
  simp only [Nat.reducePow] at h
  have hRound : ((bytes + 7) / 8 * 8).toNat = (bytes.toNat + 7) / 8 * 8 := by
    simp only [UInt64.toNat_mul, UInt64.toNat_div, UInt64.toNat_add, UInt64.reduceToNat]
    omega
  unfold allocSize
  split
  · rename_i hSmall
    rw [UInt64.lt_iff_toNat_lt, hRound] at hSmall
    simp only [UInt64.reduceToNat] at hSmall ⊢
    omega
  · rw [hRound]
    omega

/-- `StampRunsAny` from the compiler's theorem `h` that function `k` of `m` computes `f` over
bytes, for a module whose function 0 is the allocator.  The heap `heap` lies at the module's
initial store, the allocator has room for a block of `inMax + 33` bytes, and the heap after that
block's allocation, at every store with the memory's cap, satisfies the theorem's precondition for
every input of at most `inMax + 32` bytes.  The function's result is `Out` of its input, which
agrees with `f` on such inputs, and its traps are the status 1 of `unreachable` when `aborts`
holds and the status 4 of an overflow of the stack when `room` lies below `stackBound m k`.  The
allocator's stack must fit the room. -/
theorem stamp_runs_any {aborts : Bool} {m : Module} {k : Nat}
    {f : LeanExe.Bytes → LeanExe.Bytes}
    {Pre : LeanExe.Bytes → Heap → Store Unit → Prop}
    {Post : LeanExe.Bytes → Heap → Store Unit → Heap → Store Unit → Prop}
    (h : ImplementsA aborts m k f Pre Post) {typeIdx : Nat}
    (h0 : m.funcs[0]? = some (LeanExe.Runtime.allocFunction typeIdx))
    {inMax room : UInt64} {cap : Nat} {pin pout : List UInt8} {heap : Heap}
    (hheap : heap.At (m.initialStore : Store Unit)) (hinMax : inMax.toNat < 4294967296)
    (hroomA : heap.Room (initStore m cap) m (allocSize (inMax + 33)))
    (hpre : ∀ (b : LeanExe.Bytes) (st : Store Unit), b.data.size ≤ inMax.toNat + 32 →
      st.memoryCap m 0 = cap → Pre b (heap.allocate (allocSize (inMax + 33))) st)
    (h0room : stackBound m 0 ≤ room.toNat)
    {Out : List UInt8 → List UInt8}
    (hout : ∀ D : List UInt8, D.length ≤ inMax.toNat + 32 →
      (f ⟨⟨D.toArray⟩⟩).data.data.toList = Out D)
    (hok : stampEntryOk m k pin pout = true := by decide +kernel) :
    StampRunsAny m k inMax room cap pin pout Out
      fun _ c => (aborts = true ∧ c = 1) ∨ (room.toNat < stackBound m k ∧ c = 4) := by
  intro P R code svc base area is hg hcode hsvc hdom hbase p hpc hf htr h30 hal htop hstack h17
    harea hamap habove hU
  obtain ⟨-, fs, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hao, -, -, hfs, -⟩ :=
    gen_stampProgram hg
  have hcap := cap_lt_of_areaOk hao
  have h64 := memIs64_of_areaOk hao
  unfold stampEntryOk entryOkWith at hok
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
  have hN : (inMax + 33).toNat = inMax.toNat + 33 := by
    rw [UInt64.toNat_add, show (33 : UInt64).toNat = 33 from rfl]
    exact Nat.mod_eq_of_lt (by simp only [Nat.reducePow]; omega)
  have hcap0 : (initStore m cap).memoryCap m 0 ≤ 65535 := by
    have : (initStore m cap).memoryCap m 0 = cap := rfl
    omega
  have hAt0 := heapAt_initStore hheap cap
  have hneedN := le_allocSize_of_lt (bytes := inMax + 33) (by
    rw [hN]
    simp only [Nat.reducePow]
    omega)
  rw [hN] at hneedN
  have h32 : (allocSize (inMax + 33)).toNat < 4294967296 := by
    cases hT : LeanExe.Runtime.takeFirstFitFrom 0 (allocSize (inMax + 33)) heap.free with
    | none =>
        have := (hroomA hT).1
        omega
    | some _ =>
        have hB := hAt0.allocate_block 1 (need := allocSize (inMax + 33)) (by
          intro h'
          rw [hT] at h'
          cases h')
        have := hB.address
        have := allocated_capacity (allocSize (inMax + 33)) heap.free
        omega
  obtain ⟨N0, hN0⟩ : ∃ N, ∀ fuel ≥ N,
      Wasm.run fuel m 0 (initStore m cap) [.i64 (inMax + 33)] =
        .Success [.i64 (FixedArrayAllocate.root heap.top (allocSize (inMax + 33)) heap.free)]
          (heap.allocateStore (initStore m cap) (allocSize (inMax + 33)) 1) ∧
      heap.Fits (allocSize (inMax + 33)) := by
    obtain ⟨N, hN'⟩ := alloc_spec_runs false h64 himp h0 {} heap (initStore m cap)
      (inMax + 33) hAt0 (by rw [hN]; omega) hcap0 (fun _ => hroomA)
    refine ⟨N, fun fuel hf' => ?_⟩
    rcases hN' fuel hf' with ⟨vs, st, hr, hfit, rfl, rfl⟩ | hab
    · exact ⟨hr, hfit⟩
    · exact hab.elim
  have hFits := (hN0 N0 (Nat.le_refl _)).2
  have hBlock := hAt0.allocate_block 1 hFits
  have hAt1 := hAt0.allocate 1 hFits
  have hc := allocated_capacity (allocSize (inMax + 33)) heap.free
  generalize hneed : allocSize (inMax + 33) = need at hFits hN0 hneedN hBlock hAt1 hc
  generalize hroot : FixedArrayAllocate.root heap.top need heap.free = root at hN0 hBlock
  generalize hst1 : heap.allocateStore (initStore m cap) need 1 = st1 at hN0 hBlock hAt1
  generalize hC : allocatedCapacity need heap.free = C at hBlock hc
  have hfit : root.toNat + (inMax.toNat + 33) ≤ st1.mem.pages * 65536 := by
    have := hBlock.memory
    omega
  refine stampProgram_run (R := R) (P := P) (code := code) hg hcode hsvc hdom hbase himp hk hpk
    hrk h0 h0room N0 p hpc hf htr h30 hal htop hstack h17 harea hamap habove hU hinMax root st1
    (hN0 N0 (Nat.le_refl _)).1 hfit (fun st D hlen hcaps hW hD => ?_)
    (fun hlt _ => .inr ⟨hlt, rfl⟩)
  have hW' : WritesWithin st1 st root.toNat C.toNat :=
    ⟨hW.globals, hW.pages, fun a ha => hW.bytes a (by omega)⟩
  have hAt2 := hAt1.writesWithin hBlock hW'
  have hcont : ∀ (i : Nat) (hi : i < (⟨⟨D.toArray⟩⟩ : LeanExe.Bytes).data.size),
      st.mem.bytes (root.toNat + i) = (⟨⟨D.toArray⟩⟩ : LeanExe.Bytes).data[i] := by
    intro i hi
    have hi' : i < D.length := by simpa [ByteArray.size] using hi
    rw [hD i hi']
    simp [ByteArray.getElem_eq_getElem_data, hi']
  have hbuf : (heap.allocate need).Buffer st root ⟨⟨D.toArray⟩⟩ :=
    block_buffer (hBlock.writesWithin hW') hcont (by omega) (by
      show (⟨D.toArray⟩ : ByteArray).size ≤ _
      simp [ByteArray.size]
      omega)
  have hcap2 : st.memoryCap m 0 = cap := by
    unfold Store.memoryCap
    rw [hcaps]
    rfl
  have hL : (UInt64.ofNat D.length).toNat = D.length := by
    rw [UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by simp only [Nat.reducePow]; omega)
  have hrep : Represent.borrowed (heap.allocate need) st
      [.i64 root, .i64 (UInt64.ofNat D.length)] (⟨⟨D.toArray⟩⟩ : LeanExe.Bytes) :=
    ⟨root, UInt64.ofNat D.length, rfl, ⟨by rw [hL]; simp [ByteArray.size], .inr hbuf⟩⟩
  obtain ⟨N1, hN1⟩ := h {} st (heap.allocate need) [.i64 root, .i64 (UInt64.ofNat D.length)]
    ⟨⟨D.toArray⟩⟩ hAt2
    (by rw [← hneed]; exact hpre _ _ (by simp [ByteArray.size]; omega) hcap2) hrep Separate.nil
    (by rw [hcap2]; omega)
  refine ⟨N1, ?_⟩
  have hargs : ([Value.i64 root, .i64 (UInt64.ofNat D.length)]).reverse =
      [.i64 (UInt64.ofNat D.length), .i64 root] := rfl
  rcases hN1 N1 (Nat.le_refl _) with ⟨vs, st3, hr3, heap', hAt', hown, -, -, -⟩ | hab
  · rw [hargs] at hr3
    rw [hr3]
    simp only [StampFunOut]
    obtain ⟨root', len', hvs, hrep'⟩ := hown
    have hvs' : vs = [.i64 len', .i64 root'] := by
      rw [← List.reverse_reverse vs, hvs]
      rfl
    have hsz := hrep'.length_eq
    have hds : ∀ b : ByteArray, b.data.size = b.size := fun _ => rfl
    rw [← hout D hlen]
    refine ⟨root', len', hvs', by rw [Array.length_toList, hds, hsz], ?_, fun i hi => ?_⟩
    · rcases hrep'.buffer with ⟨hr0, h0'⟩ | hb'
      · rw [Array.length_toList, hds, h0', hr0]
        simp
      · have := hb'.object.below
        have := hb'.capacity
        have := hAt'.top
        rw [Array.length_toList, hds]
        omega
    · rw [Array.length_toList, hds] at hi
      rcases hrep'.buffer with ⟨-, h0'⟩ | hb'
      · rw [h0'] at hi
        omega
      · rw [Array.getElem_toList]
        exact hb'.contents i hi
  · cases aborts with
    | false => exact hab.elim
    | true =>
        obtain ⟨st', hr'⟩ := hab
        rw [hargs] at hr'
        rw [hr']
        exact .inl ⟨rfl, .inl ⟨rfl, rfl⟩⟩

/-- `stamp_runs_any` for a function that does not abort and a room that holds its stack: every
trap is excluded. -/
theorem stamp_runs_bounded_any {m : Module} {k : Nat} {f : LeanExe.Bytes → LeanExe.Bytes}
    {Pre : LeanExe.Bytes → Heap → Store Unit → Prop}
    {Post : LeanExe.Bytes → Heap → Store Unit → Heap → Store Unit → Prop}
    (h : ImplementsA false m k f Pre Post) {typeIdx : Nat}
    (h0 : m.funcs[0]? = some (LeanExe.Runtime.allocFunction typeIdx))
    {inMax room : UInt64} {cap : Nat} {pin pout : List UInt8} {heap : Heap}
    (hheap : heap.At (m.initialStore : Store Unit)) (hinMax : inMax.toNat < 4294967296)
    (hroomA : heap.Room (initStore m cap) m (allocSize (inMax + 33)))
    (hpre : ∀ (b : LeanExe.Bytes) (st : Store Unit), b.data.size ≤ inMax.toNat + 32 →
      st.memoryCap m 0 = cap → Pre b (heap.allocate (allocSize (inMax + 33))) st)
    (h0room : stackBound m 0 ≤ room.toNat) (hkroom : stackBound m k ≤ room.toNat)
    {Out : List UInt8 → List UInt8}
    (hout : ∀ D : List UInt8, D.length ≤ inMax.toNat + 32 →
      (f ⟨⟨D.toArray⟩⟩).data.data.toList = Out D)
    (hok : stampEntryOk m k pin pout = true := by decide +kernel) :
    StampRunsAny m k inMax room cap pin pout Out fun _ _ => False := by
  have hT : (fun (_ : List UInt8) (c : UInt64) =>
      (false = true ∧ c = 1) ∨ (room.toNat < stackBound m k ∧ c = 4)) = fun _ _ => False := by
    funext _ c
    refine propext ⟨fun h' => ?_, False.elim⟩
    rcases h' with ⟨h1, -⟩ | ⟨h1, -⟩
    · cases h1
    · omega
  rw [← hT]
  exact stamp_runs_any h h0 hheap hinMax hroomA hpre h0room hout hok

end LeanExe.A64
