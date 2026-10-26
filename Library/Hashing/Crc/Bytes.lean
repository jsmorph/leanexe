import Library.Hashing.Crc.Compiled
import Library.Hashing.Crc.Proof

/-! The bytes of the module `crc` compute CRC-32 and CRC-32C.  An entry, called from a ready store
with a borrowed array `msg` and a byte count `n`, returns without a trap the word whose value is
the CRC of the transcription `Library.Hashing.Crc.Spec` for the first `n` bytes of `msg`.  An
update entry, called also with the CRC of some bytes `A`, returns the CRC of `A` followed by those
bytes.  The array stays borrowed, the store stays ready, and every region of the heap before the
call keeps its bytes.  The store in which the module starts is ready. -/

namespace Library.Hashing.Crc

open Wasm LeanExe.Pipeline Library.Bytes Library.Hashing.Crc.Proof

/-- A store from which the module's entries run, with `heap` the allocator's state: the allocator
invariant holds, the tables are borrowed arrays at addresses 4096 and 6152, and the memory cap is
at most 65,535 pages. -/
def Ready (heap : Heap) (store : Store Unit) : Prop :=
  heap.At store ∧ heap.Borrowed store 4096 crc32Table ∧ heap.Borrowed store 6152 crc32cTable ∧
    store.memoryCap compiled.module 0 ≤ 65535

set_option maxRecDepth 10000 in
/-- The store in which the module starts is ready, with the heap that holds its tables.  The
address of the second table depends on the size of the first, whose unfolding needs a raised
`maxRecDepth`. -/
theorem ready_initial :
    Ready (Verified.initialHeap compiled.tables) compiled.module.initialStore := by
  obtain ⟨hAt, hCap, hBor⟩ := compiled.initial
  exact ⟨hAt, hBor 0 (by decide), hBor 1 (by decide), hCap⟩

/-- A borrowed array stays borrowed through a step that keeps the bytes of every region. -/
theorem borrowed_kept {heap heap' : Heap} {store final : Store Unit} {p : UInt64}
    {ws : Array UInt64} (hp : heap.Borrowed store p ws) (hAt : heap'.At final)
    (hkeep : ∀ r, heap.Region r → 0 < r.2 →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧ heap'.Region r) :
    heap'.Borrowed final p ws := by
  obtain ⟨hb, hr⟩ := hkeep _ hp.region (by show 0 < 8 * (ws.size + 1); omega)
  exact hp.keepIn hAt hb hr

/-- The table `t` at `p` is one of the module's tables. -/
theorem table_of_ready {heap : Heap} {store : Store Unit} {p : UInt64} {t : Array UInt64}
    (h : Ready heap store) (ht : (p, t) = (4096, crc32Table) ∨ (p, t) = (6152, crc32cTable)) :
    ∀ x ∈ [(p, t)], heap.Borrowed store x.1 x.2 ∧ Apart store [] (x.1.toNat, 8 * (x.2.size + 1)) := by
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  rcases ht with ht | ht <;> simp only [Prod.mk.injEq] at ht <;> obtain ⟨rfl, rfl⟩ := ht
  · exact ⟨h.2.1, Apart.nil⟩
  · exact ⟨h.2.2.1, Apart.nil⟩

/-- The store after a call stays ready, the array stays borrowed, and every region keeps its
bytes. -/
theorem ready_after {heap heap' : Heap} {store final : Store Unit} {ptr : UInt64}
    {msg : Array UInt64} (h : Ready heap store) (hb : heap.Borrowed store ptr msg)
    (hAt' : heap'.At final) (hcaps : final.memoryCaps = store.memoryCaps)
    (hframe : ∀ r, heap.Region r → 0 < r.2 → Apart store [] r →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region r ∧ True) :
    Ready heap' final ∧ heap'.Borrowed final ptr msg ∧
      ∀ r, heap.Region r → 0 < r.2 →
        (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
          heap'.Region r := by
  obtain ⟨_, h32, h32c, hCap⟩ := h
  have hkeep : ∀ r, heap.Region r → 0 < r.2 →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region r :=
    fun r hr hpos => ⟨(hframe r hr hpos Apart.nil).1, (hframe r hr hpos Apart.nil).2.1⟩
  exact ⟨⟨hAt', borrowed_kept h32 hAt' hkeep, borrowed_kept h32c hAt' hkeep,
    memoryCap_le_of_caps hcaps hCap⟩, borrowed_kept hb hAt' hkeep, hkeep⟩

/-- A call of an entry that computes `f` from the table `t` at `p`, from a ready store with the
borrowed array `msg` at `ptr` and the word `n`. -/
theorem entry_call {k : Nat} {p : UInt64} {t : Array UInt64} {f : Array UInt64 → UInt64 → UInt64}
    (hI : Verified.ImplementsTables false compiled.module k
      (fun x : Array UInt64 × UInt64 => f x.1 x.2) [(p, t)]
      (fun _ _ _ => True) (fun _ _ _ _ _ => True))
    (ht : (p, t) = (4096, crc32Table) ∨ (p, t) = (6152, crc32cTable))
    (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (msg : Array UInt64) (n ptr : UInt64)
    (h : Ready heap store) (hb : heap.Borrowed store ptr msg) :
    Runs false env compiled.module k store [.i64 n, .i64 ptr] fun final values =>
      values.reverse = [.i64 (f msg n)] ∧
      ∃ heap' : Heap, Ready heap' final ∧ heap'.Borrowed final ptr msg ∧
        ∀ r, heap.Region r → 0 < r.2 →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r := by
  have hargs : Represent.borrowed heap store [.i64 ptr, .i64 n] (msg, n) :=
    ⟨[.i64 ptr], [.i64 n], rfl, ⟨ptr, rfl, hb⟩, rfl⟩
  refine (hI env store heap [.i64 ptr, .i64 n] (msg, n) h.1 trivial (table_of_ready h ht) hargs
    Separate.nil h.2.2.2).mono ?_
  intro final values hpost
  obtain ⟨heap', hAt', howned, hcaps, hframe, _⟩ := hpost
  exact ⟨howned, heap', ready_after h hb hAt' hcaps fun r hr hpos hap =>
    ⟨(hframe r hr hpos hap).1, (hframe r hr hpos hap).2.1, trivial⟩⟩

/-- A call of an update entry that computes `f` from the table `t` at `p`, from a ready store with
the word `crc`, the borrowed array `msg` at `ptr`, and the word `n`. -/
theorem update_call {k : Nat} {p : UInt64} {t : Array UInt64}
    {f : UInt64 → Array UInt64 → UInt64 → UInt64}
    (hI : Verified.ImplementsTables false compiled.module k
      (fun x : UInt64 × Array UInt64 × UInt64 => f x.1 x.2.1 x.2.2) [(p, t)]
      (fun _ _ _ => True) (fun _ _ _ _ _ => True))
    (ht : (p, t) = (4096, crc32Table) ∨ (p, t) = (6152, crc32cTable))
    (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (crc : UInt64) (msg : Array UInt64)
    (n ptr : UInt64) (h : Ready heap store) (hb : heap.Borrowed store ptr msg) :
    Runs false env compiled.module k store [.i64 n, .i64 ptr, .i64 crc] fun final values =>
      values.reverse = [.i64 (f crc msg n)] ∧
      ∃ heap' : Heap, Ready heap' final ∧ heap'.Borrowed final ptr msg ∧
        ∀ r, heap.Region r → 0 < r.2 →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r := by
  have hargs : Represent.borrowed heap store [.i64 crc, .i64 ptr, .i64 n] (crc, msg, n) :=
    ⟨[.i64 crc], [.i64 ptr, .i64 n], rfl, rfl, [.i64 ptr], [.i64 n], rfl, ⟨ptr, rfl, hb⟩, rfl⟩
  refine (hI env store heap [.i64 crc, .i64 ptr, .i64 n] (crc, msg, n) h.1 trivial
    (table_of_ready h ht) hargs Separate.nil h.2.2.2).mono ?_
  intro final values hpost
  obtain ⟨heap', hAt', howned, hcaps, hframe, _⟩ := hpost
  exact ⟨howned, heap', ready_after h hb hAt' hcaps fun r hr hpos hap =>
    ⟨(hframe r hr hpos hap).1, (hframe r hr hpos hap).2.1, trivial⟩⟩

theorem crc32_export :
    ({ name := "crc32", funcIdx := 4 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem crc32c_export :
    ({ name := "crc32c", funcIdx := 5 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem crc32Update_export :
    ({ name := "crc32Update", funcIdx := 6 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem crc32cUpdate_export :
    ({ name := "crc32cUpdate", funcIdx := 7 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- Function 4, the export `crc32`, returns CRC-32 of the first `n` bytes of `msg`. -/
theorem crc32_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (msg : Array UInt64) (n ptr : UInt64) (h : Ready heap store)
    (hb : heap.Borrowed store ptr msg) :
    Runs false env compiled.module 4 store [.i64 n, .i64 ptr] fun final values =>
      ∃ c : UInt64, values.reverse = [.i64 c] ∧
        c.toNat = Spec.crc32 (messageBytes msg n.toNat) ∧
        ∃ heap' : Heap, Ready heap' final ∧ heap'.Borrowed final ptr msg ∧
          ∀ r, heap.Region r → 0 < r.2 →
            (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
              heap'.Region r :=
  (entry_call compiled.crc32.implements (.inl rfl) env heap store msg n ptr h hb).mono
    fun _ _ ⟨hv, hrest⟩ => ⟨crc32 msg n, hv, crc32_spec msg n, hrest⟩

/-- Function 5, the export `crc32c`, returns CRC-32C of the first `n` bytes of `msg`. -/
theorem crc32c_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (msg : Array UInt64) (n ptr : UInt64) (h : Ready heap store)
    (hb : heap.Borrowed store ptr msg) :
    Runs false env compiled.module 5 store [.i64 n, .i64 ptr] fun final values =>
      ∃ c : UInt64, values.reverse = [.i64 c] ∧
        c.toNat = Spec.crc32c (messageBytes msg n.toNat) ∧
        ∃ heap' : Heap, Ready heap' final ∧ heap'.Borrowed final ptr msg ∧
          ∀ r, heap.Region r → 0 < r.2 →
            (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
              heap'.Region r :=
  (entry_call compiled.crc32c.implements (.inr rfl) env heap store msg n ptr h hb).mono
    fun _ _ ⟨hv, hrest⟩ => ⟨crc32c msg n, hv, crc32c_spec msg n, hrest⟩

/-- Function 6, the export `crc32Update`, returns CRC-32 of the bytes `A` followed by the first
`n` bytes of `msg`, from CRC-32 `crc` of `A`. -/
theorem crc32Update_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (A : List UInt8) (crc : UInt64) (hcrc : crc.toNat = Spec.crc32 A) (msg : Array UInt64)
    (n ptr : UInt64) (h : Ready heap store) (hb : heap.Borrowed store ptr msg) :
    Runs false env compiled.module 6 store [.i64 n, .i64 ptr, .i64 crc] fun final values =>
      ∃ c : UInt64, values.reverse = [.i64 c] ∧
        c.toNat = Spec.crc32 (A ++ messageBytes msg n.toNat) ∧
        ∃ heap' : Heap, Ready heap' final ∧ heap'.Borrowed final ptr msg ∧
          ∀ r, heap.Region r → 0 < r.2 →
            (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
              heap'.Region r :=
  (update_call compiled.crc32Update.implements (.inl rfl) env heap store crc msg n ptr h
    hb).mono fun _ _ ⟨hv, hrest⟩ =>
      ⟨crc32Update crc msg n, hv, crc32Update_spec A crc hcrc msg n, hrest⟩

/-- Function 7, the export `crc32cUpdate`, returns CRC-32C of the bytes `A` followed by the first
`n` bytes of `msg`, from CRC-32C `crc` of `A`. -/
theorem crc32cUpdate_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (A : List UInt8) (crc : UInt64) (hcrc : crc.toNat = Spec.crc32c A) (msg : Array UInt64)
    (n ptr : UInt64) (h : Ready heap store) (hb : heap.Borrowed store ptr msg) :
    Runs false env compiled.module 7 store [.i64 n, .i64 ptr, .i64 crc] fun final values =>
      ∃ c : UInt64, values.reverse = [.i64 c] ∧
        c.toNat = Spec.crc32c (A ++ messageBytes msg n.toNat) ∧
        ∃ heap' : Heap, Ready heap' final ∧ heap'.Borrowed final ptr msg ∧
          ∀ r, heap.Region r → 0 < r.2 →
            (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
              heap'.Region r :=
  (update_call compiled.crc32cUpdate.implements (.inr rfl) env heap store crc msg n ptr h
    hb).mono fun _ _ ⟨hv, hrest⟩ =>
      ⟨crc32cUpdate crc msg n, hv, crc32cUpdate_spec A crc hcrc msg n, hrest⟩

#print axioms crc32_call
#print axioms crc32c_call
#print axioms crc32Update_call
#print axioms crc32cUpdate_call

end Library.Hashing.Crc
