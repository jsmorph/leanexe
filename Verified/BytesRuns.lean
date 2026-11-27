module

public import Verified.Correct
public import LeanExe.A64.Proof.BytesRuns

@[expose] public section

/-!
The theorems of the AArch64 programs over bytes (`LeanExe/A64/Proof/BytesRuns.lean`) whose entry
is a wrapper over tables.  A wrapper's generated theorems are `ImplementsTables` theorems, which ask
for each table borrowed in the store of the call, while `bytes_runs` takes its precondition at
every store with the memory's cap.  `ImplementsTables.implementsA_bytes` states a wrapper's
theorem over bytes as `ImplementsA` with the tables in the precondition, since the buffer of the
message moves no block.  `ImplementsTables.bytes_runs_on` and `ImplementsTables.bytes_runs_bounded`
give `BytesRuns` from the wrapper's theorems and each table borrowed at the module's initial store,
which `Verified.Ready.initial` gives from `p.initial`, through `bytes_runs_at`, whose preconditions
hold at the store of the call, where `borrowed_callStore` keeps each table borrowed.
-/

namespace Verified

open Wasm LeanExe LeanExe.Pipeline LeanExe.A64

/-- A wrapper's theorem over bytes as `ImplementsA`, with the tables in the precondition: each
table of `tables` is a borrowed array of the store.  The buffer of the message moves no block, so
the wrapper's condition that each table lie apart from the moved blocks holds. -/
theorem ImplementsTables.implementsA_bytes {aborts : Bool} {m : Module} {entry : Nat}
    {f : LeanExe.Bytes → LeanExe.Bytes} {tables : List (UInt64 × Array UInt64)}
    {Pre : LeanExe.Bytes → Heap → Store Unit → Prop}
    {Post : LeanExe.Bytes → Heap → Store Unit → Heap → Store Unit → Prop}
    (h : ImplementsTables aborts m entry f tables Pre Post) :
    ImplementsA aborts m entry f
      (fun x heap store => Pre x heap store ∧ ∀ t ∈ tables, heap.Borrowed store t.1 t.2) Post :=
  fun env store heap params x hAt hPre hArgs hSep hCap =>
    h env store heap params x hAt hPre.1 (fun t ht => ⟨hPre.2 t ht, Apart.nil⟩) hArgs hSep hCap

/-- `bytes_runs_on` for a wrapper over the tables `tables`, each a borrowed array of the module's
initial store at `heap`: from the wrapper's theorem `htf` without the trap, whose precondition
holds after the allocation of every message that satisfies `G`, and its theorem `himpl`, which may
trap, for every message.  The status 1 of the trap occurs only for a message that fails `G`. -/
theorem ImplementsTables.bytes_runs_on {m : Module} {k : Nat}
    {f : LeanExe.Bytes → LeanExe.Bytes} {tables : List (UInt64 × Array UInt64)}
    {G : LeanExe.Bytes → Prop} {Pre Pre' : LeanExe.Bytes → Heap → Store Unit → Prop}
    {Post Post' : LeanExe.Bytes → Heap → Store Unit → Heap → Store Unit → Prop}
    (htf : ImplementsTables false m k f tables Pre Post)
    (himpl : ImplementsTables true m k f tables Pre' Post')
    {typeIdx : Nat}
    (h0 : m.funcs[0]? = some (LeanExe.Runtime.allocFunction typeIdx))
    {inMax room : UInt64} {cap : Nat} {heap : Heap}
    (hheap : heap.At (m.initialStore : Store Unit))
    (htables : ∀ t ∈ tables, heap.Borrowed (m.initialStore : Store Unit) t.1 t.2)
    (hinMax : inMax.toNat ≤ 4294967296)
    (hroomA : ∀ L ≤ inMax.toNat, heap.Room (initStore m cap) m (allocSize (UInt64.ofNat L)))
    (hpre : ∀ (b : LeanExe.Bytes) (st : Store Unit), b.data.size ≤ inMax.toNat →
      st.memoryCap m 0 = cap → G b →
      Pre b (heap.allocate (allocSize (UInt64.ofNat b.data.size))) st)
    (hpre' : ∀ (b : LeanExe.Bytes) (st : Store Unit), b.data.size ≤ inMax.toNat →
      st.memoryCap m 0 = cap →
      Pre' b (heap.allocate (allocSize (UInt64.ofNat b.data.size))) st)
    (h0room : stackBound m 0 ≤ room.toNat)
    (hok : bytesEntryOk m k = true := by decide +kernel) :
    BytesRuns m k inMax room cap (fun msg => (f ⟨⟨msg.toArray⟩⟩).data.data.toList)
      fun msg c => (¬ G ⟨⟨msg.toArray⟩⟩ ∧ c = 1) ∨ (room.toNat < stackBound m k ∧ c = 4) :=
  bytes_runs_at htf.implementsA_bytes himpl.implementsA_bytes h0 hheap hinMax hroomA
    (fun msg hlen hFits hG =>
      ⟨hpre ⟨⟨msg.toArray⟩⟩ _ hlen (callStore_memoryCap m cap heap msg) hG,
        fun t ht => borrowed_callStore hheap (by omega) hFits (htables t ht)⟩)
    (fun msg hlen hFits =>
      ⟨hpre' ⟨⟨msg.toArray⟩⟩ _ hlen (callStore_memoryCap m cap heap msg),
        fun t ht => borrowed_callStore hheap (by omega) hFits (htables t ht)⟩)
    h0room hok

/-- `bytes_runs_bounded` for a wrapper over the tables `tables`, each a borrowed array of the
module's initial store at `heap`: from the wrapper's theorem without the trap, whose precondition
holds after the allocation of every message of at most `inMax` bytes, and a stack whose bound is
at most `room`, no status. -/
theorem ImplementsTables.bytes_runs_bounded {m : Module} {k : Nat}
    {f : LeanExe.Bytes → LeanExe.Bytes} {tables : List (UInt64 × Array UInt64)}
    {Pre : LeanExe.Bytes → Heap → Store Unit → Prop}
    {Post : LeanExe.Bytes → Heap → Store Unit → Heap → Store Unit → Prop}
    (h : ImplementsTables false m k f tables Pre Post) {typeIdx : Nat}
    (h0 : m.funcs[0]? = some (LeanExe.Runtime.allocFunction typeIdx))
    {inMax room : UInt64} {cap : Nat} {heap : Heap}
    (hheap : heap.At (m.initialStore : Store Unit))
    (htables : ∀ t ∈ tables, heap.Borrowed (m.initialStore : Store Unit) t.1 t.2)
    (hinMax : inMax.toNat ≤ 4294967296)
    (hroomA : ∀ L ≤ inMax.toNat, heap.Room (initStore m cap) m (allocSize (UInt64.ofNat L)))
    (hpre : ∀ (b : LeanExe.Bytes) (st : Store Unit), b.data.size ≤ inMax.toNat →
      st.memoryCap m 0 = cap →
      Pre b (heap.allocate (allocSize (UInt64.ofNat b.data.size))) st)
    (h0room : stackBound m 0 ≤ room.toNat) (hkroom : stackBound m k ≤ room.toNat)
    (hok : bytesEntryOk m k = true := by decide +kernel) :
    BytesRuns m k inMax room cap (fun msg => (f ⟨⟨msg.toArray⟩⟩).data.data.toList)
      fun _ _ => False := by
  have hA := h.implementsA_bytes
  have hP : ∀ msg : List UInt8, msg.length ≤ inMax.toNat →
      heap.Fits (allocSize (UInt64.ofNat msg.length)) →
      Pre ⟨⟨msg.toArray⟩⟩ (heap.allocate (allocSize (UInt64.ofNat msg.length)))
          (callStore m cap heap msg) ∧
        ∀ t ∈ tables, (heap.allocate (allocSize (UInt64.ofNat msg.length))).Borrowed
          (callStore m cap heap msg) t.1 t.2 :=
    fun msg hlen hFits =>
      ⟨hpre ⟨⟨msg.toArray⟩⟩ _ hlen (callStore_memoryCap m cap heap msg),
        fun t ht => borrowed_callStore hheap (by omega) hFits (htables t ht)⟩
  refine (bytes_runs_at (G := fun _ => True)
    (Pre' := fun x heap store => Pre x heap store ∧ ∀ t ∈ tables, heap.Borrowed store t.1 t.2)
    (Post' := Post) hA
    (fun env store heap params x hAt hPre hArgs hSep hCap =>
      (hA env store heap params x hAt hPre hArgs hSep hCap).weaken)
    h0 hheap hinMax hroomA (fun msg hlen hFits _ => hP msg hlen hFits) hP h0room hok).mono ?_
  intro _ _ hc
  rcases hc with ⟨hn, -⟩ | ⟨hlt, -⟩
  · exact absurd trivial hn
  · omega

end Verified
