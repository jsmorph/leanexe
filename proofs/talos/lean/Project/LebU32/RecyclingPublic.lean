import Project.LebU32.RecyclingEntry
import Project.ProofKit.HeapGlobals

namespace Project.LebU32.Spec
open Wasm Project.ProofKit Project.EulerRiemann.Execution

set_option maxRecDepth 32768
set_option maxHeartbeats 800000

/-- Every 32-bit input is encoded exactly. The release counters are live runtime
slots; the retained-value slot and any additional globals may hold arbitrary values. -/
theorem func0_encodes (env : HostEnv Unit) (st : Store Unit)
    (n g0 g2 g4 g5 : UInt64)
    (hn32 : n.toNat < 4294967296)
    (hFit32 : g0.toNat + 560 < 4294967296)
    (hFit : g0.toNat + 560 ≤ st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536)
    (hg0 : st.globals.globals[0]? = some (.i64 g0))
    (hg1 : st.globals.globals[1]? = some (.i64 0))
    (hg2 : st.globals.globals[2]? = some (.i64 g2))
    (hg4 : st.globals.globals[4]? = some (.i64 g4))
    (hg5 : st.globals.globals[5]? = some (.i64 g5)) :
    TerminatesWith env «module» 0 st [.i64 0, .i64 0, .i64 0, .i64 n, .i64 10]
      (fun final values => ∃ root : UInt64,
        values = [.i64 (UInt64.ofNat (lebList 10 n).length), .i64 root, .i64 root] ∧
        (∀ i : Nat, i < (lebList 10 n).length → final.mem.bytes (root.toNat + i) = (lebList 10 n)[i]!) ∧
        final.mem.pages = st.mem.pages ∧
        (∀ address, address < g0.toNat → final.mem.bytes address = st.mem.bytes address)) :=
  Recycling.func0_heap env st (Heap.fromGlobals st g0 g2 g4 g5) n
    (Heap.fromGlobals_at st g0 g2 g4 g5 hg0 hg1 hg2 hg4 hg5) rfl hn32 hFit32 hFit hPages

/-- The generated export returns the exact unsigned LEB128 bytes and length.
The returned root is existential because freed buffers can be reused. -/
theorem u32lebU64_correct (env : HostEnv Unit) (st : Store Unit)
    (n g0 g2 g4 g5 : UInt64)
    (hn32 : n.toNat < 4294967296)
    (hFit32 : g0.toNat + 560 < 4294967296)
    (hFit : g0.toNat + 560 ≤ st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536)
    (hg0 : st.globals.globals[0]? = some (.i64 g0))
    (hg1 : st.globals.globals[1]? = some (.i64 0))
    (hg2 : st.globals.globals[2]? = some (.i64 g2))
    (hg4 : st.globals.globals[4]? = some (.i64 g4))
    (hg5 : st.globals.globals[5]? = some (.i64 g5)) :
    TerminatesWith env «module» 1 st [.i64 n]
      (fun final values => ∃ root : UInt64,
        values = [.i64 (UInt64.ofNat (lebList 10 n).length), .i64 root] ∧
        (∀ i : Nat, i < (lebList 10 n).length → final.mem.bytes (root.toNat + i) = (lebList 10 n)[i]!) ∧
        final.mem.pages = st.mem.pages ∧
        (∀ address, address < g0.toNat → final.mem.bytes address = st.mem.bytes address)) := by
  refine TerminatesWith.of_wp_entry_for (f := func1Def) rfl ?_ (by decide)
  change wp «module» func1 _ st (func1Def.toLocals [.i64 n]) env
  unfold func1
  wp_run [func1Def]
  refine wp_call_tw (func0_encodes env st n g0 g2 g4 g5 hn32 hFit32 hFit hPages hg0 hg1 hg2 hg4 hg5) ?_
  rintro final values ⟨root, rfl, hBytes, hPages', hPrefix⟩
  wp_run
  exact ⟨root, rfl, hBytes, hPages', hPrefix⟩

#print axioms func0_encodes
#print axioms u32lebU64_correct
end Project.LebU32.Spec
