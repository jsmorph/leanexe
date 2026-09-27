import Project.ClobMatchFuel.Program
import Project.Clob
import Project.Runtime.FixedArraySpec

namespace Project.ClobMatchFuel.Allocation

open Wasm Project.Clob Project.ClobMatchFuel

abbrev orderArrayBytes (n : Nat) : Nat :=
  fixedArrayBytes n 5

abbrev orderArrayBytesU (n : Nat) : UInt64 :=
  fixedArrayBytesU n 5

abbrev tradeArrayBytes (n : Nat) : Nat :=
  fixedArrayBytes n 4

abbrev tradeArrayBytesU (n : Nat) : UInt64 :=
  fixedArrayBytesU n 4

abbrev FreshOrderArrayAt (st : Store Unit) (ptr capacity : UInt64) : Prop :=
  FreshFixedArrayAt st ptr capacity 5

abbrev FreshTradeArrayAt (st : Store Unit) (ptr capacity : UInt64) : Prop :=
  FreshFixedArrayAt st ptr capacity 4

def fixedArrayReleaseMem (st : Store Unit) (p freeHead : UInt64) : Mem :=
  (st.mem.write64 ((p - 40).toUInt32) 0).write64
    ((p - 8).toUInt32) freeHead

def fixedArrayReleaseGlobals (st : Store Unit) (p g4 g5 : UInt64) :=
  ((st.globals.globals.set 4 (.i64 (g4 + 1))).set 5
    (.i64 (g5 + 1))).set 1 (.i64 p)

theorem fixedArrayReleaseGlobals_get_of_ne
    (st : Store Unit) (p g4 g5 : UInt64) (i : Nat) (value : Value)
    (hi1 : i ≠ 1) (hi4 : i ≠ 4) (hi5 : i ≠ 5)
    (hValue : st.globals.globals[i]? = some value) :
    (fixedArrayReleaseGlobals st p g4 g5)[i]? = some value := by
  have h1i : 1 ≠ i := Ne.symm hi1
  have h4i : 4 ≠ i := Ne.symm hi4
  have h5i : 5 ≠ i := Ne.symm hi5
  simp [fixedArrayReleaseGlobals, h1i, h4i, h5i, hValue]

theorem fixedArrayReleaseGlobals_global1
    (st : Store Unit) (p g4 g5 : UInt64)
    (hLength : 1 < st.globals.globals.length) :
    (fixedArrayReleaseGlobals st p g4 g5)[1]? = some (.i64 p) := by
  simp [fixedArrayReleaseGlobals, hLength]

theorem fixedArrayReleaseGlobals_global4
    (st : Store Unit) (p g4 g5 : UInt64)
    (hLength : 4 < st.globals.globals.length) :
    (fixedArrayReleaseGlobals st p g4 g5)[4]? = some (.i64 (g4 + 1)) := by
  simp [fixedArrayReleaseGlobals, hLength]

theorem fixedArrayReleaseGlobals_global5
    (st : Store Unit) (p g4 g5 : UInt64)
    (hLength : 5 < st.globals.globals.length) :
    (fixedArrayReleaseGlobals st p g4 g5)[5]? = some (.i64 (g5 + 1)) := by
  simp [fixedArrayReleaseGlobals, hLength]

theorem func18_frees_fixed_array_zero_mask
    (env : HostEnv Unit) (st : Store Unit) (p capacity g1 g4 g5 : UInt64)
    (len stride : Nat)
    (hlen32 : len < 4294967296)
    (hstride32 : stride < 4294967296)
    (hp48 : 48 ≤ p.toNat)
    (hp32 : p.toNat < 4294967296)
    (hfit : p.toNat + 8 ≤ st.mem.pages * 65536)
    (hfresh : FreshFixedArrayAt st p capacity (UInt64.ofNat stride))
    (hlen : st.mem.read64 p.toUInt32 = UInt64.ofNat len)
    (hg1 : st.globals.globals[1]? = some (.i64 g1))
    (hg4 : st.globals.globals[4]? = some (.i64 g4))
    (hg5 : st.globals.globals[5]? = some (.i64 g5)) :
    TerminatesWith (m := «module») (id := 18) (initial := st) (env := env)
      [.i64 p]
      (fun st' vs =>
        vs = [] ∧
        st'.mem = fixedArrayReleaseMem st p g1 ∧
        st'.globals.globals = fixedArrayReleaseGlobals st p g4 g5) := by
  simpa only [fixedArrayReleaseMem, fixedArrayReleaseGlobals] using
    Project.Runtime.release_frees_fixed_array_zero_mask
    env «module» 18 st p g1 g4 g5 len stride (by rfl) rfl hlen32
    hstride32 hp48 hp32 hfit hfresh.1 hfresh.2.1 hfresh.2.2.2.1 hlen
    hfresh.2.2.2.2.1 hfresh.2.2.2.2.2 hg1 hg4 hg5

end Project.ClobMatchFuel.Allocation
