import Verified.Examples.Wgsl
import Verified.PTX.Compile

/-!
The PTX kernels of the word and Boolean builds of the WGSL examples, `flags` and `wordScan`, and
their launch theorems under the PTX memory model.
-/

namespace Verified.Examples.Ptx

def flagsPtx :=
  (Verified.PTX.compile (e := .bool) Wgsl.compiled.flags.func.body).get (by decide +kernel)
def wordsPtx :=
  (Verified.PTX.compile (e := .word) Wgsl.compiled.wordScan.func.body).get (by decide +kernel)

def verifiedFlagsKernel : LeanExe.PTX.Module := flagsPtx.module
def verifiedWordsKernel : LeanExe.PTX.Module := wordsPtx.module

theorem flags_encoding : flagsPtx.encode = Verified.boolWord := rfl
theorem words_encoding : wordsPtx.encode = id := rfl

/-- In every consistent execution of a launch of the `flags` kernel with at least `size` threads,
no access of a thread is in a data race, every thread ends, and the copy back reads `size`
followed by `Wgsl.flags xs n invert` as words.  A consistent execution exists. -/
theorem flags_executions (xs : Array Bool) (n : UInt64) (invert : Bool) (size : Nat)
    (fits : flagsPtx.spec.Fits (flagsPtx.args (.cons xs (.cons n (.cons invert .nil)))) size)
    (ys : Array UInt64) (hys : ys.size = size) (blocks block : Nat) (hb : 0 < block)
    (hb32 : block < 2 ^ 32) (hbl : blocks < 2 ^ 32) (hcover : size ≤ blocks * block)
    (hthreads : blocks * block < 2 ^ 60) :
    let L := LeanExe.PTX.buildLaunch verifiedFlagsKernel
      (flagsPtx.args (.cons xs (.cons n (.cons invert .nil)))) size ys blocks block
    (∃ E, L.Consistent E) ∧ ∀ E, L.Consistent E →
      L.NoDataRace E ∧ (∀ g, g < blocks * block → (L.events (E.oracle g) g).2 = true) ∧
        ∀ i, i < size + 1 →
          (#[UInt64.ofNat size] ++ (Wgsl.flags xs n invert).map Verified.boolWord)[i]? =
            some (E.observed i) := by
  rw [← flags_encoding]
  exact flagsPtx.executions_eq _ (.cons xs (.cons n (.cons invert .nil))) _
    (Wgsl.compiled.flags.denote_eq xs n invert) size fits ys hys blocks block hb hb32 hbl hcover
    hthreads

/-- In every consistent execution of a launch of the `wordScan` kernel with at least `size`
threads, no access of a thread is in a data race, every thread ends, and the copy back reads
`size` followed by `Wgsl.wordScan xs n`.  A consistent execution exists. -/
theorem words_executions (xs : Array UInt64) (n : UInt64) (size : Nat)
    (fits : wordsPtx.spec.Fits (wordsPtx.args (.cons xs (.cons n .nil))) size)
    (ys : Array UInt64) (hys : ys.size = size) (blocks block : Nat) (hb : 0 < block)
    (hb32 : block < 2 ^ 32) (hbl : blocks < 2 ^ 32) (hcover : size ≤ blocks * block)
    (hthreads : blocks * block < 2 ^ 60) :
    let L := LeanExe.PTX.buildLaunch verifiedWordsKernel
      (wordsPtx.args (.cons xs (.cons n .nil))) size ys blocks block
    (∃ E, L.Consistent E) ∧ ∀ E, L.Consistent E →
      L.NoDataRace E ∧ (∀ g, g < blocks * block → (L.events (E.oracle g) g).2 = true) ∧
        ∀ i, i < size + 1 → (#[UInt64.ofNat size] ++ (Wgsl.wordScan xs n).map id)[i]? =
          some (E.observed i) := by
  rw [← words_encoding]
  exact wordsPtx.executions_eq _ (.cons xs (.cons n .nil)) _
    (Wgsl.compiled.wordScan.denote_eq xs n) size fits ys hys blocks block hb hb32 hbl hcover
    hthreads

end Verified.Examples.Ptx

#print axioms Verified.Examples.Ptx.flags_executions
#print axioms Verified.Examples.Ptx.words_executions
