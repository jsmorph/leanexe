import Demos.Rcv.Tabulate
import Verified.Congr

/-!
The call theorems of the Oakland tabulator's module.  `tabulate_callSpec` is T1 over bytes: from a
ready store with room for `compiled.tabulate.bound b` bytes, function 63, called with a borrowed
buffer `b`, returns without a trap an owned buffer of the bytes of `reportFile` of the bytes of `b`,
the error report of a malformed file and the printed count of a well-formed one.  A buffer that a
store holds has fewer than `2 ^ 32` bytes (`size_lt_of_borrowed`), which `tabulate_eq` needs.
`readContest_callSpec` states the reader's result words for function 47, and `printReport_callSpec`
and `printError_callSpec` state that functions 60 and 62 compute the printers, which
`printReport_eq` and `printError_eq` equate with the report of a structure from its file and its
count's words and with the error report.  `tabulate_trapFree` states `compiled.tabulate.trapFree`
for the report of a file, and `tabulate_native` carries it to the C translation.
-/

namespace Demos.Rcv.TabulateProgram

open LeanExe LeanExe.Pipeline Demos.Rcv.ReadProgram Demos.Rcv.PrintProgram

/-- A buffer that a store holds has fewer than `2 ^ 32` bytes. -/
theorem size_lt_of_borrowed {heap : Heap} {store : Wasm.Store Unit} {params : List Wasm.Value}
    {b : Bytes} (h : Represent.borrowed heap store params b) : b.data.size < 2 ^ 32 := by
  obtain ⟨root, length, -, hrep⟩ := h
  rcases hrep.buffer with ⟨-, h0⟩ | hbuf
  · omega
  · have h1 := hbuf.object.address
    have h2 := hbuf.capacity
    omega

/-- The report of the file `b` as a buffer. -/
def tabulateSpec (b : Bytes) : Bytes := ⟨⟨(Spec.reportFile (bytesOf b)).toArray⟩⟩

/-- The reader's result words of the file `b`. -/
def readSpec (b : Bytes) : Array UInt64 := (Spec.readResult (bytesOf b)).toArray

theorem bytes_ext {x y : Bytes} (h : bytesOf x = bytesOf y) : x = y := by
  rcases x with ⟨⟨a⟩⟩
  rcases y with ⟨⟨c⟩⟩
  simp only [bytesOf] at h
  have : a = c := Array.ext' h
  rw [this]

theorem tabulate_spec (b : Bytes) (hb : b.data.size < 2 ^ 32) : tabulate b = tabulateSpec b := by
  apply bytes_ext
  rw [tabulate_eq b hb]
  simp [tabulateSpec, bytesOf]

/-- T1 over bytes: function 63 returns the report of every file. -/
theorem tabulate_callSpec :
    Verified.CallSpec compiled.module compiled.tables 63 tabulateSpec compiled.tabulate.bound :=
  (Verified.ImplementsTables.call (.ofA compiled.tabulate.trapFree) compiled.tables nofun).spec
    (fun _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ b hb => tabulate_spec b (size_lt_of_borrowed hb)

/-- The reader program returns the reader's result words. -/
theorem readContest_callSpec :
    Verified.CallSpec compiled.module compiled.tables 47 readSpec compiled.readContest.bound :=
  (Verified.ImplementsTables.call (.ofA compiled.readContest.trapFree) compiled.tables nofun).spec
    (fun _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ b hb => by
      apply Array.ext'
      rw [readContest_eq b (by have := size_lt_of_borrowed hb; omega)]
      simp [readSpec]

/-- The report's printer computes `printReport`. -/
theorem printReport_callSpec :
    Verified.CallSpec compiled.module compiled.tables 60
      (fun x : Bytes × UInt64 × Array UInt64 => printReport x.1 x.2.1 x.2.2)
      compiled.printReport.bound :=
  (Verified.ImplementsTables.call (.ofA compiled.printReport.trapFree) compiled.tables nofun).spec
    (fun _ _ _ h => h) (fun _ _ _ _ _ h => h) fun _ _ _ _ _ => rfl

/-- The error report's printer computes `printError`. -/
theorem printError_callSpec :
    Verified.CallSpec compiled.module compiled.tables 62
      (fun x : UInt64 × UInt64 => printError x.1 x.2) compiled.printError.bound :=
  (Verified.ImplementsTables.call (.ofA compiled.printError.trapFree) compiled.tables nofun).spec
    (fun _ _ _ h => h) (fun _ _ _ _ _ h => h) fun _ _ _ _ _ => rfl

/-- `compiled.tabulate.trapFree` for the report of a file: function 63, from a store with room for
`compiled.tabulate.bound b` bytes, returns without a trap a buffer of the bytes of `reportFile` of
the bytes of `b`. -/
theorem tabulate_trapFree :
    ImplementsA false compiled.module 63 tabulateSpec
      (fun b heap store => heap.Within store compiled.module (compiled.tabulate.bound b))
      (fun b heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.tabulate.bound b) :=
  Verified.implementsA_congr compiled.tabulate.trapFree
    fun _ _ _ b hb => tabulate_spec b (size_lt_of_borrowed hb)

/-- T1 for the C translation: the C function of function 63 computes `tabulateSpec` as
`tabulate_trapFree` states for the module, without a trap, under every `Archi` and every
semantics of external functions. -/
theorem tabulate_native (A : LClight.Archi) (X : LClight.ExtSem) :
    LeanExe.Native.NativeImpl tabulate_trapFree A X LeanExe.Native.nativeCap
      compiled.translation := by
  obtain ⟨fd, ps, rs, hfd, hsig, _⟩ := compiled.tabulate.native A X
  exact ⟨fd, ps, rs, hfd, hsig,
    LeanExe.Native.ImplementsA.native tabulate_trapFree compiled.translation_eq hfd hsig⟩

#print axioms tabulate_callSpec
#print axioms tabulate_native
#print axioms readContest_callSpec
#print axioms printReport_callSpec
#print axioms printError_callSpec
#print axioms tabulate_eq
#print axioms readContest_eq
#print axioms printReport_eq
#print axioms printError_eq
#print axioms Demos.Rcv.ReadProgram.readNumber_whole
#print axioms Demos.Rcv.Spec.read_write
#print axioms Demos.Rcv.Spec.write_of_read

end Demos.Rcv.TabulateProgram
