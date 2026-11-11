import TestSupport.A64.Rcv
import TestSupport.A64.Flip
import Demos.Rcv.TabulateCall
import Demos.Rcv.TabulateBound
import LeanExe.A64.Proof.BytesRuns

/-!
The theorem of the tabulator's bare-metal program of `TestSupport.A64.Rcv`.  `rcv_runs` states it
in the form `BytesRuns` with the output `Demos.Rcv.Spec.reportFile msg` for a file `msg`:
`tabulate_trapFree` excludes every trap, since the file's block and the bound of `tabulate`,
`80 L + 33,702,909` bytes for a file of `L` bytes by `tabulate_bound`, fit the cap above the heap's
`top`, and the stack that the program uses is at most the room of `TestSupport.A64.Programs`.
-/

namespace TestSupport.A64.RcvRuns

open LeanExe LeanExe.A64 LeanExe.Pipeline Demos.Rcv.TabulateProgram TestSupport.A64
open TestSupport.A64.Rcv

/-- The heap's `top` at the module's start. -/
theorem top_eq : (Verified.initialHeap compiled.tables).top.toNat = 4096 := by decide +kernel

/-- The report of the file `msg` as `tabulateSpec` gives it. -/
theorem tabulate_toList (msg : List UInt8) :
    (tabulateSpec ⟨⟨msg.toArray⟩⟩).data.data.toList = Demos.Rcv.Spec.reportFile msg := rfl

/-- Function 0 of the module is the allocator. -/
theorem alloc_eq : compiled.module.funcs[0]? = some (LeanExe.Runtime.allocFunction 0) := rfl

/-- The cap lies within the allocator's limit of 65,535 pages. -/
theorem cap_le : (initStore compiled.module rcvCap).memoryCap compiled.module 0 ≤ 65535 := by
  decide +kernel

/-- The stack that the allocator uses fits the room. -/
theorem stack_alloc : stackBound compiled.module 0 ≤ room.toNat := by decide +kernel

/-- The stack that `tabulate` uses, 6,240 bytes, fits the room. -/
theorem stack_tabulate : stackBound compiled.module entry ≤ room.toNat := by decide +kernel

/-- `tabulate` takes and returns the root and the length of a buffer. -/
theorem entry_ok : bytesEntryOk compiled.module entry = true := by decide +kernel

/-- The theorem of the tabulator's program: for a file `msg` of at most `inMax` bytes, the program
writes the report of `msg` and returns 0. -/
theorem rcv_runs :
    BytesRuns compiled.module entry inMax room rcvCap Demos.Rcv.Spec.reportFile
      fun _ _ => False := by
  have hAt := compiled.initial.1
  refine (bytes_runs_bounded tabulate_trapFree alloc_eq hAt (by decide)
    (fun L hL => Heap.Within.room ?_ cap_le) (fun b st hb hcap => ?_) stack_alloc stack_tabulate
    entry_ok).congr fun msg _ => tabulate_toList msg
  · show _ + _ ≤ 65536 * rcvCap
    have := Flip.allocSize_le_add (L := L) (by simp only [inMax, UInt64.reduceToNat] at hL; omega)
    simp only [inMax, UInt64.reduceToNat, rcvCap] at hL ⊢
    rw [top_eq]
    omega
  · show _ + _ ≤ 65536 * st.memoryCap compiled.module 0
    rw [hcap]
    simp only [inMax, UInt64.reduceToNat] at hb
    have hfit : (Verified.initialHeap compiled.tables).Fits
        (allocSize (UInt64.ofNat b.data.size)) := by
      intro _
      have := Flip.allocSize_le_add (L := b.data.size) (by omega)
      rw [top_eq]
      omega
    have htop := Heap.allocate_top hfit
    have := Flip.allocSize_le_add (L := b.data.size) (by omega)
    have := tabulate_bound b (by omega)
    simp only [Verified.allocCost, rcvCap] at htop ⊢
    rw [top_eq] at htop
    omega

#print axioms rcv_runs

end TestSupport.A64.RcvRuns
