import Project.TinyGpt2Seq.Model
import Project.ProofKit.FixedWidthArrayPrefix
import Project.EulerRiemann.HeapFrame

namespace Project.TinyGpt2Seq.RowMemory
open Wasm Project.TinyGpt2 Project.ProofKit Project.EulerRiemann.Execution

def field (row : Row) : Nat → UInt64
  | 0 => row.x0
  | 1 => row.x1
  | 2 => row.x2
  | 3 => row.x3
  | _ => 0

abbrev At := FixedWidthArray.At 4 field
abbrev PrefixAt := FixedWidthArray.PrefixAt 4 field
abbrev writeField := FixedWidthArray.writeField 4

theorem frame {before after : Heap} {initial final : Store Unit} {ptr : UInt64}
    {rows : Array Row} (h : before.Frame initial after final)
    (hProtected : before.Protects ptr.toNat (ptr.toNat+8*(4*rows.size+1)))
    (hRows : At initial ptr rows) : At final ptr rows :=
  hRows.frame h.pages (h.bytes _ _ hProtected)

#print axioms frame
end Project.TinyGpt2Seq.RowMemory
