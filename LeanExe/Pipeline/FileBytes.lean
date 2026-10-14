import Lean
import LeanExe.Encoding.Modules

/-! `binary_file% "path"` elaborates to the bytes of the file at `path`, relative to the
directory of the source file, as a `ByteArray` term.  Lean's `include_str` reads a text
file the same way.  `encode_eq_of_toList` states that a module's encoding is such a file
from a comparison of byte lists, which the kernel decides, since it reads an array element
by walking the list that represents the array, and `encode_eq_of_encoding` from the literal bytes
that `verified_compile` states. -/

open Lean Elab Term

syntax (name := binaryFile) "binary_file% " str : term

@[term_elab binaryFile] def elabBinaryFile : TermElab := fun stx _ => do
  let some path := stx[1].isStrLit? | throwUnsupportedSyntax
  let some dir := (System.FilePath.mk (← readThe Core.Context).fileName).parent
    | throwError "cannot compute the directory of the source file"
  let bytes ← IO.FS.readBinFile (dir / path)
  return mkApp (mkConst ``ByteArray.mk) (toExpr bytes.data)

namespace LeanExe.Pipeline

theorem encode_eq_of_toList {m : Wasm.Module} {file : ByteArray}
    (h : (Wasm.Encoding.encode m).toOption.map (·.data.toList) = some file.data.toList) :
    Wasm.Encoding.encode m = .ok file := by
  cases hEncode : Wasm.Encoding.encode m with
  | error _ => simp [hEncode, Except.toOption] at h
  | ok bytes =>
    simp only [hEncode, Except.toOption, Option.map_some, Option.some.injEq] at h
    rw [ByteArray.ext (Array.toList_inj.mp h)]

/-- A module's encoding is the file when the literal bytes `L` of `encode m`, which
`verified_compile` states as `p.encoded`, equal the file's bytes.  The kernel compares two lists of
literal bytes with `List.beq`, whose recursive call is in tail position, without evaluating the
encoder. -/
theorem encode_eq_of_encoding {m : Wasm.Module} {L : List UInt8} {file : ByteArray}
    (h : Wasm.Encoding.encode m = .ok ⟨L.toArray⟩) (hf : (L == file.data.toList) = true) :
    Wasm.Encoding.encode m = .ok file := by
  have hL : L = file.data.toList := beq_iff_eq.mp hf
  rw [h]
  congr 1
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simpa using hL

end LeanExe.Pipeline
