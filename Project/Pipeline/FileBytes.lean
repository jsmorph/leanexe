import Lean

/-! `binary_file% "path"` elaborates to the bytes of the file at `path`, relative to the
directory of the source file, as a `ByteArray` term.  Lean's `include_str` reads a text
file the same way. -/

open Lean Elab Term

syntax (name := binaryFile) "binary_file% " str : term

@[term_elab binaryFile] def elabBinaryFile : TermElab := fun stx _ => do
  let some path := stx[1].isStrLit? | throwUnsupportedSyntax
  let some dir := (System.FilePath.mk (← readThe Core.Context).fileName).parent
    | throwError "cannot compute the directory of the source file"
  let bytes ← IO.FS.readBinFile (dir / path)
  return mkApp (mkConst ``ByteArray.mk) (toExpr bytes.data)
