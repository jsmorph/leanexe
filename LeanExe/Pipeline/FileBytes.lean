import Lean
import LeanExe.Encoding.RoundTrip

/-! `binary_file% "path"` elaborates to the bytes of the file at `path`, relative to the
directory of the source file, as a `ByteArray` term.  Lean's `include_str` reads a text
file the same way.  `encode_eq_of_toList` states that a module's encoding is such a file
from a comparison of byte lists, which the kernel decides, since it reads an array element
by walking the list that represents the array, and `encode_eq_of_encoding` from the literal bytes
that `verified_compile` states.  `file_theorems` states the two theorems of a file module with
these lemmas and `decode_eq_of_file`: the file holds a module's encoding, and it decodes to the
module. -/

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

/-- The file that holds `encode m` decodes to `m` when the bytes of `encode m` decode to `m`. -/
theorem decode_eq_of_file {m : Wasm.Module} {file bytes : ByteArray}
    (hfile : Wasm.Encoding.encode m = .ok file) (henc : Wasm.Encoding.encode m = .ok bytes)
    (hdec : Wasm.Encoding.decode bytes = .ok m) : Wasm.Encoding.decode file = .ok m := by
  rw [Except.ok.inj (hfile.symm.trans henc)]
  exact hdec

open Meta in
/-- The number of first conjuncts that lead from a byte theorem's statement to an existential
`∃ bytes, encode m = .ok bytes ∧ decode bytes = .ok m ∧ …`, and whether the existential has a
conjunct after the decoding. -/
private partial def bytesShape (type : Expr) : MetaM (Nat × Bool) := do
  let type ← whnf type
  if let some (first, _) := type.and? then
    let (depth, rest) ← bytesShape first
    return (depth + 1, rest)
  let unexpected := m!"file_theorems: a byte theorem states \
    `∃ bytes, encode m = .ok bytes ∧ decode bytes = .ok m ∧ …` or a conjunction whose first part \
    leads to one, not{indentExpr type}"
  let .app (.app (.const ``Exists _) α) predicate := type | throwError unexpected
  withLocalDeclD `bytes α fun bytes => do
    let some (_, decoded) := (← whnf (predicate.beta #[bytes])).and? | throwError unexpected
    return (0, (← whnf decoded).isAppOf ``And)

/-- `file_theorems name p "path" from b₁, …, bₙ` states the two theorems of a file module, for the
module `p.module` and the file at `path`, relative to the directory of the source file, and prints
the axioms of each:

```
theorem name_file : Wasm.Encoding.encode p.module = .ok (binary_file% "path")
theorem name_file_decode : Wasm.Encoding.decode (binary_file% "path") = .ok p.module
```

The kernel compares the file with the literal bytes of `p.encoded` when `verified_compile` states
them, and otherwise with the bytes of `encode p.module`, which it evaluates.  The second proof takes
the bytes of `encode p.module` and their decoding from the byte theorem `b₁`, whose statement is
`∃ bytes, encode p.module = .ok bytes ∧ decode bytes = .ok p.module ∧ …` or a conjunction whose
first part leads to such a statement.  That proof contains every `bᵢ`, so its axiom report covers
them all.  Without `from`, the second theorem follows from `Wasm.Encoding.decode_encode`, and the
kernel checks the decoder's limit on the locals of each function. -/
syntax (name := fileTheorems) "file_theorems " ident ident str (" from " term,+)? : command

open Meta Command in
@[command_elab fileTheorems] def elabFileTheorems : CommandElab := fun stx => do
  let `(file_theorems $name $p $path $[from $bytes,*]?) := stx | throwUnsupportedSyntax
  let fileId := mkIdent (name.getId.appendAfter "_file")
  let decodeId := mkIdent (name.getId.appendAfter "_file_decode")
  let moduleId := mkIdent (p.getId ++ `module)
  let encodedId := mkIdent (p.getId ++ `encoded)
  let fileProof ← if (← resolveGlobalName encodedId.getId).any (·.2.isEmpty) then
      `(encode_eq_of_encoding (And.left $encodedId) (by decide +kernel))
    else
      `(encode_eq_of_toList (by decide +kernel))
  let decodeProof ← match bytes with
    | none => `(Wasm.Encoding.decode_encode $moduleId _ (by decide +kernel) $fileId)
    | some bytes =>
      let bytes := bytes.getElems
      let all ← bytes.pop.foldrM (fun b acc => `(And.intro $b $acc)) bytes.back!
      let (depth, rest) ← liftTermElabM do
        bytesShape (← instantiateMVars (← inferType (← elabTermAndSynthesize all none)))
      let mut source := all
      for _ in [0:depth] do
        source ← `(And.left $source)
      if rest then
        `(by obtain ⟨_, henc, hdec, _⟩ := $source; exact decode_eq_of_file $fileId henc hdec)
      else
        `(by obtain ⟨_, henc, hdec⟩ := $source; exact decode_eq_of_file $fileId henc hdec)
  elabCommand (← `(set_option maxRecDepth 100000 in
    theorem $fileId : Wasm.Encoding.encode $moduleId = .ok (binary_file% $path) := $fileProof))
  elabCommand (← `(set_option maxRecDepth 100000 in
    theorem $decodeId : Wasm.Encoding.decode (binary_file% $path) = .ok $moduleId :=
      $decodeProof))
  elabCommand (← `(#print axioms $fileId))
  elabCommand (← `(#print axioms $decodeId))

end LeanExe.Pipeline
