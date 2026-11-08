# VKB entry template

An entry is a directory `entries/NAME/`, where `NAME` is a short lowercase name with hyphens, containing `entry.json` and `README.md`.  Write the README for a prover who has the goal and no other context.  Support each claim with a declaration or a file that a reader can check.

## `entry.json`

```json
{
  "id": "NAME",
  "goals": ["a goal shape as Lean text, with the constants that identify it"],
  "modules": ["Module.That.Declares.Them"],
  "declarations": ["Full.Name.Of.A.Lemma"],
  "examples": ["Full.Name.Of.A.Theorem.That.Uses.It"],
  "unimported": {"path/of/a/File.lean": ["Full.Name.Of.A.Theorem.In.That.File"]}
}
```

`modules` must import every name in `declarations` and `examples`, directly or through the imports of the listed modules, and the check fails on a name that the entry's own modules do not import.  It lists only modules that the first step of the full check builds, which are the root modules of the libraries `LeanExe`, `Library`, `Demos`, `Examples`, `Verified`, and `TestSupport` and of that step's test executables, with everything they import.  A module under `Demos/` or `tests/` that no root imports, such as the root of a test executable outside that step, is not built.  It never lists a module that reads a file at elaboration, such as an image theorem's module, a file-theorem module, an Isla trace module, or a module that reads Isla's features.  `goals` is text for search, which the check does not read.

`unimported` is the marker for the names that the README cites from modules that the check cannot import: modules that read a file at elaboration and modules that the first step does not build.  It maps the path of each such module's file, from the repository's root, to the full names that the README cites from it, and an entry without such names omits it.  The README names each such theorem together with its module's file.  The check exempts these names from the resolution of the README's names below, and it fails when a listed file does not exist or when an imported module declares a listed name.

## `README.md`

```markdown
# Title in plain words

When the entry applies: the goal or the task, in a paragraph.

What to do: the lemmas, tactics, or steps, with each declaration by its full name.

What fails: approaches that look right and do not work, with the reason.

Worked example: the finished proofs that use it.
```

Write the four parts as paragraphs without headings, merge or drop a part that would be empty, and write each paragraph in full sentences.

The check reads every inline code span of the README, outside fenced blocks, that has the form of a qualified name: identifiers separated by dots, the first of which starts with an upper-case letter.  Such a span must name a declaration, a module, or a namespace of the environment that the entries' modules import, or a file at the repository's root such as `AGENTS.md`, unless `unimported` lists it.  Write a declaration by its full name and a file by its path from the repository's root, since a bare `Ldr.lean` has the form of a name and resolves to nothing.  A span that starts with a lower-case letter, such as `p.f.implements` or `compiled.f.pure`, is an expression over local or generated names, and the check does not read it.

## Rules for the text

Cite tracked files, declarations by their full names, and documents by their section headings.  Give no line numbers, no lines of the untracked journal `devnotes.md`, no commit hashes, and no counts of files, theorems, declarations, or copies.  A measurement appears only when a tracked file records it, with the configuration that the file gives, or as the ratio that a fix gave.  A failure that only a journal records appears as its cause, its symptom, such as the error message, a timeout, or memory exhaustion, and its remedy, with the remedy's declaration or file.

Name targets by the codes of [the index](../index.md): WASM, SPEC, WASMF, WASI, C, CALIGN, METAL, A64, M7, WGSL, and PTX.  Refer to another entry by a link to its README, `../ID/README.md`, whose text names the entry's subject, such as "the entry on image files", so that the link check fails when the entry is renamed or merged.  A proposal in a journal or a report has the content of the two files, so that a reviewer can admit it without rewriting it.

## Internal references

- [Verification knowledge base (VKB): Check](README.md#check)
