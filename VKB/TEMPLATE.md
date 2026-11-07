# VKB entry template

An entry is a directory `entries/NAME/`, where `NAME` is a short lowercase name with hyphens, containing `entry.json` and `README.md`.  Write the README for a prover who has the goal and no other context.  Support each claim with a declaration or a file that a reader can check.

## `entry.json`

```json
{
  "id": "NAME",
  "goals": ["a goal shape as Lean text, with the constants that identify it"],
  "modules": ["Module.That.Declares.Them"],
  "declarations": ["Full.Name.Of.A.Lemma"],
  "examples": ["Full.Name.Of.A.Theorem.That.Uses.It"]
}
```

`modules` must import every name in `declarations` and `examples`, and it must not name a module that reads a file at elaboration.  `goals` is text for search, which the check does not read.

## `README.md`

```markdown
# Title in plain words

When the entry applies: the goal or the task, in a paragraph.

What to do: the lemmas, tactics, or steps, with each declaration by its full name.

What fails: approaches that look right and do not work, with the reason.

Worked example: the finished proofs that use it.
```

Write the four parts as paragraphs without headings, merge or drop a part that would be empty, and write each paragraph in full sentences.

## Internal references

- [Verification knowledge base (VKB): Check](README.md#check)
