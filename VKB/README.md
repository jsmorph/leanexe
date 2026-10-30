# Verification knowledge base (VKB)

The VKB collects what agents and people learn while proving properties of programs that the verified compiler compiles: lemmas, proof recipes, worked examples, and the ways proofs fail.  The compiler's universal theorem gives every accepted program its execution theorem, `p.f.implements`, so the work that remains comes after it.  That work includes equality with an independent specification, call and file theorems, allocation bounds for `p.f.trapFree`, numerical error bounds, WASI totality, and native and bare-metal results.  No compiler, runtime, or trusted statement imports the VKB, so an entry can help a proof or fail its own check but cannot change a theorem.

## Entries

Each entry is a directory under [`entries/`](entries) with a `README.md` and an `entry.json`.  The README states when the entry applies, what to do, what fails, and where a worked example lives, in prose that a prover can follow without other context.  `entry.json` names the modules to import, the declarations the entry relies on, the worked examples, the goal shapes it addresses, and the journal entries it comes from.  A search for a constant or a goal therefore finds the entry, and [the template](TEMPLATE.md) gives the form of both files.

An entry names existing declarations instead of restating them.  When several proofs repeat a lemma, the entry points to the copies, and replacing them with one shared lemma is a separate code change.  An entry may record a failure without a fix, because a recorded failure saves the next prover the same hours.

## Admission and growth

Every proof task ends with proposals for new entries or changes to existing ones, in the form of the template, as [the repository instructions](../AGENTS.md#verification-knowledge-base) require.  A reviewer admits a proposal when its guidance applies beyond the task, its declarations exist, and no entry already covers it.  Otherwise the reviewer merges it into an existing entry or declines it with a reason.

The VKB has no fixed list of categories.  A prover finds an entry by the declarations and goals it names, so the scope grows with the work.  Entries that the work no longer needs leave only when they are wrong, stale, or duplicated without a distinct lesson.

## Check

[`Check.lean`](Check.lean) imports the modules that the entries list.  It reports every listed declaration or example that does not exist and every entry whose directory name differs from its `id`.  Run it from the repository root:

```sh
tools/leanrun --timeout 10m lake env lean --run VKB/Check.lean VKB/entries
```

The check catches renamed and removed declarations, but not guidance that a change to the compiler or the library has made wrong.  After such a change, reread the entries that name the changed declarations.  A module that reads a file at elaboration, such as a file-theorem module, does not belong in `modules`, because the check would then depend on emitted files.

## Relation to LTG

[LTG](../ltg/README.md) serves the per-program proofs of the LeanExe compiler, whose hints name its rule lemmas.  The VKB serves programs of the verified compiler, which needs no per-program correctness proof.  LTG's general lemma entries will move here once the LeanExe compiler's future is decided.
