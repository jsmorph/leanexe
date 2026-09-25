# Boolean monadic bindings

Candidate `d17cbd2f` supports standard Id Boolean binds in scalar
expressions, captured helper bodies, loop steps and computations surrounding a
loop. The independent BooleanAction grammar preserves direct Boolean values,
standard pure/run wrappers and metadata. BooleanType retains Bool and nested Id
annotations on these wrappers. The bind input and lambda domain remain exactly
Bool. Executable parsers have acceptance, exact reconstruction and size proofs.
Boolean bindings retain their own type and use the existing proved zero/one
representation. Source evaluation, support and totality and the scalar, step
and outer-loop extraction proofs all cover the new form.

Both final commands exited 0 with pinned Lean 4.34.0-rc2
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0 and authorized
local serial tools/leanrun execution:

- `tools/arithmetic-check.js proof`: all nine audits, including complete module
  type validation, exact bytes and terminating source-equal exported execution.
- `tools/arithmetic-check.js subset-engine boolean-bind`: admission,
  reserved exports and 623 native Lean/V8 comparisons across 34 declarations.

All 304 focused native/IR comparisons pass across eight pure and eight range
cases. Cases include aliases, nested actions, shadowing, helper captures,
dependent branches, joined do updates, unused operands, loop steps, break,
continue, bounds and binds before/after a loop. Four declaration rejections
check custom Pure/Bind instances and unsupported unused operands. Six raw bind
rejections check wrong input/domain/action types and attempts to read a Boolean
as a word. Two metadata tests cover wrapped actions in scalar and step code.

The first run rejected the nested action in boolBindWrapped because Lean infers
Id Bool annotations on both pure and run. That failure and its inspected syntax
are retained. The action grammar and proofs were extended; the same fixture
then passed without changing its source.

No emitter or runtime code changed. All selected modules, expected results and
logs are retained with sizes and SHA-256 hashes in verification.json. Eighteen
selected preceding modules kept identical bytes. This focused run checks 34
declarations; the complete corpus contains 407. The last full 259-declaration
execution evidence remains in ../extrema-2026-09-25. Cached dependencies were
reused, with small bounded builds for affected modules. The fixed arithmetic
archive and unrelated runtime suite were not rebuilt.
