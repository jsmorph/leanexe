# Deslop status

Last updated 2026-09-29 on branch `deslop`.  The repository is one Lake package at its root, with the libraries `LeanExe` (source programs) and `Project` (IR, compiler, pipeline, proofs).  `README.md` gives the layout and commands, and `devnotes.md` is the development journal.

## Goal

The deslop replaces the repository's parallel proof routes with one pipeline and removes everything else.  A compiler translates a Lean function to an IR, `compile` translates the IR to a Talos `Wasm.Module`, `encode` produces the bytes, and a per-program proof shows that the module computes the Lean function exactly.  A binary decoder, tested against the official WebAssembly testsuite, defines what the bytes mean, and `decode_encode` carries each theorem to the bytes.  The user treats the deslop as a clean, new development with no concern for legacy code.

## Design

The compiler is not verified at first.  Its rules are verified one at a time, and each proved rule enters the LTG knowledge base, so per-program proofs shrink while the trusted base stays the same.  The system stays as small as possible, and per-program proofs carry the rest of the burden with help from LTG.

| Component | Design | State |
|---|---|---|
| IR | Embedded in Lean: expressions over locals, assignment, `if`, `while`, loads, stores, and calls.  Values are 64-bit words, Booleans, or binary64 bit patterns.  It has no arrays, structures, or ownership. | Expressions and statements exist.  `f64` expressions read locals, take literals, add, subtract, multiply, divide, take square roots and absolute values, compare, and branch.  Assignment works at any type, and a load reads a stored word as a 64-bit word or as an `f64`. |
| Translation | `compile : IR → Wasm.Module`, with one `wp` rule per construct proved once against Talos.  The IR means what its compiled code does. | `Expr.program_spec`, a `Triple` rule for each statement, and the frame notion `State.Frame` with `Expr.eval_frame`.  `Triple` takes the module, so the call rule can use the callee's specification. |
| Compiler | Lean to IR, reading each definition's unfolding equation.  Verifying a rule means proving that its template implements its source construct, stated in terms of Lean's own functions, so no `Lean.Expr` semantics is trusted. | `UInt64` arithmetic, comparisons, `if`, tail recursion, `Array UInt64` parameters, and `Array.foldl` over an array parameter or an array literal, which becomes a temporary released after the fold.  `xs.size.toUInt64` loads the length word, and a function may return an array literal.  `Float` parameters, results, and literals, with `+`, `-`, `*`, `/`, negation, `Float.sqrt`, `Float.abs`, `min`, `max`, comparisons, `==`, and `if`.  `Array Float` parameters, and folds over them.  A fold's accumulator is `UInt64` or `Float`.  `UInt64.toFloat` and `Float.toUInt64`, and `xs.size.toUInt64` for either array type.  The tail-recursion, fold, array-size, array-literal, release, and float-arithmetic rules are proved. |
| Hints | Untrusted annotations: the rule behind each fragment, its source term, its instruction path in the decoded module, and the name of each local.  A wrong hint costs proof time and cannot produce a false theorem. | Emitted for every IR node. |
| Runtime | `alloc`, `retain`, and `release` with reference counting, specified and proved once.  The compiler places `retain` and `release`, and per-program proofs check the placement until a rule lemma covers it. | The three functions are in every module and pass host tests.  `alloc_spec` covers every request, and `release_run` covers an owned array with count one and no child pointers.  `retain` and the release of shared or nested objects are not specified. |
| Statement | `Implements`, over a `Represent` class that says how a value appears as WASM values and heap data. | Instances for `UInt64`, `Float`, tuples of scalars, `Array UInt64`, and `Array Float`.  `Func.implements_heap` takes arguments and a result of any `Represent` type and a body that may allocate and free. |
| Bytes | The encoder, `decode_encode`, and one decoder. | Done, with `f64.const`, `f64.eq`, `f64.lt`, `f64.le`, and `f64.abs` added for floats. |
| Floating point | The WebAssembly deterministic profile.  See "Floating point". | Binary32 and binary64 equality proofs for addition, subtraction, multiplication, division, and square root; binary64 comparisons, negation, and absolute value. |

The trusted base is Lean's kernel, Talos's semantics, the decoder, and any I/O adapter.  The source dialect has fixed-width integers and IEEE floats, compiles `panic` to `default`, allows recursive values, and does I/O through a pure step function driven by a fixed adapter.  Rule lemmas must state what their templates leave unchanged, meaning the locals they do not write and the memory outside the blocks they allocate or write, because lemmas for nested templates do not compose otherwise.

## Files

| File | Role |
|---|---|
| `LeanExe/Examples/Scale.lean`, `Gcd.lean`, `SumArray.lean`, `PairSum.lean`, `SumCount.lean` | Source programs. |
| `LeanExe/Float32.lean`, `Float64.lean`, `Signed32.lean` | Raw-bit wrappers that the binary32 equality proofs state their results about. |
| `Project/IR/Expr.lean` | IR expressions, the IR state, `Expr.eval`, the expression rule `Expr.program_spec`, and `State.Frame` with `Expr.eval_frame`.  `State.Frame` says a state changed only given locals and scratch locals. |
| `Project/IR/Stmt.lean` | IR statements, their compiled code, `Triple`, one rule per statement, `Triple.mono`, and `Triple.of_forall`. |
| `Project/IR/Function.lean` | `Func` (parameters, compiler variables, body, result) and `compile`, which gives each module a memory, the runtime globals, and an export. |
| `Project/IR/Correct.lean` | `Func.implements_heap`: a body that ends with some heap satisfying the allocator invariant, the arguments still represented, the allocation bounds met, and the result evaluating to `f x` gives `Implements`.  `Func.implements` is the case of a body that keeps the store. |
| `Project/IR/TailLoop.lean` | `Func.tail_implements`, the rule lemma for tail recursion, and `TailStep`, its obligation about one loop iteration. |
| `Project/IR/Fold.lean` | `Stmt.fold`, the compiler's template for `Array.foldl`, and `Stmt.arraySize`, its template for an array's size, with their rule lemmas. |
| `Project/IR/ArrayLiteral.lean`, `Release.lean` | The templates for an array literal and for releasing a temporary, with their rule lemmas. |
| `Project/IR/Hint.lean` | Hint types. |
| `Project/Compiler/Scalar.lean`, `Command.lean` | The compiler and `leanexe_compile p := f`, which adds `p.ir`, `p.module := compile p.ir name`, and `p.hints`. |
| `Project/Pipeline/Implements.lean` | `Represent`, `Scalar`, `Implements`, `Satisfies`, and `Implements.transfer`. |
| `Project/Pipeline/Runtime.lean` | The heap state and the invariants `Heap.At`, `Heap.Borrowed`, `Heap.Owned`, and `Heap.Room`. |
| `Project/Pipeline/Allocation.lean` | What one allocation guarantees: the block, the allocator invariant, the bounds, and the preservation of borrowed arrays. |
| `Project/Pipeline/RuntimeSpec.lean` | `alloc_spec`, `release_run`, and the heap after a release. |
| `Project/Runtime/` | `Defs.lean`, the code of `alloc`, `retain`, and `release`; `FreeList.lean`, the free-list layout that `Heap.At` uses; and `Tree.lean`, the old model of the structure a `release` frees. |
| `Project/Pipeline/Emit.lean` | Script: evaluates a module constant, encodes it, checks that `decode` returns it, and writes the file. |
| `Project/Encoding/` | The encoder, the decoder, `decode_encode`, and `DecodeTest.lean`, a script that runs the decoder over the testsuite. |
| `Project/ProofKit/` | 83 modules of general lemmas: memory, arrays, allocation, frames, and the binary32 and binary64 equality chain. |
| `Project/Scale/`, `Project/Gcd/`, `Project/SumArray/`, `Project/PairSum/`, `Project/SumCount/`, `Project/Axpy/`, `Project/ScaledHypot/`, `Project/Piecewise/` | Each program's `leanexe_compile` and theorems. |
| `Project/LTG/Check.lean` | Script: imports every module the LTG entries list and reports declarations that do not exist. |
| `ltg/` | The LTG knowledge base: 11 entries, each an `entry.json` and a `README.md`. |

## Proved

`scale_implements` states that `scale.module` implements `scale a b c = a * b / c + 1` on every triple of `UInt64` arguments.  Its proof applies `Func.implements` and one `simp` call; the only remaining step is Lean's `a * b / 0 = 0`.

`gcd_implements` states that `gcd.module` implements Euclid's algorithm on every pair of `UInt64` arguments.  The compiler produced a `while` loop over a `done` flag whose body branches on `b = 0`.  The proof applies `Func.tail_implements` and proves only `gcd_step`, one iteration, in 29 lines; the first proof, which gave the invariant, state measure, entry, and exit directly to `Stmt.while_spec`, took 63 lines by the same count (non-blank, non-comment).

`sumArray_implements` states that `sumArray.module` implements `sumArray xs = xs.foldl (· + ·) 0` on every borrowed `Array UInt64`.  The compiler produced an assignment of 0 to an accumulator followed by `Stmt.fold`, a loop that loads the length word and then each element.  The proof applies `Func.implements`, the assignment rule, and `Stmt.fold_spec`, and it takes 20 lines including the statement.  `Stmt.fold_spec` needs the array's layout in memory, which `Heap.Borrowed` provides, and an obligation that the fold body evaluates to `g a e`.

`pairSum_implements` states that `pairSum.module` implements `pairSum a b = #[a, b].foldl (· + ·) 0` on every pair of `UInt64` arguments, allocating at most 72 bytes.  The compiled code calls `alloc`, stores the length and the two elements, folds, and calls `release`.  The proof applies `Func.implements_heap`, `Stmt.arrayLiteral_spec`, the assignment rule, `Stmt.fold_spec`, and `Stmt.release_spec` with `Heap.At.release`, in 56 lines including the statement.  The runtime proofs under it are `alloc_spec`, which reuses ProofKit's proof of the allocation program, and `release_run`, which steps through `release`'s code for an array with count one.

`sumCount_implements` states that `sumCount.module` implements `sumCount xs = #[xs.foldl (· + ·) 0, xs.size.toUInt64]` on every borrowed `Array UInt64`: the result is an array that the caller owns, the argument stays borrowed, and the call allocates at most 72 bytes.  The proof applies `Func.implements_heap`, `Stmt.fold_spec`, `Stmt.arraySize_spec`, and `Stmt.arrayLiteral_spec`, whose preservation clause keeps the argument borrowed, in 55 lines including the statement.

`axpy_implements` states that `axpy.module` computes `axpy a x y = a * x + y` bit for bit on every triple of `Float` arguments, NaN included.  The proof applies `Func.implements` and one `simp` call with `F64Bits.toBits_add` and `toBits_mul`.  `scaledHypot_implements` does the same for `scaledHypot x y s = (x * x + y * y).sqrt / s`, adding `toBits_div` and `toBits_sqrt`.  `piecewise_implements` covers a function with `==`, `<`, `≤`, negation, `Float.abs`, `min`, `max`, three literals, and nested `if`, in 29 lines including the statement.

`sumSquares_implements` states that `sumSquares.module` computes `sumSquares xs = xs.foldl (fun acc x => acc + x * x) 0.0` bit for bit on every borrowed `Array Float`.  An `Array Float` is stored as the `Array UInt64` of its elements' bit patterns, and the fold's accumulator and element locals have type `f64`.  The proof applies `Stmt.fold_spec` with a step on bit patterns, in 21 lines including the statement, and a 7-line lemma converts the result with core's `Array.foldl_map` and `Array.foldl_hom`.

`mean_implements` proves `mean xs = xs.foldl (· + ·) 0.0 / xs.size.toUInt64.toFloat` bit for bit, with the fold, the array-size rule, and `F64Convert.toBits_toFloat`.  `bucket_implements` proves `bucket x lo width = ((x - lo) / width).toUInt64`, a histogram index, with one `simp` call and `F64Convert.toUInt64_eq`.  Both conversion theorems cover NaN, the infinities, and out-of-range values.

`scale_bytes`, `gcd_bytes`, `sumArray_bytes`, `pairSum_bytes`, `sumCount_bytes`, `axpy_bytes`, `scaledHypot_bytes`, `piecewise_bytes`, `sumSquares_bytes`, `mean_bytes`, and `bucket_bytes` combine these with `round_trip`: `encode` succeeds on the module, and the decoder reads the bytes back as a module that implements the function.  The kernel checks that encoding succeeds by evaluating the encoder (`decide +kernel`), in about half a second per module.  All of these theorems, the rule lemmas, the runtime specifications, and `decode_encode` depend only on `propext`, `Classical.choice`, and `Quot.sound`.  An audit found that CodeLib's `Mem.read64_write64_same`, a `simp` lemma proved with `bv_decide`, had added an axiom for compiled code to `pairSum_bytes`.  The proofs now use ProofKit's kernel-checked `Memory.read64_write64` and remove CodeLib's lemma from the `simp` set in `RuntimeSpec.lean`.

## Tested

Every module contains the runtime functions, so the sizes below are mostly runtime code.  `scale.wasm` is 1,292 bytes with sha256 `a4891fd53b3c69f57cb2c460cb76fc968ab31ee70eec27bb8cb052ec60095176`.  Wasmtime returned 9, 1, 6148914691236517205, 1, 1, and 1 for `(6, 7, 5)`, `(6, 7, 0)`, `(2^64-1, 2, 3)`, `(0, 0, 0)`, `(2^32, 2^32, 1)`, and `(2^64-1, 2^64-1, 2^64-1)`, the values native Lean returned.  `gcd.wasm` is 1,340 bytes with sha256 `6fbf8b51fae594ad91eabed6c55519e9c085fc3f7733af4a2d4f5be7d12b06e6`.  Wasmtime returned 6, 5, 5, 0, 1, 2^62, and 1 for `(48, 18)`, `(0, 5)`, `(5, 0)`, `(0, 0)`, the consecutive Fibonacci numbers `(12200160415121876738, 7540113804746346429)`, `(2^63, 2^62)`, and `(2^64-1, 2^64-59)`, the values native Lean returned.

`sumArray.wasm` is 1,332 bytes with sha256 `23e36ce2402338437065e04856372c02ca4dff20f6450893d30f14125abfcb8f`.  With the host allocating the input through `alloc`, Wasmtime and native Lean both returned 6 for `[1, 2, 3]`, 1 for `[2^64-1, 2]`, 0 for `[]`, 60 for `[10, 20, 30]`, and 18029489283092536988 for the 1,000 elements `i * 0x9E3779B97F4A7C15 mod 2^64`.  The counters read one allocation and no retains, releases, or frees after each call, and one allocation, one release, and one free after the host released the input.

`pairSum.wasm` is 1,374 bytes with sha256 `09249d6ff0c98a292e9fea418d56859daa71fda56c690a61eed54863cc166e77`.  Wasmtime and native Lean both returned 7 for `(3, 4)`, 1 for `(2^64-1, 2)`, 0 for `(0, 0)`, 11 for `(5, 6)`, and 15 for `(7, 8)`.  One call leaves one allocation, one release, and one free.  Two calls in one session leave two of each, and a third allocation afterward shows the second call reused the freed block.  Releasing an array whose child mask marks its one element as a pointer freed both the array and the child.

`sumCount.wasm` is 1,380 bytes with sha256 `cc5eb56bc47a099183d389410646164406374490f132c413286a91547b806a0d`.  Wasmtime and native Lean both returned `[6, 3]` for `[1, 2, 3]`, `[1, 2]` for `[2^64-1, 2]`, `[0, 0]` for `[]`, `[60, 3]` for `[10, 20, 30]`, and `[18029489283092536988, 1000]` for the 1,000-element array.  After the host released the result and then the input, the counters read two allocations, two releases, and two frees.

`axpy.wasm` is 1,265 bytes with sha256 `a4f288ebf1a0d3a154e16495837747a466dd2fdbc898ad37299540eaf5f3f1cd`.  Wasmtime and native Lean returned the same bits for 54 inputs: 14 chosen cases, with infinities, the canonical NaN, signed zeros, a subnormal result, overflow, and two-rounding cases, and 40 pseudo-random triples.  The host passes and prints `f64` values as bit patterns (`f64:BITS`).

`scaledHypot.wasm` is 1,279 bytes with sha256 `143bd3a3b4cc14983e90d04ee145e3e910d1ca958f501d72819807b09a9b93f2`.  Wasmtime and native Lean returned the same bits for 60 inputs, including division by both signed zeros, overflow and underflow in the squares, NaN, and 40 pseudo-random triples.

`piecewise.wasm` is 1,374 bytes with sha256 `0bd8d6df8798d1eea0e7513117144902a9cb6e816e2cf2602ff928e98f4875be`.  Wasmtime and native Lean returned the same bits for 66 inputs, including equal values, both signed zeros, NaN in each position, and inverted bounds.

`sumSquares.wasm` is 1,345 bytes with sha256 `12d9540ca159343a9ee2626c839aac9214c088d5b3955c2dde7341b3b85ead09`.  Wasmtime and native Lean returned the same bits for 48 arrays: 18 chosen arrays, including the empty array, infinities, NaN, subnormals, overflow, and small terms added before and after a large one, and 30 pseudo-random arrays of up to six elements.  The host passes the array as `array-u64:` with the elements' bit patterns.

`mean.wasm` is 1,350 bytes with sha256 `9102a3ca740d734f7e8f09fc3ff5e3cd7ec270eadc536f71e09b9a2ecd8feffe`, and it matched native Lean on 48 arrays, six of them empty.  `bucket.wasm` is 1,269 bytes with sha256 `baef3dfa47695f47d3ed085fdccf57401ec2e146bf9ce31c3e016960c0640000`, and it matched native Lean on 104 inputs, including NaN in each position, infinities, division by zero, results at and beyond `2^64 - 1`, and 40 pseudo-random triples.

`wasm-tools` validated all eleven modules.  The earlier modules kept their hashes through the float changes and the change to typed locals.  Host tests of the runtime functions are recorded in `devnotes.md` under 2026-09-29.  After the decoder gained the float comparison, absolute-value, and constant opcodes, the testsuite run found all 479 valid modules in the subset equal to the reference and round-tripping and rejected all 670 malformed modules in the subset; 1,735 valid and 41 malformed modules fall outside it.

## Decisions

| Decision | Reason |
|---|---|
| The system stays as small as possible, and per-program IR proofs carry more of the burden. | The user's principle.  LTG knowledge bases help with those proofs. |
| The compiler starts unverified and is verified rule by rule, and each proved rule enters LTG. | The user's central idea for the project. |
| Development is iterative.  Each iteration carries one program from Lean source to bytes, a proved `Implements`, a Wasmtime comparison with native Lean, an axiom audit, and a commit, adding only what that program needs. | The user rejected building whole layers before connecting them. |
| A new, small compiler translates Lean to the IR. | The old compiler (about 40,000 lines) trapped on panics and `Nat` overflow, supported bounded `Nat`, and placed `release` conservatively, all against the new dialect. |
| The compiler reads unfolding equations (`getUnfoldEqnFor?`), so a recursive call appears as a call of the definition. | It avoids recognizing the term shapes Lean generates for structural and well-founded recursion. |
| The compiler emits the IR as a definition and the module as `compile ir`. | The module is tied to the IR by definition, and a wrong compiler match makes the proof fail. |
| The compiler emits hints of any useful kind, keyed to positions in the decoded module.  They move into a WASM custom section, with names in the `name` section, once proving from the bytes alone becomes a goal. | Hints need not be exact.  The decoder skips custom sections, so no theorem changes. |
| Statements get `wp` rules only, packaged as `Triple` over the store and IR state.  `while` is the only loop, with a `done` local for several exits. | It keeps one semantics, Talos's, and adds no simulation theorem.  Every IR rule is a lemma about WASM code, which serves proving from bytes later.  A big-step relation and a fuel evaluator, recommended earlier, each added a second semantics. |
| `Expr.eval` with `Expr.program_spec`, taken from the old `ProofKit/ScalarTransition.lean`, serves as the expression rule. | It is proved, and per-program proofs can rewrite with the evaluator. |
| `Implements` is one statement over a `Represent` class.  Every compiled module has a memory and the six runtime globals. | A module without memory would make `Heap.At` false and the theorem vacuous. |
| The runtime keeps reference counting. | Lean values can be shared, so a compiler cannot free them statically. |
| Runtime integers are fixed-width only.  `panic` compiles to `default`.  Recursive values stay. | Bounded `Nat` traps where Lean returns the exact value, and Lean's logic gives `default` for an out-of-bounds `a[i]!`. |
| I/O uses a pure step function, `State → Input → State × Output`, driven by a fixed adapter that is trusted at first and proved later.  The `ByteIO` monad is dropped. | The opaque `ByteIO` primitives give a program no Lean meaning.  Each `step` call is pure, so `Implements` covers it. |
| `LeanExe.Runtime.release` and the runtime counters leave the source dialect.  Modules keep the counters as globals. | Their values are 0 in Lean and real in WASM. |
| Floating-point theorems describe the WebAssembly deterministic profile. | Talos implements it, and it matches Lean's float model. |
| Programs use Lean's `Float` and `Float32`.  `neg`, `abs`, and `ofBits` get a NaN check, and `min` and `max` compile as a comparison and a select. | Lean's model and WASM differ on those operations. |
| `f32` and `f64` enter the IR when floats arrive. | The expression proofs never case on the value type, so adding types later changes only `denote` and `value`. |
| The binary64 equality proofs copy the binary32 proofs. | Copying changes no existing definition or proof. |
| `origin/wgsl` stays unmerged as a reference.  The GPU path is designed after the Wasm path proves `sumCount` and one float program. | The branch builds on the old compiler. |
| The repository is one Lake package at its root.  The old compiler, the JavaScript tools, and the old docs are deleted. | The user asked to clean house before iteration 3. |
| LTG is entries only, searched directly and checked by a Lean script. | The JavaScript LTG tools depended on the deleted generator library and accepted only ProofKit modules. |
| Memory access is two IR statements, `load dst address` and `store address value`, with 64-bit words, 32-bit address wrapping, and an in-bounds premise in the load rule; expressions stay pure. | Adding memory to `Expr.eval` would reopen `Expr.eval`, `Expr.program_spec`, and every proof built on them. |
| The runtime is three functions in every module, `alloc`, `retain`, and `release`, reached by an IR call statement through Talos's `wp_call_tw`, and exported with the counters for hosts; `reset` is dropped.  `alloc` wraps the proved `FixedArrayAllocate.program`, which also counts the allocation, with size rounding.  `release` is new and non-recursive: a count that reaches zero puts the object on a pending list linked through its count field, and a loop decrements children, adds those that reach zero, and frees each block after its children.  `retain` is copied from the old runtime.  The magic-number check stays. | Garbage collection comes before arrays at the user's direction.  A recursive `release` uses one WASM stack frame per node.  The old `release` proofs cover the old recursive code, so the new `release` is proved from scratch with them as templates. |
| Reference counts are specified locally: the caller describes the structure reachable from a released pointer, as the old tree model does, and `release`'s specification gives the effect for that description, including `Heap.At`.  No global count invariant. | The host holds references outside the theorem, so a global invariant cannot be established at the call boundary. |
| A value that needs statements (a load or a loop) compiles to statements before its expression, placed inside the branch that needs them, never hoisted out of an `if`.  `Array.foldl` with a lambda and default bounds becomes a counted loop, `Nat.toUInt64 xs.size` a load of the length word, and an array literal of k elements an allocation of 48 + 8(k + 1) bytes followed by stores. | Hoisting a load out of a guarding branch can trap where Lean returns a value. |
| For now the compiler places a fold's statements only at the start of the function body, so it rejects a fold in a branch, in a fold body, or in a recursive definition. | Placement inside branches is added when a program needs it. |
| `Stmt.fold` is a definition built from existing statements, and its rule lemma is stated about that definition.  The fold body is an expression, so a nested fold is rejected. | The IR keeps six constructors, and the lemma needs no new `wp` rule. |
| Rule lemmas state what they leave unchanged with `State.Frame scratch writes before after`: the same numbers of parameters and locals, and the same value at every local below `scratch` outside `writes`.  A rule lemma takes a precondition that fixes the store and the state, and `Triple.of_forall` reaches that form from any precondition. | `State.Frame` is transitive, expressions preserve it (`Expr.eval_frame`), and the lengths let later assignments and scratch writes succeed. |
| `Func.implements_heap` takes arguments of any `Represent` type, and its body `Triple` may use `Heap.At`, `Heap.Room`, and the arguments' representation in the initial store.  It ends with some heap for which the invariant, the arguments' representation, and the bounds on `top` and pages hold.  `Func.implements` is its case for a body that keeps the store. |
| The compiler computes hint positions from code lengths, which do not depend on the scratch index, and no longer tracks the scratch index. | The number of compiler variables, and so the scratch index, is known only after translation. |
| `Triple` takes the module as a parameter. | A call rule needs the callee's `TerminatesWith` in that module, which `wp_call_tw` consumes. |
| `call func args result` is one IR statement for any function, with a rule parameterized by the callee's specification, and `store address value` writes a word. | The same statement serves the runtime functions and later calls between compiled functions. |
| `release` checks the child mask before it walks any slots. | Freeing an array without child pointers took one loop iteration per element to test a zero mask, and the check also removes two nested loops from the proof of the common case. |
| `Heap.Owned` records that the object ends inside the 32-bit address space. | The freed block's free-list entry needs it, and every allocated block satisfies it. |
| An array literal that a fold consumes becomes a temporary: the compiler allocates it before the fold and releases it right after. | The fold is the temporary's only use. |
| A function may return an `Array UInt64` only as an array literal, which the caller owns.  `xs.size.toUInt64` compiles to a load of the length word into a fresh local. | Returning a borrowed argument would need `retain`, which comes with sharing.  Lean's `Nat.toUInt64` is `UInt64.ofNat`, so the loaded word is the exact value. |
| Proofs may not use `bv_decide` or `native_decide`. | Both add an axiom that trusts compiled code.  `Project/Common.lean` had two unused lemmas proved with `bv_decide`, now deleted. |
| IR `f64` values are bit patterns, and `Expr.eval` applies Talos's `IEEE64` functions.  Per-program proofs connect Lean's `Float` through `F64Bits.toBits_add` and its siblings. | The IR means what its compiled code does, and the equality theorems enter once, as `simp` lemmas. |
| `Func` is typed: `params` and `vars` list the types of the parameters and the compiler's variables, and `result` pairs a type with an expression of that type.  Scratch locals are 64-bit words. | `Float` arguments, results, and variables use WebAssembly's `f64` type, and a load of an `f64` adds `f64.reinterpret_i64`.  A dependent pair keeps equations such as `func.result = ⟨.u64, .get n⟩` free of casts. |
| Tail recursion stays `UInt64`-only.  Folds run over an `Array UInt64` or an `Array Float` with a `UInt64` or `Float` accumulator. | An `Array Float` is stored as the `Array UInt64` of its elements' bit patterns, so the fold rule and the heap specifications apply to it unchanged. |
| The dialect's float array is `Array Float`, and `FloatArray` is not supported. | Lean core has no lemmas about `FloatArray`, and the loop of `FloatArray.foldlM` is private, so a proof about its fold depends on a private declaration.  `Array` has public lemmas and literal syntax.  In WebAssembly both types have the same unboxed layout.  In native Lean, `Array Float` stores each element as a separate heap object, which costs speed and memory in native runs only. |
| The first real program is a CLOB, built in increments that each run end to end: `marketBuy`, then a limit order, a cancel, a depth query, and a function that applies a command.  A CPU GPT follows, and the GPU path waits until both run.  (User, 2026-09-29.) | The CLOB uses only `UInt64` arithmetic, which the compiler covers, so its proofs concern control flow and arrays.  The GPT needs `exp` written in Lean, because Lean's `Float.exp` is `opaque`. |
| Loops use `LeanExe.loop (n : UInt64) (init : α) (f : UInt64 → α → α) : α`, with `UInt64` indices and `xs[i.toNat]!`, which yields 0 out of bounds.  A loop state of several variables compiles to several locals. | Compiled `UInt64` arithmetic equals Lean's, so no proof concerns overflow, and the loop rule resembles the fold rule.  `Nat.fold` would need overflow facts for index arithmetic, a tail-recursive helper needs a proof of each iteration, and `for` loops would require recognizing the elaborated `forIn`.  Loops do not stop early; tail recursion covers early exit if an operation needs it. |
| Programs build arrays with Lean's operations (`set!`, `insertIdx`, `eraseIdx`, `extract`, `map`, `push`).  The compiler implements each one with a single copying template, whose rule is proved once, and one lemma per operation equates the operation to the template by `Array.ext` and core's `size_*` and `getElem_*` lemmas.  `LeanExe.build` builds arrays computed by index. | The source is the specification, and Lean's operation names state it more clearly than index functions.  Core's lemmas about these operations serve later proofs about programs, and the same source can compile to in-place updates once ownership exists.  A `push` in a loop copies until then. |
| A module holds several functions: `leanexe_compile name := [f, g, …]` compiles the listed definitions, exports each, and compiles a call to a listed function as `call`.  Each function has its own `Implements` theorem, and a call rule takes the callee's theorem as its premise.  The call graph must be acyclic at first. | Each callee is proved once.  Inlining would repeat callee proofs at every call site and cannot handle recursion, and separate linked modules need theorems across instances.  The explicit list keeps the module's contents in the source. |
| `-x` compiles to `-0.0 - x`, `Float.abs` to `f64.abs`, and `min` and `max` to `f64.le` and a conditional.  `min` and `max` evaluate their operands twice, because the compiler does not yet bind operands to float locals. | Subtracting from negative zero is exact and canonicalizes NaN as Lean's negation does, and it evaluates `x` once. |
| The compiler computes a float literal's bits, and proofs check them with `decide`. | The kernel evaluates Lean's `Float.ofScientific` for ordinary literals; exponents beyond Lean's default threshold need options raised. |
| Iteration 3 runs in three steps.  3a: `sumArray xs = xs.foldl (· + ·) 0` with the fold rule's lemma, modules carrying the runtime functions for hosts, and no runtime specifications yet.  3b: `pairSum`, where compiled code allocates and releases a temporary, with the call statement and the specifications of `alloc` and of `release` for objects without children.  3c: `sumCount`, whose result the host owns and releases.  `retain`'s specification and the loop over children are proved when first used. | Each specification is proved in the iteration whose program uses it. |
| `Heap.At` requires at most 65,536 pages, and `Heap.Borrowed` requires only that the input lies below `top` and outside every free block. | A 32-bit memory has at most 65,536 pages, and an earlier header condition existed only to fit a reused lemma. |

## Floating point

Lean 4.34 defines `Float` and `Float32` through `Float.Model` and `Float32.Model`, IEEE binary64 and binary32 with round-to-nearest, ties to even.  Every NaN in both models is the positive quiet NaN with only the top fraction bit set, `0x7FF8000000000000` or `0x7FC00000`, and `ofBits` converts every NaN input to it.  Talos's `IEEE64` and `IEEE32` return the same constants for every NaN result.

ProofKit proves `LeanExe.Float32.xBits = Wasm.IEEE32.x` for `add`, `sub`, `mul`, `div`, and `sqrt`, for all inputs including NaN, in 25 files and 2,101 lines.  The binary64 counterparts for all five operations are 21 files in `F64*.lean`, plus `F64Bits`, 1,831 lines in all, translated from the binary32 files with a script that maps the format constants.  Lemmas that do not depend on the format moved to `FloatRounding`, `FloatShift`, `FloatRationalRounding`, `FloatSqrtRounding`, and `FloatCommon`, which both chains import.  One lemma is new: `IEEE64.roundDyadicMagnitude` and `roundRationalMagnitude` pass `rounded * 2^shift` to `roundScaledMagnitude` where the binary32 rounders encode the fields directly, and `roundScaled_mul_pow` bridges the two forms.  `F64Bits` restates the results as `(a + b).toBits = IEEE64.add a.toBits b.toBits` for Lean floats.  The wrappers are thin: `LeanExe.Float32.addBits` applies Lean's `Float32` addition to decoded bits, so the theorems also justify compiling Lean's float types directly.

Lean and WASM differ in three places:
1. Lean's `neg` and `abs` return the positive canonical NaN for a NaN input.  WASM `fneg` and `fabs` change only the sign bit.
2. Lean's `ofBits` canonicalizes NaN.  WASM `reinterpret` keeps the payload.
3. Lean's `min` and `max` choose an operand by `≤`.  WASM `fmin` and `fmax` return NaN for a NaN operand and order `-0` below `+0`.

The WebAssembly specification ([numerics](https://webassembly.github.io/spec/core/exec/numerics.html)) makes the sign of a generated NaN nondeterministic and its payload canonical only when every NaN input is canonical.  Its deterministic profile ([profiles](https://webassembly.github.io/spec/core/appendix/profiles.html)) requires that "All NaN values generated by floating-point instructions are canonical and positive," and Talos implements that behavior.  `tools/wasmtime-host.c` enables Cranelift's NaN canonicalization.  Browsers do not implement the profile, and on x86 `0/0` produces a negative NaN.  On this aarch64 machine, native Lean's `toBits` returned `0x7FF8000000000000` for a NaN with a payload, for `0/0`, and for `-(0/0)`.  Modeling the full profile in Talos, with an oracle choosing NaN results and the compiler canonicalizing NaN where bits become observable, remains the route if theorems must cover results computed in a browser.

`IEEE64` has the same functions as `IEEE32` and calls `IEEE32.roundShift`, `roundQuotient`, and `roundSqrtIntegral` directly, so lemmas about those helpers are imported, not copied.  The binary32 chain states its format constants about 270 times, and proofs with the larger binary64 constants may behave differently under `decide`, `omega`, and `simp`.  The binary64 translation needed no changes for `decide`, `omega`, or `simp` behavior with the larger constants.  Binary64 comparisons rest on a new lemma, `F64Compare.compare_canonical`, since the binary32 chain has no comparisons.  Decoding a non-NaN bit pattern gives a canonical unpacked float whose value is Talos's `scaledValue`, and Lean's comparison of canonical floats orders them by value.  Negation compiles to `-0.0 - x` (`F64Sign.sub_negZero`), absolute value to `f64.abs`, and `min` and `max` to a comparison and a conditional, which removes the three differences listed above.  Conversions have no theorems yet, and binary32 has no comparison or sign theorems.

## GPU

GPU support is on `origin/wgsl` (`9c7c7898`), about 99,000 added lines that were not merged.  Its README files describe a compiler, `LeanExe.WGSL.Compile`, that reads a restricted kernel form and emits WGSL, checking a source equality and a statement execution theorem per compilation, with strict shader execution and host transfers as premises.  The same design could cover kernels through a kernel IR, a small translation to WGSL, and per-kernel proofs.  The trusted base would grow by the repository's WGSL semantics, the browser's WGSL compiler, the GPU, and host transfers, and exact word equality would need a strict-execution premise.

## Repository state

Two cleanups removed about 22,200 tracked files.  The first deleted the examples, demos, benchmarks, old tests and tooling, unused ProofKit files, and `LocalRegion/` and `FunctionRegion/`, which referenced an undefined declaration and defined one declaration twice.  The second deleted the old compiler, the old `sumCount` proof, 191 unused Lean files, 31 LTG entries for old compiler patterns and benchmarks, the Node-based LTG and knowledge tools, and the old docs; then the proof workspace moved from `proofs/talos/lean` to the root.  The first inventory kept the LTG tools without checking their dependencies, and deleting `tools/leanexegen-lib.js` broke them before the second cleanup removed them.

The tracked tree holds `paper/` and `data/` (publication records), `Project/`, `LeanExe/`, `ltg/`, `tools/` (the Lean runner and the Wasmtime host builder), and root files.  The move rebuilt only the project's own modules.  Ignored directories remain: `.lake/` (dependencies and builds, 34 GB), `build/` (the Wasmtime host and emitted modules), and `tmp/` (579 MB, not examined).

## Scope of the theorem

1. The claim is about Talos's semantics.  Wasmtime appears only in tests, and the Talos interpreter and the decoder are trusted.
2. The premises `Heap.At`, `Heap.Borrowed`, and `Heap.Room` are assumed.  No theorem covers instantiation or the host.
3. `Implements` protects only the arguments and the allocator invariant.  It states nothing about other live objects.
4. `Emit.lean` evaluates `encode` with compiled Lean code, and no theorem connects the written file to the proved bytes.  The user deferred this item.
5. Until 2026-09-29, each `_bytes` theorem assumed `encode m = .ok bytes` and held vacuously if encoding failed, as `piecewise_bytes` did until the encoder gained the float comparison and constant instructions.  Each now proves that encoding succeeds.

The user doubted that items 2 and 3 need work, and no work on them is planned.

## Plan

- [x] Proof of concept, decoder, and design, committed.
- [x] First deletion stage.
- [x] Iteration 1, scalar arithmetic: `scale`.
- [x] Iteration 2, tail recursion: `gcd`, the rule lemma `Func.tail_implements`, `gcd` reproved with it, and the first LTG entry.
- [x] Clean house: the old compiler, JavaScript tools, and old docs deleted, LTG checked by a Lean script, and one package at the root.
- [x] Runtime functions in every module, with host tests.
- [x] Iteration 3a: `sumArray`, the `load` statement, `State.Frame`, `Func.implements` for `Represent` arguments, the compiler's fold rule, `Stmt.fold_spec`, and the `array-fold-loop` LTG entry.
- [x] Iteration 3b: `pairSum`, the `store` and `call` statements, `Triple` over a module, `Func.implements_heap`, `alloc_spec`, `release_run`, and the array-literal and release rules with their LTG entries.
- [x] Iteration 3c: `sumCount`, whose result the host owns and releases, with array results, `Nat.toUInt64 xs.size`, and `Func.implements_heap` over any result type.
- [x] Move `Expr`, `State`, and their lemmas into `Project/IR/Expr.lean`, delete the old IR and the three modules that only it used, and review the LTG entries written for the old pipeline.
- [ ] Iteration 4, sharing: a program that shares a value, with `retain`'s specification.
- [ ] Iteration 5, I/O: a step-function program with the trusted adapter.
- [x] Iteration 6a, floating point: binary64 `add`, `sub`, and `mul` equality proofs, `f64` in the IR, `Float` in the compiler, and `axpy`.
- [x] Iteration 6b: binary64 `div` and `sqrt`, and `scaledHypot`.
- [x] Iteration 6c: scalar `Float`: literals, comparisons, `==`, negation, `abs`, `min`, `max`, and `if`, with `piecewise`.
- [x] Iteration 6d: float arrays, with typed variables, `Array Float`, and `sumSquares`.
- [x] Conversions between `UInt64` and `Float`, with `mean` and `bucket`.
- [ ] CLOB 1: `marketBuy`, with `LeanExe.loop`, array reads, a loop state of two variables, and arguments that combine arrays and words.
- [ ] CLOB 2 and later: a limit order, a cancel, and a depth query with the copying template and Lean's array operations; then several functions per module and a function that applies a command.
- [ ] Later: `Array Float` literals, binary32 comparisons and sign operations, and `Float32` programs.
- [ ] Iteration 7, recursive values: a program over a list or tree, with recursive `release`.
- [ ] CPU GPT kernels: dot product, matrix-vector product, softmax with `exp` in Lean, layer norm, and one transformer block.
- [ ] Then design the GPU kernel path, and prove the I/O adapter.

Unknowns: the cost of a per-program proof over explicit memory; whether rule lemmas compose once memory arrives; how Talos's semantics is tested against the WebAssembly specification; and whether Talos bounds call depth.

## Commands

```sh
export PATH="$HOME/.elan/bin:$PATH"
tools/leanrun --timeout 60m lake build
tools/leanrun --timeout 10m lake env lean --run Project/Pipeline/Emit.lean \
  Project.Gcd.Module Project.Gcd.gcd.module build/gcd/gcd.wasm
wasm-tools validate build/gcd/gcd.wasm
build/tools/leanexe-wasmtime-host call build/gcd/gcd.wasm gcd i64 i64:48 i64:18
build/tools/leanexe-wasmtime-host call-stats build/sumArray/sumArray.wasm sumArray i64 \
  array-u64:1,2,3
tools/leanrun --timeout 10m lake env lean --run Project/LTG/Check.lean ltg/entries
tools/leanrun --timeout 60m lake env lean --run Project/Encoding/DecodeTest.lean \
  "$(command -v wasm-tools)" build/decode-test
```

The last command expects `build/decode-test` to hold `wasm-tools json-from-wast` output for the testsuite scripts in the CodeLib checkout.  The axiom audit is a Lean file that imports a program's `Verify` module and runs `#print axioms` on its theorems.

## Why the previous agent was fired

The user fired the agent that first wrote this file, Claude, on 2026-09-28.  There were two reasons: gross errors, and spinning those errors after they were found.

The gross errors were these:
- The first proof of `sumModule_implements` depended on Euler–Riemann and CLOB proof files, which the pipeline is meant to replace.
- The agent changed the hypotheses of `sumModule_implements` without discussion.  One of the added conditions existed only to fit a reused lemma.
- Told to remove that dependency, the agent began a mechanical copy of 223 declarations instead of moving the nine that caused it.
- `Implements` was written with a constant `need`, so no function whose allocation grows with its input can be stated.
- A requested critical review called a frame condition and host-level theorems defects to fix first, without checking whether anything needed them.

The spinning was this:
- When the user challenged the review, the agent agreed at once, without new evidence.
- It then twice described its wrong recommendations as "overstated" instead of wrong.
