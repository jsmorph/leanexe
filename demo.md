# JSON Tree WASI Demo

## Purpose

This demo shows two Lean functions compiled to standalone WASM command modules and run with Wasmtime.  The first command reads a JSON array of unsigned integers from stdin and writes a binary-search tree encoded as JSON.  The second command reads that tree JSON from stdin, reads one search key from argv, and writes a JSON boolean result.

The shape mirrors an ordinary command pipeline: `make-tree` transforms one JSON document into another JSON document, and `search-tree` consumes the intermediate document.  The Lean source remains pure; the generated WASI adapters perform stdin, argv, stdout, stderr, and exit-status handling.  The command modules run directly under Wasmtime and do not require a JavaScript host.

## Source Program

The source lives in the [JSON tree command](LeanExe/Examples/JsonTreeCommand.lean).  It defines a recursive `Tree` type with `empty` and `node` constructors, inserts input numbers into that tree, renders the tree through the JSON AST renderer, decodes the tree back from JSON, and searches it structurally.  The public entries are `LeanExe.Examples.JsonTreeCommand.makeTree` and `LeanExe.Examples.JsonTreeCommand.searchTree`.

`makeTree : ByteArray -> Except ByteArray ByteArray` parses stdin with `LeanExe.Ascii.Json.parseBytes`, accepts only a top-level JSON array of unsigned `UInt64` numbers, and returns `Except.ok` containing the rendered tree JSON.  `searchTree : ByteArray -> Array ByteArray -> Except ByteArray ByteArray` parses the tree JSON from stdin, decodes it into the source-level `Tree`, parses one decimal argv value, and returns `{"found":true}` or `{"found":false}`.  Both entries return `Except.error {"error":1}` for malformed input or unsupported shapes.

## Build

Build the compiler before compiling the demo entries.  The commands below place the generated WASM modules in `build/demo`.  The byte and argv limits are explicit because the WASI adapters allocate bounded input regions inside the generated module.

```sh
lake build lean-wasm
mkdir -p build/demo

.lake/build/bin/lean-wasm compile-wasi-stdin-except \
  --max-input-bytes 4096 \
  --module LeanExe.Examples.JsonTreeCommand \
  --entry LeanExe.Examples.JsonTreeCommand.makeTree \
  --out build/demo/make-tree.wasm

.lake/build/bin/lean-wasm compile-wasi-stdin-argv-except \
  --max-input-bytes 8192 \
  --max-args 8 \
  --max-argv-bytes 256 \
  --module LeanExe.Examples.JsonTreeCommand \
  --entry LeanExe.Examples.JsonTreeCommand.searchTree \
  --out build/demo/search-tree.wasm
```

The first compile command selects the stdin-to-`Except` adapter because `makeTree` has one `ByteArray` input and an explicit success-or-error result.  The second compile command selects the stdin-plus-argv-to-`Except` adapter because `searchTree` takes the tree document from stdin and the search key from argv.  Both generated commands write `Except.ok` bytes to stdout, write `Except.error` bytes to stderr, and return a nonzero status for source-level errors.

## Run

Set `WASMTIME` to the Wasmtime binary in this repository, or replace it with `wasmtime` if Wasmtime is on `PATH`.  The example input inserts the numbers in array order, so the produced tree is deterministic.  Duplicate values go into the right branch because `insert` uses a strict less-than test for the left branch.

```sh
WASMTIME=build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime

printf '%s' '[1,6,4,100,33,5,5,20]' \
  | "$WASMTIME" run build/demo/make-tree.wasm
```

Expected output:

```json
{"value":1,"left":null,"right":{"value":6,"left":{"value":4,"left":null,"right":{"value":5,"left":null,"right":{"value":5,"left":null,"right":null}}},"right":{"value":100,"left":{"value":33,"left":{"value":20,"left":null,"right":null},"right":null},"right":null}}}
```

The full pipeline searches the generated tree without storing the intermediate JSON in a file.  Searching for `4` succeeds because the input array contains that value.  Searching for `7` fails because the input array does not contain that value.

```sh
printf '%s' '[1,6,4,100,33,5,5,20]' \
  | "$WASMTIME" run build/demo/make-tree.wasm \
  | "$WASMTIME" run build/demo/search-tree.wasm 4
```

Expected output:

```json
{"found":true}
```

```sh
printf '%s' '[1,6,4,100,33,5,5,20]' \
  | "$WASMTIME" run build/demo/make-tree.wasm \
  | "$WASMTIME" run build/demo/search-tree.wasm 7
```

Expected output:

```json
{"found":false}
```

Malformed input reaches the source-level `Except.error` path.  The WASI adapter writes the error payload to stderr and exits with status `1`.  This example fails because the top-level array contains a string instead of an unsigned integer.

```sh
printf '%s' '[1,"x"]' \
  | "$WASMTIME" run build/demo/make-tree.wasm
```

Expected stderr:

```json
{"error":1}
```

## What This Exercises

| Feature | Use in the demo |
|---------|-----------------|
| Recursive inductive data | `Tree` is a source-defined recursive type compiled as an internal heap value. |
| Structural recursion | `insert`, `treeValue`, `decodeTree`, and `contains` recurse over source-level data. |
| Array folds | `buildTree` folds over the parsed JSON array, and `decodeTree` folds over attached object fields. |
| JSON AST parsing | `parseBytes` parses complete nested JSON into `LeanExe.Ascii.Json.Value`. |
| JSON AST rendering | `treeValue` constructs a JSON AST, and `render?` serializes it to bytes. |
| WASI command adapters | `compile-wasi-stdin-except` and `compile-wasi-stdin-argv-except` provide observable command behavior. |

The demo keeps recursive values internal to the generated module.  The public command boundary uses `ByteArray`, `Array ByteArray`, and `Except ByteArray ByteArray`, which the WASI adapters know how to populate and observe.  This matches the current ABI rule: recursive data structures may be built, traversed, and returned between internal helpers, but public entry parameters and public entry results use first-order ABI shapes.

The `decodeTree` implementation uses `fields.attach.foldl` rather than a generic object getter.  That spelling exposes the field-membership proof used in the Lean termination argument for recursive calls on child JSON values.  It also matches the well-founded-recursion shape currently accepted by the compiler.

## Verification

The end-to-end checks for this document compile both command modules from the current source and run them under Wasmtime.  The tree-producing command returned the nested JSON object shown above.  The pipeline returned `{"found":true}` for key `4`, returned `{"found":false}` for key `7`, and returned `{"error":1}` with exit status `1` for `[1,"x"]`.
