# Seminumerical libraries

This PoC develops small LeanExe components, runnable clients, and technical reports.  It contains number-theory, polynomial, and transcendental libraries.  Components have stated specifications and execution tests.  Correctness proofs are deferred.

## Components

| Task | Algorithm | Implementation | Documentation |
|------|-----------|----------------|---------------|
| Greatest common divisor | Euclidean remainder algorithm | `UInt64` loop | [GCD](../LeanExe/Lib/NumberTheory/Gcd/README.md) |
| Greatest common divisor | Binary GCD | `UInt64` shifts and subtraction | [Binary GCD](../LeanExe/Lib/NumberTheory/BinaryGcd/README.md) |
| Polynomial evaluation | Horner's rule | Checked `UInt64` loop | [Horner evaluation](../LeanExe/Lib/Polynomial/Horner/README.md) |
| Exponential | Degree-six Taylor approximation | Binary64 Horner evaluation on `[-1, 0]` | [Bounded exponential](../LeanExe/Lib/Transcendental/Exp/README.md) |

A task may have several algorithms, and an algorithm may have several implementations.  Each catalog entry identifies one implementation and its public Lean declaration.  A library groups related components.  Clients select implementations through ordinary imports and function calls.

## Setup and commands

The [development guide](../DEVELOPING.md#prerequisites) describes Lean, Node.js, and Wasmtime setup.  The commands use the existing Lean runner and Wasmtime host.  An existing Wasmtime C API installation can be selected with `WASMTIME_C_API`, or an existing host with `LEANEXE_WASMTIME_HOST`.

```sh
tools/seminum gcd 48 18
tools/seminum fraction 48 18
tools/seminum polynomial 2 1,3,2
tools/seminum ratio 2 1,3,2 2,2
tools/seminum fraction-binary 48 18
tools/seminum decay 0.5
node test/seminum.js
tools/seminum inspect
```

The outputs of the first six commands are `6`, `8/3`, `15`, `5/2`, `8/3`, and `0.6065321180555556`.  The polynomial-ratio client uses the number-theory and polynomial libraries.  The two fraction clients select different GCD algorithms.  The decay client uses the transcendental library.

Integer commands accept decimal `UInt64` values.  Array arguments use comma-separated coefficients in ascending degree order, with `[]` for an empty array.  `exp` and `decay` accept decimal floating-point values.  `exp-bits` accepts sixteen hexadecimal binary64 digits.  Successful commands write results to stdout.  Invalid inputs, domain errors, and integer overflow exit with status 2 and a diagnostic on stderr.  Build and execution failures exit with status 1.  `tools/seminum --help` lists the commands.

`tools/seminum build` creates `build/seminum/examples.wasm`.  It also asks the compiler for its existing source-name and instruction annotations.  The tool matches the source names against the [component catalog](catalog.json) and writes `build/seminum/components.json`.  That generated inventory records which component declarations appear in the program and their WASM indexes.  The catalog supplies intended specifications and documentation references.  `inspect` prints this inventory.

## Reports and development

Each component directory under `LeanExe/Lib` contains its implementation in `Basic.lean`, its README, and its report in LaTeX and PDF form.  Reports include listings from the executable Lean files.  From the repository root, `tools/seminum reports` builds every report with `pdflatex` and copies the PDFs into the component directories.  Auxiliary files remain under `build/seminum/reports`.  The PDFs can be read without a TeX installation.

The [development journal](../devnotes.md) records batch reviews and remaining work.  The first batch introduced Euclidean GCD and Horner evaluation.  The second added binary GCD and a bounded exponential.  The combined test suite passes 252 WASM/native comparisons and checks CLI errors, mathematical references, and component discovery.  The reports include the exact commands and scope of the numerical comparison.

## Adding a component or library

A contribution can contain one component or a group of components.  Its README describes the API, intended behavior, runnable example, test and proof status, and references with an explanation of their use.  A short report explains the algorithm and implementation choices.  Related implementations can share explanatory material and tests.

These initial libraries use modules under `LeanExe.Lib` because the current compiler accepts executable helper dependencies under the entry module's root namespace.  The [language specification](../docs/spec.md) describes that boundary.  Independently named external libraries need an extension to dependency admission.  Private helpers also encounter this boundary because Lean gives them names rooted at `_private`.  The current components use public definitions.

An entry in the catalog makes a public declaration discoverable through compiler annotations.  The example driver and tests select the desired exported clients.  Individual components can also be imported and called from another LeanExe program without using the example driver.
