#!/usr/bin/env node

const path = require("path");
const { spawnResult, withoutLeanrunNotices } = require("../tools/run-process");

const leanExe = process.env.LEAN_WASM_EXE || path.join(".lake", "build", "bin", "lean-wasm");

function run(args) {
  return spawnResult([leanExe, ...args], { encoding: "utf8" });
}

function expectFailure(name, args, status, fragments) {
  const result = run(args);
  if (result.status !== status) {
    throw new Error(
      `${name}: expected status ${status}, got ${result.status}\nstdout:\n${result.stdout}\nstderr:\n${result.stderr}`,
    );
  }
  if (result.stdout !== "") {
    throw new Error(`${name}: expected empty stdout, got ${JSON.stringify(result.stdout)}`);
  }
  for (const fragment of fragments) {
    if (!result.stderr.includes(fragment)) {
      throw new Error(`${name}: stderr is missing ${JSON.stringify(fragment)}:\n${result.stderr}`);
    }
  }
  if (result.stderr.includes("uncaught exception")) {
    throw new Error(`${name}: stderr contains an uncaught exception marker:\n${result.stderr}`);
  }
  if (result.stderr.includes("\u001b[")) {
    throw new Error(`${name}: stderr contains an ANSI escape:\n${JSON.stringify(result.stderr)}`);
  }
}

function main() {
  expectFailure("invalid command shape", ["compile"], 2, [
    'lean-wasm: usage: command "compile": invalid command or arguments',
    "lean-wasm commands:",
  ]);

  expectFailure(
    "invalid numeric bound",
    [
      "compile-wasi-stdin",
      "--max-input-bytes",
      "nope",
      "--module",
      "LeanExe.Examples.JsonAdd",
      "--entry",
      "LeanExe.Examples.JsonAdd.transform",
      "--out",
      ".lake/build/cli-errors/invalid-bound.wasm",
    ],
    2,
    [
      'lean-wasm: usage: command "compile-wasi-stdin"',
      'invalid value for --max-input-bytes: expected a natural number, got "nope"',
    ],
  );

  expectFailure(
    "excessive numeric bound",
    [
      "compile-wasi-stdin",
      "--max-input-bytes",
      "999999999999999999999",
      "--module",
      "LeanExe.Examples.JsonAdd",
      "--entry",
      "LeanExe.Examples.JsonAdd.transform",
      "--out",
      ".lake/build/cli-errors/excessive-bound.wasm",
    ],
    2,
    [
      'lean-wasm: usage: command "compile-wasi-stdin"',
      "max input bytes exceeds WASM memory capacity: 999999999999999999999",
    ],
  );

  expectFailure(
    "missing module",
    [
      "compile",
      "--module",
      "LeanExe.Examples.DoesNotExist",
      "--entry",
      "LeanExe.Examples.DoesNotExist.run",
      "--out",
      ".lake/build/cli-errors/missing-module.wasm",
    ],
    3,
    [
      'lean-wasm: source: command "compile", module "LeanExe.Examples.DoesNotExist", entry "LeanExe.Examples.DoesNotExist.run"',
      "of module LeanExe.Examples.DoesNotExist does not exist",
    ],
  );

  expectFailure(
    "missing entry",
    [
      "compile",
      "--module",
      "LeanExe.Examples.Correctness",
      "--entry",
      "LeanExe.Examples.Correctness.doesNotExist",
      "--out",
      ".lake/build/cli-errors/missing-entry.wasm",
    ],
    3,
    [
      'lean-wasm: source: command "compile", module "LeanExe.Examples.Correctness", entry "LeanExe.Examples.Correctness.doesNotExist"',
      "entry not found: LeanExe.Examples.Correctness.doesNotExist",
    ],
  );

  expectFailure(
    "wrong program entry type",
    [
      "compile-wasi",
      "--module",
      "LeanExe.Examples.TalosGcd",
      "--entry",
      "LeanExe.Examples.TalosGcd.gcd",
      "--out",
      ".lake/build/cli-errors/wrong-type.wasm",
    ],
    3,
    [
      'lean-wasm: source: command "compile-wasi", module "LeanExe.Examples.TalosGcd", entry "LeanExe.Examples.TalosGcd.gcd"',
      "program entry must take no parameters: LeanExe.Examples.TalosGcd.gcd",
    ],
  );

  expectFailure(
    "unsupported declaration",
    [
      "compile",
      "--module",
      "LeanExe.Examples.Correctness",
      "--entry",
      "LeanExe.Examples.Correctness.rejectHugeNatLiteral",
      "--out",
      ".lake/build/cli-errors/unsupported.wasm",
    ],
    3,
    [
      'lean-wasm: source: command "compile", module "LeanExe.Examples.Correctness", entry "LeanExe.Examples.Correctness.rejectHugeNatLiteral"',
      "Nat literal exceeds bounded runtime representation: 18446744073709551616",
    ],
  );

  expectFailure(
    "reserved export",
    [
      "compile",
      "--module",
      "LeanExe.Examples.Correctness",
      "--entry",
      "LeanExe.Examples.Correctness.alloc",
      "--out",
      ".lake/build/cli-errors/reserved.wasm",
    ],
    3,
    [
      'lean-wasm: source: command "compile", module "LeanExe.Examples.Correctness", entry "LeanExe.Examples.Correctness.alloc"',
      "entry export name is reserved by the runtime ABI: alloc",
    ],
  );

  expectFailure("failed output write", ["emit", "--out", ".lake/build"], 4, [
    'lean-wasm: I/O: command "emit", output ".lake/build"',
    "inappropriate type",
    "file: .lake/build",
  ]);

  expectFailure("invalid byte I/O command shape", ["compile-wasi-io"], 2, [
    'lean-wasm: usage: command "compile-wasi-io": invalid command or arguments',
  ]);
  for (const [module, entry] of [
    ["LeanExe.Examples.Correctness", "byteArrayStringLiteralReturn"],
    ["LeanExe.Examples.Correctness", "rejectIO"],
    ["LeanExe.Examples.ByteIO", "mark"],
  ]) {
    expectFailure(`invalid byte I/O entry ${entry}`, [
      "compile-wasi-io", "--module", module, "--entry", `${module}.${entry}`,
      "--out", ".lake/build/cli-errors/rejected-io.wasm",
    ], 3, ['lean-wasm: source: command "compile-wasi-io"',
      "ByteIO entry must have type ByteIO UInt32"]);
  }
  expectFailure("missing byte I/O entry", [
    "compile-wasi-io", "--module", "LeanExe.Examples.ByteIO",
    "--entry", "LeanExe.Examples.ByteIO.doesNotExist",
    "--out", ".lake/build/cli-errors/missing-io.wasm",
  ], 3, ['lean-wasm: source: command "compile-wasi-io"',
    "entry not found: LeanExe.Examples.ByteIO.doesNotExist"]);
  expectFailure("byte I/O output write failure", [
    "compile-wasi-io", "--module", "LeanExe.Examples.ByteIO",
    "--entry", "LeanExe.Examples.ByteIO.echo", "--out", ".lake/build",
  ], 4, ['lean-wasm: I/O: command "compile-wasi-io"', "file: .lake/build"]);

  const help = run(["--help"]);
  // Local runners announce the user-authorized operating limits on stderr.
  // Allow only those exact notices; compiler diagnostics must still be absent.
  const helpStderr = withoutLeanrunNotices(help.stderr);
  if (help.status !== 0 || helpStderr !== "" || !help.stdout.startsWith("lean-wasm commands:\n")) {
    throw new Error(
      `help: unexpected result\nstatus: ${help.status}\nstdout:\n${help.stdout}\nstderr:\n${help.stderr}`,
    );
  }

  console.log("checked 15 CLI error cases and help output");
}

try {
  main();
} catch (error) {
  process.stderr.write(`${error.message}\n`);
  process.exit(1);
}
