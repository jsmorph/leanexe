#!/usr/bin/env node

const path = require("path");
const { spawnSync } = require("child_process");

const leanExe = process.env.LEAN_WASM_EXE || path.join(".lake", "build", "bin", "lean-wasm");

function run(args) {
  const result = spawnSync(leanExe, args, { encoding: "utf8" });
  if (result.error) {
    throw result.error;
  }
  return result;
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

  const help = run(["--help"]);
  if (help.status !== 0 || help.stderr !== "" || !help.stdout.startsWith("lean-wasm commands:\n")) {
    throw new Error(
      `help: unexpected result\nstatus: ${help.status}\nstdout:\n${help.stdout}\nstderr:\n${help.stderr}`,
    );
  }

  console.log("checked 9 CLI error cases and help output");
}

try {
  main();
} catch (error) {
  process.stderr.write(`${error.message}\n`);
  process.exit(1);
}
