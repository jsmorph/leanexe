#!/usr/bin/env node

const { runChecked } = require("../tools/run-process");

function expectFailure(args, expected) {
  try {
    runChecked(args, { encoding: "utf8" });
  } catch (error) {
    for (const text of expected) {
      if (!error.message.includes(text)) {
        throw new Error(`missing ${JSON.stringify(text)} in ${JSON.stringify(error.message)}`);
      }
    }
    return;
  }
  throw new Error(`${args[0]} succeeded but should have failed`);
}

expectFailure(["leanexe-command-that-does-not-exist"], [
  "leanexe-command-that-does-not-exist",
  "failed to start",
  "ENOENT",
]);
expectFailure([
  process.execPath,
  "-e",
  "process.stderr.write('specific failure\\n'); process.exit(7)",
], ["exited with status 7", "specific failure"]);
runChecked([process.execPath, "-e", "process.exit(0)"], { stdio: "ignore" });

process.stdout.write("checked 3 process error cases\n");
