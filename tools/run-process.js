const { spawnSync } = require("child_process");

function formatCommand(args) {
  return args.map((arg) => JSON.stringify(String(arg))).join(" ");
}

function spawnResult(args, options = {}) {
  const result = spawnSync(args[0], args.slice(1), options);
  if (result.error) {
    throw new Error(
      `${formatCommand(args)} failed to start: ${result.error.message}`,
      { cause: result.error },
    );
  }
  return result;
}

function outputText(value) {
  if (value === undefined || value === null) {
    return "";
  }
  return Buffer.isBuffer(value) ? value.toString("utf8") : String(value);
}

function runChecked(args, options = {}) {
  const result = spawnResult(args, options);
  if (result.status !== 0) {
    const output = [outputText(result.stderr).trim(), outputText(result.stdout).trim()]
      .filter((part) => part.length > 0)
      .join("\n");
    const termination = result.signal
      ? `terminated by ${result.signal}`
      : `exited with status ${result.status}`;
    const detail = output.length > 0 ? `:\n${output}` : "";
    throw new Error(`${formatCommand(args)} ${termination}${detail}`);
  }
  return result;
}

module.exports = { runChecked, spawnResult };
