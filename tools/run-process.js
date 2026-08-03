const { spawn, spawnSync } = require("child_process");
const path = require("path");

const leanrun = path.join(__dirname, "leanrun");
const guardedExecutables = new Set([
  "lake",
  "lean",
  "lean-wasm",
  "leanc",
  "leanchecker",
  "leanmake",
]);

function formatCommand(args) {
  return args.map((arg) => JSON.stringify(String(arg))).join(" ");
}

function guardedInvocation(args, options) {
  if (!guardedExecutables.has(path.basename(args[0]))) {
    return { args, options };
  }

  const guardedOptions = { ...options };
  const env = { ...process.env, ...(options.env || {}) };
  if (options.timeout !== undefined) {
    env.LEANRUN_TIMEOUT = `${Math.max(1, Math.ceil(options.timeout / 1000))}s`;
    delete guardedOptions.timeout;
  }
  guardedOptions.env = env;
  return { args: [leanrun, ...args], options: guardedOptions };
}

function spawnResult(args, options = {}) {
  const invocation = guardedInvocation(args, options);
  const result = spawnSync(
    invocation.args[0],
    invocation.args.slice(1),
    invocation.options,
  );
  if (result.error) {
    throw new Error(
      `${formatCommand(args)} failed to start: ${result.error.message}`,
      { cause: result.error },
    );
  }
  return result;
}

function signalProcess(child, signal) {
  if (process.platform === "win32") {
    child.kill(signal);
    return;
  }
  try {
    process.kill(-child.pid, signal);
  } catch (error) {
    if (error.code !== "ESRCH") throw error;
  }
}

function spawnResultAsync(args, options = {}) {
  const invocation = guardedInvocation(args, options);
  const spawnOptions = {
    ...invocation.options,
    detached: process.platform !== "win32",
  };
  return new Promise((resolve, reject) => {
    const child = spawn(
      invocation.args[0],
      invocation.args.slice(1),
      spawnOptions,
    );
    const stdout = [];
    const stderr = [];
    if (child.stdout) child.stdout.on("data", (chunk) => stdout.push(Buffer.from(chunk)));
    if (child.stderr) child.stderr.on("data", (chunk) => stderr.push(Buffer.from(chunk)));
    let forwardedSignal = null;
    const handlers = new Map();
    const cleanup = () => {
      for (const [signal, handler] of handlers) {
        process.removeListener(signal, handler);
      }
    };
    for (const signal of ["SIGINT", "SIGTERM"]) {
      const handler = () => {
        forwardedSignal = forwardedSignal || signal;
        signalProcess(child, signal);
      };
      handlers.set(signal, handler);
      process.once(signal, handler);
    }
    child.once("error", (error) => {
      cleanup();
      reject(new Error(
        `${formatCommand(args)} failed to start: ${error.message}`,
        { cause: error },
      ));
    });
    child.once("close", (status, signal) => {
      cleanup();
      resolve({
        status: forwardedSignal === null ? status : null,
        signal: forwardedSignal || signal,
        stdout: Buffer.concat(stdout),
        stderr: Buffer.concat(stderr),
      });
    });
  });
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

async function runCheckedAsync(args, options = {}) {
  const result = await spawnResultAsync(args, options);
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

module.exports = {
  guardedInvocation,
  runChecked,
  runCheckedAsync,
  spawnResult,
  spawnResultAsync,
};
