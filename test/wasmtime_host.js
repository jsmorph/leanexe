const fs = require("fs");
const path = require("path");
const { spawnSync } = require("child_process");

const hostExe = process.env.LEANEXE_WASMTIME_HOST || path.join("build", "tools", "leanexe-wasmtime-host");

function run(args, options = {}) {
  const result = spawnSync(args[0], args.slice(1), { encoding: "utf8", ...options });
  if (result.status !== 0) {
    throw new Error(result.stderr.trim() || result.stdout.trim() || `${args.join(" ")} failed`);
  }
  return result.stdout.trim();
}

function ensureHost() {
  if (fs.existsSync(hostExe)) {
    return hostExe;
  }
  run([path.join("tools", "build-wasmtime-host.sh")]);
  if (!fs.existsSync(hostExe)) {
    throw new Error(`Wasmtime host runner was not built: ${hostExe}`);
  }
  return hostExe;
}

function toHex(bytes) {
  return Array.from(bytes, (byte) => byte.toString(16).padStart(2, "0")).join("");
}

function fromHex(hex) {
  if (hex.length % 2 !== 0) {
    throw new Error(`invalid hex output: ${hex}`);
  }
  const bytes = new Uint8Array(hex.length / 2);
  for (let index = 0; index < bytes.length; index += 1) {
    bytes[index] = Number.parseInt(hex.slice(index * 2, index * 2 + 2), 16);
  }
  return bytes;
}

function i64(value) {
  return `i64:${BigInt(value).toString()}`;
}

function byteArray(bytes) {
  return `bytes:${toHex(bytes)}`;
}

function arrayU64(values) {
  return `array-u64:${values.map((value) => BigInt(value).toString()).join(",")}`;
}

function call(wasm, entry, resultKind, args = []) {
  const exe = ensureHost();
  return run([exe, "call", wasm, entry, resultKind, ...args]);
}

function callI64(wasm, entry, args = []) {
  return BigInt(call(wasm, entry, "i64", args));
}

function callBytes(wasm, entry, args = []) {
  return fromHex(call(wasm, entry, "bytes", args));
}

function callStats(wasm, entry, resultKind, args = []) {
  const exe = ensureHost();
  const output = run([exe, "call-stats", wasm, entry, resultKind, ...args]);
  const lines = output.split(/\r?\n/);
  const parts = lines[lines.length - 1].split(/\s+/);
  if (parts[0] !== "stats" || parts.length !== 5) {
    throw new Error(`missing stats line from Wasmtime host: ${output}`);
  }
  return {
    result: lines.slice(0, -1).join("\n"),
    allocs: BigInt(parts[1]),
    retains: BigInt(parts[2]),
    releases: BigInt(parts[3]),
    frees: BigInt(parts[4]),
  };
}

function script(wasm, commands, entry, resultCount, readCommands = []) {
  const exe = ensureHost();
  const input = `${commands.join("\n")}\ncall ${entry} ${resultCount}\n${readCommands.join("\n")}\ndone\n`;
  const result = spawnSync(exe, ["script", wasm], {
    encoding: "utf8",
    input,
    maxBuffer: 8 * 1024 * 1024,
  });
  if (result.status !== 0) {
    throw new Error(result.stderr.trim() || result.stdout.trim() || `${exe} script failed`);
  }
  const lines = result.stdout.split(/\r?\n/).filter((line) => line.length > 0);
  const resultLine = lines.find((line) => line.startsWith("results"));
  if (!resultLine) {
    throw new Error("Wasmtime host script did not return result slots");
  }
  const slots = resultLine.split(/\s+/).slice(1).map((value) => BigInt(value));
  const memoryChunks = lines
    .filter((line) => line.startsWith("memory "))
    .map((line) => {
      const parts = line.split(/\s+/);
      if (parts.length < 3) {
        throw new Error(`invalid memory line from Wasmtime host: ${line}`);
      }
      const start = BigInt(parts[1]);
      const length = Number(BigInt(parts[2]));
      const bytes = fromHex(parts[3] || "");
      if (bytes.length !== length) {
        throw new Error(`Wasmtime host returned ${bytes.length} bytes for ${length}-byte memory range`);
      }
      return { start, bytes };
    });
  return {
    slots,
    memoryChunks,
  };
}

module.exports = {
  arrayU64,
  byteArray,
  call,
  callBytes,
  callI64,
  callStats,
  ensureHost,
  i64,
  script,
};
