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

module.exports = {
  arrayU64,
  byteArray,
  call,
  callBytes,
  callI64,
  ensureHost,
  i64,
};
