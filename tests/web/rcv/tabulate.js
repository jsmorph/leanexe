// The call of the export `tabulate` of the tabulator's modules that the recount page makes, and
// that tests/rcv/page.mjs runs under Node.  For the Oakland module rcvTabulate.wasm,
// `tabulate_callSpec` of Demos/Rcv/TabulateCall.lean states T1: function 63, the export
// `tabulate`, called with a borrowed buffer `b` from a ready store in which the allocator's `top`
// can rise by `compiled.tabulate.bound b` bytes within the memory cap, returns without a trap an
// owned buffer that holds `reportFile` of the bytes of `b`, and `tabulate_bound` of
// Demos/Rcv/TabulateBound.lean bounds `compiled.tabulate.bound b` by 80 L + 33,702,909 for a file
// of L < 2^32 bytes.  For the Maine module rcvMaine.wasm, `tabulate_callSpec` of
// Demos/Rcv/Maine/TabulateCall.lean states the same of function 64 and the Maine `reportFile`, and
// `tabulate_bound` of Demos/Rcv/Maine/TabulateBound.lean gives 80 L + 33,958,029.  A fresh
// instance's store is ready (`Verified.Ready.initial`).  `top` lies inside the memory
// (`Heap.At.top`), and `alloc` of `n` bytes raises it by at most 48 + allocSize(n)
// (`Heap.allocate_top`) and returns the root of a buffer object whose bytes the host then writes.

const PAGE = 65536n;

/** The memory cap of every module of the verified compiler, 65,535 pages, in bytes. */
const CAP = 65535n * PAGE;

/** The modules: the file that the page loads and the constant of `tabulate_bound`. */
export const MODULES = {
  oakland: { file: "rcvTabulate.wasm", constant: 33702909n },
  maine: { file: "rcvMaine.wasm", constant: 33958029n },
};

/** The payload that `alloc` requests for `n` bytes, `allocSize` of
LeanExe/Pipeline/RuntimeSpec.lean: `n` rounded up to a multiple of 8, and at least 8. */
function allocSize(n) {
  const rounded = (n + 7n) / 8n * 8n;
  return rounded < 8n ? 8n : rounded;
}

/** A file that the page does not pass to the module, since the call would fall outside the
theorem's premises or the browser would not provide the memory. */
export class Refusal extends Error {}

/** `80 length + constant`, which the module's `tabulate_bound` proves at least
`compiled.tabulate.bound b` for every file `b` of `length` bytes when `length < 2^32`, with the
module's constant from `MODULES`, and null for a longer file. */
export function boundOf(length, constant) {
  const L = BigInt(length);
  return L < 2n ** 32n ? 80n * L + constant : null;
}

/** The SHA-256 of the module's bytes in hexadecimal, and the compiled module. */
export async function load(bytes) {
  const digest = new Uint8Array(await crypto.subtle.digest("SHA-256", bytes));
  return {
    sha256: Array.from(digest, b => b.toString(16).padStart(2, "0")).join(""),
    module: await WebAssembly.compile(bytes),
  };
}

/** The bytes that need to fit above the memory's size for a call on a file of `length` bytes
with the bound `bound`: the block that `alloc` adds for the file, and the bound. */
export function room(length, bound) {
  return 48n + allocSize(BigInt(length)) + bound;
}

/** The report of the file `file`, a Uint8Array, from a fresh instance of `module`, with `bound`
at least `compiled.tabulate.bound` of the file.  The memory's size plus `room` must be at most the
cap, which gives `top` plus the bound at most the cap after `alloc`.  The memory grows to that size
before `alloc`, so that neither `alloc` nor `tabulate` grows it, and a browser that refuses the
memory refuses it here, before any call. */
export async function tabulate(module, file, bound) {
  const x = (await WebAssembly.instantiate(module)).exports;
  const need = room(file.length, bound);
  const size = BigInt(x.memory.buffer.byteLength);
  if (size + need > CAP) {
    throw new Refusal(`the call needs ${need} bytes above the module's memory of ${size} bytes, ` +
                      `and the memory cap of 65,535 pages leaves ${CAP - size}`);
  }
  const pages = (need + PAGE - 1n) / PAGE;
  try {
    x.memory.grow(Number(pages));
  } catch (e) {
    if (e instanceof RangeError) {
      throw new Refusal(`the browser did not grow the module's memory by ${pages} pages: ${e.message}`);
    }
    throw e;
  }
  const length = BigInt(file.length);
  const root = x.alloc(length);
  new Uint8Array(x.memory.buffer, Number(root), file.length).set(file);
  const [report, reportLength] = x.tabulate(root, length);
  return new Uint8Array(x.memory.buffer, Number(report), Number(reportLength)).slice();
}
