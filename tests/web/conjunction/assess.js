// The call of the export `assess` of build/verified/conjunction.wasm that the conjunction page
// makes, and that tests/conjunction/page.mjs runs under Node.  `compiled.assess.implements` of
// Demos/Conjunction/Verified.lean states that the module's entry 55, the export `assess`, called
// with the words of `m1 m2 c11 c12 c22 r t : Float` and `n : UInt64` from a store with the
// allocator's invariant that holds the table of `exp` at address 4,096, returns without a trap the
// words of `Demos.Conjunction.assess` of the arguments: the status, `lo`, `hi`, and the verdict.
// The generated `compiled.initial` states that a fresh instance's store is such a store.
// `assess_sound` of Demos/Conjunction/Soundness.lean gives the meaning of an accepted result.

/** The largest panel count that `assess` accepts. */
export const PANELS = 1048576n;

/** The SHA-256 of the module's bytes in hexadecimal, and the compiled module. */
export async function load(bytes) {
  const digest = new Uint8Array(await crypto.subtle.digest("SHA-256", bytes));
  return {
    sha256: Array.from(digest, b => b.toString(16).padStart(2, "0")).join(""),
    module: await WebAssembly.compile(bytes),
  };
}

/** `assess` of a fresh instance of `module` on the encounter-plane inputs: the numbers `m1`,
`m2`, `c11`, `c12`, `c22`, `r`, and `t`, and the BigInt `n`.  The result holds the status and the
verdict as BigInts and `lo` and `hi` as numbers. */
export async function assess(module, { m1, m2, c11, c12, c22, r, t, n }) {
  const x = (await WebAssembly.instantiate(module)).exports;
  const [status, lo, hi, verdict] = x.assess(m1, m2, c11, c12, c22, r, t, n);
  return { status, lo, hi, verdict };
}
