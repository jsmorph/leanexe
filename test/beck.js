"use strict";

const assert = require("node:assert/strict");
const { runChecked } = require("../tools/run-process");
const beck = require("../tools/beck");

const cases = [];
function valid(input) { cases.push({ input, words: beck.encode(input), status: 0 }); }
function invalid(words, status) { cases.push({ words, status }); }

for (let n = 0; n <= 3; n++) {
  for (let code = 0; code < 8 ** n; code++) {
    let rest = code;
    const jobs = [];
    for (let job = 0; job < n; job++) {
      const bits = rest % 8;
      rest = Math.floor(rest / 8);
      jobs.push([0, 1, 2].filter(category => bits & (1 << category)));
    }
    valid({ categories: 3, jobs });
  }
}

valid({ categories: 0, jobs: [] });
valid({ categories: 0, jobs: Array.from({ length: 6 }, () => []) });
valid({ categories: 8, jobs: Array.from({ length: 6 }, () => [7]) });
valid(require("../data/beck/overlap.json"));
valid({ categories: 4, jobs: [[0, 1], [0, 2], [0, 3], [1, 2], [1, 3], [2, 3]] });
valid({ categories: 8, jobs: Array.from({ length: 6 }, () => [7, 6, 5, 4, 3, 2, 1, 0]) });

let seed = 76231;
function next(n) {
  seed = (Math.imul(seed, 1664525) + 1013904223) >>> 0;
  return (seed >>> 8) % n;
}
for (let k = 0; k < 128; k++) {
  const jobs = Array.from({ length: 6 }, () => {
    const a = next(4);
    const b = next(4);
    return a === b ? [a] : [a, b];
  });
  valid({ categories: 4, jobs });
}

invalid([], 1);
invalid([0], 1);
invalid([0, 0, 0], 1);
invalid([1, 1], 1);
invalid([1, 1, 1], 1);
invalid([1, 1, 1, 1], 1);
invalid([1, 2, 2, 0, 0], 1);
invalid([1, 0, 1, 0], 1);
invalid([7, 0], 2);
invalid([0, 9], 2);
invalid(["18446744073709551615", 0], 2);
invalid([1, 1, "18446744073709551615"], 1);
invalid([1, 1, 1, "18446744073709551615"], 1);

beck.prepare();
const native = runChecked(["lake", "env", "lean", "--run", "test/BeckNative.lean"], {
  cwd: beck.root, encoding: "utf8", timeout: 120000,
  input: cases.map(test => test.words.join(",")).join("\n") + "\n",
}).stdout.trim().split("\n").map(line => JSON.parse(line));
assert.equal(native.length, cases.length);

cases.forEach((test, index) => {
  const result = beck.execute(test.words);
  assert.deepEqual(result, native[index], `native/WASM case ${index}`);
  assert.equal(result[0], test.status, `status case ${index}`);
  if (test.status === 0) assert.equal(beck.check(test.input, result).status, "ok");
  else assert.equal(result.length, 1);
});

console.log(`beck: ${cases.length} native/WASM comparisons and independent output checks passed`);
