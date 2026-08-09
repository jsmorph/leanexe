#!/usr/bin/env node
"use strict";

const assert = require("node:assert");
const fs = require("node:fs");
const os = require("node:os");
const path = require("node:path");
const { spawnSync } = require("node:child_process");
const {
  catalogMetrics,
  catalogDigest,
  checkCatalog,
  defaultRoot,
  loadCatalog,
  taskCatalogFiles,
} = require("../tools/ltg-lib");

function expectFailure(action, pattern) {
  let error = null;
  try {
    action();
  } catch (caught) {
    error = caught;
  }
  assert(error !== null && pattern.test(error.message),
    `expected ${pattern}, found ${error === null ? "success" : error.message}`);
}

function categoryRecords(task, category) {
  return task.files.get(`categories/${category}/tools.jsonl`).trim().split("\n")
    .filter((line) => line.length > 0)
    .map((line) => JSON.parse(line));
}

function main() {
  const catalog = checkCatalog();
  assert(catalog.categories.some((category) => category.id === "worked-examples") &&
    catalog.entries.some((entry) => entry.id === "euclidean-gcd-loop"),
  "LTG catalog omitted a required category or canonical entry");
  const mapAdd = catalog.entries.find((entry) => entry.id === "fixed-array-map-add");
  assert(mapAdd !== undefined && mapAdd.categories.includes("arrays") &&
    mapAdd.categories.includes("loops") && mapAdd.categories.includes("compiler-motifs"),
  "map-add entry did not appear in overlapping semantic categories");

  const complete = taskCatalogFiles();
  assert(complete.entryIds.length === catalog.entries.length &&
    complete.excludedEntryIds.length === 0 &&
    complete.files.has("entries/fixed-array-map-add/entry.json") &&
    categoryRecords(complete, "arrays").some((entry) =>
      entry.id === "fixed-array-map-add" && entry.path ===
        "../../entries/fixed-array-map-add"),
  "complete task catalog omitted a canonical entry or category reference");
  const initialSingletonQuery =
    /singleton_wrapper|FixedArrayPairResult|publicPost|entryFrame|function_1/;
  assert(categoryRecords(complete, "arrays").some((entry) =>
    entry.id === "fixed-array-singleton-wrapper" &&
      initialSingletonQuery.test(JSON.stringify(entry))),
  "category index cannot answer the first Demo 6 singleton-wrapper query");

  const demo4 = taskCatalogFiles({
    artifactSha256: "c538d40936b426ba875b3dae1913e62ff00a44b34adff2adcd70922e5a4c95ff",
  });
  assert(demo4.excludedEntryIds.join(",") === "demo4-map-proof-example" &&
    !demo4.files.has("entries/demo4-map-proof-example/entry.json") &&
    !categoryRecords(demo4, "worked-examples").some((entry) =>
      entry.id === "demo4-map-proof-example") &&
    demo4.files.has("entries/fixed-array-map-add/entry.json"),
  "exact-artifact exclusion removed the wrong LTG content");

  const counterDerivative = taskCatalogFiles({
    excludedDerivativeGroups: ["counter-transfer-singleton"],
  });
  assert(counterDerivative.excludedEntryIds.join(",") ===
      "demo7-counter-transfer-example,demo8-counter-transfer-example" &&
    counterDerivative.files.has("entries/counter-transition/entry.json"),
  "derivative exclusion removed canonical support or retained worked examples");
  expectFailure(() => taskCatalogFiles({ excludedDerivativeGroups: ["Bad Group"] }),
    /unique identifiers/);
  assert(catalogDigest(complete.files) === catalogDigest(taskCatalogFiles().files),
    "task catalog digest is nondeterministic");

  const metrics = catalogMetrics(catalog);
  const repeatedMetrics = catalogMetrics(catalog);
  assert.deepStrictEqual(metrics, repeatedMetrics, "LTG metrics are nondeterministic");
  assert(metrics.catalog.categories === catalog.categories.length &&
    metrics.catalog.entries === catalog.entries.length &&
    metrics.categoryStructure.memberships === catalog.entries.reduce(
      (total, entry) => total + entry.categories.length, 0) &&
    metrics.leanSupport.catalogDeclarationReferences === catalog.entries.reduce(
      (total, entry) => total + entry.declarations.length, 0),
  "LTG metrics disagree with canonical catalog structure");
  assert(metrics.content.canonicalCatalogBytes +
      metrics.content.generatedCategoryIndexBytes === metrics.content.physicalCatalogBytes &&
    metrics.content.physicalCatalogBytes === metrics.content.taskBundleBytes,
  "LTG metrics mix canonical content with generated index duplication");
  assert(metrics.leanSupport.missingLocalCatalogDeclarationNames.length === 0 &&
    metrics.graphAndExclusions.structurallyDanglingCategoryModuleOrEntryReferences === 0,
  "LTG metrics found a missing local declaration or structural reference");
  assert(metrics.leanSupport.tacticDefinitions > 0 &&
    metrics.coverage.entriesImportingTacticModules > 0,
  "LTG metrics omitted proof-kit tactic support");

  const temporaryRoot = fs.mkdtempSync(path.join(os.tmpdir(), "leanexe-ltg-test-"));
  let scaleSearchMilliseconds;
  try {
    const copyRoot = path.join(temporaryRoot, "ltg");
    fs.cpSync(defaultRoot, copyRoot, { recursive: true, errorOnExist: true });
    fs.appendFileSync(
      path.join(copyRoot, "categories", "arrays", "tools.jsonl"), "{}\n");
    expectFailure(() => checkCatalog(copyRoot), /is stale/);
    assert(loadCatalog(copyRoot).entries.length === catalog.entries.length,
      "stale generated index changed canonical entry validation");

    const loopRecords = categoryRecords(complete, "loops");
    const scalarLoop = loopRecords.find((entry) => entry.id === "scalar-post-test-loop");
    const gcdLoop = loopRecords.find((entry) => entry.id === "euclidean-gcd-loop");
    assert(scalarLoop !== undefined && gcdLoop !== undefined,
      "scale search lacks its two real target entries");
    const synthetic = Array.from({ length: 10000 }, (_, index) => JSON.stringify(
      index === 2499 ? scalarLoop : index === 7499 ? gcdLoop : {
        id: `synthetic-${String(index).padStart(5, "0")}`,
        title: `Synthetic item ${index}`,
        summary: "Opaque proof item used to test bounded index retrieval.",
        features: ["synthetic"],
        declarations: [`Synthetic.declaration${index}`],
        path: `../../entries/synthetic-${String(index).padStart(5, "0")}`,
      })).join("\n");
    const scaleIndex = path.join(temporaryRoot, "tools.jsonl");
    fs.writeFileSync(scaleIndex, `${synthetic}\n`);
    const startedAt = process.hrtime.bigint();
    const search = spawnSync("rg", [
      "-n", "postTestProgram_spec|Nat\\.gcd|euclidean|remainder", scaleIndex,
    ], { encoding: "utf8" });
    scaleSearchMilliseconds = Number(process.hrtime.bigint() - startedAt) / 1000000;
    const matches = search.stdout.trim().split("\n").filter(Boolean);
    assert(search.status === 0 && matches.length === 2 &&
      matches.some((line) => line.includes('"id":"scalar-post-test-loop"')) &&
      matches.some((line) => line.includes('"id":"euclidean-gcd-loop"')) &&
      Buffer.byteLength(search.stdout) < 10000,
    "10,000-record category search did not return its bounded relevant set");
  } finally {
    fs.rmSync(temporaryRoot, { recursive: true });
  }

  process.stdout.write("LTG catalog, indexes, exclusions, and digest tests passed; " +
    `10,000-record search: ${scaleSearchMilliseconds.toFixed(3)} ms\n`);
}

main();
