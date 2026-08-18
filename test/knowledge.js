#!/usr/bin/env node
"use strict";

const assert = require("node:assert");
const fs = require("node:fs");
const path = require("node:path");
const {
  createKnowledgePackage,
  knowledgeDigest,
  loadForest,
  taskKnowledgeFiles,
} = require("../tools/knowledge-lib");
const { validateKnowledgeTask } = require("../tools/leanexegen-lib");
const { promoteKnowledge } = require("../tools/leanexegen");
const { makeTemporaryDirectory } = require("../tools/temp-directory");

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

function main() {
  const root = makeTemporaryDirectory("knowledge-test-");
  try {
    const packageRoot = path.join(root, "package");
    const packageId = "test-package";
    const moduleName = "LeanExeGen.Knowledge.TestPackage.Proposed";
    const artifactSha256 = "1".repeat(64);
    const entryId = "test-memory-frame";
    const source = `import Project.ProofKit.Control\n\n` +
      `namespace ${moduleName}\n\n` +
      `theorem true_intro : True := by trivial\n\n` +
      `end ${moduleName}\n`;
    createKnowledgePackage(packageRoot, {
      manifest: {
        schemaVersion: 1,
        id: packageId,
        version: 1,
        title: "Test package",
        summary: "Checked test knowledge.",
        maturity: "experimental",
        dependencies: [],
        catalogRoot: "catalog",
        leanSources: [],
        evidence: [],
      },
      catalogReadme: "# Test knowledge\n\nThis catalog contains one checked test entry.  The entry has one package-local Lean theorem.  Its evidence file identifies the source test.\n",
      categories: {
        schemaVersion: 1,
        categories: [{
          id: "proof-construction",
          title: "Proof construction",
          summary: "Checked proof construction support.",
        }],
      },
      entries: [{
        metadata: {
          schemaVersion: 4,
          id: entryId,
          title: "Test memory frame",
          summary: "Checks package-local declarations and filtered evidence.",
          roles: ["checked-proof-asset", "guidance"],
          categories: ["proof-construction"],
          scope: "generic-semantics",
          evidenceStatus: "provisional",
          features: ["frame"],
          annotationKinds: [],
          modules: [moduleName],
          declarations: [`${moduleName}.true_intro`],
          premises: ["True"],
          result: "True",
          consumers: [],
          relatedEntries: [],
          exclusion: {
            artifactSha256: [artifactSha256],
          },
          tactics: [],
        },
        readme: "# Test memory frame\n\nThe entry exposes one package-local theorem.  The package task includes its source when the entry is selected.  Exact-artifact exclusion removes the entry, source, and evidence together.\n",
      }],
      leanSources: new Map([[moduleName, source]]),
      evidence: new Map([["evidence/result.md", {
        source: "The checked test produced one package-local theorem.\n",
        entries: [entryId],
      }]]),
      dependencyForestPath: null,
    });
    const forestPath = path.join(root, "forest.json");
    fs.writeFileSync(forestPath, `${JSON.stringify({
      schemaVersion: 1,
      packages: [{ id: packageId, path: "package" }],
    }, null, 2)}\n`);
    const forest = loadForest(forestPath);
    assert(forest.packages.length === 1 &&
      forest.packages[0].catalog.entries[0].id === entryId,
    "knowledge forest omitted its package or entry");
    const complete = taskKnowledgeFiles({ forestPath });
    assert(complete.manifest.schemaVersion === 2 &&
      !("derivativeGroups" in complete.manifest) &&
      complete.manifest.entries === 1 &&
      complete.leanSources.get(moduleName) === source &&
      complete.files.has(`packages/${packageId}/evidence/result.md`) &&
      complete.files.has(`packages/${packageId}/lean/${moduleName.replaceAll(".", "/")}.lean`),
    "knowledge task omitted selected source or evidence");
    const checked = validateKnowledgeTask(
      complete.manifest, complete.files, complete.manifest.artifactSha256);
    assert(checked.leanSources.get(moduleName) === source,
      "archived knowledge validation omitted its Lean source");
    const legacyManifest = {
      ...structuredClone(complete.manifest),
      schemaVersion: 1,
      derivativeGroups: [],
    };
    assert(validateKnowledgeTask(
      legacyManifest, complete.files, complete.manifest.artifactSha256)
      .leanSources.get(moduleName) === source,
    "knowledge validation rejected a schema-1 archive");
    const excluded = taskKnowledgeFiles({ forestPath, artifactSha256 });
    assert(excluded.manifest.entries === 0 && excluded.manifest.excludedEntries === 1 &&
      excluded.leanSources.size === 0 &&
      !excluded.files.has(`packages/${packageId}/evidence/result.md`),
    "knowledge task retained excluded entry source or evidence");
    expectFailure(() => taskKnowledgeFiles({
      forestPath,
      excludedDerivativeGroups: ["test-artifact"],
    }), /exact artifact exclusions only/);
    const changed = structuredClone(complete.manifest);
    changed.sha256 = "0".repeat(64);
    expectFailure(() => validateKnowledgeTask(
      changed, complete.files, complete.manifest.artifactSha256), /digest differs/);

    const dependencyRoot = path.join(root, "dependency-package");
    const dependencyModule = "LeanExeGen.Knowledge.DependencyPackage.Base";
    createKnowledgePackage(dependencyRoot, {
      manifest: {
        schemaVersion: 1,
        id: "dependency-package",
        version: 1,
        title: "Dependency package",
        summary: "Supplies one checked dependency theorem.",
        maturity: "promoted",
        dependencies: [],
        catalogRoot: "catalog",
        leanSources: [],
        evidence: [],
      },
      catalogReadme: "# Dependency knowledge\n\nThis package supplies one checked dependency theorem.  A second package imports the theorem through an explicit package dependency.  The archive test removes that dependency and requires validation to fail.\n",
      categories: {
        schemaVersion: 1,
        categories: [{
          id: "proof-construction",
          title: "Proof construction",
          summary: "Checked proof construction support.",
        }],
      },
      entries: [{
        metadata: {
          schemaVersion: 3,
          id: "dependency-true",
          title: "Dependency truth",
          summary: "Supplies a theorem consumed by another knowledge package.",
          roles: ["checked-proof-asset"],
          categories: ["proof-construction"],
          scope: "generic-semantics",
          evidenceStatus: "promoted",
          features: ["dependency-test"],
          annotationKinds: [],
          modules: [dependencyModule],
          declarations: [`${dependencyModule}.dependency_true`],
          premises: ["True"],
          result: "True",
          consumers: [],
          relatedEntries: [],
          exclusion: null,
          tactics: [],
        },
        readme: "# Dependency truth\n\nThe theorem provides a checked package dependency for the archive validator test.  Its consumer must declare the package dependency before importing this module.  Removing that declaration invalidates the archived forest.\n",
      }],
      leanSources: new Map([[dependencyModule,
        `namespace ${dependencyModule}\n\ntheorem dependency_true : True := by trivial\n\n` +
        `end ${dependencyModule}\n`]]),
      evidence: new Map(),
      dependencyForestPath: null,
    });
    const dependencyForestPath = path.join(root, "dependency-forest.json");
    fs.writeFileSync(dependencyForestPath, `${JSON.stringify({
      schemaVersion: 1,
      packages: [{ id: "dependency-package", path: "dependency-package" }],
    }, null, 2)}\n`);
    const consumerRoot = path.join(root, "consumer-package");
    const consumerModule = "LeanExeGen.Knowledge.ConsumerPackage.Use";
    createKnowledgePackage(consumerRoot, {
      manifest: {
        schemaVersion: 1,
        id: "consumer-package",
        version: 1,
        title: "Consumer package",
        summary: "Imports one checked theorem from its declared dependency.",
        maturity: "experimental",
        dependencies: ["dependency-package"],
        catalogRoot: "catalog",
        leanSources: [],
        evidence: [],
      },
      catalogReadme: "# Consumer knowledge\n\nThis package imports one theorem from its declared package dependency.  The forest validator resolves that dependency before admitting the import.  The task archive preserves the same dependency edge.\n",
      categories: {
        schemaVersion: 1,
        categories: [{
          id: "proof-construction",
          title: "Proof construction",
          summary: "Checked proof construction support.",
        }],
      },
      entries: [{
        metadata: {
          schemaVersion: 3,
          id: "consumer-true",
          title: "Consumer truth",
          summary: "Uses a theorem from an explicitly declared knowledge package.",
          roles: ["checked-proof-asset"],
          categories: ["proof-construction"],
          scope: "generic-semantics",
          evidenceStatus: "promoted",
          features: ["dependency-test"],
          annotationKinds: [],
          modules: [consumerModule],
          declarations: [`${consumerModule}.consumer_true`],
          premises: ["True"],
          result: "True",
          consumers: [],
          relatedEntries: [],
          exclusion: null,
          tactics: [],
        },
        readme: "# Consumer truth\n\nThe theorem uses a declaration from another selected package.  Its package manifest records that dependency.  Both live and archived forest validation enforce the edge.\n",
      }],
      leanSources: new Map([[consumerModule,
        `import ${dependencyModule}\n\nnamespace ${consumerModule}\n\n` +
        `theorem consumer_true : True := ${dependencyModule}.dependency_true\n\n` +
        `end ${consumerModule}\n`]]),
      evidence: new Map(),
      dependencyForestPath,
    });
    const consumerForestPath = path.join(root, "consumer-forest.json");
    fs.writeFileSync(consumerForestPath, `${JSON.stringify({
      schemaVersion: 1,
      packages: [
        { id: "consumer-package", path: "consumer-package" },
        { id: "dependency-package", path: "dependency-package" },
      ],
    }, null, 2)}\n`);
    const transitiveRoot = path.join(root, "transitive-package");
    const transitiveModule = "LeanExeGen.Knowledge.TransitivePackage.Use";
    const transitiveDescriptor = createKnowledgePackage(transitiveRoot, {
      manifest: {
        schemaVersion: 1,
        id: "transitive-package",
        version: 1,
        title: "Transitive package",
        summary: "Imports a theorem whose package has its own dependency.",
        maturity: "experimental",
        dependencies: ["consumer-package"],
        catalogRoot: "catalog",
        leanSources: [],
        evidence: [],
      },
      catalogReadme: "# Transitive knowledge\n\nThis package imports a theorem from its direct dependency.  Package validation also mounts that dependency's transitive closure.\n",
      categories: {
        schemaVersion: 1,
        categories: [{
          id: "proof-construction",
          title: "Proof construction",
          summary: "Checked proof construction support.",
        }],
      },
      entries: [{
        metadata: {
          schemaVersion: 3,
          id: "transitive-true",
          title: "Transitive truth",
          summary: "Uses a theorem from a package with its own dependency.",
          roles: ["checked-proof-asset"],
          categories: ["proof-construction"],
          scope: "generic-semantics",
          evidenceStatus: "promoted",
          features: ["dependency-test"],
          annotationKinds: [],
          modules: [transitiveModule],
          declarations: [`${transitiveModule}.transitive_true`],
          premises: ["True"],
          result: "True",
          consumers: [],
          relatedEntries: [],
          exclusion: null,
          tactics: [],
        },
        readme: "# Transitive truth\n\nThe theorem uses a declaration from its direct dependency.  That package uses a declaration from its own dependency.\n",
      }],
      leanSources: new Map([[transitiveModule,
        `import ${consumerModule}\n\nnamespace ${transitiveModule}\n\n` +
        `theorem transitive_true : True := ${consumerModule}.consumer_true\n\n` +
        `end ${transitiveModule}\n`]]),
      evidence: new Map(),
      dependencyForestPath: consumerForestPath,
    });
    assert(JSON.stringify(transitiveDescriptor.dependencies) ===
      JSON.stringify(["consumer-package"]),
    "package creation changed direct dependencies to their transitive closure");
    const combinedForestPath = path.join(root, "combined-forest.json");
    fs.writeFileSync(combinedForestPath, `${JSON.stringify({
      schemaVersion: 1,
      packages: [
        { id: "consumer-package", path: "consumer-package" },
        { id: "dependency-package", path: "dependency-package" },
        { id: "transitive-package", path: "transitive-package" },
      ],
    }, null, 2)}\n`);
    const dependencyTask = taskKnowledgeFiles({ forestPath: combinedForestPath });
    validateKnowledgeTask(
      dependencyTask.manifest, dependencyTask.files, dependencyTask.manifest.artifactSha256);
    const dependencyTamperedFiles = new Map(dependencyTask.files);
    const consumerManifestPath =
      "packages/consumer-package/knowledge-package.json";
    const consumerManifest = JSON.parse(
      dependencyTamperedFiles.get(consumerManifestPath).toString("utf8"));
    consumerManifest.dependencies = [];
    dependencyTamperedFiles.set(consumerManifestPath,
      Buffer.from(`${JSON.stringify(consumerManifest, null, 2)}\n`));
    const dependencyTamperedManifest = structuredClone(dependencyTask.manifest);
    const consumerRecord = dependencyTamperedManifest.packages.find(
      (package_) => package_.id === "consumer-package");
    consumerRecord.dependencies = [];
    consumerRecord.sha256 = knowledgeDigest(new Map([...dependencyTamperedFiles]
      .filter(([relative]) => relative.startsWith("packages/consumer-package/"))
      .map(([relative, source]) => [
        relative.slice("packages/consumer-package/".length), source,
      ])));
    dependencyTamperedManifest.sha256 = knowledgeDigest(dependencyTamperedFiles);
    expectFailure(() => validateKnowledgeTask(
      dependencyTamperedManifest, dependencyTamperedFiles,
      dependencyTamperedManifest.artifactSha256), /unsupported archived knowledge dependency/);
    if (process.argv.includes("--lean")) {
      const dependentPromotedRoot = path.join(root, "dependent-promoted");
      promoteKnowledge({
        mode: "promote",
        forestPath: dependencyForestPath,
        inputPath: consumerRoot,
        outputPath: dependentPromotedRoot,
      });
      const dependentPromoted = loadForest(
        path.join(dependentPromotedRoot, "forest.json"));
      assert(dependentPromoted.packages.find((item) =>
        item.id === "consumer-package")?.maturity === "promoted" &&
        dependentPromoted.packages.every((item) =>
          item.root.startsWith(path.join(dependentPromotedRoot, "packages") + path.sep)),
      "Lean-checked dependent promotion did not produce a self-contained snapshot");
      const promotedRoot = path.join(root, "promoted");
      promoteKnowledge({
        mode: "promote",
        forestPath: path.join(__dirname, "..", "knowledge", "forest.json"),
        inputPath: packageRoot,
        outputPath: promotedRoot,
      });
      const promoted = loadForest(path.join(promotedRoot, "forest.json"));
      const package_ = promoted.packages.find((item) => item.id === packageId);
      assert(package_ !== undefined && package_.maturity === "promoted" &&
        package_.version === 2,
      "Lean-checked promotion omitted the candidate package version");
    }
  } finally {
    fs.rmSync(root, { recursive: true });
  }
  process.stdout.write("Knowledge package, forest, filtering, and archive tests passed\n");
}

main();
