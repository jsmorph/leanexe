"use strict";

const crypto = require("node:crypto");
const fs = require("node:fs");
const path = require("node:path");
const {
  collectFiles,
  exactKeys,
  imports,
  moduleFile,
  proofKitModules,
  sha256,
  writeAtomic,
} = require("./leanexegen-lib");
const {
  loadCatalog,
  renderCategoryIndex,
  leanSourceDeclarations,
} = require("./ltg-lib");

const repoRoot = path.resolve(__dirname, "..");
const proofRoot = path.join(repoRoot, "proofs", "talos", "lean");
const defaultForestPath = path.join(repoRoot, "knowledge", "forest.json");
const idPattern = /^[a-z][a-z0-9]*(?:-[a-z0-9]+)*$/;
const modulePattern = /^[A-Z][A-Za-z0-9_]*(?:\.[A-Z][A-Za-z0-9_]*)*$/;
const digestPattern = /^[0-9a-f]{64}$/;
const maturities = new Set(["experimental", "promoted"]);

function fail(message) {
  throw new Error(message);
}

function text(value, description) {
  if (typeof value !== "string" || value.trim() !== value || value.length === 0) {
    fail(`${description} must be a trimmed, nonempty string`);
  }
  return value;
}

function id(value, description) {
  text(value, description);
  if (!idPattern.test(value)) fail(`${description} must be a lowercase kebab-case identifier`);
  return value;
}

function stringArray(value, description, options = {}) {
  if (!Array.isArray(value) || (options.nonempty && value.length === 0)) {
    fail(`${description} must be ${options.nonempty ? "a nonempty" : "an"} array`);
  }
  const result = value.map((item, index) => text(item, `${description}[${index}]`));
  if (new Set(result).size !== result.length) fail(`${description} contains duplicates`);
  if (options.sorted && result.some((item, index) =>
    index > 0 && result[index - 1] > item)) {
    fail(`${description} must be sorted`);
  }
  return result;
}

function readRegularFile(file, description, encoding = null) {
  let stat;
  try {
    stat = fs.lstatSync(file);
  } catch (error) {
    fail(`${description} is unavailable: ${error.message}`);
  }
  if (!stat.isFile() || stat.isSymbolicLink()) fail(`${description} is not a regular file`);
  return fs.readFileSync(file, encoding === null ? undefined : encoding);
}

function requireRegularDirectory(directory, description) {
  let stat;
  try {
    stat = fs.lstatSync(directory);
  } catch (error) {
    fail(`${description} is unavailable: ${error.message}`);
  }
  if (!stat.isDirectory() || stat.isSymbolicLink()) {
    fail(`${description} is not a regular directory`);
  }
}

function readJson(file, description) {
  try {
    return JSON.parse(readRegularFile(file, description, "utf8"));
  } catch (error) {
    fail(`${description} is invalid: ${error.message}`);
  }
}

function packageRelative(value, description, options = {}) {
  text(value, description);
  if (path.isAbsolute(value) || value.includes("\\")) {
    fail(`${description} must be a portable relative path`);
  }
  const normalized = path.posix.normalize(value);
  if (normalized !== value || (!options.allowDot && value === ".") ||
      (!options.allowParent && (value === ".." || value.startsWith("../")))) {
    fail(`${description} must be a normalized relative path`);
  }
  return value;
}

function packagePascalName(packageId) {
  return packageId.split("-").map((part) =>
    `${part[0].toUpperCase()}${part.slice(1)}`).join("");
}

function proofKitSource(moduleName) {
  if (!proofKitModules.includes(moduleName)) return null;
  return readRegularFile(
    path.join(proofRoot, `${moduleName.replaceAll(".", path.sep)}.lean`),
    `${moduleName} proof-kit source`, "utf8");
}

function readPackageDescriptor(packageRoot) {
  requireRegularDirectory(packageRoot, "knowledge package root");
  const manifestPath = path.join(packageRoot, "knowledge-package.json");
  const value = readJson(manifestPath, `${packageRoot}/knowledge-package.json`);
  exactKeys(value, [
    "schemaVersion", "id", "version", "title", "summary", "maturity",
    "dependencies", "catalogRoot", "leanSources", "evidence",
  ], "knowledge-package.json");
  if (value.schemaVersion !== 1 || !Number.isSafeInteger(value.version) || value.version < 1) {
    fail("knowledge-package.json has an unsupported schema or version");
  }
  const packageId = id(value.id, "knowledge-package.json.id");
  const maturity = text(value.maturity, "knowledge-package.json.maturity");
  if (!maturities.has(maturity)) fail("knowledge-package.json.maturity is unsupported");
  const dependencies = stringArray(
    value.dependencies, "knowledge-package.json.dependencies", { sorted: true });
  if (dependencies.some((dependency) => !idPattern.test(dependency) || dependency === packageId)) {
    fail("knowledge-package.json.dependencies contains an invalid package identifier");
  }
  const catalogRelative = packageRelative(
    value.catalogRoot, "knowledge-package.json.catalogRoot", { allowDot: true });
  if (catalogRelative.startsWith("lean/") || catalogRelative.startsWith("evidence/")) {
    fail("knowledge-package.json.catalogRoot overlaps a reserved package directory");
  }
  const catalogRoot = path.join(packageRoot, ...catalogRelative.split("/"));
  requireRegularDirectory(catalogRoot, `${packageId} catalog root`);
  if (!Array.isArray(value.leanSources)) {
    fail("knowledge-package.json.leanSources must be an array");
  }
  const sourceModules = new Map();
  const leanSources = value.leanSources.map((record, index) => {
    exactKeys(record, ["module", "path"], `knowledge-package.json.leanSources[${index}]`);
    const moduleName = text(record.module,
      `knowledge-package.json.leanSources[${index}].module`);
    const expectedPrefix = `LeanExeGen.Knowledge.${packagePascalName(packageId)}.`;
    if (!modulePattern.test(moduleName) || !moduleName.startsWith(expectedPrefix)) {
      fail(`knowledge package source module must begin with ${expectedPrefix}`);
    }
    const relative = packageRelative(
      record.path, `knowledge-package.json.leanSources[${index}].path`);
    if (relative !== `lean/${moduleFile(moduleName)}`) {
      fail(`knowledge package source path must be lean/${moduleFile(moduleName)}`);
    }
    if (sourceModules.has(moduleName)) fail(`duplicate knowledge source module ${moduleName}`);
    const source = readRegularFile(path.join(packageRoot, ...relative.split("/")),
      `${packageId} source ${moduleName}`, "utf8");
    sourceModules.set(moduleName, source);
    return { module: moduleName, path: relative };
  });
  if (leanSources.some((record, index) =>
    index > 0 && leanSources[index - 1].module > record.module)) {
    fail("knowledge-package.json.leanSources must be sorted by module");
  }
  if (!Array.isArray(value.evidence)) fail("knowledge-package.json.evidence must be an array");
  const evidencePaths = new Set();
  const evidence = value.evidence.map((record, index) => {
    exactKeys(record, ["path", "entries"], `knowledge-package.json.evidence[${index}]`);
    const relative = packageRelative(
      record.path, `knowledge-package.json.evidence[${index}].path`);
    if (!relative.startsWith("evidence/")) {
      fail("knowledge-package.json evidence paths must begin with evidence/");
    }
    if (evidencePaths.has(relative)) fail(`duplicate knowledge evidence path ${relative}`);
    evidencePaths.add(relative);
    readRegularFile(path.join(packageRoot, ...relative.split("/")),
      `${packageId} evidence ${relative}`);
    const entries = stringArray(record.entries,
      `knowledge-package.json.evidence[${index}].entries`, { nonempty: true, sorted: true });
    if (entries.some((entryId) => !idPattern.test(entryId))) {
      fail(`knowledge-package.json evidence ${relative} has an invalid entry identifier`);
    }
    return { path: relative, entries };
  });
  if (evidence.some((record, index) =>
    index > 0 && evidence[index - 1].path > record.path)) {
    fail("knowledge-package.json.evidence must be sorted by path");
  }
  return {
    root: packageRoot,
    manifestPath,
    manifestSource: readRegularFile(manifestPath, "knowledge-package.json"),
    id: packageId,
    version: value.version,
    title: text(value.title, "knowledge-package.json.title"),
    summary: text(value.summary, "knowledge-package.json.summary"),
    maturity,
    dependencies,
    catalogRelative,
    catalogRoot,
    leanSources,
    sourceModules,
    evidence,
  };
}

function dependencyClosure(packageId, descriptors, visiting = new Set(), found = new Set()) {
  if (found.has(packageId)) return found;
  if (visiting.has(packageId)) fail(`knowledge package dependency cycle includes ${packageId}`);
  visiting.add(packageId);
  const descriptor = descriptors.get(packageId);
  for (const dependency of descriptor.dependencies) {
    if (!descriptors.has(dependency)) {
      fail(`${packageId} depends on missing knowledge package ${dependency}`);
    }
    dependencyClosure(dependency, descriptors, visiting, found);
  }
  visiting.delete(packageId);
  found.add(packageId);
  return found;
}

function validateSourceImports(descriptor, allowedModules) {
  for (const [moduleName, source] of descriptor.sourceModules) {
    for (const imported of imports(source)) {
      const dependency = imported === "CodeLib" || imported.startsWith("CodeLib.") ||
        imported.startsWith("Init.") || imported.startsWith("Std.") ||
        imported.startsWith("Mathlib.") || imported === "Interpreter" ||
        imported.startsWith("Interpreter.");
      if (!dependency && !allowedModules.has(imported)) {
        fail(`${moduleName} imports unsupported knowledge dependency ${imported}`);
      }
    }
  }
}

function validateCatalogIndexes(catalog) {
  for (const category of catalog.categories) {
    const relative = `categories/${category.id}/tools.jsonl`;
    const found = readRegularFile(path.join(catalog.root, ...relative.split("/")),
      `${catalog.root}/${relative}`, "utf8");
    if (found !== renderCategoryIndex(catalog, category.id)) {
      fail(`${catalog.root}/${relative} is stale`);
    }
  }
  const categoriesRoot = path.join(catalog.root, "categories");
  const found = fs.readdirSync(categoriesRoot, { withFileTypes: true });
  const expected = new Set(catalog.categories.map((category) => category.id));
  for (const entry of found) {
    if (!entry.isDirectory() || entry.isSymbolicLink() || !expected.has(entry.name)) {
      fail(`unexpected knowledge category path: ${entry.name}`);
    }
    const files = collectFiles(path.join(categoriesRoot, entry.name));
    if (files.length !== 1 || files[0] !== "tools.jsonl") {
      fail(`knowledge category ${entry.name} must contain only tools.jsonl`);
    }
  }
}

function validatePackageFiles(descriptor, catalog) {
  const expected = new Set(["knowledge-package.json"]);
  for (const relative of collectFiles(descriptor.catalogRoot)) {
    const catalogPath = descriptor.catalogRelative === "."
      ? relative
      : `${descriptor.catalogRelative}/${relative}`;
    expected.add(catalogPath);
  }
  for (const source of descriptor.leanSources) expected.add(source.path);
  for (const evidence of descriptor.evidence) expected.add(evidence.path);
  const found = collectFiles(descriptor.root);
  if (found.length !== expected.size || found.some((relative) => !expected.has(relative))) {
    const unexpected = found.filter((relative) => !expected.has(relative));
    const missing = [...expected].filter((relative) => !found.includes(relative));
    fail(`${descriptor.id} package file set differs from its manifest` +
      `${unexpected.length === 0 ? "" : `; unexpected: ${unexpected.join(", ")}`}` +
      `${missing.length === 0 ? "" : `; missing: ${missing.join(", ")}`}`);
  }
  const entryIds = new Set(catalog.entries.map((entry) => entry.id));
  for (const evidence of descriptor.evidence) {
    if (evidence.entries.some((entryId) => !entryIds.has(entryId))) {
      fail(`${descriptor.id} evidence ${evidence.path} refers to an unknown entry`);
    }
  }
}

function loadForest(forestPath = defaultForestPath) {
  const absoluteForest = path.resolve(forestPath);
  const value = readJson(absoluteForest, "knowledge forest");
  exactKeys(value, ["schemaVersion", "packages"], "knowledge forest");
  if (value.schemaVersion !== 1 || !Array.isArray(value.packages) ||
      value.packages.length === 0) {
    fail("knowledge forest has an unsupported schema or no packages");
  }
  const mounts = value.packages.map((record, index) => {
    exactKeys(record, ["id", "path"], `knowledge forest package ${index}`);
    return {
      id: id(record.id, `knowledge forest package ${index}.id`),
      path: packageRelative(record.path,
        `knowledge forest package ${index}.path`, { allowDot: true, allowParent: true }),
    };
  });
  if (new Set(mounts.map((mount) => mount.id)).size !== mounts.length ||
      mounts.some((mount, index) => index > 0 && mounts[index - 1].id > mount.id)) {
    fail("knowledge forest packages must have unique sorted identifiers");
  }
  const descriptors = new Map();
  for (const mount of mounts) {
    const packageRoot = path.resolve(path.dirname(absoluteForest), mount.path);
    const descriptor = readPackageDescriptor(packageRoot);
    if (descriptor.id !== mount.id) {
      fail(`knowledge forest mount ${mount.id} contains package ${descriptor.id}`);
    }
    descriptors.set(mount.id, descriptor);
  }
  const globalSourceModules = new Map();
  for (const descriptor of descriptors.values()) {
    for (const [moduleName, source] of descriptor.sourceModules) {
      if (globalSourceModules.has(moduleName)) {
        fail(`duplicate knowledge source module ${moduleName}`);
      }
      globalSourceModules.set(moduleName, source);
    }
  }
  const packages = [];
  const globalEntryIds = new Set();
  for (const mount of mounts) {
    const descriptor = descriptors.get(mount.id);
    const closure = dependencyClosure(mount.id, descriptors);
    const availableSourceModules = new Set();
    for (const dependencyId of closure) {
      for (const moduleName of descriptors.get(dependencyId).sourceModules.keys()) {
        availableSourceModules.add(moduleName);
      }
    }
    const allowedModules = new Set([...proofKitModules, ...availableSourceModules]);
    validateSourceImports(descriptor, allowedModules);
    const catalog = loadCatalog(descriptor.catalogRoot, {
      allowedModules,
      moduleSource: (moduleName) =>
        globalSourceModules.get(moduleName) ?? proofKitSource(moduleName),
    });
    validateCatalogIndexes(catalog);
    validatePackageFiles(descriptor, catalog);
    const ownDeclarations = new Set([...descriptor.sourceModules].flatMap(
      ([moduleName, source]) => leanSourceDeclarations(moduleName, source)
        .filter((declaration) => declaration.fullName !== null)
        .map((declaration) => declaration.fullName)));
    for (const entry of catalog.entries) {
      if (globalEntryIds.has(entry.id)) fail(`duplicate knowledge entry identifier ${entry.id}`);
      globalEntryIds.add(entry.id);
      for (const declaration of entry.declarations) {
        if (declaration.startsWith(`LeanExeGen.Knowledge.${packagePascalName(descriptor.id)}.`) &&
            !ownDeclarations.has(declaration)) {
          fail(`${descriptor.id}/${entry.id} refers to missing declaration ${declaration}`);
        }
      }
    }
    packages.push({ ...descriptor, catalog, dependencyClosure: closure });
  }
  return {
    schemaVersion: 1,
    path: absoluteForest,
    source: readRegularFile(absoluteForest, "knowledge forest"),
    packages,
  };
}

function entryIncluded(entry, artifactSha256) {
  return entry.exclusion === null ||
    !entry.exclusion.artifactSha256.includes(artifactSha256);
}

function taskCatalog(package_, artifactSha256) {
  const included = package_.catalog.entries.filter((entry) =>
    entryIncluded(entry, artifactSha256));
  const includedIds = new Set(included.map((entry) => entry.id));
  const files = new Map([
    ["README.md", readRegularFile(path.join(package_.catalogRoot, "README.md"),
      `${package_.id} catalog README.md`)],
    ["categories.json", readRegularFile(path.join(package_.catalogRoot, "categories.json"),
      `${package_.id} categories.json`)],
  ]);
  for (const category of package_.catalog.categories) {
    files.set(`categories/${category.id}/tools.jsonl`,
      Buffer.from(renderCategoryIndex(package_.catalog, category.id, included)));
  }
  for (const entry of included) {
    for (const relative of collectFiles(entry.root)) {
      files.set(`entries/${entry.id}/${relative}`,
        readRegularFile(path.join(entry.root, ...relative.split("/")),
          `${package_.id}/${entry.id}/${relative}`));
    }
  }
  return {
    files,
    included,
    includedIds,
    excluded: package_.catalog.entries.filter((entry) => !includedIds.has(entry.id)),
  };
}

function knowledgeDigest(files) {
  const hash = crypto.createHash("sha256");
  hash.update("leanexe-knowledge-task-v1\0");
  for (const [relative, source] of [...files].sort(([left], [right]) =>
    left.localeCompare(right))) {
    hash.update(relative);
    hash.update("\0");
    hash.update(source);
    hash.update("\0");
  }
  return hash.digest("hex");
}

function taskKnowledgeFiles(options = {}) {
  if (Object.hasOwn(options, "excludedDerivativeGroups")) {
    fail("knowledge tasks support exact artifact exclusions only");
  }
  const forest = loadForest(options.forestPath || defaultForestPath);
  const artifactSha256 = options.artifactSha256 ?? null;
  if (artifactSha256 !== null && !digestPattern.test(artifactSha256)) {
    fail("knowledge task artifactSha256 is invalid");
  }
  const selections = forest.packages.map((package_) => ({
    package_,
    catalog: taskCatalog(package_, artifactSha256),
  }));
  const referencedModules = new Set(selections.flatMap(({ catalog }) =>
    catalog.included.flatMap((entry) => entry.modules)));
  let changed = true;
  while (changed) {
    changed = false;
    for (const package_ of forest.packages) {
      for (const [moduleName, source] of package_.sourceModules) {
        if (!referencedModules.has(moduleName)) continue;
        for (const imported of imports(source)) {
          if (!referencedModules.has(imported) &&
              forest.packages.some((item) => item.sourceModules.has(imported))) {
            referencedModules.add(imported);
            changed = true;
          }
        }
      }
    }
  }
  const files = new Map();
  const taskForest = {
    schemaVersion: 1,
    packages: forest.packages.map((package_) => ({
      id: package_.id,
      path: `packages/${package_.id}`,
    })),
  };
  files.set("forest.json", Buffer.from(`${JSON.stringify(taskForest, null, 2)}\n`));
  const leanSources = new Map();
  const packageRecords = [];
  for (const { package_, catalog } of selections) {
    const packageFiles = new Map();
    for (const [relative, source] of catalog.files) {
      packageFiles.set(`catalog/${relative}`, source);
    }
    const includedModules = [];
    for (const sourceRecord of package_.leanSources) {
      if (!referencedModules.has(sourceRecord.module)) continue;
      const source = package_.sourceModules.get(sourceRecord.module);
      packageFiles.set(sourceRecord.path, Buffer.from(source));
      leanSources.set(sourceRecord.module, source);
      includedModules.push(sourceRecord.module);
    }
    const includedEvidence = [];
    for (const evidence of package_.evidence) {
      if (!evidence.entries.some((entryId) => catalog.includedIds.has(entryId))) continue;
      packageFiles.set(evidence.path,
        readRegularFile(path.join(package_.root, ...evidence.path.split("/")),
          `${package_.id} ${evidence.path}`));
      includedEvidence.push({
        path: evidence.path,
        entries: evidence.entries.filter((entryId) => catalog.includedIds.has(entryId)),
      });
    }
    const taskManifest = {
      schemaVersion: 1,
      id: package_.id,
      version: package_.version,
      title: package_.title,
      summary: package_.summary,
      maturity: package_.maturity,
      dependencies: package_.dependencies,
      catalogRoot: "catalog",
      leanSources: package_.leanSources.filter((source) =>
        referencedModules.has(source.module)),
      evidence: includedEvidence,
    };
    packageFiles.set("knowledge-package.json",
      Buffer.from(`${JSON.stringify(taskManifest, null, 2)}\n`));
    for (const [relative, source] of packageFiles) {
      files.set(`packages/${package_.id}/${relative}`, source);
    }
    packageRecords.push({
      id: package_.id,
      version: package_.version,
      maturity: package_.maturity,
      dependencies: package_.dependencies,
      entries: catalog.included.length,
      entryIds: catalog.included.map((entry) => entry.id),
      excludedEntries: catalog.excluded.length,
      excludedEntryIds: catalog.excluded.map((entry) => entry.id),
      leanModules: includedModules,
      sha256: knowledgeDigest(packageFiles),
    });
  }
  const totalEntries = packageRecords.reduce((total, package_) => total + package_.entries, 0);
  const totalExcludedEntries = packageRecords.reduce(
    (total, package_) => total + package_.excludedEntries, 0);
  return {
    files,
    leanSources,
    allowedModules: new Set([...proofKitModules, ...leanSources.keys()]),
    manifest: {
      schemaVersion: 2,
      artifactSha256,
      packages: packageRecords,
      entries: totalEntries,
      excludedEntries: totalExcludedEntries,
      sha256: knowledgeDigest(files),
    },
  };
}

function forestMetrics(forestPath = defaultForestPath) {
  const forest = loadForest(forestPath);
  const complete = taskKnowledgeFiles({ forestPath });
  return {
    schemaVersion: 1,
    packages: forest.packages.length,
    promotedPackages: forest.packages.filter((package_) =>
      package_.maturity === "promoted").length,
    experimentalPackages: forest.packages.filter((package_) =>
      package_.maturity === "experimental").length,
    categories: forest.packages.reduce(
      (total, package_) => total + package_.catalog.categories.length, 0),
    entries: forest.packages.reduce(
      (total, package_) => total + package_.catalog.entries.length, 0),
    leanModules: forest.packages.reduce(
      (total, package_) => total + package_.sourceModules.size, 0),
    evidenceFiles: forest.packages.reduce(
      (total, package_) => total + package_.evidence.length, 0),
    taskFiles: complete.files.size,
    taskBytes: [...complete.files.values()].reduce(
      (total, source) => total + Buffer.byteLength(source), 0),
    taskSha256: complete.manifest.sha256,
  };
}

function createKnowledgePackage(outputRoot, definition) {
  if (fs.existsSync(outputRoot)) fail(`${outputRoot} exists`);
  fs.mkdirSync(path.dirname(outputRoot), { recursive: true });
  const staged = path.join(path.dirname(outputRoot),
    `.${path.basename(outputRoot)}.${process.pid}-${Date.now()}`);
  try {
    fs.mkdirSync(staged);
    const manifest = structuredClone(definition.manifest);
    const sourceRecords = [...definition.leanSources].sort(([left], [right]) =>
      left.localeCompare(right)).map(([moduleName, source]) => {
      const relative = `lean/${moduleFile(moduleName)}`;
      writeAtomic(path.join(staged, ...relative.split("/")), Buffer.from(source));
      return { module: moduleName, path: relative };
    });
    const evidenceRecords = [...definition.evidence].sort(([left], [right]) =>
      left.localeCompare(right)).map(([relative, record]) => {
      writeAtomic(path.join(staged, ...relative.split("/")), Buffer.from(record.source));
      return { path: relative, entries: [...record.entries].sort() };
    });
    manifest.leanSources = sourceRecords;
    manifest.evidence = evidenceRecords;
    writeAtomic(path.join(staged, "knowledge-package.json"),
      Buffer.from(`${JSON.stringify(manifest, null, 2)}\n`));
    const catalogRoot = path.join(staged, ...manifest.catalogRoot.split("/"));
    writeAtomic(path.join(catalogRoot, "README.md"), Buffer.from(definition.catalogReadme));
    writeAtomic(path.join(catalogRoot, "categories.json"),
      Buffer.from(`${JSON.stringify(definition.categories, null, 2)}\n`));
    for (const entry of definition.entries) {
      const entryRoot = path.join(catalogRoot, "entries", entry.metadata.id);
      writeAtomic(path.join(entryRoot, "entry.json"),
        Buffer.from(`${JSON.stringify(entry.metadata, null, 2)}\n`));
      writeAtomic(path.join(entryRoot, "README.md"), Buffer.from(entry.readme));
    }
    const ownModules = new Map(definition.leanSources);
    const catalog = loadCatalog(catalogRoot, {
      allowedModules: new Set([...proofKitModules, ...ownModules.keys()]),
      moduleSource: (moduleName) => ownModules.get(moduleName) ?? proofKitSource(moduleName),
    });
    for (const category of catalog.categories) {
      writeAtomic(path.join(catalogRoot, "categories", category.id, "tools.jsonl"),
        Buffer.from(renderCategoryIndex(catalog, category.id)));
    }
    const validationForestPath = `${staged}.forest.json`;
    const dependencyForest = definition.dependencyForestPath === null
      ? { packages: [] }
      : loadForest(definition.dependencyForestPath || defaultForestPath);
    const directDependencyIds = new Set(manifest.dependencies);
    const directDependencies = dependencyForest.packages.filter((package_) =>
      directDependencyIds.has(package_.id));
    if (directDependencies.length !== directDependencyIds.size) {
      fail(`${manifest.id} dependencies are absent from its validation forest`);
    }
    const dependencyIds = new Set(directDependencies.flatMap((package_) =>
      [...package_.dependencyClosure]));
    const mounts = dependencyForest.packages.filter((package_) =>
      dependencyIds.has(package_.id)).map((package_) => ({
      id: package_.id,
      path: path.relative(path.dirname(validationForestPath), package_.root)
        .split(path.sep).join("/"),
    }));
    mounts.push({
      id: manifest.id,
      path: path.relative(path.dirname(validationForestPath), staged).split(path.sep).join("/"),
    });
    mounts.sort((left, right) => left.id.localeCompare(right.id));
    writeAtomic(validationForestPath, Buffer.from(`${JSON.stringify({
      schemaVersion: 1,
      packages: mounts,
    }, null, 2)}\n`));
    loadForest(validationForestPath);
    fs.rmSync(validationForestPath);
    fs.renameSync(staged, outputRoot);
  } catch (error) {
    try {
      fs.rmSync(staged, { recursive: true, force: true });
      fs.rmSync(`${staged}.forest.json`, { force: true });
    } catch (cleanupError) {
      throw new AggregateError([error, cleanupError], `could not create ${outputRoot}`);
    }
    throw error;
  }
  return readPackageDescriptor(outputRoot);
}

module.exports = {
  createKnowledgePackage,
  defaultForestPath,
  forestMetrics,
  knowledgeDigest,
  loadForest,
  packagePascalName,
  readPackageDescriptor,
  taskKnowledgeFiles,
};
