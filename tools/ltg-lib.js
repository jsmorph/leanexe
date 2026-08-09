"use strict";

const crypto = require("node:crypto");
const fs = require("node:fs");
const path = require("node:path");
const {
  collectFiles,
  proofKitModules,
  writeAtomic,
} = require("./leanexegen-lib");

const repoRoot = path.resolve(__dirname, "..");
const defaultRoot = path.join(repoRoot, "ltg");
const leanCheckPath = path.join(
  repoRoot, "proofs", "talos", "lean", "Project", "ProofKit", "LTGCheck.lean");
const idPattern = /^[a-z][a-z0-9]*(?:-[a-z0-9]+)*$/;
const digestPattern = /^[0-9a-f]{64}$/;
const roles = new Set([
  "annotation-support",
  "checked-proof-asset",
  "guidance",
  "proof-generation-mechanism",
  "worked-example",
]);
const scopes = new Set([
  "benchmark-local",
  "compiler-runtime-motif",
  "generic-semantics",
]);
const evidenceStatuses = new Set(["promoted", "provisional", "rejected"]);

function fail(message) {
  throw new Error(message);
}

function exactKeys(value, keys, description) {
  if (value === null || typeof value !== "object" || Array.isArray(value)) {
    fail(`${description} must be an object`);
  }
  const found = Object.keys(value).sort();
  const expected = [...keys].sort();
  if (found.length !== expected.length ||
      found.some((key, index) => key !== expected[index])) {
    fail(`${description} must contain exactly: ${expected.join(", ")}`);
  }
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
  if (options.sorted && result.some((item, index) => index > 0 && result[index - 1] > item)) {
    fail(`${description} must be sorted`);
  }
  return result;
}

function readRegularFile(file, description) {
  const stat = fs.lstatSync(file);
  if (!stat.isFile() || stat.isSymbolicLink()) fail(`${description} is not a regular file`);
  return fs.readFileSync(file, "utf8");
}

function readJson(file, description) {
  try {
    return JSON.parse(readRegularFile(file, description));
  } catch (error) {
    fail(`${description} is invalid: ${error.message}`);
  }
}

function validateCategories(root) {
  const document = readJson(path.join(root, "categories.json"), "categories.json");
  exactKeys(document, ["schemaVersion", "categories"], "categories.json");
  if (document.schemaVersion !== 1 || !Array.isArray(document.categories) ||
      document.categories.length === 0) {
    fail("categories.json has an unsupported schema or no categories");
  }
  const result = [];
  for (const [index, category] of document.categories.entries()) {
    exactKeys(category, ["id", "title", "summary"], `categories[${index}]`);
    result.push({
      id: id(category.id, `categories[${index}].id`),
      title: text(category.title, `categories[${index}].title`),
      summary: text(category.summary, `categories[${index}].summary`),
    });
  }
  if (new Set(result.map((category) => category.id)).size !== result.length) {
    fail("categories.json contains duplicate category identifiers");
  }
  if (result.some((category, index) => index > 0 && result[index - 1].id > category.id)) {
    fail("categories.json categories must be sorted by id");
  }
  return result;
}

function validateExclusion(value, description) {
  if (value === null) return null;
  exactKeys(value, ["artifactSha256", "derivativeGroup"], description);
  const artifactSha256 = stringArray(
    value.artifactSha256, `${description}.artifactSha256`, { nonempty: true, sorted: true });
  if (artifactSha256.some((digest) => !digestPattern.test(digest))) {
    fail(`${description}.artifactSha256 contains an invalid digest`);
  }
  return {
    artifactSha256,
    derivativeGroup: id(value.derivativeGroup, `${description}.derivativeGroup`),
  };
}

function validateEntry(root, directory, categoryIds) {
  id(directory, `entry directory ${directory}`);
  const entryRoot = path.join(root, "entries", directory);
  const value = readJson(path.join(entryRoot, "entry.json"), `${directory}/entry.json`);
  exactKeys(value, [
    "schemaVersion", "id", "title", "summary", "roles", "categories", "scope",
    "evidenceStatus", "features", "annotationKinds", "modules", "declarations",
    "premises", "result", "consumers", "relatedEntries", "exclusion",
  ], `${directory}/entry.json`);
  if (value.schemaVersion !== 1) fail(`${directory}/entry.json has an unsupported schema`);
  const entryId = id(value.id, `${directory}.id`);
  if (entryId !== directory) fail(`${directory}/entry.json id differs from its directory`);
  const entryRoles = stringArray(value.roles, `${directory}.roles`, {
    nonempty: true, sorted: true,
  });
  if (entryRoles.some((role) => !roles.has(role))) fail(`${directory}.roles is unsupported`);
  const categories = stringArray(value.categories, `${directory}.categories`, {
    nonempty: true, sorted: true,
  });
  if (categories.some((category) => !categoryIds.has(category))) {
    fail(`${directory}.categories refers to an unknown category`);
  }
  const scope = text(value.scope, `${directory}.scope`);
  if (!scopes.has(scope)) fail(`${directory}.scope is unsupported`);
  const evidenceStatus = text(value.evidenceStatus, `${directory}.evidenceStatus`);
  if (!evidenceStatuses.has(evidenceStatus)) {
    fail(`${directory}.evidenceStatus is unsupported`);
  }
  const modules = stringArray(value.modules, `${directory}.modules`, {
    nonempty: true, sorted: true,
  });
  if (modules.some((moduleName) => !proofKitModules.includes(moduleName))) {
    fail(`${directory}.modules refers to a module outside the checked proof kit`);
  }
  const readme = readRegularFile(path.join(entryRoot, "README.md"), `${directory}/README.md`);
  if (readme.trim().length === 0) fail(`${directory}/README.md is empty`);
  collectFiles(entryRoot);
  return {
    schemaVersion: 1,
    id: entryId,
    title: text(value.title, `${directory}.title`),
    summary: text(value.summary, `${directory}.summary`),
    roles: entryRoles,
    categories,
    scope,
    evidenceStatus,
    features: stringArray(value.features, `${directory}.features`, {
      nonempty: true, sorted: true,
    }),
    annotationKinds: stringArray(value.annotationKinds, `${directory}.annotationKinds`, {
      sorted: true,
    }),
    modules,
    declarations: stringArray(value.declarations, `${directory}.declarations`, {
      nonempty: true, sorted: true,
    }),
    premises: stringArray(value.premises, `${directory}.premises`, { nonempty: true }),
    result: text(value.result, `${directory}.result`),
    consumers: stringArray(value.consumers, `${directory}.consumers`, { sorted: true }),
    relatedEntries: stringArray(value.relatedEntries, `${directory}.relatedEntries`, {
      sorted: true,
    }),
    exclusion: validateExclusion(value.exclusion, `${directory}.exclusion`),
    root: entryRoot,
  };
}

function loadCatalog(root = defaultRoot) {
  readRegularFile(path.join(root, "README.md"), "LTG README.md");
  const categories = validateCategories(root);
  const categoryIds = new Set(categories.map((category) => category.id));
  const entriesRoot = path.join(root, "entries");
  const directories = fs.readdirSync(entriesRoot, { withFileTypes: true });
  if (directories.some((entry) => !entry.isDirectory() || entry.isSymbolicLink())) {
    fail("LTG entries must contain only ordinary directories");
  }
  const names = directories.map((entry) => entry.name).sort();
  const entries = names.map((name) => validateEntry(root, name, categoryIds));
  const entryIds = new Set(entries.map((entry) => entry.id));
  for (const entry of entries) {
    for (const related of entry.relatedEntries) {
      if (!entryIds.has(related)) fail(`${entry.id}.relatedEntries refers to unknown ${related}`);
      if (related === entry.id) fail(`${entry.id}.relatedEntries refers to itself`);
    }
  }
  return { root, categories, entries };
}

function indexRecord(entry) {
  const searchTerms = [...new Set([
    entry.id.replaceAll("-", "_"),
    ...entry.features.map((feature) => feature.replaceAll("-", "_")),
    ...entry.annotationKinds.map((kind) => kind.replaceAll("-", "_")),
    ...entry.modules,
    ...entry.declarations,
  ])].sort();
  return {
    id: entry.id,
    title: entry.title,
    summary: entry.summary,
    roles: entry.roles,
    scope: entry.scope,
    evidenceStatus: entry.evidenceStatus,
    features: entry.features,
    annotationKinds: entry.annotationKinds,
    modules: entry.modules,
    declarations: entry.declarations,
    searchTerms,
    path: `../../entries/${entry.id}`,
  };
}

function renderCategoryIndex(catalog, categoryId, includedEntries = catalog.entries) {
  const lines = includedEntries
    .filter((entry) => entry.categories.includes(categoryId))
    .sort((left, right) => left.id.localeCompare(right.id))
    .map((entry) => JSON.stringify(indexRecord(entry)));
  return `${lines.join("\n")}\n`;
}

function renderLeanCheck(catalog) {
  const modules = [...new Set(catalog.entries.flatMap((entry) => entry.modules))].sort();
  const declarations = [...new Set(
    catalog.entries.flatMap((entry) => entry.declarations))].sort();
  return `${modules.map((moduleName) => `import ${moduleName}`).join("\n")}\n\n` +
    `${declarations.map((declaration) => `#check ${declaration}`).join("\n")}\n`;
}

function expectedGeneratedFiles(catalog) {
  const result = new Map(catalog.categories.map((category) => [
    path.join(catalog.root, "categories", category.id, "tools.jsonl"),
    renderCategoryIndex(catalog, category.id),
  ]));
  result.set(leanCheckPath, renderLeanCheck(catalog));
  return result;
}

function rebuildCatalog(root = defaultRoot) {
  const catalog = loadCatalog(root);
  for (const [file, source] of expectedGeneratedFiles(catalog)) {
    writeAtomic(file, Buffer.from(source));
  }
  return catalog;
}

function checkCatalog(root = defaultRoot) {
  const catalog = loadCatalog(root);
  const expected = expectedGeneratedFiles(catalog);
  for (const [file, source] of expected) {
    let found;
    try {
      found = readRegularFile(file, path.relative(repoRoot, file));
    } catch (error) {
      fail(`${path.relative(repoRoot, file)} is missing or invalid: ${error.message}`);
    }
    if (found !== source) fail(`${path.relative(repoRoot, file)} is stale; run tools/ltg rebuild`);
  }
  const categoriesRoot = path.join(root, "categories");
  const foundCategories = fs.readdirSync(categoriesRoot, { withFileTypes: true });
  const expectedCategoryIds = new Set(catalog.categories.map((category) => category.id));
  for (const entry of foundCategories) {
    if (!entry.isDirectory() || entry.isSymbolicLink() || !expectedCategoryIds.has(entry.name)) {
      fail(`unexpected LTG category path: categories/${entry.name}`);
    }
    const files = collectFiles(path.join(categoriesRoot, entry.name));
    if (files.length !== 1 || files[0] !== "tools.jsonl") {
      fail(`categories/${entry.name} must contain only tools.jsonl`);
    }
  }
  return catalog;
}

function taskCatalogFiles(options = {}) {
  const catalog = loadCatalog(options.root || defaultRoot);
  const excludedArtifact = options.artifactSha256 || null;
  if (excludedArtifact !== null && !digestPattern.test(excludedArtifact)) {
    fail("task LTG artifactSha256 is invalid");
  }
  const excludedDerivativeGroupList = options.excludedDerivativeGroups || [];
  if (!Array.isArray(excludedDerivativeGroupList) ||
      excludedDerivativeGroupList.some((group) =>
        typeof group !== "string" || !idPattern.test(group)) ||
      new Set(excludedDerivativeGroupList).size !== excludedDerivativeGroupList.length) {
    fail("task LTG excludedDerivativeGroups must contain unique identifiers");
  }
  const excludedDerivativeGroups = new Set(excludedDerivativeGroupList);
  const includedEntries = catalog.entries.filter((entry) => entry.exclusion === null ||
    (!entry.exclusion.artifactSha256.includes(excludedArtifact) &&
      !excludedDerivativeGroups.has(entry.exclusion.derivativeGroup)));
  const files = new Map([
    ["README.md", readRegularFile(path.join(catalog.root, "README.md"), "LTG README.md")],
    ["categories.json", readRegularFile(
      path.join(catalog.root, "categories.json"), "LTG categories.json")],
  ]);
  for (const category of catalog.categories) {
    files.set(
      `categories/${category.id}/tools.jsonl`,
      renderCategoryIndex(catalog, category.id, includedEntries));
  }
  for (const entry of includedEntries) {
    for (const relative of collectFiles(entry.root)) {
      files.set(`entries/${entry.id}/${relative}`, fs.readFileSync(path.join(entry.root, relative)));
    }
  }
  return {
    files,
    entryIds: includedEntries.map((entry) => entry.id),
    excludedEntryIds: catalog.entries
      .filter((entry) => !includedEntries.includes(entry))
      .map((entry) => entry.id),
  };
}

function catalogDigest(files) {
  const hash = crypto.createHash("sha256");
  hash.update("leanexe-ltg-task-v1\0");
  for (const [relative, source] of [...files].sort(([left], [right]) =>
    left.localeCompare(right))) {
    hash.update(relative);
    hash.update("\0");
    hash.update(source);
    hash.update("\0");
  }
  return hash.digest("hex");
}

module.exports = {
  catalogDigest,
  checkCatalog,
  defaultRoot,
  loadCatalog,
  rebuildCatalog,
  renderCategoryIndex,
  renderLeanCheck,
  taskCatalogFiles,
};
