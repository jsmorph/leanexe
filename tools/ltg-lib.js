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
const leanDeclarationKinds = [
  "abbrev", "class", "def", "elab", "inductive", "instance", "lemma", "macro",
  "opaque", "structure", "theorem",
];

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

function counts(values, domain = []) {
  const frequencies = new Map([...domain].map((value) => [value, 0]));
  for (const value of values) {
    frequencies.set(value, (frequencies.get(value) || 0) + 1);
  }
  const result = {};
  for (const value of [...frequencies.keys()].sort()) {
    result[value] = frequencies.get(value);
  }
  return result;
}

function sumByteLengths(files) {
  return [...files.values()].reduce(
    (total, source) => total + Buffer.byteLength(source), 0);
}

function proofKitModulePath(moduleName) {
  return path.join(repoRoot, "proofs", "talos", "lean",
    `${moduleName.replaceAll(".", path.sep)}.lean`);
}

function leanSourceDeclarations(moduleName, source) {
  const lines = source.split("\n");
  const blocks = [];
  const declarations = [];
  let offset = 0;
  for (const line of lines) {
    const trimmed = line.trim();
    const namespaceMatch = /^namespace\s+([^\s]+)\s*$/.exec(trimmed);
    if (namespaceMatch !== null) {
      const enclosing = blocks.filter((block) => block.kind === "namespace")
        .map((block) => block.name).join(".");
      const name = namespaceMatch[1];
      blocks.push({
        kind: "namespace",
        name: name.includes(".") || enclosing.length === 0 ? name : `${enclosing}.${name}`,
      });
      offset += line.length + 1;
      continue;
    }
    if (/^(?:section|mutual)(?:\s+[^\s]+)?\s*$/.test(trimmed)) {
      blocks.push({ kind: "other" });
      offset += line.length + 1;
      continue;
    }
    if (/^end(?:\s+[^\s]+)?\s*$/.test(trimmed)) {
      blocks.pop();
      offset += line.length + 1;
      continue;
    }
    const declarationMatch = /^(?:(private|protected|noncomputable|unsafe|partial)\s+)*(theorem|lemma|def|abbrev|opaque|structure|class|inductive|instance|macro|elab)\b(?:\s+([^\s(:{]+))?/.exec(trimmed);
    if (declarationMatch !== null) {
      const kind = declarationMatch[2];
      const name = kind === "macro" || kind === "elab"
        ? null
        : declarationMatch[3] || null;
      const namespace = [...blocks].reverse()
        .find((block) => block.kind === "namespace")?.name || "";
      declarations.push({
        module: moduleName,
        kind,
        private: trimmed.slice(0, trimmed.indexOf(kind)).split(/\s+/).includes("private"),
        name,
        fullName: name === null ? null : namespace.length === 0 ? name : `${namespace}.${name}`,
        offset,
      });
    }
    offset += line.length + 1;
  }
  for (const [index, declaration] of declarations.entries()) {
    if (declaration.kind !== "macro" && declaration.kind !== "elab") continue;
    const end = declarations[index + 1]?.offset || source.length;
    const header = source.slice(declaration.offset, end).split("=>", 1)[0];
    declaration.tactic = /:\s*tactic\s*$/.test(header.trim());
    const commandMatch = /"([^"\n]+)"/.exec(header);
    declaration.tacticCommand = declaration.tactic && commandMatch !== null
      ? commandMatch[1].trim()
      : null;
  }
  return declarations;
}

function catalogMetrics(catalog = checkCatalog()) {
  const entryRoleAssignments = catalog.entries.flatMap((entry) => entry.roles);
  const categoryMemberships = catalog.entries.flatMap((entry) => entry.categories);
  const annotationAssignments = catalog.entries.flatMap((entry) => entry.annotationKinds);
  const moduleAssignments = catalog.entries.flatMap((entry) => entry.modules);
  const declarationReferences = catalog.entries.flatMap((entry) => entry.declarations);
  const featureAssignments = catalog.entries.flatMap((entry) => entry.features);
  const consumerAssignments = catalog.entries.flatMap((entry) => entry.consumers);
  const membershipCounts = catalog.entries.map((entry) => entry.categories.length);
  const categoryPairs = [];
  for (const entry of catalog.entries) {
    for (let left = 0; left < entry.categories.length; left += 1) {
      for (let right = left + 1; right < entry.categories.length; right += 1) {
        categoryPairs.push(`${entry.categories[left]} + ${entry.categories[right]}`);
      }
    }
  }

  const proofKitFiles = new Map();
  const proofKitDeclarations = [];
  for (const moduleName of proofKitModules) {
    const file = proofKitModulePath(moduleName);
    const source = readRegularFile(file, `${moduleName} proof-kit source`);
    proofKitFiles.set(path.relative(repoRoot, file), source);
    proofKitDeclarations.push(...leanSourceDeclarations(moduleName, source));
  }
  const proofKitByName = new Map(proofKitDeclarations
    .filter((declaration) => declaration.fullName !== null && !declaration.private)
    .map((declaration) => [declaration.fullName, declaration]));
  const uniqueDeclarationReferences = [...new Set(declarationReferences)].sort();
  const localDeclarationReferences = uniqueDeclarationReferences
    .filter((name) => proofKitByName.has(name));
  const missingLocalDeclarationReferences = uniqueDeclarationReferences
    .filter((name) => name.startsWith("Project.ProofKit.") && !proofKitByName.has(name));
  const importedDeclarationReferences = uniqueDeclarationReferences
    .filter((name) => !name.startsWith("Project.ProofKit."));
  const tacticDeclarations = proofKitDeclarations.filter((declaration) => declaration.tactic);
  const tacticModules = new Set(tacticDeclarations.map((declaration) => declaration.module));
  const uniqueCatalogModules = new Set(moduleAssignments);
  const publicNamedProofKitDeclarations = proofKitDeclarations.filter((declaration) =>
    !declaration.private && declaration.fullName !== null);

  const canonicalFiles = new Map([
    ["README.md", readRegularFile(path.join(catalog.root, "README.md"), "LTG README.md")],
    ["categories.json", readRegularFile(
      path.join(catalog.root, "categories.json"), "LTG categories.json")],
  ]);
  const entryFiles = new Map();
  const markdownFiles = new Map([["README.md", canonicalFiles.get("README.md")]]);
  const metadataFiles = new Map([["categories.json", canonicalFiles.get("categories.json")]]);
  for (const entry of catalog.entries) {
    for (const relative of collectFiles(entry.root)) {
      const name = `entries/${entry.id}/${relative}`;
      const source = fs.readFileSync(path.join(entry.root, relative));
      canonicalFiles.set(name, source);
      entryFiles.set(name, source);
      if (relative.endsWith(".md")) markdownFiles.set(name, source);
      if (relative.endsWith(".json")) metadataFiles.set(name, source);
    }
  }
  const generatedIndexFiles = new Map(catalog.categories.map((category) => {
    const name = `categories/${category.id}/tools.jsonl`;
    return [name, readRegularFile(path.join(catalog.root, name), name)];
  }));
  const task = taskCatalogFiles({ root: catalog.root });
  const physicalCatalogFiles = new Map(collectFiles(catalog.root).map((relative) => [
    relative,
    fs.readFileSync(path.join(catalog.root, relative)),
  ]));
  const proofKitReadme = readRegularFile(
    path.join(repoRoot, "proofs", "talos", "lean", "Project", "ProofKit", "README.md"),
    "proof-kit README.md");
  const generatedLeanCheck = readRegularFile(leanCheckPath, "generated LTGCheck.lean");

  const relatedLinks = catalog.entries.flatMap((entry) => entry.relatedEntries
    .map((related) => `${entry.id}\0${related}`));
  const relatedLinkSet = new Set(relatedLinks);
  const reciprocalPairs = relatedLinks.filter((link) => {
    const [source, target] = link.split("\0");
    return source < target && relatedLinkSet.has(`${target}\0${source}`);
  });
  const excludedEntries = catalog.entries.filter((entry) => entry.exclusion !== null);
  const localKindCounts = counts(localDeclarationReferences
    .map((name) => proofKitByName.get(name).kind), leanDeclarationKinds);
  const proofKitKindCounts = counts(proofKitDeclarations
    .map((declaration) => declaration.kind), leanDeclarationKinds);

  return {
    schemaVersion: 1,
    catalog: {
      categories: catalog.categories.length,
      entries: catalog.entries.length,
      roles: counts(entryRoleAssignments, roles),
      roleAssignments: entryRoleAssignments.length,
      scopes: counts(catalog.entries.map((entry) => entry.scope), scopes),
      evidenceStatuses: counts(
        catalog.entries.map((entry) => entry.evidenceStatus), evidenceStatuses),
    },
    categoryStructure: {
      memberships: categoryMemberships.length,
      entriesPerCategory: counts(categoryMemberships),
      membershipsPerEntry: counts(membershipCounts.map(String)),
      minimumMembershipsPerEntry: Math.min(...membershipCounts),
      maximumMembershipsPerEntry: Math.max(...membershipCounts),
      meanMembershipsPerEntry: Number(
        (categoryMemberships.length / catalog.entries.length).toFixed(3)),
      entriesInMultipleCategories: membershipCounts.filter((count) => count > 1).length,
      pairIntersections: counts(categoryPairs),
    },
    coverage: {
      entriesWithGuidanceRole: catalog.entries.filter((entry) =>
        entry.roles.includes("guidance")).length,
      guidanceOnlyEntries: catalog.entries.filter((entry) =>
        entry.roles.length === 1 && entry.roles[0] === "guidance").length,
      entriesWithCheckedProofAssetRole: catalog.entries.filter((entry) =>
        entry.roles.includes("checked-proof-asset")).length,
      entriesWithAnnotationSupportRole: catalog.entries.filter((entry) =>
        entry.roles.includes("annotation-support")).length,
      entriesWithProofGenerationMechanismRole: catalog.entries.filter((entry) =>
        entry.roles.includes("proof-generation-mechanism")).length,
      entriesWithWorkedExampleRole: catalog.entries.filter((entry) =>
        entry.roles.includes("worked-example")).length,
      entriesWithExecutableRole: catalog.entries.filter((entry) =>
        entry.roles.some((role) => role === "checked-proof-asset" ||
          role === "proof-generation-mechanism")).length,
      entriesWithDeclaredLeanSupport: catalog.entries.filter((entry) =>
        entry.modules.length > 0 && entry.declarations.length > 0).length,
      entriesWithLocalProofKitDeclarations: catalog.entries.filter((entry) =>
        entry.declarations.some((name) => proofKitByName.has(name))).length,
      entriesImportingTacticModules: catalog.entries.filter((entry) =>
        entry.modules.some((moduleName) => tacticModules.has(moduleName))).length,
    },
    retrievalVocabulary: {
      uniqueFeatures: new Set(featureAssignments).size,
      featureAssignments: featureAssignments.length,
      features: counts(featureAssignments),
      uniqueAnnotationKinds: new Set(annotationAssignments).size,
      annotationAssignments: annotationAssignments.length,
      annotationKinds: counts(annotationAssignments),
      entriesWithAnnotationKinds: catalog.entries.filter((entry) =>
        entry.annotationKinds.length > 0).length,
    },
    consumers: {
      unique: new Set(consumerAssignments).size,
      assignments: consumerAssignments.length,
      entriesWithoutConsumers: catalog.entries.filter((entry) =>
        entry.consumers.length === 0).length,
      byConsumer: counts(consumerAssignments),
    },
    leanSupport: {
      catalogDeclarationReferences: declarationReferences.length,
      uniqueCatalogDeclarationNames: uniqueDeclarationReferences.length,
      duplicateCatalogDeclarationReferences:
        declarationReferences.length - uniqueDeclarationReferences.length,
      uniqueLocalProofKitDeclarationNames: localDeclarationReferences.length,
      uniqueImportedDeclarationNames: importedDeclarationReferences.length,
      localCatalogDeclarationKinds: localKindCounts,
      missingLocalCatalogDeclarationNames: missingLocalDeclarationReferences,
      catalogModuleReferences: moduleAssignments.length,
      uniqueCatalogModuleNames: uniqueCatalogModules.size,
      proofKitModules: proofKitModules.length,
      catalogModuleCoverageOfProofKit: Number(
        (uniqueCatalogModules.size / proofKitModules.length).toFixed(3)),
      proofKitSourceDeclarations: proofKitDeclarations.length,
      proofKitPublicSourceDeclarations: proofKitDeclarations.filter((declaration) =>
        !declaration.private).length,
      proofKitPublicNamedSourceDeclarations: publicNamedProofKitDeclarations.length,
      proofKitPrivateSourceDeclarations: proofKitDeclarations.filter((declaration) =>
        declaration.private).length,
      proofKitSourceDeclarationKinds: proofKitKindCounts,
      indexedLocalDeclarationCoverageOfPublicNamedProofKit: Number(
        (localDeclarationReferences.length / publicNamedProofKitDeclarations.length).toFixed(3)),
      tacticDefinitions: tacticDeclarations.length,
      tacticMacroDefinitions: tacticDeclarations.filter((declaration) =>
        declaration.kind === "macro").length,
      tacticElaboratorDefinitions: tacticDeclarations.filter((declaration) =>
        declaration.kind === "elab").length,
      distinctTacticCommands: new Set(tacticDeclarations
        .map((declaration) => declaration.tacticCommand)
        .filter((name) => name !== null)).size,
      tacticBearingModules: tacticModules.size,
    },
    graphAndExclusions: {
      relatedEntryLinks: relatedLinks.length,
      reciprocalRelatedEntryPairs: reciprocalPairs.length,
      asymmetricRelatedEntryLinks: relatedLinks.length - reciprocalPairs.length * 2,
      entriesWithoutRelatedEntries: catalog.entries.filter((entry) =>
        entry.relatedEntries.length === 0).length,
      excludedEntries: excludedEntries.length,
      excludedArtifactDigests: new Set(excludedEntries.flatMap((entry) =>
        entry.exclusion.artifactSha256)).size,
      excludedDerivativeGroups: new Set(excludedEntries.map((entry) =>
        entry.exclusion.derivativeGroup)).size,
      structurallyDanglingCategoryModuleOrEntryReferences: 0,
    },
    content: {
      canonicalEntryFiles: entryFiles.size,
      canonicalEntryContentBytes: sumByteLengths(entryFiles),
      canonicalCatalogFiles: canonicalFiles.size,
      canonicalCatalogBytes: sumByteLengths(canonicalFiles),
      markdownFiles: markdownFiles.size,
      markdownBytes: sumByteLengths(markdownFiles),
      metadataFiles: metadataFiles.size,
      metadataBytes: sumByteLengths(metadataFiles),
      generatedCategoryIndexFiles: generatedIndexFiles.size,
      generatedCategoryIndexBytes: sumByteLengths(generatedIndexFiles),
      physicalCatalogFiles: physicalCatalogFiles.size,
      physicalCatalogBytes: sumByteLengths(physicalCatalogFiles),
      taskBundleFiles: task.files.size,
      taskBundleBytes: sumByteLengths(task.files),
      taskBundleSha256: catalogDigest(task.files),
      proofKitLeanFiles: proofKitFiles.size,
      proofKitLeanBytes: sumByteLengths(proofKitFiles),
      proofKitReadmeBytes: Buffer.byteLength(proofKitReadme),
      generatedLeanCheckBytes: Buffer.byteLength(generatedLeanCheck),
      combinedPhysicalKnowledgeBytes: sumByteLengths(physicalCatalogFiles) +
        sumByteLengths(proofKitFiles) + Buffer.byteLength(proofKitReadme),
    },
  };
}

module.exports = {
  catalogMetrics,
  catalogDigest,
  checkCatalog,
  defaultRoot,
  loadCatalog,
  rebuildCatalog,
  renderCategoryIndex,
  renderLeanCheck,
  taskCatalogFiles,
};
