#!/usr/bin/env node
"use strict";

const fs = require("node:fs");
const os = require("node:os");
const path = require("node:path");
const {
  artifactSources,
  createPackage,
  currentToolPins,
  kernelAuditFindings,
  makeJob,
  moduleFile,
  programExportIndex,
  rewriteProgramNamespace,
  sha256,
  validateCodexTaskOutcome,
  validatePackage,
  validateProgramImports,
  validateProofImports,
  validateStageReports,
} = require("../tools/leanexegen-lib");
const {
  StageError,
  auditAxioms,
  codexCommandArgs,
  codexOutcomeSchema,
  parseCodexVersion,
  formalSpecificationCheckSources,
  formalSpecificationSource,
  formalTaskContext,
  generationResult,
  parseProofStrategySections,
  parseArgs,
  proofPackagePath,
  proofStrategyBundle,
  proofTaskContext,
  readPackageSources,
  requireFrozenProofKitIsolation,
  reprovePinsMatch,
  reproveSourceSets,
  programPrompt,
  programTaskContext,
  proofPrompt,
  publish,
  runCodexOutcome,
  runTaskSession,
  stageHeading,
  verificationCheckSources,
  warnings,
} = require("../tools/leanexegen");
const {
  createStage5Telemetry,
  validateStage5Telemetry,
} = require("../tools/leanexegen-telemetry");

const repoRoot = path.resolve(__dirname, "..");
const temporaryRoot = fs.mkdtempSync(path.join(os.tmpdir(), "leanexegen-test-"));

function assert(condition, message) {
  if (!condition) throw new Error(message);
}

function expectFailure(action, pattern) {
  try {
    action();
  } catch (error) {
    if (!pattern.test(error.message)) throw error;
    return error;
  }
  throw new Error(`expected failure matching ${pattern}`);
}

function outcome(task, source, values = {}) {
  return {
    schemaVersion: 2,
    task,
    outcome: "generated",
    summary: values.summary || `${task} result`,
    decisions: values.decisions || ["Use the fixed array ABI."],
    questions: [],
    problems: [],
    source,
    samples: values.samples || [],
    hostAssumptions: values.hostAssumptions || [],
  };
}

function stageReport(task, sourceModule, source) {
  const diagnostic = `${task} accepted`;
  const sourceSha256 = sha256(Buffer.from(source));
  const report = {
    summary: `${task} result`,
    decisions: ["Use the fixed array ABI."],
    attempts: [{
      number: 1,
      outcome: "accepted",
      sourceSha256,
      diagnosticSha256: sha256(Buffer.from(diagnostic)),
      diagnostic,
    }],
  };
  return {
    task,
    sourceModule,
    sourceSha256,
    reportSha256: sha256(Buffer.from(`${JSON.stringify(report, null, 2)}\n`)),
    report,
  };
}

function testArguments() {
  const generated = parseArgs([
    "-s", "-o", "x.wasm", "request.txt",
  ]);
  assert(generated.command === "generate" && generated.silent,
    "generation arguments were parsed incorrectly");
  const verified = parseArgs(["verify", "-s", "x.proof"]);
  assert(verified.command === "verify" && verified.silent,
    "verification arguments were parsed incorrectly");
  const reproved = parseArgs(["reprove", "-s", "-o", "new.wasm", "x.proof"]);
  assert(reproved.command === "reprove" && reproved.silent &&
    reproved.outputPath.endsWith("/new.wasm") && reproved.packagePath.endsWith("/x.proof"),
  "reproof arguments were parsed incorrectly");
  const run = parseArgs(["run", "x.wasm", "1", "2"]);
  assert(run.command === "run" && run.wasmPath.endsWith("/x.wasm") &&
    JSON.stringify(run.input) === JSON.stringify(["1", "2"]),
  "array execution arguments were parsed incorrectly");
  const benchmark = parseArgs(["benchmark", "-o", "measured.wasm", "benchmarks/example"]);
  assert(benchmark.command === "benchmark" &&
    benchmark.outputPath.endsWith("/measured.wasm") &&
    benchmark.benchmarkRoot.endsWith("/benchmarks/example"),
  "benchmark arguments were parsed incorrectly");
  assert(proofPackagePath("/tmp/x.wasm") === "/tmp/x.proof",
    "proof package path was derived incorrectly");
  expectFailure(() => parseArgs(["-o", "x.wasm"]), /usage:/);
  expectFailure(() => parseArgs([
    "--no-proof-kit", "-o", "x.wasm", "request.txt",
  ]), /usage:/);
  assert(generationResult(true, [{ input: ["1"], output: ["1"] }], ["leanexegen"]) === "",
    "silent generation produced standard output");
  assert(stageHeading(3, "Lean program", new Date("2026-08-03T12:34:57.000Z")) ===
    "2026-08-03T12:34:57.000Z Stage 3: Lean program\n\n",
    "stage heading did not contain the UTC start time");
}

function testStage5Telemetry() {
  const clockValues = [0n, 1000000000n, 4000000000n, 5000000000n,
    7000000000n, 8000000000n];
  const dates = [
    new Date("2026-08-05T15:23:01.431Z"),
    new Date("2026-08-05T15:23:09.431Z"),
  ];
  const telemetry = createStage5Telemetry({
    clock: () => clockValues.shift(),
    now: () => dates.shift(),
  });
  assert(telemetry.measureCodexSession(() => "generated") === "generated",
    "stage-5 telemetry changed the Codex result");
  assert(telemetry.measureOuterAcceptance(() => "accepted") === "accepted",
    "stage-5 telemetry changed the outer acceptance result");
  const sourceSha256 = "a".repeat(64);
  const report = telemetry.accept(sourceSha256);
  assert(report.stageStartedAt === "2026-08-05T15:23:01.431Z" &&
    report.firstAcceptedAt === "2026-08-05T15:23:09.431Z" &&
    report.codexSessionMilliseconds === 3000 &&
    report.outerAcceptanceMilliseconds === 2000 &&
    report.totalMilliseconds === 8000 &&
    report.acceptedSourceSha256 === sourceSha256,
  "stage-5 telemetry recorded incorrect intervals");
  const invalid = structuredClone(report);
  invalid.totalMilliseconds = 4000;
  expectFailure(() => validateStage5Telemetry(invalid),
    /components exceed totalMilliseconds/);
}

function testCodexProtocol() {
  const job = makeJob("compute one unsigned integer array\n");
  assert(parseCodexVersion({
    stdout: "codex-cli 0.146.0\n",
    stderr: "WARNING: could not create PATH aliases\n",
  }) === "codex-cli 0.146.0", "Codex identity included an unrelated warning");
  assert(JSON.stringify(job) === JSON.stringify(makeJob("compute one unsigned integer array\n")),
    "job identity was not deterministic");
  assert(job.formalSpecDefinition === `${job.namespace}.FormalSpec.ArtifactSpec` &&
    job.formalSpecType === "Wasm.Module → Prop" &&
    job.sourceEntry === `${job.namespace}.Source.compute` && job.exportName === "compute",
  "job did not fix the array formal and program interfaces");

  const formalRaw = `import CodeLib\n\nnamespace ${job.namespace}.FormalSpec\n\n` +
    `def expected (values : Array UInt64) : Array UInt64 := values\n\n` +
    `end ${job.namespace}.FormalSpec\n`;
  const formalOutcome = outcome("formal-specification", formalRaw, {
    hostAssumptions: ["The module imports no host functions."],
  });
  validateCodexTaskOutcome(formalOutcome, "formal-specification");
  validateCodexTaskOutcome({
    schemaVersion: 2,
    task: "artifact-proof",
    outcome: "questions",
    summary: "The property is ambiguous.",
    decisions: [],
    questions: ["What should zero mean?"],
    problems: [],
    source: "",
    samples: [],
    hostAssumptions: [],
  }, "artifact-proof");
  const invalid = structuredClone(formalOutcome);
  invalid.samples = [{ input: ["1"], expectedOutput: ["1"] }];
  expectFailure(() => validateCodexTaskOutcome(invalid, "formal-specification"),
    /must not contain samples/);
  const invalidSample = outcome("lean-program", formalRaw, {
    samples: [{ input: ["42"], expectedOutput: ["42\n"] }],
  });
  expectFailure(() => validateCodexTaskOutcome(invalidSample, "lean-program"),
    /expectedOutput\[0\] must be a UInt64 decimal/);
  const excessiveSample = outcome("lean-program", formalRaw, {
    samples: [{ input: ["18446744073709551616"], expectedOutput: ["0"] }],
  });
  expectFailure(() => validateCodexTaskOutcome(excessiveSample, "lean-program"),
    /input\[0\] must be a UInt64 decimal/);
  const programProblem = outcome("lean-program", "candidate", {
    samples: [{ input: ["1"], expectedOutput: ["1"] }],
  });
  programProblem.outcome = "problems";
  programProblem.problems = ["compiler rejected the candidate"];
  programProblem.source = "";
  assert(validateCodexTaskOutcome(programProblem, "lean-program") === programProblem,
    "problem outcomes rejected irrelevant generated-result metadata");
  const formalSource = formalSpecificationSource(job, formalRaw);
  assert(formalSource.includes("def UInt64ArrayAt") &&
    formalSource.includes("def RuntimeReady") &&
    formalSource.includes("initial.mem.pages ≤ 65536") &&
    formalSource.includes("def ArtifactSpec (module_ : Wasm.Module) : Prop :=") &&
    formalSource.includes('module_.findExport "compute" = some entry') &&
    formalSource.includes("Wasm.TerminatesWith env module_ entry initial [.i64 inputPtr]") &&
    formalSource.includes("UInt64ArrayAt final outputPtr (expected input)"),
  "the orchestrator did not append the fixed formal interface");
  const checks = formalSpecificationCheckSources(job, "FormalSpecCheck");
  const checkSource = checks.sources.get(checks.target);
  assert(checkSource.includes(`#check (${job.expectedDefinition} : Array UInt64 → Array UInt64)`) &&
    checkSource.includes(`#check (${job.formalSpecDefinition} : ${job.formalSpecType})`),
  "formal declaration checks did not name both fixed declarations and types");
  const formalContext = formalTaskContext("request\n", job);
  assert(formalContext.get("request.txt") === "request\n" &&
    formalContext.get(moduleFile(`${job.namespace}.FormalSessionCheck`))
      .includes(job.expectedDefinition),
  "formal task did not receive its request and declaration check");
  const programContext = programTaskContext("request\n", job, formalSource);
  const prompt = programPrompt("request\n", job);
  assert(programContext.get(`LeanExeGen/${job.leanModule}/FormalSpec.lean`) === formalSource &&
    prompt.includes(job.formalSpecDefinition) &&
    prompt.includes("do not import it from Source") &&
    prompt.includes("tools/leanrun") &&
    prompt.includes("continue until all three commands succeed"),
  "program task did not receive or target the frozen formal specification");
  const artifactPrompt = proofPrompt("request\n", job, 3);
  assert(artifactPrompt.includes("refine ⟨3, rfl, ?_⟩") &&
    artifactPrompt.includes("intro env initial inputPtr input hInput") &&
    artifactPrompt.includes("PROOF_LIBRARY.md catalogs checked proof abstractions") &&
    artifactPrompt.includes("Project.ProofKit.Control") &&
    artifactPrompt.includes("Project.ProofKit.Allocation") &&
    artifactPrompt.includes("bumpFacts") &&
    artifactPrompt.includes("wordAddress_toNat") &&
    artifactPrompt.includes("Project.ProofKit.FixedArrayAllocator") &&
    artifactPrompt.includes("region_spec") &&
    artifactPrompt.includes("Project.ProofKit.FixedArraySingleton") &&
    artifactPrompt.includes("region_result_spec") &&
    artifactPrompt.includes("Project.ProofKit.UInt64Array.At") &&
    artifactPrompt.includes("word_reads") &&
    artifactPrompt.includes("wp_entry_to_loop <functionDef>") &&
    artifactPrompt.includes(`wp_entry_single_call ${job.namespace}.func3Def`) &&
    artifactPrompt.includes("PROOF_STRATEGIES.md contains optional") &&
    artifactPrompt.includes("PROOF_TASK_FEATURES.json") &&
    artifactPrompt.includes("Use read-only commands to inspect FormalSpec, Program"),
  "artifact-proof task did not receive the proof-kit catalog or tactics");
  expectFailure(() => validateProgramImports(
    job, `import ${job.formalSpecModule}\n\ndef compute (a : Array UInt64) := a\n`),
  /must not import/);

  const behaviorSource = `import ${job.sourceModule}\n`;
  expectFailure(() => validateProofImports(job, [{
    module: job.behaviorModule,
    source: behaviorSource,
  }]), /unsupported proof dependency/);
  validateProofImports(job, [{
    module: job.behaviorModule,
    source: "import Project.ProofKit.Control\n",
  }]);
  validateProofImports(job, [{
    module: job.behaviorModule,
    source: "import Project.ProofKit.Array\n",
  }]);
  validateProofImports(job, [{
    module: job.behaviorModule,
    source: "import Project.ProofKit.Allocation\n",
  }]);
  validateProofImports(job, [{
    module: job.behaviorModule,
    source: "import Project.ProofKit.FixedArrayAllocator\n",
  }]);
  validateProofImports(job, [{
    module: job.behaviorModule,
    source: "import Project.ProofKit.FixedArraySingleton\n",
  }]);
  expectFailure(() => validateProofImports(job, [{
    module: job.behaviorModule,
    source: "import Project.Common\n",
  }]), /unsupported proof dependency/);
  return { job, formalSource };
}

function testMockedCodex(job) {
  const taskRoot = path.join(temporaryRoot, "mock-codex");
  fs.mkdirSync(taskRoot);
  const candidateSource =
    `namespace ${job.namespace}.Source\n\ndef compute (a : Array UInt64) := a\n`;
  const generated = outcome("lean-program", "", {
    samples: [{ input: ["7"], expectedOutput: ["7"] }],
  });
  let recorded = null;
  const response = runCodexOutcome({
    codex: "/usr/bin/codex",
    task: "lean-program",
    stage: 3,
    taskRoot,
    contextFiles: new Map([["request.txt", "identity\n"]]),
    candidateFile: moduleFile(job.sourceModule),
    timeout: 1000,
    prompt: "mock prompt",
    execute: (args, options) => {
      recorded = { args, options };
      const candidate = path.join(taskRoot, moduleFile(job.sourceModule));
      fs.mkdirSync(path.dirname(candidate), { recursive: true });
      fs.writeFileSync(candidate, candidateSource);
      const output = args[args.indexOf("-o") + 1];
      fs.writeFileSync(output, `${JSON.stringify(generated)}\n`);
      return { stdout: "", stderr: "" };
    },
  });
  assert(response.task === "lean-program" && response.source === candidateSource &&
    recorded.options.input === "mock prompt",
    "mocked Codex outcome was not returned");
  for (const flag of [
    "-C", "--sandbox", "--skip-git-repo-check", "--ephemeral", "--json",
    "--output-schema", "-o",
  ]) {
    assert(recorded.args.includes(flag), `Codex invocation omitted ${flag}`);
  }
  assert(recorded.args[recorded.args.length - 1] === "-" &&
    recorded.args[0].endsWith("/tools/leanrun") &&
    recorded.args[recorded.args.indexOf("--sandbox") + 1] === "workspace-write" &&
    fs.readFileSync(path.join(taskRoot, "request.txt"), "utf8") === "identity\n" &&
    fs.existsSync(path.join(taskRoot, "lakefile.toml")),
  "Codex invocation did not use stdin, the requested sandbox, or isolated context");
  const schema = codexOutcomeSchema();
  assert(codexCommandArgs("codex", "/tmp/job", "/tmp/schema", "/tmp/out").includes("--ephemeral") &&
    schema.additionalProperties === false &&
    schema.properties.schemaVersion.type === "integer" &&
    schema.properties.task.type === "string" &&
    schema.properties.outcome.type === "string" &&
    schema.properties.samples.items.properties.input.maxItems === 256 &&
    schema.properties.samples.items.properties.expectedOutput.items.pattern ===
      "^(?:0|[1-9][0-9]*)$",
  "Codex command or schema was not deterministic");

  let invocations = 0;
  const telemetryCalls = [];
  const session = runTaskSession({
    task: "lean-program",
    stage: 3,
    stageName: "Lean program",
    sourceModule: job.sourceModule,
    invoke: (prompt) => {
      assert(prompt === "one iterative session", "task session received the wrong prompt");
      invocations += 1;
      return outcome("lean-program", "good", {
        samples: [{ input: ["7"], expectedOutput: ["7"] }],
      });
    },
    prompt: "one iterative session",
    materialize: (source) => source,
    diagnose: () => "outer diagnostic accepted source",
    telemetry: {
      measureCodexSession: (action) => {
        telemetryCalls.push("codex");
        return action();
      },
      measureOuterAcceptance: (action) => {
        telemetryCalls.push("outer");
        return action();
      },
      accept: (sourceSha256) => {
        telemetryCalls.push("accepted");
        return { acceptedSourceSha256: sourceSha256 };
      },
    },
  });
  assert(invocations === 1 && session.stageReport.report.attempts.length === 1 &&
    session.stageReport.report.attempts[0].outcome === "accepted" &&
    telemetryCalls.join(",") === "codex,outer,accepted" &&
    session.proofTelemetry.acceptedSourceSha256 === session.stageReport.sourceSha256,
  "task orchestration invoked more than one Codex session");
  expectFailure(() => runTaskSession({
    task: "lean-program",
    stage: 3,
    stageName: "Lean program",
    sourceModule: job.sourceModule,
    invoke: () => outcome("lean-program", "bad", {
      samples: [{ input: ["7"], expectedOutput: ["7"] }],
    }),
    prompt: "one iterative session",
    materialize: (source) => source,
    diagnose: () => { throw new Error("unknown declaration bad"); },
  }), /independent outer check rejected.*unknown declaration bad/s);
}

function testArtifactPackage(job, formalSource) {
  const raw = "{ functionTypeIndices := [0] }";
  const emitted = `namespace Project.${job.leanModule}\n\n` +
    `def func0 : Wasm.Program :=\n  [.localGet 0]\n\n` +
    `def func0Def : Wasm.Function :=\n` +
    `  { params := [.i64], locals := [], body := func0, results := [.i64] }\n\n` +
    `def «module» : Wasm.Module :=\n` +
    `{ funcs := [func0Def], exports := [{ name := "compute", funcIdx := 0 }] }\n\n` +
    `end Project.${job.leanModule}\n`;
  const talosProgram = rewriteProgramNamespace(emitted, job);
  assert(programExportIndex(talosProgram, "compute") === 0,
    "Talos export index was not resolved");
  expectFailure(() => programExportIndex(talosProgram, "missing"), /0 exports named missing/);
  const wasm = Buffer.from([0, 97, 115, 109, 1, 0, 0, 0]);
  const generated = artifactSources(job, wasm, raw, talosProgram);
  assert(generated.sources.get(job.artifactTarget).includes(job.formalSpecDefinition) &&
    generated.artifact.property === job.formalSpecDefinition,
  "artifact result did not use the fixed formal declaration");
  const proofContext = proofTaskContext("request\n", job, formalSource, generated.sources);
  assert(proofContext.has(`LeanExeGen/${job.leanModule}/Program.lean`) &&
    proofContext.get("PROOF_LIBRARY.md").includes("wp_entry_single_call") &&
    proofContext.get("PROOF_LIBRARY.md").includes("bumpFacts") &&
    proofContext.get("PROOF_STRATEGIES.md").includes("strategy.core") &&
    proofContext.get("PROOF_STRATEGIES.md").includes("strategy.arrays") &&
    JSON.parse(proofContext.get("PROOF_TASK_FEATURES.json")).exportIndex === 0 &&
    !proofContext.has(`LeanExeGen/${job.leanModule}/Source.lean`),
  "proof task context omitted proof guidance or Program, or exposed Source");
  const strategyBundle = proofStrategyBundle(talosProgram, 0);
  assert(strategyBundle.features.selectedSections.some((item) => item.id === "strategy.core") &&
    strategyBundle.features.selectedSections.some((item) => item.id === "strategy.arrays") &&
    strategyBundle.features.selectedSections.some((item) => item.id === "strategy.diagnostics") &&
    !strategyBundle.features.selectedSections.some((item) => item.id === "strategy.loops"),
  "proof-strategy selection disagreed with the synthetic Program");
  expectFailure(() => parseProofStrategySections(
    "<!-- leanexegen-section:strategy.core begin -->\n" +
    "### `strategy.other`: wrong\n" +
    "<!-- leanexegen-section:strategy.core end -->\n"), /mismatched heading/);
  const programSource = `namespace ${job.namespace}.Source\n\n` +
    `def compute (a : Array UInt64) := a\n`;
  const behaviorSource = `import ${job.programModule}\nimport ${job.formalSpecModule}\n\n` +
    `namespace ${job.namespace}.Behavior\n\ntheorem artifact_behavior : ` +
    `${job.formalSpecDefinition} ${job.namespace}.«module» := by\n` +
    `  simp [${job.formalSpecDefinition}]\n\n` +
    `end ${job.namespace}.Behavior\n`;
  const sources = new Map([
    [job.formalSpecModule, formalSource],
    [job.sourceModule, programSource],
    [job.behaviorModule, behaviorSource],
    ...generated.sources,
  ]);
  const artifact = {
    ...generated.artifact,
    export: job.exportName,
    invocation: ["tools/leanexegen", "run", "<program.wasm>", "<UInt64>..."],
  };
  const verification = verificationCheckSources(job, artifact);
  assert(verification.fileTarget.endsWith(".VerifierCheckFile") &&
    verification.sources.get(verification.declarationTarget).includes(artifact.artifactTheorem),
  "independent verification modules did not use the recorded theorem identity");
  const stageReports = {
    schemaVersion: 1,
    codexVersion: "codex-cli test",
    maximumAttempts: 3,
    tasks: {
      formalSpecification: stageReport(
        "formal-specification", job.formalSpecModule, formalSource),
      leanProgram: stageReport("lean-program", job.sourceModule, programSource),
      artifactProof: stageReport("artifact-proof", job.behaviorModule, behaviorSource),
    },
  };
  const proofTelemetry = {
    schemaVersion: 1,
    metric: "stage-5-start-to-first-accepted-proof",
    stage: 5,
    stageName: "Direct artifact proof",
    stageStartedAt: "2026-08-05T15:23:01.431Z",
    firstAcceptedAt: "2026-08-05T15:23:04.431Z",
    codexSessionMilliseconds: 1000,
    outerAcceptanceMilliseconds: 1000,
    totalMilliseconds: 3000,
    acceptedSourceSha256: stageReports.tasks.artifactProof.sourceSha256,
  };
  const packageRoot = path.join(temporaryRoot, "package");
  createPackage(packageRoot, {
    request: "compute one unsigned integer array\n",
    interpretation: {
      formalSpecification: { summary: "spec", decisions: [] },
      leanProgram: { summary: "program", decisions: [] },
      artifactProof: { summary: "proof", decisions: [] },
    },
    artifact,
    samples: [{ input: ["7"], output: ["7"], invocation: [] }],
    hostAssumptions: ["The module imports no host functions."],
    stageReports,
    proofTelemetry,
    toolPins: currentToolPins(repoRoot),
    proofLibraryCatalog: fs.readFileSync(
      path.join(repoRoot, "proofs", "talos", "lean", "Project", "ProofKit", "README.md"),
      "utf8"),
    proofStrategies: strategyBundle.notes,
    proofTaskFeatures: strategyBundle.features,
    wasmBytes: wasm,
    sources,
    job,
    formalSpecification: {
      module: job.formalSpecModule,
      definition: job.formalSpecDefinition,
      type: job.formalSpecType,
    },
    warnings,
  });
  const checked = validatePackage(packageRoot);
  assert(checked.artifact.sha256 === generated.artifact.sha256 &&
    checked.stageReports.tasks.leanProgram.sourceSha256 === sha256(Buffer.from(programSource)) &&
    checked.proofTelemetry.totalMilliseconds === 3000,
  "validated package returned the wrong artifact or stage report");
  assert(fs.readFileSync(path.join(packageRoot, "proof-strategies.md"), "utf8") ===
    strategyBundle.notes &&
    JSON.parse(fs.readFileSync(path.join(packageRoot, "proof-task-features.json"), "utf8"))
      .sourceSha256 === strategyBundle.features.sourceSha256,
  "proof package did not archive its selected strategy context");
  const legacyRoot = path.join(temporaryRoot, "legacy-package");
  fs.cpSync(packageRoot, legacyRoot, { recursive: true });
  fs.unlinkSync(path.join(legacyRoot, "proof-strategies.md"));
  fs.unlinkSync(path.join(legacyRoot, "proof-task-features.json"));
  fs.unlinkSync(path.join(legacyRoot, "proof-telemetry.json"));
  const legacyManifestPath = path.join(legacyRoot, "package.json");
  const legacyManifest = JSON.parse(fs.readFileSync(legacyManifestPath, "utf8"));
  legacyManifest.schemaVersion = 3;
  legacyManifest.files = legacyManifest.files.filter((record) =>
    !["proof-strategies.md", "proof-task-features.json", "proof-telemetry.json"]
      .includes(record.path));
  fs.writeFileSync(legacyManifestPath, `${JSON.stringify(legacyManifest, null, 2)}\n`);
  assert(validatePackage(legacyRoot).manifest.schemaVersion === 3,
    "package validation rejected a schema-3 package without strategy context");
  const packageSources = readPackageSources(packageRoot);
  const sourceSets = reproveSourceSets(packageSources, job);
  assert(sourceSets.frozen.get(job.sourceModule) === programSource &&
    !sourceSets.frozen.has(job.behaviorModule) &&
    !sourceSets.proofContext.has(job.sourceModule) &&
    !sourceSets.proofContext.has(job.formalSpecModule) &&
    sourceSets.proofContext.get(job.programModule) === talosProgram,
  "reproof source selection did not freeze the artifact inputs or exclude Source");
  const currentPins = currentToolPins(repoRoot);
  const changedKitPins = { ...currentPins, proofKitSourceSha256: "0".repeat(64) };
  assert(reprovePinsMatch(changedKitPins, currentPins),
    "reproof rejected a proof-library-only pin change");
  const changedTalosPins = { ...currentPins, talosRevision: "0".repeat(40) };
  assert(!reprovePinsMatch(changedTalosPins, currentPins),
    "reproof accepted a semantic dependency pin change");
  requireFrozenProofKitIsolation(sourceSets.frozen);
  expectFailure(() => requireFrozenProofKitIsolation(new Map([[
    job.programModule,
    "import Project.ProofKit.Control\n",
  ]])), /frozen module.*imports mutable proof-library module/);
  const tamperedReports = structuredClone(stageReports);
  tamperedReports.tasks.artifactProof.report.summary = "changed";
  expectFailure(() => validateStageReports(tamperedReports, packageRoot, job),
    /report digest mismatch/);
  fs.appendFileSync(path.join(packageRoot, "request.txt"), "changed\n");
  expectFailure(() => validatePackage(packageRoot), /disagrees|mismatch/);
}

function testPublication() {
  const output = path.join(temporaryRoot, "published", "program.wasm");
  const proof = path.join(temporaryRoot, "published", "program.proof");
  const bytes = Buffer.from([0, 97, 115, 109]);
  publish(output, proof, bytes, (root) => {
    fs.writeFileSync(path.join(root, "complete"), "yes\n");
  });
  assert(fs.readFileSync(output).equals(bytes) &&
    fs.readFileSync(path.join(proof, "complete"), "utf8") === "yes\n",
  "publication did not install both outputs");
  const failedOutput = path.join(temporaryRoot, "failed", "program.wasm");
  const failedProof = path.join(temporaryRoot, "failed", "program.proof");
  const error = expectFailure(() => publish(failedOutput, failedProof, bytes, () => {
    throw new Error("package failure");
  }), /package failure/);
  assert(error instanceof StageError && !fs.existsSync(failedOutput) && !fs.existsSync(failedProof),
    "failed publication left an output");
}

function testAxiomAudit() {
  const clean = Array.from({ length: 7 }, (_, index) =>
    `theorem${index} does not depend on any axioms`).join("\n");
  auditAxioms(clean);
  expectFailure(() => auditAxioms(`${clean}\n'bad' depends on axioms: [sorryAx]`), /sorryAx/);
}

function testKernelAudit() {
  const review = currentToolPins(repoRoot).kernelReview;
  assert(kernelAuditFindings(new Map([["Safe", "def value := 1\n"]]), review).length === 0,
    "kernel audit rejected safe source");
  const findings = kernelAuditFindings(new Map([[
    "Unsafe",
    `def value := 1\n-- ${review.forbiddenIdentifiers[0]}\n`,
  ]]), review);
  assert(findings.length === 1 && findings[0].startsWith("Unsafe:2:"),
    "kernel audit did not identify a forbidden identifier");
}

try {
  testArguments();
  testStage5Telemetry();
  const { job, formalSource } = testCodexProtocol();
  testMockedCodex(job);
  testArtifactPackage(job, formalSource);
  testPublication();
  testAxiomAudit();
  testKernelAudit();
  process.stdout.write("leanexegen Codex protocol, package, publication, and exit tests passed\n");
} finally {
  fs.rmSync(temporaryRoot, { recursive: true, force: true });
}
