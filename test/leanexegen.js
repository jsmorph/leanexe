#!/usr/bin/env node
"use strict";

const fs = require("node:fs");
const os = require("node:os");
const path = require("node:path");
const { spawnSync } = require("node:child_process");
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
  stageReportCodexVersion,
  stageReportCodexVersions,
  validateCodexTaskOutcome,
  validateLtgTask,
  validatePackage,
  validateProgramImports,
  validateProofImports,
  validateStageReports,
} = require("../tools/leanexegen-lib");
const {
  StageError,
  artifactProofStarter,
  artifactProofStarterExpectedComplete,
  auditAxioms,
  codexCommandArgs,
  codexOutcomeSchema,
  fixedArrayEqNodeFeatures,
  parseCodexVersion,
  formalSpecificationCheckSources,
  formalSpecificationSource,
  formalTaskContext,
  generationResult,
  ltgTaskBundle,
  parseProofStrategySections,
  parseArgs,
  preserveReproveFailure,
  proofPackagePath,
  proofStrategyBundle,
  proofTaskContext,
  readPackageSources,
  requireFrozenProofKitIsolation,
  requirePublicationTargetsAvailable,
  reprovePinsMatch,
  reproveSourceSets,
  programPrompt,
  programTaskContext,
  proofPrompt,
  publish,
  runCodexOutcome,
  runDeterministicTaskSession,
  runTaskSession,
  selectAnnotationRegions,
  stageHeading,
  verificationCheckSources,
  warnings,
} = require("../tools/leanexegen");
const {
  createStage5Telemetry,
  validateStage5Telemetry,
} = require("../tools/leanexegen-telemetry");
const {
  annotationMatchesSource,
  fixedArraySingletonWrapperCompositions,
  fixedArraySearchChainCompositions,
  fixedArraySearchTreeCompositions,
  proofRecipePlan,
  validateAnnotationDocument,
  validateProofRecipePlan,
} = require("../tools/leanexegen-annotations");
const { catalogDigest } = require("../tools/ltg-lib");

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
    !reproved.newCodexSeries &&
    reproved.outputPath.endsWith("/new.wasm") && reproved.packagePath.endsWith("/x.proof"),
  "reproof arguments were parsed incorrectly");
  const newSeries = parseArgs([
    "reprove", "--new-codex-series", "-o", "new.wasm", "x.proof",
  ]);
  assert(newSeries.command === "reprove" && newSeries.newCodexSeries,
    "new Codex series arguments were parsed incorrectly");
  expectFailure(() => parseArgs([
    "reprove", "--new-codex-series", "--new-codex-series",
    "-o", "new.wasm", "x.proof",
  ]), /usage:/);
  expectFailure(() => parseArgs([
    "--new-codex-series", "-o", "new.wasm", "request.txt",
  ]), /usage:/);
  const annotated = parseArgs(["annotate", "-o", "new.proof", "x.proof"]);
  assert(annotated.command === "annotate" &&
    annotated.selectedRegions.length === 0 &&
    annotated.outputPath.endsWith("/new.proof") &&
    annotated.packagePath.endsWith("/x.proof"),
  "annotation arguments were parsed incorrectly");
  const selectedAnnotation = parseArgs([
    "annotate", "--only-region", "function-0.while-loop-0",
    "--only-region", "function-1.direct-call-0", "-o", "new.proof", "x.proof",
  ]);
  assert(JSON.stringify(selectedAnnotation.selectedRegions) === JSON.stringify([
    "function-0.while-loop-0", "function-1.direct-call-0",
  ]), "selected annotation regions were parsed incorrectly");
  expectFailure(() => parseArgs([
    "annotate", "--only-region", "same", "--only-region", "same",
    "-o", "new.proof", "x.proof",
  ]), /usage:/);
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

  const directClockValues = [0n, 1000000000n, 3000000000n, 4000000000n];
  const directDates = [
    new Date("2026-08-05T16:00:00.000Z"),
    new Date("2026-08-05T16:00:04.000Z"),
  ];
  const direct = createStage5Telemetry({
    clock: () => directClockValues.shift(),
    now: () => directDates.shift(),
  });
  direct.skipCodexSession();
  assert(direct.measureOuterAcceptance(() => "accepted") === "accepted",
    "direct stage-5 telemetry changed the acceptance result");
  const directReport = direct.accept("b".repeat(64));
  assert(directReport.codexSessionMilliseconds === 0 &&
    directReport.outerAcceptanceMilliseconds === 2000 &&
    directReport.totalMilliseconds === 4000,
  "direct stage-5 telemetry recorded incorrect intervals");
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
    job.heapReserveDefinition === `${job.namespace}.FormalSpec.heapReserveBytes` &&
    job.formalSpecType === "Wasm.Module → Prop" &&
    job.sourceEntry === `${job.namespace}.Source.compute` && job.exportName === "compute",
  "job did not fix the array formal and program interfaces");

  const formalRaw = `import CodeLib\n\nnamespace ${job.namespace}.FormalSpec\n\n` +
    `def expected (values : Array UInt64) : Array UInt64 := values\n\n` +
    `def heapReserveBytes (values : Array UInt64) : Nat :=\n` +
    `  48 + 8 * (values.size + 1)\n\n` +
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
    formalSource.includes("heapTop.toNat + heapReserveBytes input ≤ 4294967296") &&
    formalSource.includes(
      "heapTop.toNat + heapReserveBytes input ≤ initial.mem.pages * 65536") &&
    formalSource.includes("initial.mem.pages ≤ 65536") &&
    formalSource.includes("def ArtifactSpec (module_ : Wasm.Module) : Prop :=") &&
    formalSource.includes('module_.findExport "compute" = some entry') &&
    formalSource.includes("Wasm.TerminatesWith env module_ entry initial [.i64 inputPtr]") &&
    formalSource.includes("UInt64ArrayAt final outputPtr (expected input)"),
  "the orchestrator did not append the fixed formal interface");
  const checks = formalSpecificationCheckSources(job, "FormalSpecCheck");
  const checkSource = checks.sources.get(checks.target);
  assert(checkSource.includes(`#check (${job.expectedDefinition} : Array UInt64 → Array UInt64)`) &&
    checkSource.includes(`#check (${job.heapReserveDefinition} : Array UInt64 → Nat)`) &&
    checkSource.includes(`#check (${job.formalSpecDefinition} : ${job.formalSpecType})`),
  "formal declaration checks did not name the fixed declarations and types");
  const legacyChecks = formalSpecificationCheckSources(job, "LegacyFormalSpecCheck", false);
  assert(!legacyChecks.sources.get(legacyChecks.target).includes(job.heapReserveDefinition),
    "legacy formal declaration checks required the schema-6 heap reserve");
  const formalContext = formalTaskContext("request\n", job);
  assert(formalContext.get("request.txt") === "request\n" &&
    formalContext.get(moduleFile(`${job.namespace}.FormalSessionCheck`))
      .includes(job.expectedDefinition) &&
    formalContext.get(moduleFile(`${job.namespace}.FormalSessionCheck`))
      .includes(job.heapReserveDefinition),
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
    artifactPrompt.includes("LTG/categories.json") &&
    artifactPrompt.includes("tools.jsonl files with rg") &&
    artifactPrompt.includes("Open only the entry.json and README.md") &&
    artifactPrompt.includes("do not read the complete LTG tree") &&
    artifactPrompt.includes("Record each search query, entry inspected, entry used") &&
    artifactPrompt.includes("PROOF_STRATEGIES.md contains optional guidance") &&
    artifactPrompt.includes("PROOF_TASK_FEATURES.json") &&
    artifactPrompt.includes("PROGRAM_ANNOTATIONS.json") &&
    artifactPrompt.includes("PROOF_RECIPES.json") &&
    artifactPrompt.includes("Attempt an exact direct recipe or complete composition") &&
    artifactPrompt.includes("Do not search for or read artifact proofs outside") &&
    artifactPrompt.includes("omits worked examples excluded for this exact artifact") &&
    artifactPrompt.includes("Keep PROOF_JOURNAL.md as frequent, natural Markdown prose") &&
    artifactPrompt.includes("after each Lean check") &&
    artifactPrompt.includes("missing general annotation, lemma, tactic, guidance") &&
    artifactPrompt.includes("node PROOF_IMPORT_CHECK.js") &&
    artifactPrompt.includes("deterministic theorem starter") &&
    artifactPrompt.includes("Use read-only commands to inspect FormalSpec") &&
    !artifactPrompt.includes("PROOF_LIBRARY.md") &&
    !artifactPrompt.includes("bumpFacts") &&
    Buffer.byteLength(artifactPrompt) < 9000,
  "artifact-proof task did not receive the compact LTG retrieval protocol");
  const wrapperStarter = artifactProofStarter(job, 3, true, {
    schemaVersion: 1,
    attemptOrder: ["direct", "composition", "tactic", "focused-guidance"],
    compositions: [{
      compositionVersion: 2,
      kind: "fixed-array-search-tree-v1",
      functionIndex: 3,
      descriptor: `${job.namespace}.AnnotationMatches.function_3_search_tree_0`,
      regionEquality: `${job.namespace}.AnnotationMatches.function_3_search_tree_0_eq`,
      direct: {
        module: "Project.ProofKit.FixedArraySearchTree",
        theorem: "Project.ProofKit.FixedArraySearchTree.Tree.wrapperProgram_spec",
      },
      wrapper: {
        expectedSize: 15,
        inputLocal: 15,
        invalidDestination: 1,
        keyIndex: 0,
        keyLocal: 2,
        offset: 10,
      },
    }],
    recipes: [],
  });
  assert(wrapperStarter.includes("search.wrapperProgram 15 15 10") &&
    wrapperStarter.includes("2 1)") &&
    wrapperStarter.includes("search.wrapperProgram_spec") &&
    wrapperStarter.includes("?_ ?_ ?_") &&
    wrapperStarter.includes("FixedArraySearchTree.Tree.result") &&
    !wrapperStarter.includes("import Project.ProofKit.FixedArrayLtNode") &&
    !wrapperStarter.includes("have hLengthRead"),
  "complete search-tree composition did not select the semantic-goal starter");
  const singletonStarter = artifactProofStarter(job, 3, true, {
    schemaVersion: 1,
    attemptOrder: ["direct", "composition", "tactic", "focused-guidance"],
    compositions: [{
      compositionVersion: 1,
      kind: "fixed-array-singleton-wrapper-v1",
      functionIndex: 3,
      calleeIndex: 2,
      descriptor: `${job.namespace}.AnnotationMatches.function_3_singleton_wrapper_0`,
      regionEquality:
        `${job.namespace}.AnnotationMatches.function_3_singleton_wrapper_0_eq`,
      direct: {
        module: "Project.ProofKit.FixedArraySingletonWrapper",
        theorem: "Project.ProofKit.FixedArraySingletonWrapper.wrapperProgram_spec",
      },
    }],
    recipes: [],
  });
  assert(singletonStarter.includes("import Project.ProofKit.FixedArraySingletonWrapper") &&
    singletonStarter.includes("FixedArraySingletonWrapper.entryFrame inputPtr") &&
    singletonStarter.includes("function_3_singleton_wrapper_0_eq") &&
    singletonStarter.includes("FixedArrayPairResult.publicPost") &&
    !singletonStarter.includes("have hLengthRead"),
  "complete singleton-wrapper composition did not select the wrapper-boundary starter");
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
    source: "import Project.ProofKit.Annotation\n",
  }]);
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
    source: "import Project.ProofKit.FixedArrayAllocatorWindow\n",
  }]);
  validateProofImports(job, [{
    module: job.behaviorModule,
    source: "import Project.ProofKit.FixedArrayInput\n",
  }]);
  validateProofImports(job, [{
    module: job.behaviorModule,
    source: "import Project.ProofKit.FixedArrayEqNode\n",
  }]);
  validateProofImports(job, [{
    module: job.behaviorModule,
    source: "import Project.ProofKit.FixedArrayLengthDispatch\n",
  }]);
  validateProofImports(job, [{
    module: job.behaviorModule,
    source: "import Project.ProofKit.FixedArrayLtNode\n",
  }]);
  validateProofImports(job, [{
    module: job.behaviorModule,
    source: "import Project.ProofKit.FixedArrayTraversalInput\n",
  }]);
  validateProofImports(job, [{
    module: job.behaviorModule,
    source: "import Project.ProofKit.FixedArrayPairResult\n",
  }]);
  validateProofImports(job, [{
    module: job.behaviorModule,
    source: "import Project.ProofKit.FixedArrayResult\n",
  }]);
  validateProofImports(job, [{
    module: job.behaviorModule,
    source: "import Project.ProofKit.FixedArraySearch\n",
  }]);
  validateProofImports(job, [{
    module: job.behaviorModule,
    source: "import Project.ProofKit.FixedArraySingleton\n",
  }]);
  validateProofImports(job, [{
    module: job.behaviorModule,
    source: "import Project.ProofKit.FixedArraySingletonWrapper\n",
  }]);
  validateProofImports(job, [{
    module: job.behaviorModule,
    source: "import Project.ProofKit.ScalarTransitionU64\n",
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

  const proofTaskRoot = path.join(temporaryRoot, "mock-proof-journal");
  fs.mkdirSync(proofTaskRoot);
  const proofSource = `namespace ${job.namespace}.Behavior\n\ntheorem placeholder : True := by trivial\n`;
  const proofResponse = runCodexOutcome({
    codex: "/usr/bin/codex",
    task: "artifact-proof",
    stage: 5,
    taskRoot: proofTaskRoot,
    contextFiles: new Map([["PROOF_JOURNAL.md", "# Proof Journal\n\n"]]),
    candidateFile: moduleFile(job.behaviorModule),
    journalFile: "PROOF_JOURNAL.md",
    timeout: 1000,
    prompt: "mock proof prompt",
    execute: (args) => {
      const candidate = path.join(proofTaskRoot, moduleFile(job.behaviorModule));
      fs.mkdirSync(path.dirname(candidate), { recursive: true });
      fs.writeFileSync(candidate, proofSource);
      fs.writeFileSync(path.join(proofTaskRoot, "PROOF_JOURNAL.md"),
        "# Proof Journal\n\nLean accepted the direct region theorem.\n");
      const output = args[args.indexOf("-o") + 1];
      fs.writeFileSync(output, `${JSON.stringify(outcome("artifact-proof", ""))}\n`);
      return { stdout: "", stderr: "" };
    },
  });
  assert(proofResponse.source === proofSource &&
    proofResponse.proofJournal.includes("direct region theorem"),
  "mocked artifact-proof task did not return its journal");

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
  const directTelemetryCalls = [];
  const directSession = runDeterministicTaskSession({
    task: "artifact-proof",
    stage: 5,
    stageName: "artifact proof",
    sourceModule: job.behaviorModule,
    outcome: {
      ...outcome("artifact-proof", "checked source"),
      proofJournal: "# Proof Journal\n\nDirect check accepted.\n",
    },
    materialize: (source) => source,
    diagnose: () => "outer diagnostic accepted source",
    telemetry: {
      skipCodexSession: () => directTelemetryCalls.push("skip"),
      measureOuterAcceptance: (action) => {
        directTelemetryCalls.push("outer");
        return action();
      },
      accept: (sourceSha256) => {
        directTelemetryCalls.push("accepted");
        return { acceptedSourceSha256: sourceSha256 };
      },
    },
  });
  assert(directTelemetryCalls.join(",") === "outer,skip,accepted" &&
    directSession.source === "checked source" &&
    directSession.proofJournal.includes("Direct check accepted"),
  "deterministic task session did not skip Codex before outer acceptance");
  const fallbackTelemetryCalls = [];
  const fallbackSession = runDeterministicTaskSession({
    task: "artifact-proof",
    stage: 5,
    stageName: "artifact proof",
    sourceModule: job.behaviorModule,
    outcome: {
      ...outcome("artifact-proof", "incomplete source"),
      proofJournal: "# Proof Journal\n\n",
    },
    materialize: (source) => source,
    diagnose: () => null,
    telemetry: {
      skipCodexSession: () => fallbackTelemetryCalls.push("skip"),
      measureOuterAcceptance: (action) => {
        fallbackTelemetryCalls.push("outer");
        return action();
      },
      accept: () => fallbackTelemetryCalls.push("accepted"),
    },
  });
  assert(fallbackSession === null && fallbackTelemetryCalls.join(",") === "outer",
    "incomplete deterministic starter did not return control to Codex");
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

function testFixedArrayEqNodeFeatures() {
  const body = `
    .localGet 0,
    .localSet 15,
    .constI64 (3 : UInt64),
    .localSet 16,
    .localGet 16,
    .localGet 15,
    .wrapI64,
    .load64 (0 : UInt32),
    .ltUI64,
    .iff 0 1 [
      .localGet 15,
      .localGet 16,
      .constI64 (1 : UInt64),
      .mulI64,
      .constI64 (1 : UInt64),
      .addI64,
      .constI64 (8 : UInt64),
      .mulI64,
      .addI64,
      .wrapI64,
      .load64 (0 : UInt32)
    ] [
      .unreachable
    ],
    .localGet 2,
    .eqI64,
    .iff 0 1 [
      .constI64 (1 : UInt64)
    ] [
      .constI64 (0 : UInt64)
    ],
    .constI64 (0 : UInt64),
    .eqI64,
    .eqz,
    .iff 0 0 [
      .localGet 2,
      .localGet 0,
      .localSet 15,
      .constI64 (5 : UInt64),
      .localSet 16,
      .localGet 16,
      .localGet 15,
      .wrapI64,
      .load64 (0 : UInt32),
      .ltUI64,
      .iff 0 1 [
        .localGet 15,
        .localGet 16,
        .constI64 (1 : UInt64),
        .mulI64,
        .constI64 (1 : UInt64),
        .addI64,
        .constI64 (8 : UInt64),
        .mulI64,
        .addI64,
        .wrapI64,
        .load64 (0 : UInt32)
      ] [
        .unreachable
      ],
      .eqI64,
      .iff 0 1 [
        .constI64 (1 : UInt64)
      ] [
        .constI64 (0 : UInt64)
      ],
      .constI64 (0 : UInt64),
      .eqI64,
      .eqz,
      .iff 0 0 [
  `;
  const nodes = fixedArrayEqNodeFeatures(body);
  assert(JSON.stringify(nodes) === JSON.stringify([
    { offset: 10, index: 3, keyLocal: 2, order: "loaded-first" },
    { offset: 10, index: 5, keyLocal: 2, order: "key-first" },
  ]), "fixed-array equality-node extraction lost an exact emitted node");
}

function testAnnotationRecipePlan() {
  const wasm = Buffer.from([0, 97, 115, 109, 1, 0, 0, 0]);
  const document = {
    schemaVersion: 1,
    artifact: { byteLength: wasm.length },
    functions: [{
      wasmIndex: 0,
      definedFunction: 0,
      sourceName: "Example.callee",
      exports: [],
      parameters: 2,
      results: 1,
      locals: 0,
      regions: [],
    }, {
      wasmIndex: 1,
      definedFunction: 1,
      sourceName: "Example.wrapper",
      exports: ["compute"],
      parameters: 1,
      results: 1,
      locals: 6,
      regions: [{
        id: "function-1.direct-call-0",
        kind: "leanexe.call.direct.v1",
        location: { listPath: [], startIndex: 0, endIndex: 4 },
        parameters: {
          calleeIndex: 0,
          argumentLocals: [2, 4],
          resultLocals: [5],
          resultPlacement: "locals",
          continuation: "fallthrough",
        },
        generatedBy: [
          "LeanExe.Wasm.Binary.CoreWasm.emitStmt",
          "LeanExe.Wasm.Binary.CoreWasm.emitFuncInstrs",
        ],
      }],
    }],
  };
  const program = `def func0 : Wasm.Program :=
  [
  .localGet 0
]

def func0Def : Wasm.Function :=
  { params := [.i64, .i64], locals := [], body := func0, results := [.i64] }

def func1 : Wasm.Program :=
  [
  .localGet 2,
  .localGet 4,
  .call 0,
  .localSet 5,
  .localGet 5
]

def func1Def : Wasm.Function :=
  { params := [.i64], locals := [.i64], body := func1, results := [.i64] }
`;
  validateAnnotationDocument(document, wasm);
  const plan = proofRecipePlan(document, program, ["strategy.calls", "strategy.frames"]);
  assert(plan.recipes.length === 1 &&
    plan.recipes[0].direct.module === "Project.ProofKit.Control" &&
    plan.recipes[0].direct.tactic === "wp_entry_single_call" &&
    plan.recipes[0].direct.invocation.includes("func1Def") &&
    plan.recipes[0].supporting.some((item) => item.declaration === "Wasm.wp_call_tw") &&
    JSON.stringify(plan.recipes[0].guidance) ===
      JSON.stringify(["strategy.calls", "strategy.frames"]),
  "direct-call annotation did not select its direct and indirect proof recipe");
  const wrongLength = structuredClone(document);
  wrongLength.artifact.byteLength += 1;
  expectFailure(() => validateAnnotationDocument(wrongLength, wasm), /byte length differs/);
  const wrongCall = structuredClone(document);
  wrongCall.functions[1].regions[0].parameters.calleeIndex = 2;
  expectFailure(() => validateAnnotationDocument(wrongCall, wasm), /callee is outside/);

  const nested = structuredClone(document);
  nested.functions[1].regions[0].location = {
    listPath: [{ instructionIndex: 1, field: "else" }],
    startIndex: 0,
    endIndex: 4,
  };
  const nestedProgram = `def func0 : Wasm.Program :=
  [
  .localGet 0
]

def func0Def : Wasm.Function :=
  { params := [.i64, .i64], locals := [], body := func0, results := [.i64] }

def func1 : Wasm.Program :=
  [
  .constI64 (1 : UInt64),
  .iff 0 0 [
    .constI64 (0 : UInt64)
  ] [
    .localGet 2,
    .localGet 4,
    .call 0,
    .localSet 5
  ],
  .localGet 5
]

def func1Def : Wasm.Function :=
  { params := [.i64], locals := [.i64], body := func1, results := [.i64] }
`;
  assert(proofRecipePlan(nested, nestedProgram).recipes.length === 1,
    "nested direct-call annotation did not match the decoded else branch");
}

function lengthDispatchProgram(encoding, expectedSize = 21) {
  if (encoding === "le-unsigned-v1") {
    return `def func0 : Wasm.Program :=
  [
  .localGet 0,
  .localSet 10,
  .localGet 10,
  .wrapI64,
  .load64 (0 : UInt32),
  .constI64 (${expectedSize} : UInt64),
  .leUI64,
  .iff 0 0 [
    .constI64 (0 : UInt64)
  ] [
    .constI64 (1 : UInt64)
  ],
  .localGet 0
  ]

def func0Def : Wasm.Function :=
  { params := [.i64], locals := [.i64], body := func0, results := [.i64] }
`;
  }
  const normalized = encoding === "eq-normalized-v1" ? `
  .constI64 (1 : UInt64),
  .eqI64,
  .iff 0 1 [
    .constI64 (1 : UInt64)
  ] [
    .constI64 (0 : UInt64)
  ],
  .constI64 (0 : UInt64),
  .eqI64,
  .eqz,` : `
  .constI64 (0 : UInt64),
  .eqI64,
  .eqz,
  .eqz,
  .iff 0 1 [
    .constI64 (1 : UInt64)
  ] [
    .constI64 (0 : UInt64)
  ],
  .constI64 (1 : UInt64),
  .eqI64,
  .iff 0 1 [
    .constI64 (1 : UInt64)
  ] [
    .constI64 (0 : UInt64)
  ],
  .constI64 (0 : UInt64),
  .eqI64,
  .eqz,`;
  return `def func0 : Wasm.Program :=
  [
  .localGet 0,
  .localSet 10,
  .localGet 10,
  .wrapI64,
  .load64 (0 : UInt32),
  .constI64 (${expectedSize} : UInt64),
  .eqI64,
  .iff 0 1 [
    .constI64 (1 : UInt64)
  ] [
    .constI64 (0 : UInt64)
  ],${normalized}
  .iff 0 0 [
    .constI64 (0 : UInt64)
  ] [
    .constI64 (1 : UInt64)
  ],
  .localGet 0
  ]

def func0Def : Wasm.Function :=
  { params := [.i64], locals := [.i64], body := func0, results := [.i64] }
`;
}

function lengthDispatchDocument(wasm, encoding) {
  const equality = encoding === "eq-normalized-v1";
  const bounded = encoding === "le-unsigned-v1";
  return {
    schemaVersion: 1,
    artifact: { byteLength: wasm.length },
    functions: [{
      wasmIndex: 0,
      definedFunction: 0,
      sourceName: "Example.compute",
      exports: ["compute"],
      parameters: 1,
      results: 1,
      locals: 1,
      regions: [{
        id: "function-0.length-dispatch-0",
        kind: "leanexe.array.length-dispatch.v1",
        location: {
          listPath: [],
          startIndex: 0,
          endIndex: bounded ? 8 : equality ? 15 : 20,
        },
        parameters: {
          inputLocal: 10,
          expectedSize: 21,
          encoding,
          invalidBranch: equality || bounded ? "else" : "then",
          validBranch: equality || bounded ? "then" : "else",
          continuation: "fallthrough",
        },
        generatedBy: [
          "LeanExe.Wasm.Binary.CoreWasm.emitCondWithRelease",
          "LeanExe.Wasm.Binary.CoreWasm.emitStmtAnnotated",
        ],
      }],
    }],
  };
}

function testLengthDispatchAnnotationRecipes() {
  const wasm = Buffer.from([0, 97, 115, 109, 1, 0, 0, 0]);
  for (const encoding of [
    "eq-normalized-v1", "ne-normalized-v1", "le-unsigned-v1",
  ]) {
    const document = lengthDispatchDocument(wasm, encoding);
    const program = lengthDispatchProgram(encoding);
    validateAnnotationDocument(document, wasm);
    const plan = proofRecipePlan(document, program, ["strategy.arrays", "strategy.frames"]);
    validateProofRecipePlan(plan, document);
    const equality = encoding === "eq-normalized-v1";
    const bounded = encoding === "le-unsigned-v1";
    const expectedTheorem = bounded ? "leProgram_spec" :
      equality ? "eqProgram_spec" : "program_spec";
    const expectedTactic = bounded ? "wp_fixed_array_length_le_dispatch" :
      equality ? "wp_fixed_array_length_eq_dispatch" : "wp_fixed_array_length_dispatch";
    assert(plan.recipes.length === 1 &&
      plan.recipes[0].direct.theorem.endsWith(expectedTheorem) &&
      plan.recipes[0].direct.tactic === expectedTactic &&
      JSON.stringify(plan.recipes[0].guidance) ===
        JSON.stringify(["strategy.arrays", "strategy.frames"]),
    `${encoding} did not select its exact length-dispatch recipe`);

    const wrongSize = structuredClone(document);
    wrongSize.functions[0].regions[0].parameters.expectedSize = 15;
    expectFailure(() => proofRecipePlan(wrongSize, program), /do not match/);

    if (bounded) {
      const wrongComparison = program.replace(".leUI64,", ".ltUI64,");
      expectFailure(() => proofRecipePlan(document, wrongComparison), /do not match/);
    } else {
      const wrongBooleanBranch = program.replace(
        ".constI64 (1 : UInt64)\n  ] [",
        ".constI64 (2 : UInt64)\n  ] [");
      expectFailure(() => proofRecipePlan(document, wrongBooleanBranch),
        /Boolean-normalization then branch does not match/);
    }
  }
  const invalidEncoding = lengthDispatchDocument(wasm, "eq-normalized-v1");
  invalidEncoding.functions[0].regions[0].parameters.encoding = "unknown";
  expectFailure(() => validateAnnotationDocument(invalidEncoding, wasm),
    /encoding is unsupported/);
}

function testMapAddAnnotationRecipe() {
  const wasm = fs.readFileSync(path.join(repoRoot, "demos/demo-4/program.wasm"));
  const program = `def func0 : Wasm.Program :=
  [
  .localGet 0,
  .iff 0 0 [] [],
  .localGet 4
  ]

def func0Def : Wasm.Function :=
  { params := [.i64], locals := [.i64], body := func0, results := [.i64] }
`;
  const document = {
    schemaVersion: 1,
    artifact: { byteLength: wasm.length },
    functions: [{
      wasmIndex: 0,
      definedFunction: 0,
      sourceName: "Example.compute",
      exports: ["compute"],
      parameters: 1,
      results: 1,
      locals: 16,
      regions: [{
        id: "function-0.map-add-0",
        kind: "leanexe.array.map-add.v1",
        location: { listPath: [], startIndex: 0, endIndex: 3 },
        parameters: {
          maximumSize: 8,
          addend: "1",
          continuation: "function-return",
        },
        generatedBy: ["LeanExe.Wasm.Binary.CoreWasm.emitFuncAnnotated"],
      }],
    }],
  };
  validateAnnotationDocument(document, wasm);
  const plan = proofRecipePlan(document, program, [
    "strategy.arrays", "strategy.loops", "strategy.allocation", "strategy.frames",
  ], "Example.Generated.AnnotationMatches");
  validateProofRecipePlan(plan, document);
  assert(plan.recipes.length === 1 &&
    plan.recipes[0].direct.module === "Project.ProofKit.FixedArrayMapAdd" &&
    plan.recipes[0].direct.theorem.endsWith("wrapperProgram_spec") &&
    plan.recipes[0].direct.program.endsWith("wrapperProgram 8 1"),
  "map-add annotation did not select the complete wrapper theorem");
  const source = annotationMatchesSource(document, {
    namespace: "Example.Generated",
    programModule: "Example.Generated.Program",
  }).source;
  assert(source.includes("import Project.ProofKit.FixedArrayMapAdd") &&
    source.includes("FixedArrayMapAdd.wrapperProgram\n          8 1"),
  "annotation matches omitted the checked map-add wrapper equality");
  const starter = artifactProofStarter(makeJob("bounded wrapping map\n"), 0, true, plan);
  assert(starter.includes("FixedArrayMapAdd.wrapperProgram_spec 8 1") &&
    starter.includes("FixedArrayMapAdd.expected 8 1 input") &&
    starter.includes("function_0_map_add_0_eq") &&
    !starter.includes("have hLengthRead"),
  "map-add recipe did not select the complete semantic starter");

  const invalidAddend = structuredClone(document);
  invalidAddend.functions[0].regions[0].parameters.addend = "01";
  expectFailure(() => validateAnnotationDocument(invalidAddend, wasm),
    /canonical UInt64 decimal/);
  const truncated = program.replace("  .localGet 4\n  ]", "  .localGet 3\n  ]");
  expectFailure(() => proofRecipePlan(document, truncated), /boundary does not match/);
}

function testFilterLtAnnotationRecipe() {
  const wasm = fs.readFileSync(path.join(repoRoot, "demos/demo-5/program.wasm"));
  const program = `def func0 : Wasm.Program :=
  [
  .localGet 0,
  .iff 0 0 [] [],
  .localGet 4
  ]

def func0Def : Wasm.Function :=
  { params := [.i64], locals := [.i64], body := func0, results := [.i64] }
`;
  const document = {
    schemaVersion: 1,
    artifact: { byteLength: wasm.length },
    functions: [{
      wasmIndex: 0,
      definedFunction: 0,
      sourceName: "Example.compute",
      exports: ["compute"],
      parameters: 1,
      results: 1,
      locals: 21,
      regions: [{
        id: "function-0.filter-lt-0",
        kind: "leanexe.array.filter-lt.v1",
        location: { listPath: [], startIndex: 0, endIndex: 3 },
        parameters: {
          maximumSize: 8,
          threshold: "100",
          continuation: "function-return",
        },
        generatedBy: ["LeanExe.Wasm.Binary.CoreWasm.emitFuncAnnotated"],
      }],
    }],
  };
  validateAnnotationDocument(document, wasm);
  const plan = proofRecipePlan(document, program, [
    "strategy.arrays", "strategy.loops", "strategy.allocation", "strategy.frames",
  ], "Example.Generated.AnnotationMatches");
  validateProofRecipePlan(plan, document);
  assert(plan.recipes.length === 1 &&
    plan.recipes[0].direct.module === "Project.ProofKit.FixedArrayFilterLt" &&
    plan.recipes[0].direct.theorem.endsWith("wrapperProgram_spec") &&
    plan.recipes[0].direct.program.endsWith("wrapperProgram 8 100"),
  "filter-lt annotation did not select the complete wrapper theorem");
  const source = annotationMatchesSource(document, {
    namespace: "Example.Generated",
    programModule: "Example.Generated.Program",
  }).source;
  assert(source.includes("import Project.ProofKit.FixedArrayFilterLt") &&
    source.includes("FixedArrayFilterLt.wrapperProgram\n          8 100"),
  "annotation matches omitted the checked filter-lt wrapper equality");
  const job = makeJob("bounded stable filter\n");
  const starter = artifactProofStarter(job, 0, true, plan);
  assert(starter.includes("FixedArrayFilterLt.wrapperProgram_spec 8 100") &&
    starter.includes("FixedArrayFilterLt.expected 8 100 input") &&
    starter.includes("FixedArrayFilterLt.heapReserveBytes 8 input") &&
    starter.includes("function_0_filter_lt_0_eq") &&
    !starter.includes("have hLengthRead"),
  "filter-lt recipe did not select the complete semantic starter");
  const legacyStarter = artifactProofStarter(job, 0, true, plan, 1);
  assert(!legacyStarter.includes("FixedArrayFilterLt.wrapperProgram_spec") &&
    legacyStarter.includes("have hLengthRead"),
  "filter-lt recipe bypassed the schema-6 resource precondition");

  const invalidThreshold = structuredClone(document);
  invalidThreshold.functions[0].regions[0].parameters.threshold = "0100";
  expectFailure(() => validateAnnotationDocument(invalidThreshold, wasm),
    /canonical UInt64 decimal/);
  const truncated = program.replace("  .localGet 4\n  ]", "  .localGet 3\n  ]");
  expectFailure(() => proofRecipePlan(document, truncated), /boundary does not match/);
}

function testLoopAnnotationRecipes() {
  const wasm = Buffer.from([0, 97, 115, 109, 1, 0, 0, 0]);
  const whileProgram = `def func0 : Wasm.Program :=
  [
  .constI64 (0 : UInt64),
  .localSet 3,
  .block 0 0 [
    .loop 0 0 [
      .localGet 0,
      .constI64 (0 : UInt64),
      .eqI64,
      .eqz,
      .br_if 1,
      .localGet 1,
      .localSet 2,
      .br 0
    ]
  ],
  .localGet 2
]

def func0Def : Wasm.Function :=
  { params := [.i64], locals := [.i64, .i64, .i64], body := func0, results := [.i64] }
`;
  const whileDocument = {
    schemaVersion: 1,
    artifact: { byteLength: wasm.length },
    functions: [{
      wasmIndex: 0,
      definedFunction: 0,
      sourceName: "Example.loop",
      exports: [],
      parameters: 1,
      results: 1,
      locals: 3,
      regions: [{
        id: "function-0.while-loop-0",
        kind: "leanexe.loop.while.v1",
        location: { listPath: [], startIndex: 2, endIndex: 3 },
        parameters: {
          condition: "Cond.eqU64 (Expr.local 0) (Expr.u64 0)",
          body: "Stmt.assign 2 (Expr.local 1)",
          descriptorVersion: 1,
          descriptor: {
            condition: {
              kind: "eq",
              left: { kind: "get", index: 0 },
              right: { kind: "const", value: "0" },
            },
            body: {
              kind: "assign",
              index: 2,
              value: { kind: "get", index: 1 },
            },
          },
          scratchStart: 4,
          continuation: "fallthrough",
        },
        generatedBy: ["LeanExe.Wasm.Binary.CoreWasm.emitStmtAnnotated"],
      }],
    }],
  };
  const selectedWhile = selectAnnotationRegions(
    whileDocument, ["function-0.while-loop-0"]);
  assert(selectedWhile.functions[0].regions.length === 1 &&
    selectedWhile.functions[0].regions[0].id === "function-0.while-loop-0" &&
    selectedWhile !== whileDocument,
  "annotation region selection did not preserve the requested region");
  expectFailure(() => selectAnnotationRegions(whileDocument, ["missing"]),
    /does not exist/);
  validateAnnotationDocument(whileDocument, wasm);
  const whilePlan = proofRecipePlan(whileDocument, whileProgram, [
    "strategy.loops", "strategy.frames", "strategy.arithmetic",
  ]);
  validateProofRecipePlan(whilePlan, whileDocument);
  assert(whilePlan.recipes.length === 1 &&
    whilePlan.recipes[0].direct.theorem ===
      "Project.ProofKit.ScalarTransition.whileProgram_spec" &&
    whilePlan.recipes[0].direct.regionEquality ===
      "Project.AnnotationMatches.function_0_while_loop_0_eq" &&
    whilePlan.recipes[0].supporting.some((entry) => entry.declaration ===
      "Project.AnnotationMatches.function_0_while_loop_0_terminates_with_of_loop") &&
    whilePlan.recipes[0].supporting.some((entry) => entry.declaration ===
      "Project.AnnotationMatches.function_0_while_loop_0_entry_to_loop") &&
    whilePlan.recipes[0].supporting.some((entry) => entry.declaration ===
      "Project.ProofKit.ScalarTransition.Stmt.eval_preserves_below") &&
    whilePlan.recipes[0].guidance.length === 3,
  "while descriptor did not select the checked scalar loop recipe");
  const whileMatches = annotationMatchesSource(whileDocument, {
    namespace: "Example.Generated",
    programModule: "Example.Generated.Artifact",
  }, whileProgram);
  assert(whileMatches.source.includes("def function_0_while_loop_0_condition") &&
    whileMatches.source.includes("ScalarTransition.whileProgram") &&
    whileMatches.source.includes("import Project.ProofKit.ScalarTransitionU64") &&
    whileMatches.source.includes("function_0_while_loop_0_condition_evalU64") &&
    whileMatches.source.includes("function_0_while_loop_0_body_evalU64") &&
    whileMatches.source.includes("function_0_while_loop_0_condition_eval") &&
    whileMatches.source.includes("function_0_while_loop_0_body_eval") &&
    whileMatches.source.includes("theorem function_0_while_loop_0_entry_to_loop") &&
    whileMatches.source.includes("theorem function_0_while_loop_0_terminates_with_of_loop") &&
    whileMatches.source.includes("initial [.i64 v0] P") &&
    whileMatches.source.includes("function_0_while_loop_0_state (v0) ((0 : UInt64))") &&
    whileMatches.source.includes("    4 function_0_while_loop_0_condition") &&
    whileMatches.source.includes("theorem function_0_while_loop_0_eq"),
  "while descriptor did not produce the checked region equality");
  expectFailure(() => proofRecipePlan(
    whileDocument, whileProgram.replace("      .br 0", "      .br 1")), /back edge/);
  const malformedWhile = structuredClone(whileDocument);
  malformedWhile.functions[0].regions[0].parameters.descriptor.condition.kind = "gt-u";
  expectFailure(() => validateAnnotationDocument(malformedWhile, wasm), /unsupported/);
  const wrongDescriptorVersion = structuredClone(whileDocument);
  wrongDescriptorVersion.functions[0].regions[0].parameters.descriptorVersion = 2;
  expectFailure(() => validateAnnotationDocument(wrongDescriptorVersion, wasm), /unsupported/);
  const unreifiedWhile = structuredClone(whileDocument);
  unreifiedWhile.functions[0].regions[0].parameters.descriptor = null;
  validateAnnotationDocument(unreifiedWhile, wasm);
  const unreifiedPlan = proofRecipePlan(unreifiedWhile, whileProgram);
  validateProofRecipePlan(unreifiedPlan, unreifiedWhile);
  assert(unreifiedPlan.recipes[0].direct.theorem === "Wasm.wp_loop_cons",
    "unreified while did not retain the generic loop recipe");

  const postTestProgram = `def func0 : Wasm.Program :=
  [
  .localGet 0,
  .localSet 1,
  .constI64 (0 : UInt64),
  .localSet 5,
  .block 0 0 [
    .loop 0 0 [
      .localGet 1,
      .constI64 (1 : UInt64),
      .subI64,
      .localSet 1,
      .localGet 2,
      .constI64 (1 : UInt64),
      .addI64,
      .localSet 2,
      .localGet 1,
      .constI64 (5 : UInt64),
      .neI64,
      .br_if 1,
      .br 0
    ]
  ],
  .localGet 1,
  .localSet 2,
  .localGet 2
]

def func0Def : Wasm.Function :=
  { params := [.i64], locals := [.i64, .i64, .i64, .i64, .i64], body := func0,
    results := [.i64] }
`;
  const postTestDocument = {
    schemaVersion: 1,
    artifact: { byteLength: wasm.length },
    functions: [{
      wasmIndex: 0,
      definedFunction: 0,
      sourceName: "Example.postTest",
      exports: [],
      parameters: 1,
      results: 1,
      locals: 5,
      regions: [{
        id: "function-0.scalar-post-test-loop-0",
        kind: "leanexe.loop.scalar-post-test.v1",
        location: { listPath: [], startIndex: 4, endIndex: 5 },
        parameters: {
          resultWidth: 1,
          accumulatorStart: 1,
          accumulatorLocals: [1],
          initialValues: ["LeanExe.IR.Expr.local 0"],
          resultSlot: 0,
          destination: 2,
          releaseOffsets: [],
          descriptorVersion: 1,
          descriptor: {
            condition: {
              kind: "ne",
              left: { kind: "get", index: 1 },
              right: { kind: "const", value: "5" },
            },
            body: {
              kind: "seq",
              first: {
                kind: "assign",
                index: 1,
                value: {
                  kind: "bin",
                  operation: "sub",
                  left: { kind: "get", index: 1 },
                  right: { kind: "const", value: "1" },
                },
              },
              second: {
                kind: "assign",
                index: 2,
                value: {
                  kind: "bin",
                  operation: "add",
                  left: { kind: "get", index: 2 },
                  right: { kind: "const", value: "1" },
                },
              },
            },
          },
          scratchStart: 5,
          continuation: "fallthrough",
        },
        generatedBy: ["LeanExe.Wasm.Binary.CoreWasm.scalarPostTestLoopInStmt?"],
      }],
    }],
  };
  validateAnnotationDocument(postTestDocument, wasm);
  const postTestPlan = proofRecipePlan(
    postTestDocument, postTestProgram, ["strategy.loops", "strategy.frames"]);
  validateProofRecipePlan(postTestPlan, postTestDocument);
  assert(postTestPlan.recipes[0].direct.theorem ===
      "Project.ProofKit.ScalarTransition.postTestProgram_spec" &&
    postTestPlan.recipes[0].supporting.some((entry) => entry.declaration ===
      "Project.ProofKit.ScalarTransition.postTestProgram_spec") &&
    postTestPlan.recipes[0].supporting.some((entry) => entry.declaration ===
      "Project.ProofKit.ScalarTransition.State.localU64ToNat") &&
    postTestPlan.recipes[0].supporting.some((entry) => entry.declaration ===
      "Project.ProofKit.ScalarTransition.U64Op.apply") &&
    postTestPlan.recipes[0].supporting.some((entry) => entry.declaration ===
      "Project.ProofKit.ScalarTransition.CounterTransition.decrement_toNat_lt") &&
    postTestPlan.recipes[0].supporting.some((entry) => entry.declaration ===
      "Project.ProofKit.ScalarTransition.CounterTransition.decrement_add_increment") &&
    !postTestPlan.recipes[0].supporting.some((entry) => entry.declaration ===
      "Project.ProofKit.ScalarTransition.whileProgram_spec"),
  "scalar post-test annotation did not select its checked composition theorem");
  const postTestMatches = annotationMatchesSource(postTestDocument, {
    namespace: "Example.Generated",
    programModule: "Example.Generated.Artifact",
  }, postTestProgram);
  assert(postTestMatches.source.includes("ScalarTransition.postTestProgram") &&
    postTestMatches.source.includes(".ne (.get 1) (.const (5 : UInt64))") &&
    postTestMatches.source.includes("function_0_scalar_post_test_loop_0_entry_to_loop") &&
    postTestMatches.source.includes("function_0_scalar_post_test_loop_0_body_eval") &&
    postTestMatches.source.includes("function_0_scalar_post_test_loop_0_eq"),
  "scalar post-test descriptor did not produce checked generated declarations");
  expectFailure(() => proofRecipePlan(postTestDocument,
    postTestProgram.replace("      .br_if 1", "      .br_if 2")), /back edge/);

  const foldProgram = `def func0 : Wasm.Program :=
  [
  .constI64 (7 : UInt64),
  .localSet 1,
  .constI64 (0 : UInt64),
  .localSet 6,
  .block 0 0 [
    .loop 0 0 [
      .localGet 1,
      .localSet 5,
      .localGet 5,
      .localSet 1,
      .constI64 (1 : UInt64),
      .localSet 6,
      .localGet 4,
      .constI64 (0 : UInt64),
      .eqI64,
      .eqz,
      .br_if 1,
      .br 0
    ]
  ],
  .localGet 1,
  .localSet 7,
  .localGet 7
]

def func0Def : Wasm.Function :=
  { params := [.i64], locals := [.i64, .i64, .i64], body := func0, results := [.i64] }
`;
  const foldDocument = {
    schemaVersion: 1,
    artifact: { byteLength: wasm.length },
    functions: [{
      wasmIndex: 0,
      definedFunction: 0,
      sourceName: "Example.fold",
      exports: [],
      parameters: 1,
      results: 1,
      locals: 7,
      regions: [{
        id: "function-0.loop-fold-0",
        kind: "leanexe.loop.fold.v1",
        location: { listPath: [], startIndex: 0, endIndex: 7 },
        parameters: {
          resultWidth: 1,
          accumulatorStart: 1,
          accumulatorLocals: [1],
          initialValues: ["Expr.u64 7"],
          bodyValues: ["Expr.local 1"],
          bodyLets: [],
          doneValue: "Expr.local 4",
          releaseOffsets: [],
          scratchStart: 4,
          doneLocal: 4,
          stagedValueStart: 5,
          releaseReadyLocal: 6,
          resultLocals: [7],
          continuation: "function-results",
        },
        generatedBy: ["LeanExe.Wasm.Binary.CoreWasm.emitLoopFoldMultiSlotAssign"],
      }],
    }],
  };
  validateAnnotationDocument(foldDocument, wasm);
  const foldPlan = proofRecipePlan(foldDocument, foldProgram, ["strategy.loops"]);
  validateProofRecipePlan(foldPlan, foldDocument);
  assert(foldPlan.recipes.length === 1 &&
    foldPlan.recipes[0].direct.module === "Project.ProofKit.Control",
  "loop-fold annotation did not select the generic loop recipe");
  const wrongAccumulator = structuredClone(foldDocument);
  wrongAccumulator.functions[0].regions[0].parameters.accumulatorLocals = [2];
  expectFailure(() => validateAnnotationDocument(wrongAccumulator, wasm), /must be consecutive/);
}

function testLessThanNodeAnnotationRecipes() {
  const wasm = Buffer.from([0, 97, 115, 109, 1, 0, 0, 0]);
  const document = {
    schemaVersion: 1,
    artifact: { byteLength: wasm.length },
    functions: [{
      wasmIndex: 0,
      definedFunction: 0,
      sourceName: "Example.compute",
      exports: ["compute"],
      parameters: 1,
      results: 1,
      locals: 24,
      regions: [{
        id: "function-0.lt-node-0",
        kind: "leanexe.array.lt-node.v1",
        location: {
          listPath: [{ instructionIndex: 16, field: "else" }],
          startIndex: 0,
          endIndex: 13,
        },
        parameters: {
          offset: 10,
          index: 3,
          keyLocal: 2,
          operandOrder: "key-first",
          comparison: "key-lt-element-v1",
          lessBranch: "then",
          notLessBranch: "else",
          continuation: "fallthrough",
        },
        generatedBy: ["LeanExe.Wasm.Binary.CoreWasm.annotateFixedArrayLtNodesInList"],
      }, {
        id: "function-0.eq-node-0",
        kind: "leanexe.array.eq-node.v1",
        location: { listPath: [], startIndex: 0, endIndex: 17 },
        parameters: {
          offset: 10,
          index: 1,
          keyLocal: 2,
          operandOrder: "key-first",
          equalBranch: "then",
          unequalBranch: "else",
          continuation: "fallthrough",
        },
        generatedBy: ["LeanExe.Wasm.Binary.CoreWasm.annotateFixedArrayEqNodesInList"],
      }],
    }],
  };
  const program = `def func0 : Wasm.Program :=
  [
  .localGet 2,
  .localGet 0,
  .localSet 15,
  .constI64 (1 : UInt64),
  .localSet 16,
  .localGet 16,
  .localGet 15,
  .wrapI64,
  .load64 (0 : UInt32),
  .ltUI64,
  .iff 0 1 [
    .localGet 15,
    .localGet 16,
    .constI64 (1 : UInt64),
    .mulI64,
    .constI64 (1 : UInt64),
    .addI64,
    .constI64 (8 : UInt64),
    .mulI64,
    .addI64,
    .wrapI64,
    .load64 (0 : UInt32)
  ] [
    .unreachable
  ],
  .eqI64,
  .iff 0 1 [
    .constI64 (1 : UInt64)
  ] [
    .constI64 (0 : UInt64)
  ],
  .constI64 (0 : UInt64),
  .eqI64,
  .eqz,
  .iff 0 0 [
    .constI64 (1 : UInt64)
  ] [
    .localGet 2,
    .localGet 0,
    .localSet 15,
    .constI64 (3 : UInt64),
    .localSet 16,
    .localGet 16,
    .localGet 15,
    .wrapI64,
    .load64 (0 : UInt32),
    .ltUI64,
    .iff 0 1 [
      .localGet 15,
      .localGet 16,
      .constI64 (1 : UInt64),
      .mulI64,
      .constI64 (1 : UInt64),
      .addI64,
      .constI64 (8 : UInt64),
      .mulI64,
      .addI64,
      .wrapI64,
      .load64 (0 : UInt32)
    ] [
      .unreachable
    ],
    .ltUI64,
    .iff 0 0 [
      .constI64 (2 : UInt64)
    ] [
      .constI64 (3 : UInt64)
    ]
  ]
  ]

def func0Def : Wasm.Function :=
  { params := [.i64], locals := [.i64], body := func0, results := [.i64] }
`;
  validateAnnotationDocument(document, wasm);
  const plan = proofRecipePlan(document, program, ["strategy.arrays", "strategy.frames"]);
  validateProofRecipePlan(plan, document);
  assert(JSON.stringify(plan.recipes.map((recipe) => recipe.regionId)) ===
      JSON.stringify(["function-0.eq-node-0", "function-0.lt-node-0"]) &&
    plan.recipes[1].direct.theorem ===
      "Project.ProofKit.FixedArrayLtNode.program_spec" &&
    plan.recipes[1].direct.tactic === "wp_fixed_array_lt_node",
  "nested comparison annotations did not produce structural recipe order");

  const wrongShape = structuredClone(document);
  wrongShape.functions[0].regions[0].parameters.comparison = "element-lt-key-v1";
  expectFailure(() => validateAnnotationDocument(wrongShape, wasm),
    /invalid less-than-node shape/);
  const wrongProgram = program.replace(
    "    .ltUI64,\n    .iff 0 0 [",
    "    .eqI64,\n    .iff 0 0 [");
  expectFailure(() => proofRecipePlan(document, wrongProgram),
    /do not match the less-than-node annotation/);
}

function testSearchTreeComposition() {
  const document = {
    schemaVersion: 1,
    artifact: { byteLength: 8 },
    functions: [{
      wasmIndex: 0,
      regions: [{
        id: "function-0.eq-node-0",
        kind: "leanexe.array.eq-node.v1",
        location: { listPath: [], startIndex: 0, endIndex: 17 },
        parameters: {
          offset: 10,
          index: 1,
          keyLocal: 2,
          operandOrder: "key-first",
        },
      }, {
        id: "function-0.pair-result-0",
        kind: "leanexe.array.pair-result.v1",
        location: {
          listPath: [{ instructionIndex: 16, field: "then" }],
          startIndex: 0,
          endIndex: 80,
        },
        parameters: {
          destination: 3,
          inputIndex: 2,
          mode: "input-index-and-one-v1",
          offset: 10,
          secondValue: "1",
        },
      }, {
        id: "function-0.pair-result-1",
        kind: "leanexe.array.pair-result.v1",
        location: {
          listPath: [{ instructionIndex: 16, field: "else" }],
          startIndex: 0,
          endIndex: 71,
        },
        parameters: {
          destination: 4,
          firstValue: "0",
          mode: "constants-v1",
          offset: 10,
          secondValue: "0",
        },
      }],
    }],
  };
  const compositions = fixedArraySearchTreeCompositions(document);
  assert(compositions.length === 1 &&
    compositions[0].tree === ".leaf 1 2 3 4" &&
    compositions[0].name === "function_0_search_tree_0",
  "fixed search-tree composition did not recover a complete leaf");
  const chainDocument = structuredClone(document);
  chainDocument.functions[0].regions[0].parameters.operandOrder = "loaded-first";
  const chains = fixedArraySearchChainCompositions(chainDocument);
  assert(chains.length === 1 && chains[0].chain === ".last 1 2 3 4" &&
    chains[0].name === "function_0_search_chain_0",
  "fixed search-chain composition did not recover a complete last node");
  const source = annotationMatchesSource(document, {
    namespace: "Example.Generated",
    programModule: "Example.Generated.Program",
  }).source;
  assert(source.includes("import Project.ProofKit.FixedArraySearchTree") &&
    source.includes("set_option maxRecDepth 1048576") &&
    source.includes("def function_0_search_tree_0") &&
    source.includes("function_0_search_tree_0.program 10 2"),
  "annotation matches omitted the checked fixed search-tree descriptor");
  const chainSource = annotationMatchesSource(chainDocument, {
    namespace: "Example.Generated",
    programModule: "Example.Generated.Program",
  }).source;
  assert(chainSource.includes("import Project.ProofKit.FixedArraySearchChain") &&
    chainSource.includes("def function_0_search_chain_0") &&
    chainSource.includes("function_0_search_chain_0.program 10 2"),
  "annotation matches omitted the checked fixed search-chain descriptor");

  const wrapperDocument = structuredClone(document);
  const validPath = [{ instructionIndex: 19, field: "else" }];
  wrapperDocument.functions[0].regions[0].location = {
    listPath: validPath,
    startIndex: 11,
    endIndex: 28,
  };
  wrapperDocument.functions[0].regions[1].location.listPath = [
    ...validPath, { instructionIndex: 27, field: "then" },
  ];
  wrapperDocument.functions[0].regions[2].location.listPath = [
    ...validPath, { instructionIndex: 27, field: "else" },
  ];
  wrapperDocument.functions[0].regions.unshift({
    id: "function-0.length-dispatch-0",
    kind: "leanexe.array.length-dispatch.v1",
    location: { listPath: [], startIndex: 0, endIndex: 20 },
    parameters: {
      continuation: "fallthrough",
      encoding: "ne-normalized-v1",
      expectedSize: 3,
      inputLocal: 15,
      invalidBranch: "then",
      validBranch: "else",
    },
  }, {
    id: "function-0.search-key-0",
    kind: "leanexe.array.search-key.v1",
    location: { listPath: validPath, startIndex: 0, endIndex: 11 },
    parameters: {
      continuation: "fallthrough",
      index: 0,
      keyLocal: 2,
      offset: 10,
    },
  }, {
    id: "function-0.pair-result-invalid",
    kind: "leanexe.array.pair-result.v1",
    location: {
      listPath: [{ instructionIndex: 19, field: "then" }],
      startIndex: 0,
      endIndex: 71,
    },
    parameters: {
      destination: 1,
      firstValue: "0",
      mode: "constants-v1",
      offset: 10,
      secondValue: "0",
    },
  });
  const instructions = (count, indentation) => Array.from(
    { length: count }, () => `${indentation}.constI64 (0 : UInt64),`).join("\n");
  const wrapperProgram = `def func0 : Wasm.Program :=
  [
${instructions(19, "  ")}
  .iff 0 0 [
${instructions(71, "    ")}
  ] [
${instructions(27, "    ")}
    .iff 0 0 [
      .constI64 (0 : UInt64)
    ] [
      .constI64 (0 : UInt64)
    ]
  ],
  .localGet 14
  ]

def func0Def : Wasm.Function :=
  { params := [.i64], locals := [], body := func0, results := [.i64] }
`;
  const wrapperCompositions = fixedArraySearchTreeCompositions(
    wrapperDocument, wrapperProgram);
  assert(wrapperCompositions.length === 1 &&
    JSON.stringify(wrapperCompositions[0].wrapper) === JSON.stringify({
      expectedSize: 3,
      inputLocal: 15,
      invalidDestination: 1,
      keyIndex: 0,
      keyLocal: 2,
      offset: 10,
    }),
  "complete fixed search wrapper did not produce wrapper parameters");
}

function testPairResultAnnotationRecipes() {
  const wasm = Buffer.from([0, 97, 115, 109, 1, 0, 0, 0]);
  const document = {
    schemaVersion: 1,
    artifact: { byteLength: wasm.length },
    functions: [{
      wasmIndex: 0,
      definedFunction: 0,
      sourceName: "Example.compute",
      exports: ["compute"],
      parameters: 1,
      results: 1,
      locals: 24,
      regions: [{
        id: "function-0.pair-result-0",
        kind: "leanexe.array.pair-result.v1",
        location: { listPath: [], startIndex: 0, endIndex: 2 },
        parameters: {
          offset: 10,
          mode: "constants-v1",
          firstValue: "0",
          secondValue: "0",
          inputIndex: null,
          destination: 3,
          continuation: "fallthrough",
        },
        generatedBy: ["LeanExe.Wasm.Binary.CoreWasm.emitStmtAnnotated"],
      }],
    }],
  };
  const program = `def func0 : Wasm.Program :=
  [
  .constI64 (8 : UInt64),
  .localSet 14
  ]

def func0Def : Wasm.Function :=
  { params := [.i64], locals := [.i64], body := func0, results := [.i64] }
`;
  validateAnnotationDocument(document, wasm);
  const namespace = "LeanExeGen.GeneratedTest.AnnotationMatches";
  const plan = proofRecipePlan(
    document, program, ["strategy.arrays", "strategy.frames"], namespace);
  validateProofRecipePlan(plan, document);
  assert(plan.recipes[0].direct.theorem ===
      "Project.ProofKit.FixedArrayPairResult.constResultProgram_spec" &&
    plan.recipes[0].direct.regionEquality ===
      `${namespace}.function_0_pair_result_0_eq`,
  "pair-result annotation did not select its checked theorem and region equality");
  const job = {
    namespace: "LeanExeGen.GeneratedTest",
    programModule: "LeanExeGen.GeneratedTest.Program",
  };
  const matches = annotationMatchesSource(document, job);
  assert(matches.module === namespace &&
    matches.source.includes("constResultProgram 0 0 3") &&
    matches.source.includes("function_0_pair_result_0_eq") &&
    matches.source.includes("  rfl"),
  "pair-result annotation did not generate its checked Lean equality");

  const invalid = structuredClone(document);
  invalid.functions[0].regions[0].parameters.firstValue = null;
  expectFailure(() => validateAnnotationDocument(invalid, wasm),
    /firstValue must be a trimmed/);
  expectFailure(() => proofRecipePlan(document,
    program.replace(".localSet 14", ".localSet 13"), [], namespace),
  /pair-result boundary does not match/);
}

function testSingletonWrapperComposition() {
  const packageRoot = path.join(
    repoRoot, "benchmarks", "leanexegen", "demo1-array", "scalar-calls-control-1",
    "program.proof");
  const document = JSON.parse(fs.readFileSync(
    path.join(packageRoot, "program.annotations.json"), "utf8"));
  const program = fs.readFileSync(path.join(
    packageRoot, "proof", "LeanExeGen", "GeneratedRbade8cb1a4e3a423", "Program.lean"),
  "utf8");
  const compositions = fixedArraySingletonWrapperCompositions(document, program);
  assert(compositions.length === 1 &&
    compositions[0].functionIndex === 2 && compositions[0].calleeIndex === 1,
  "singleton wrapper composition did not match the frozen Demo 1 entry function");
  const namespace = "LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches";
  const plan = proofRecipePlan(document, program, [], namespace);
  validateProofRecipePlan(plan, document);
  assert(plan.compositions.length === 1 &&
    plan.compositions[0].kind === "fixed-array-singleton-wrapper-v1" &&
    plan.compositions[0].calleeIndex === 1 &&
    plan.compositions[0].direct.theorem ===
      "Project.ProofKit.FixedArraySingletonWrapper.wrapperProgram_spec",
  "singleton wrapper composition did not select the complete theorem");
  const changedCallee = structuredClone(plan);
  changedCallee.compositions[0].calleeIndex = 0;
  expectFailure(() => validateProofRecipePlan(changedCallee, document),
    /calleeIndex does not identify the checked wrapper call/);
  const source = annotationMatchesSource(document, {
    namespace: "LeanExeGen.GeneratedRbade8cb1a4e3a423",
    programModule: "LeanExeGen.GeneratedRbade8cb1a4e3a423.Program",
  }, program).source;
  assert(source.includes("import Project.ProofKit.FixedArraySingletonWrapper") &&
    source.includes("function_2_singleton_wrapper_0_eq") &&
    source.includes("FixedArraySingletonWrapper.wrapperProgram\n    1"),
  "annotation matches omitted the singleton wrapper equality");
  const changed = program.replace(
    "    .localGet 3,\n    .localSet 4\n  ] [",
    "    .localGet 3,\n    .localSet 3\n  ] [");
  assert(changed !== program &&
    fixedArraySingletonWrapperCompositions(document, changed).length === 0,
  "singleton wrapper composition accepted a changed result-local assignment");
}

function testScalarTransitionSpecialization() {
  const packageRoot = path.join(
    repoRoot, "benchmarks", "leanexegen", "demo1-array", "scalar-only-1",
    "program.proof");
  const document = JSON.parse(fs.readFileSync(
    path.join(packageRoot, "program.annotations.json"), "utf8"));
  const program = fs.readFileSync(path.join(
    packageRoot, "proof", "LeanExeGen", "GeneratedRbade8cb1a4e3a423", "Program.lean"),
  "utf8");
  const selected = selectAnnotationRegions(document, ["function-0.while-loop-0"]);
  const source = annotationMatchesSource(selected, {
    namespace: "LeanExeGen.GeneratedRbade8cb1a4e3a423",
    programModule: "LeanExeGen.GeneratedRbade8cb1a4e3a423.Program",
  }, program).source;
  assert((source.match(/\bby_cases\b/g) ?? []).length === 5 &&
    source.includes("function_0_while_loop_0_bodyTransition") &&
    source.includes("U64Op.apply .remU (v1) (v2)") &&
    source.includes("theorem function_0_while_loop_0_entry_to_loop") &&
    source.includes("theorem function_0_while_loop_0_terminates_with_of_loop") &&
    source.includes("initial [.i64 v3, .i64 v2, .i64 v1, .i64 v0] P") &&
    source.includes("func0Def.toLocals [.i64 v0, .i64 v1, .i64 v2, .i64 v3]"),
  "scalar transition specialization did not retain Demo 1's five semantic tests");
}

function testCounterTransferIdentitySummary() {
  const packageRoot = path.join(
    repoRoot, "benchmarks", "leanexegen", "demo7-counter-transfer", "ltg-final-1");
  const document = JSON.parse(fs.readFileSync(
    path.join(packageRoot, "program.annotations.json"), "utf8"));
  const program = fs.readFileSync(path.join(
    packageRoot, "proof", "LeanExeGen", "GeneratedR1b9b2027715ddee5", "Program.lean"),
  "utf8");
  const namespace = "LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches";
  const plan = proofRecipePlan(document, program, [], namespace);
  validateProofRecipePlan(plan, document);
  const theorem = `${namespace}.function_0_scalar_post_test_loop_0_` +
    "terminates_with_counter_transfer_identity";
  assert(plan.recipes[0].supporting.some((entry) => entry.declaration === theorem),
    "counter-transfer recipe omitted its complete checked identity theorem");
  assert(plan.compositions.length === 1 &&
    plan.compositions[0].calleeIndex === 0,
  "counter-transfer plan omitted the checked wrapper callee identity");
  const request = fs.readFileSync(path.join(packageRoot, "request.txt"), "utf8");
  const starter = artifactProofStarter(makeJob(request), 1, true, plan);
  assert(starter.includes("FixedArraySingletonWrapper.wrapperProgram_spec") &&
    starter.includes("(callee := 0) (transform := fun value => value)") &&
    starter.includes(`${theorem} env initial value`) &&
    starter.includes("simp_all") &&
    starter.includes("Array.size_eq_one_iff.mp hSize") &&
    starter.trimEnd().endsWith("end LeanExeGen.GeneratedR1b9b2027715ddee5.Behavior"),
  "counter-transfer composition did not close every deterministic premise");
  assert(artifactProofStarterExpectedComplete(plan, 1),
    "counter-transfer composition did not select deterministic preflight");
  assert(!artifactProofStarterExpectedComplete(
    { compositions: plan.compositions, recipes: [] }, 1),
  "singleton wrapper without a checked scalar summary selected deterministic preflight");
  assert(!artifactProofStarterExpectedComplete(
    { compositions: [], recipes: plan.recipes }, 1),
  "checked scalar summary without a singleton wrapper selected deterministic preflight");
  const source = annotationMatchesSource(document, {
    namespace: "LeanExeGen.GeneratedR1b9b2027715ddee5",
    programModule: "LeanExeGen.GeneratedR1b9b2027715ddee5.Program",
  }, program).source;
  assert(source.includes("theorem function_0_scalar_post_test_loop_0_" +
      "terminates_with_counter_transfer_identity") &&
    source.includes("CounterTransition.postTestProgram_spec") &&
    source.includes("fun final results => final = initial ∧ results = [.i64 input]"),
  "counter-transfer annotation omitted its checked semantic summary");
  const changed = program.replace(
    "  .localGet 4,\n  .localSet 11,\n  .localGet 11\n]",
    "  .localGet 3,\n  .localSet 11,\n  .localGet 11\n]");
  assert(changed !== program, "counter-transfer suffix mutation did not change the Program");
  const changedPlan = proofRecipePlan(document, changed, [], namespace);
  assert(!changedPlan.recipes[0].supporting.some((entry) => entry.declaration === theorem),
    "counter-transfer summary accepted a changed return accumulator");
  const changedInitial = program.replace(
    ".constI64 (0 : UInt64),\n  .localSet 2,",
    ".constI64 (1 : UInt64),\n  .localSet 2,");
  assert(changedInitial !== program && !proofRecipePlan(
    document, changedInitial, [], namespace).recipes[0].supporting.some(
      (entry) => entry.declaration === theorem),
  "counter-transfer summary accepted a nonzero initial result");
  const changedBody = structuredClone(document);
  const encodedBody = JSON.stringify(changedBody);
  const mutatedBody = JSON.parse(encodedBody.replace(
    '"operation":"sub"', '"operation":"add"'));
  assert(JSON.stringify(mutatedBody) !== encodedBody && !proofRecipePlan(
    mutatedBody, program, [], namespace).recipes[0].supporting.some(
      (entry) => entry.declaration === theorem),
  "counter-transfer summary accepted a changed counter update");
  const changedCondition = structuredClone(document);
  changedCondition.functions[0].regions[0].parameters.descriptor.condition.kind = "eq";
  assert(!proofRecipePlan(
    changedCondition, program, [], namespace).recipes[0].supporting.some(
      (entry) => entry.declaration === theorem),
  "counter-transfer summary accepted an inverted loop condition");
}

function testThreeAccumulatorCounterTransferSummary() {
  const fixtureRoot = path.join(
    repoRoot, "test", "fixtures", "counter-transfer-three-accumulator");
  const document = JSON.parse(fs.readFileSync(
    path.join(fixtureRoot, "program.annotations.json"), "utf8"));
  const program = fs.readFileSync(path.join(fixtureRoot, "Program.lean"), "utf8");
  validateAnnotationDocument(
    document, fs.readFileSync(path.join(fixtureRoot, "program.wasm")));
  const namespace = "Project.CounterLayout.AnnotationMatches";
  const theorem = `${namespace}.function_0_scalar_post_test_loop_0_` +
    "terminates_with_counter_transfer_identity";
  const plan = proofRecipePlan(document, program, [], namespace);
  validateProofRecipePlan(plan, document);
  assert(plan.recipes[0].supporting.some((entry) => entry.declaration === theorem),
    "three-accumulator counter transfer omitted its complete identity theorem");
  const source = annotationMatchesSource(document, {
    namespace: "Project.CounterLayout",
    programModule: "Project.CounterLayout.Program",
  }, program).source;
  assert(source.includes("theorem function_0_scalar_post_test_loop_0_" +
      "terminates_with_counter_transfer_identity") &&
    source.includes("∃ v1 v2 v3 v4 v7") &&
    source.includes("U64Op.apply .add (v4) ((2 : UInt64))"),
  "three-accumulator summary did not preserve the independent audit transition");
  const changedResult = structuredClone(document);
  changedResult.functions[0].regions[0].parameters.resultSlot = 1;
  assert(!proofRecipePlan(
    changedResult, program, [], namespace).recipes[0].supporting.some(
      (entry) => entry.declaration === theorem),
  "three-accumulator summary accepted the remaining counter as its result");
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
  const completeLtgTask = ltgTaskBundle();
  const proofContext = proofTaskContext(
    "request\n", job, formalSource, generated.sources, null, 2, null, completeLtgTask);
  assert(proofContext.has(`LeanExeGen/${job.leanModule}/Program.lean`) &&
    proofContext.get(moduleFile(job.behaviorModule)) === artifactProofStarter(job, 0) &&
    proofContext.get("LTG/README.md").includes("categories.json") &&
    JSON.parse(proofContext.get("LTG/categories.json")).categories.length === 7 &&
    proofContext.get("LTG/categories/arrays/tools.jsonl")
      .includes('"id":"fixed-array-map-add"') &&
    proofContext.has("LTG/entries/fixed-array-map-add/entry.json") &&
    JSON.parse(proofContext.get("LTG_TASK.json")).entries ===
      completeLtgTask.manifest.entries &&
    proofContext.get("PROOF_LIBRARY.md").startsWith("# Artifact Proof Kit\n") &&
    proofContext.get("PROOF_STRATEGIES.md").includes("strategy.core") &&
    proofContext.get("PROOF_STRATEGIES.md").includes("strategy.arrays") &&
    proofContext.get("PROOF_IMPORT_CHECK.js").includes("unsupported proof dependency") &&
    !proofContext.get("PROOF_IMPORT_CHECK.js").includes('"Project.Common"') &&
    proofContext.get("PROOF_JOURNAL.md") === "# Proof Journal\n\n" &&
    JSON.parse(proofContext.get("PROOF_TASK_FEATURES.json")).exportIndex === 0 &&
    !proofContext.has(`LeanExeGen/${job.leanModule}/Source.lean`),
  "proof task context omitted proof guidance or Program, or exposed Source");
  const excludedExampleContext = proofTaskContext(
    "request\n", job, formalSource, generated.sources, null, 2,
    "c538d40936b426ba875b3dae1913e62ff00a44b34adff2adcd70922e5a4c95ff");
  assert(!excludedExampleContext.has("LTG/entries/demo4-map-proof-example/entry.json") &&
    excludedExampleContext.has("LTG/entries/fixed-array-map-add/entry.json") &&
    JSON.parse(excludedExampleContext.get("LTG_TASK.json")).excludedEntries === 1,
  "proof task context exposed an exact-artifact example or removed canonical support");
  const demo4Artifact =
    "c538d40936b426ba875b3dae1913e62ff00a44b34adff2adcd70922e5a4c95ff";
  const filteredLtg = ltgTaskBundle(demo4Artifact);
  validateLtgTask(filteredLtg.manifest, filteredLtg.files, demo4Artifact);
  const exposedLtg = {
    manifest: structuredClone(filteredLtg.manifest),
    files: new Map(filteredLtg.files),
  };
  exposedLtg.files.set("entries/demo4-map-proof-example/entry.json", Buffer.from("{}\n"));
  exposedLtg.manifest.sha256 = catalogDigest(exposedLtg.files);
  expectFailure(() => validateLtgTask(
    exposedLtg.manifest, exposedLtg.files, demo4Artifact), /unindexed path/);
  const importCheckRoot = path.join(temporaryRoot, "proof-import-check");
  fs.mkdirSync(importCheckRoot);
  const importCheckFile = path.join(importCheckRoot, "PROOF_IMPORT_CHECK.js");
  const importCandidate = path.join(importCheckRoot, "Behavior.lean");
  fs.writeFileSync(importCheckFile, proofContext.get("PROOF_IMPORT_CHECK.js"));
  fs.writeFileSync(importCandidate, "import Project.ProofKit.Control\n");
  const acceptedImports = spawnSync(process.execPath, [importCheckFile, importCandidate], {
    encoding: "utf8",
  });
  assert(acceptedImports.status === 0,
    "proof-task import check rejected an allowed proof-kit module");
  fs.writeFileSync(importCandidate, "import Project.Common\n");
  const rejectedImports = spawnSync(process.execPath, [importCheckFile, importCandidate], {
    encoding: "utf8",
  });
  assert(rejectedImports.status === 1 &&
    rejectedImports.stderr.includes("unsupported proof dependency: Project.Common"),
  `proof-task import check accepted an unsupported Project module: ` +
    `status ${rejectedImports.status}, stderr ${JSON.stringify(rejectedImports.stderr)}`);
  const legacyStarter = artifactProofStarter(job, 0, false, null, 1);
  assert(legacyStarter.includes("hInputBelow, hFit32, hFitMemory, hPages") &&
    !legacyStarter.includes("hHeapFit32"),
  "schema-5 artifact-proof starter did not retain the old RuntimeReady fields");
  const strategyBundle = proofStrategyBundle(talosProgram, 0);
  assert(strategyBundle.features.selectedSections.some((item) => item.id === "strategy.core") &&
    strategyBundle.features.selectedSections.some((item) => item.id === "strategy.arrays") &&
    strategyBundle.features.selectedSections.some((item) => item.id === "strategy.diagnostics") &&
    !strategyBundle.features.selectedSections.some((item) => item.id === "strategy.loops"),
  "proof-strategy selection disagreed with the synthetic Program");
  strategyBundle.compilerAnnotations = {
    schemaVersion: 1,
    artifact: { byteLength: wasm.length },
    functions: [],
  };
  strategyBundle.proofRecipes = {
    schemaVersion: 1,
    attemptOrder: ["direct", "composition", "tactic", "focused-guidance"],
    recipes: [],
  };
  const annotatedContext = proofTaskContext(
    "request\n", job, formalSource, generated.sources, strategyBundle);
  assert(JSON.parse(annotatedContext.get("PROGRAM_ANNOTATIONS.json")).schemaVersion === 1 &&
    JSON.parse(annotatedContext.get("PROOF_RECIPES.json")).schemaVersion === 1 &&
    annotatedContext.has(moduleFile(`${job.namespace}.AnnotationMatches`)) &&
    annotatedContext.get(moduleFile(job.behaviorModule))
      .includes(`import ${job.namespace}.AnnotationMatches`) &&
    !annotatedContext.get(moduleFile(job.behaviorModule))
      .includes("Project.ProofKit.FixedArrayLtNode"),
  "proof task omitted the compiler annotation and proof-recipe context");
  const selectedStarter = artifactProofStarter(job, 0, true, { recipes: [{
    regionKind: "leanexe.array.eq-node.v1",
    direct: { module: "Project.ProofKit.FixedArrayEqNode" },
    supporting: [{
      declaration: "Project.ProofKit.FixedArraySearch.pairPost_branchN_conseq",
    }],
  }] });
  assert(selectedStarter.includes("import Project.ProofKit.FixedArrayEqNode") &&
    selectedStarter.includes("import Project.ProofKit.FixedArraySearch") &&
    !selectedStarter.includes("import Project.ProofKit.FixedArrayLtNode") &&
    !selectedStarter.includes("import Project.ProofKit.FixedArraySearchTree"),
  "artifact-proof starter did not select imports from checked recipes");
  const treeStarter = artifactProofStarter(job, 0, true, {
    compositions: [{ direct: { module: "Project.ProofKit.FixedArraySearchTree" } }],
    recipes: [],
  });
  assert(treeStarter.includes("import Project.ProofKit.FixedArraySearchTree"),
  "artifact-proof starter did not offer tree composition for a checked tree");
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
  const compilerAnnotations = {
    schemaVersion: 1,
    artifact: { byteLength: wasm.length },
    functions: [],
  };
  const proofRecipes = {
    schemaVersion: 1,
    attemptOrder: ["direct", "composition", "tactic", "focused-guidance"],
    recipes: [],
  };
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
    proofJournal: "# Proof journal\n\nI reduced the artifact theorem with the checked array lemmas.\n",
    toolPins: currentToolPins(repoRoot),
    proofLibraryCatalog: fs.readFileSync(
      path.join(repoRoot, "proofs", "talos", "lean", "Project", "ProofKit", "README.md"),
      "utf8"),
    proofStrategies: strategyBundle.notes,
    proofTaskFeatures: strategyBundle.features,
    ltgTask: ltgTaskBundle(artifact.sha256),
    compilerAnnotations,
    proofRecipes,
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
    checked.proofTelemetry.totalMilliseconds === 3000 &&
    checked.proofJournal.includes("checked array lemmas") &&
    checked.manifest.schemaVersion === 7 &&
    checked.compilerAnnotations.artifact.byteLength === wasm.length &&
    checked.proofRecipes.recipes.length === 0 &&
    checked.ltgTask.manifest.artifactSha256 === artifact.sha256 &&
    checked.ltgTask.manifest.entries === ltgTaskBundle(artifact.sha256).manifest.entries,
  "validated package returned the wrong artifact or stage report");
  assert(fs.readFileSync(path.join(packageRoot, "proof-strategies.md"), "utf8") ===
    strategyBundle.notes &&
    JSON.parse(fs.readFileSync(path.join(packageRoot, "proof-task-features.json"), "utf8"))
      .sourceSha256 === strategyBundle.features.sourceSha256,
  "proof package did not archive its selected strategy context");
  assert(fs.existsSync(path.join(packageRoot, "program.annotations.json")) &&
    fs.existsSync(path.join(packageRoot, "proof-recipes.json")) &&
    fs.existsSync(path.join(packageRoot, "ltg-task.json")) &&
    fs.existsSync(path.join(packageRoot, "ltg", "categories", "loops", "tools.jsonl")),
  "proof package did not archive annotations, proof recipes, and structured LTG");
  assert(fs.readFileSync(path.join(packageRoot, "proof-journal.md"), "utf8") ===
    checked.proofJournal,
  "proof package did not archive the proving-agent journal");
  const schema4Root = path.join(temporaryRoot, "schema-4-package");
  fs.cpSync(packageRoot, schema4Root, { recursive: true });
  fs.unlinkSync(path.join(schema4Root, "program.annotations.json"));
  fs.unlinkSync(path.join(schema4Root, "proof-recipes.json"));
  const schema4ManifestPath = path.join(schema4Root, "package.json");
  const schema4Manifest = JSON.parse(fs.readFileSync(schema4ManifestPath, "utf8"));
  schema4Manifest.schemaVersion = 4;
  schema4Manifest.files = schema4Manifest.files.filter((record) =>
    !["program.annotations.json", "proof-recipes.json"].includes(record.path));
  fs.writeFileSync(schema4ManifestPath, `${JSON.stringify(schema4Manifest, null, 2)}\n`);
  assert(validatePackage(schema4Root).manifest.schemaVersion === 4,
    "package validation rejected a schema-4 package without annotations");
  const legacyRoot = path.join(temporaryRoot, "legacy-package");
  fs.cpSync(schema4Root, legacyRoot, { recursive: true });
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
  const splitCodexReports = {
    schemaVersion: 2,
    codexVersions: {
      formalSpecification: "codex-cli 0.146.0",
      leanProgram: "codex-cli 0.146.0",
      artifactProof: "codex-cli 0.147.0",
    },
    maximumAttempts: stageReports.maximumAttempts,
    tasks: stageReports.tasks,
  };
  validateStageReports(splitCodexReports, packageRoot, job);
  assert(stageReportCodexVersion(splitCodexReports, "artifactProof") ===
      "codex-cli 0.147.0" &&
    JSON.stringify(stageReportCodexVersions(stageReports)) === JSON.stringify({
      formalSpecification: "codex-cli test",
      leanProgram: "codex-cli test",
      artifactProof: "codex-cli test",
    }),
  "stage reports did not preserve per-task Codex identities");
  const malformedSplitReports = structuredClone(splitCodexReports);
  delete malformedSplitReports.codexVersions.leanProgram;
  expectFailure(() => validateStageReports(malformedSplitReports, packageRoot, job),
    /codexVersions must contain exactly/);
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
  const collision = expectFailure(
    () => requirePublicationTargetsAvailable(output), /program\.wasm exists/);
  assert(collision instanceof StageError && collision.stage === 1,
    "publication preflight did not reject an existing output during job setup");
  const proofOnlyOutput = path.join(temporaryRoot, "proof-only", "program.wasm");
  const proofOnlyPackage = proofPackagePath(proofOnlyOutput);
  fs.mkdirSync(proofOnlyPackage, { recursive: true });
  const proofCollision = expectFailure(
    () => requirePublicationTargetsAvailable(proofOnlyOutput), /program\.proof exists/);
  assert(proofCollision instanceof StageError && proofCollision.stage === 1,
    "publication preflight did not reject an existing proof package during job setup");
  const failedOutput = path.join(temporaryRoot, "failed", "program.wasm");
  const failedProof = path.join(temporaryRoot, "failed", "program.proof");
  const error = expectFailure(() => publish(failedOutput, failedProof, bytes, () => {
    throw new Error("package failure");
  }), /package failure/);
  assert(error instanceof StageError && !fs.existsSync(failedOutput) && !fs.existsSync(failedProof),
    "failed publication left an output");

  const failureOutput = path.join(temporaryRoot, "reprove-failure", "program.wasm");
  const failureProof = proofPackagePath(failureOutput);
  const failureTask = path.join(temporaryRoot, "reprove-failure-task");
  const failureJob = makeJob("preserve one failed proof\n");
  const candidate = moduleFile(failureJob.behaviorModule);
  fs.mkdirSync(path.dirname(path.join(failureTask, candidate)), { recursive: true });
  fs.writeFileSync(path.join(failureTask, candidate), "theorem candidate : True := by trivial\n");
  fs.writeFileSync(path.join(failureTask, "PROOF_JOURNAL.md"),
    "# Proof Journal\n\nThe outer check exceeded its heartbeat limit.\n");
  fs.writeFileSync(path.join(failureTask, ".leanexegen-outcome.json"),
    `${JSON.stringify({ outcome: "generated" })}\n`);
  const failurePath = preserveReproveFailure(
    failureProof, failureTask, failureJob,
    new StageError(5, "artifact proof", "outer check failed"),
  );
  const failureRecord = JSON.parse(fs.readFileSync(
    path.join(failurePath, "failure.json"), "utf8"));
  assert(failurePath === `${failureProof}.failure` &&
    fs.readFileSync(path.join(failurePath, "candidate.lean"), "utf8").includes("candidate") &&
    fs.readFileSync(path.join(failurePath, "proof-journal.md"), "utf8")
      .includes("heartbeat") &&
    failureRecord.stage === 5 && failureRecord.error === "outer check failed" &&
    failureRecord.files.every((file) => /^[0-9a-f]{64}$/.test(file.sha256)),
  "artifact-proof failure record omitted its candidate, journal, diagnostic, or hashes");
  const failureCollision = expectFailure(
    () => requirePublicationTargetsAvailable(failureOutput), /program\.proof\.failure exists/);
  assert(failureCollision instanceof StageError && failureCollision.stage === 1,
    "publication preflight did not preserve an existing failure record");
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
  testFixedArrayEqNodeFeatures();
  testAnnotationRecipePlan();
  testLengthDispatchAnnotationRecipes();
  testMapAddAnnotationRecipe();
  testFilterLtAnnotationRecipe();
  testLoopAnnotationRecipes();
  testLessThanNodeAnnotationRecipes();
  testSearchTreeComposition();
  testSingletonWrapperComposition();
  testScalarTransitionSpecialization();
  testCounterTransferIdentitySummary();
  testThreeAccumulatorCounterTransferSummary();
  testPairResultAnnotationRecipes();
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
