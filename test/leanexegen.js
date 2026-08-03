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
  fromWasmtimeI64,
  generationResult,
  parseArgs,
  proofPackagePath,
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
  toWasmtimeI64,
  verificationCheckSources,
  warnings,
} = require("../tools/leanexegen");

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
    schemaVersion: 1,
    task,
    outcome: "generated",
    summary: values.summary || `${task} result`,
    decisions: values.decisions || ["Use the fixed unary ABI."],
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
    decisions: ["Use the fixed unary ABI."],
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
  const generated = parseArgs(["-s", "-o", "x.wasm", "request.txt"]);
  assert(generated.command === "generate" && generated.silent,
    "generation arguments were parsed incorrectly");
  const verified = parseArgs(["verify", "-s", "x.proof"]);
  assert(verified.command === "verify" && verified.silent,
    "verification arguments were parsed incorrectly");
  const reproved = parseArgs(["reprove", "-s", "-o", "new.wasm", "x.proof"]);
  assert(reproved.command === "reprove" && reproved.silent &&
    reproved.outputPath.endsWith("/new.wasm") && reproved.packagePath.endsWith("/x.proof"),
  "reproof arguments were parsed incorrectly");
  assert(proofPackagePath("/tmp/x.wasm") === "/tmp/x.proof",
    "proof package path was derived incorrectly");
  expectFailure(() => parseArgs(["-o", "x.wasm"]), /usage:/);
  assert(generationResult(true, [{ arguments: ["1"], stdout: "1" }], ["wasmtime"]) === "",
    "silent generation produced standard output");
  assert(stageHeading(3, "Lean program", new Date("2026-08-03T12:34:57.000Z")) ===
    "2026-08-03T12:34:57.000Z Stage 3: Lean program\n\n",
    "stage heading did not contain the UTC start time");
}

function testCodexProtocol() {
  const job = makeJob("compute one unsigned integer\n");
  assert(parseCodexVersion({
    stdout: "codex-cli 0.146.0\n",
    stderr: "WARNING: could not create PATH aliases\n",
  }) === "codex-cli 0.146.0", "Codex identity included an unrelated warning");
  assert(JSON.stringify(job) === JSON.stringify(makeJob("compute one unsigned integer\n")),
    "job identity was not deterministic");
  assert(job.formalSpecDefinition === `${job.namespace}.FormalSpec.ArtifactSpec` &&
    job.formalSpecType === "Wasm.Module → Prop" &&
    job.sourceEntry === `${job.namespace}.Source.compute` && job.exportName === "compute",
  "job did not fix the unary formal and program interfaces");

  const formalRaw = `import CodeLib\n\nnamespace ${job.namespace}.FormalSpec\n\n` +
    `def expected (n : UInt64) : UInt64 := n\n\nend ${job.namespace}.FormalSpec\n`;
  const formalOutcome = outcome("formal-specification", formalRaw, {
    hostAssumptions: ["The module imports no host functions."],
  });
  validateCodexTaskOutcome(formalOutcome, "formal-specification");
  validateCodexTaskOutcome({
    schemaVersion: 1,
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
  invalid.samples = [{ arguments: ["1"], expectedStdout: "1" }];
  expectFailure(() => validateCodexTaskOutcome(invalid, "formal-specification"),
    /must not contain samples/);
  const invalidSample = outcome("lean-program", formalRaw, {
    samples: [{ arguments: ["42"], expectedStdout: "42\n" }],
  });
  expectFailure(() => validateCodexTaskOutcome(invalidSample, "lean-program"),
    /expectedStdout must be a UInt64 decimal/);
  const excessiveSample = outcome("lean-program", formalRaw, {
    samples: [{ arguments: ["18446744073709551616"], expectedStdout: "0" }],
  });
  expectFailure(() => validateCodexTaskOutcome(excessiveSample, "lean-program"),
    /arguments\[0\] must be a UInt64 decimal/);
  const wideSample = outcome("lean-program", formalRaw, {
    samples: [{ arguments: ["1", "2"], expectedStdout: "3" }],
  });
  expectFailure(() => validateCodexTaskOutcome(wideSample, "lean-program"),
    /must contain exactly one UInt64/);
  const programProblem = outcome("lean-program", "candidate", {
    samples: [{ arguments: ["1"], expectedStdout: "1" }],
  });
  programProblem.outcome = "problems";
  programProblem.problems = ["compiler rejected the candidate"];
  programProblem.source = "";
  assert(validateCodexTaskOutcome(programProblem, "lean-program") === programProblem,
    "problem outcomes rejected irrelevant generated-result metadata");
  assert(toWasmtimeI64("0") === "0" &&
    toWasmtimeI64("9223372036854775808") === "-9223372036854775808" &&
    toWasmtimeI64("18446744073709551615") === "-1" &&
    fromWasmtimeI64("-1") === "18446744073709551615" &&
    fromWasmtimeI64("-9223372036854775808") === "9223372036854775808" &&
    fromWasmtimeI64("9223372036854775808") === null,
  "UInt64 and Wasmtime i64 decimal conversion disagreed");

  const formalSource = formalSpecificationSource(job, formalRaw);
  assert(formalSource.includes("def ArtifactSpec (module_ : Wasm.Module) : Prop :=") &&
    formalSource.includes('module_.findExport "compute" = some entry') &&
    formalSource.includes("Wasm.TerminatesWith env module_ entry initial [.i64 n]") &&
    formalSource.includes("results = [.i64 (expected n)]"),
  "the orchestrator did not append the fixed formal interface");
  const checks = formalSpecificationCheckSources(job, "FormalSpecCheck");
  const checkSource = checks.sources.get(checks.target);
  assert(checkSource.includes(`#check (${job.expectedDefinition} : UInt64 → UInt64)`) &&
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
    artifactPrompt.includes("intro env initial n") &&
    artifactPrompt.includes("Read PROOF_LIBRARY.md") &&
    artifactPrompt.includes("import Project.ProofKit.Control") &&
    artifactPrompt.includes(`wp_entry ${job.namespace}.func3Def as initial'`) &&
    artifactPrompt.includes("wp_entry_to_loop <functionDef>") &&
    artifactPrompt.includes(`wp_entry_single_call ${job.namespace}.func3Def`) &&
    artifactPrompt.includes("Use read-only commands to inspect FormalSpec, Program"),
  "artifact-proof task did not receive the proof-kit catalog or tactics");
  expectFailure(() => validateProgramImports(
    job, `import ${job.formalSpecModule}\n\ndef compute (n : UInt64) := n\n`),
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
    `namespace ${job.namespace}.Source\n\ndef compute (n : UInt64) := n\n`;
  const generated = outcome("lean-program", "", {
    samples: [{ arguments: ["7"], expectedStdout: "7" }],
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
    schema.properties.samples.items.properties.arguments.maxItems === 1 &&
    schema.properties.samples.items.properties.expectedStdout.pattern ===
      "^(?:0|[1-9][0-9]*)$",
  "Codex command or schema was not deterministic");

  let invocations = 0;
  const session = runTaskSession({
    task: "lean-program",
    stage: 3,
    stageName: "Lean program",
    sourceModule: job.sourceModule,
    invoke: (prompt) => {
      assert(prompt === "one iterative session", "task session received the wrong prompt");
      invocations += 1;
      return outcome("lean-program", "good", {
        samples: [{ arguments: ["7"], expectedStdout: "7" }],
      });
    },
    prompt: "one iterative session",
    materialize: (source) => source,
    diagnose: () => "outer diagnostic accepted source",
  });
  assert(invocations === 1 && session.stageReport.report.attempts.length === 1 &&
    session.stageReport.report.attempts[0].outcome === "accepted",
  "task orchestration invoked more than one Codex session");
  expectFailure(() => runTaskSession({
    task: "lean-program",
    stage: 3,
    stageName: "Lean program",
    sourceModule: job.sourceModule,
    invoke: () => outcome("lean-program", "bad", {
      samples: [{ arguments: ["7"], expectedStdout: "7" }],
    }),
    prompt: "one iterative session",
    materialize: (source) => source,
    diagnose: () => { throw new Error("unknown declaration bad"); },
  }), /independent outer check rejected.*unknown declaration bad/s);
}

function testArtifactPackage(job, formalSource) {
  const raw = "{ functionTypeIndices := [0] }";
  const emitted = `namespace Project.${job.leanModule}\n\n` +
    `def func0Def : Wasm.Function := default\n\ndef module : Wasm.Module :=\n` +
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
    !proofContext.has(`LeanExeGen/${job.leanModule}/Source.lean`),
  "proof task context omitted the catalog or Program, or exposed Source");
  const programSource = `namespace ${job.namespace}.Source\n\ndef compute (n : UInt64) := n\n`;
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
    invocation: ["wasmtime", "run", "--invoke", "compute", "<program.wasm>", "<argument-1>"],
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
  const packageRoot = path.join(temporaryRoot, "package");
  createPackage(packageRoot, {
    request: "compute one unsigned integer\n",
    interpretation: {
      formalSpecification: { summary: "spec", decisions: [] },
      leanProgram: { summary: "program", decisions: [] },
      artifactProof: { summary: "proof", decisions: [] },
    },
    artifact,
    samples: [{ arguments: ["7"], stdout: "7", invocation: [] }],
    hostAssumptions: ["The module imports no host functions."],
    stageReports,
    toolPins: currentToolPins(repoRoot),
    proofLibraryCatalog: fs.readFileSync(
      path.join(repoRoot, "proofs", "talos", "lean", "Project", "ProofKit", "README.md"),
      "utf8"),
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
    checked.stageReports.tasks.leanProgram.sourceSha256 === sha256(Buffer.from(programSource)),
  "validated package returned the wrong artifact or stage report");
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
