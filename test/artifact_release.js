#!/usr/bin/env node
"use strict";

const {
  derivedBlockers,
  loadEvidence,
  validateEvidence,
} = require("../tools/artifact-release");

function copy(value) {
  return JSON.parse(JSON.stringify(value));
}

function expectFailure(value, pattern) {
  try {
    validateEvidence(value);
  } catch (error) {
    if (!pattern.test(error.message)) throw error;
    return;
  }
  throw new Error(`release evidence unexpectedly passed: ${pattern}`);
}

const { evidence, blockers } = loadEvidence();
const expectedBlockers = [
  "No immutable source revision records the current proof implementation.",
  "The release gates have not passed from a cold checkout of the recorded source revision.",
];
if (evidence.status !== "draft" || evidence.packages.length !== 20 ||
    JSON.stringify(blockers) !== JSON.stringify(expectedBlockers)) {
  throw new Error("the draft release record has the wrong state");
}
if (JSON.stringify(blockers) !== JSON.stringify(derivedBlockers(evidence))) {
  throw new Error("release blockers are not derived from the evidence fields");
}
if (blockers.some((blocker) => blocker.includes("kernel"))) {
  throw new Error("the accepted audited kernel disposition remains a blocker");
}

for (const count of ["fail", "cascade", "decodeError", "interpreterError", "outOfFuel"]) {
  const changed = copy(evidence);
  changed.semanticConformance.talos[count] += 1;
  expectFailure(changed, /semantic conformance result/);
}

const wrongResult = copy(evidence);
wrongResult.semanticConformance.result = "passed";
expectFailure(wrongResult, /semantic conformance result/);

const wrongKernel = copy(evidence);
wrongKernel.kernelReview.candidateToolchain = "leanprover/lean4:v0.0.0";
expectFailure(wrongKernel, /audited affected toolchain/);

const staleArtifactProof = copy(evidence);
staleArtifactProof.artifactProof.releaseInputSha256 = "0".repeat(64);
expectFailure(staleArtifactProof, /artifact proof release input identity/);

const staleConformance = copy(evidence);
staleConformance.semanticConformance.releaseInputSha256 = "0".repeat(64);
expectFailure(staleConformance, /semantic conformance release input identity/);

const ready = copy(evidence);
ready.sourceRevision = "1".repeat(40);
ready.coldCheckout = {
  status: "passed",
  sourceRevision: ready.sourceRevision,
  releaseInputSha256: ready.releaseInputSha256,
  date: ready.recordedDate,
  command: "tools/artifact-release.js check-cold <revision>",
};
ready.blockers = [];
ready.status = "ready";
validateEvidence(ready);

process.stdout.write("checked release identities, receipts, pins, results, and blockers\n");
