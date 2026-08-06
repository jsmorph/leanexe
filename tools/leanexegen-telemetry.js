"use strict";

const stage5Metric = "stage-5-start-to-first-accepted-proof";
const sha256Pattern = /^[0-9a-f]{64}$/;

function fail(message) {
  throw new Error(message);
}

function milliseconds(nanoseconds) {
  return Math.round(Number(nanoseconds) / 1000) / 1000;
}

function isoTimestamp(value, description) {
  if (typeof value !== "string") fail(`${description} must be a UTC timestamp`);
  const parsed = new Date(value);
  if (!Number.isFinite(parsed.valueOf()) || parsed.toISOString() !== value) {
    fail(`${description} must be a canonical UTC timestamp`);
  }
  return parsed;
}

function duration(value, description) {
  if (typeof value !== "number" || !Number.isFinite(value) || value < 0) {
    fail(`${description} must be a nonnegative number`);
  }
  return value;
}

function validateStage5Telemetry(value, expectedSourceSha256 = null) {
  if (value === null || typeof value !== "object" || Array.isArray(value)) {
    fail("proof-telemetry.json must contain an object");
  }
  const expectedKeys = [
    "schemaVersion",
    "metric",
    "stage",
    "stageName",
    "stageStartedAt",
    "firstAcceptedAt",
    "codexSessionMilliseconds",
    "outerAcceptanceMilliseconds",
    "totalMilliseconds",
    "acceptedSourceSha256",
  ].sort();
  const foundKeys = Object.keys(value).sort();
  if (foundKeys.length !== expectedKeys.length ||
      foundKeys.some((key, index) => key !== expectedKeys[index])) {
    fail(`proof-telemetry.json must contain exactly: ${expectedKeys.join(", ")}`);
  }
  if (value.schemaVersion !== 1 || value.metric !== stage5Metric ||
      value.stage !== 5 || value.stageName !== "Direct artifact proof") {
    fail("proof-telemetry.json has an unsupported metric identity");
  }
  const started = isoTimestamp(value.stageStartedAt, "stageStartedAt");
  const accepted = isoTimestamp(value.firstAcceptedAt, "firstAcceptedAt");
  if (accepted < started) fail("firstAcceptedAt precedes stageStartedAt");
  const codex = duration(value.codexSessionMilliseconds, "codexSessionMilliseconds");
  const outer = duration(
    value.outerAcceptanceMilliseconds, "outerAcceptanceMilliseconds");
  const total = duration(value.totalMilliseconds, "totalMilliseconds");
  if (codex + outer > total + 0.002) {
    fail("measured stage-5 components exceed totalMilliseconds");
  }
  if (!sha256Pattern.test(value.acceptedSourceSha256)) {
    fail("acceptedSourceSha256 must be a SHA-256 digest");
  }
  if (expectedSourceSha256 !== null &&
      value.acceptedSourceSha256 !== expectedSourceSha256) {
    fail("acceptedSourceSha256 differs from the accepted artifact proof");
  }
  return value;
}

function createStage5Telemetry(options = {}) {
  const clock = options.clock || process.hrtime.bigint;
  const now = options.now || (() => new Date());
  const startedNanoseconds = clock();
  const stageStartedAt = now().toISOString();
  let codexSessionMilliseconds = null;
  let outerAcceptanceMilliseconds = null;
  let accepted = false;

  function measure(action, setDuration) {
    const before = clock();
    try {
      return action();
    } finally {
      setDuration(milliseconds(clock() - before));
    }
  }

  return {
    stageStartedAt,
    measureCodexSession(action) {
      return measure(action, (value) => { codexSessionMilliseconds = value; });
    },
    measureOuterAcceptance(action) {
      return measure(action, (value) => { outerAcceptanceMilliseconds = value; });
    },
    accept(acceptedSourceSha256) {
      if (accepted) fail("stage-5 telemetry recorded more than one accepted proof");
      if (codexSessionMilliseconds === null || outerAcceptanceMilliseconds === null) {
        fail("stage-5 telemetry lacks a Codex session or outer acceptance measurement");
      }
      accepted = true;
      return validateStage5Telemetry({
        schemaVersion: 1,
        metric: stage5Metric,
        stage: 5,
        stageName: "Direct artifact proof",
        stageStartedAt,
        firstAcceptedAt: now().toISOString(),
        codexSessionMilliseconds,
        outerAcceptanceMilliseconds,
        totalMilliseconds: milliseconds(clock() - startedNanoseconds),
        acceptedSourceSha256,
      }, acceptedSourceSha256);
    },
  };
}

module.exports = {
  createStage5Telemetry,
  stage5Metric,
  validateStage5Telemetry,
};
