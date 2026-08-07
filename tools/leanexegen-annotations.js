"use strict";

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

function natural(value, description) {
  if (!Number.isSafeInteger(value) || value < 0) {
    fail(`${description} must be a natural number`);
  }
  return value;
}

function string(value, description) {
  if (typeof value !== "string" || value.length === 0 || value.trim() !== value) {
    fail(`${description} must be a trimmed, nonempty string`);
  }
  return value;
}

function uint64String(value, description) {
  string(value, description);
  if (!/^(?:0|[1-9][0-9]*)$/.test(value) ||
      BigInt(value) > 18446744073709551615n) {
    fail(`${description} must be a canonical UInt64 decimal`);
  }
  return value;
}

function array(value, description) {
  if (!Array.isArray(value)) fail(`${description} must be an array`);
  return value;
}

function validateDirectCall(region, description) {
  exactKeys(region, ["generatedBy", "id", "kind", "location", "parameters"], description);
  string(region.id, `${description}.id`);
  if (region.kind !== "leanexe.call.direct.v1") {
    fail(`${description}.kind is unsupported`);
  }
  exactKeys(region.location, ["endIndex", "listPath", "startIndex"],
    `${description}.location`);
  natural(region.location.startIndex, `${description}.location.startIndex`);
  natural(region.location.endIndex, `${description}.location.endIndex`);
  if (region.location.startIndex >= region.location.endIndex) {
    fail(`${description}.location must be nonempty`);
  }
  for (const [index, step] of array(
    region.location.listPath, `${description}.location.listPath`).entries()) {
    exactKeys(step, ["field", "instructionIndex"],
      `${description}.location.listPath[${index}]`);
    natural(step.instructionIndex,
      `${description}.location.listPath[${index}].instructionIndex`);
    if (!["block", "loop", "then", "else"].includes(step.field)) {
      fail(`${description}.location.listPath[${index}].field is unsupported`);
    }
  }
  exactKeys(region.parameters, [
    "argumentLocals", "calleeIndex", "continuation", "resultLocals", "resultPlacement",
  ], `${description}.parameters`);
  natural(region.parameters.calleeIndex, `${description}.parameters.calleeIndex`);
  for (const [index, local] of array(
    region.parameters.argumentLocals, `${description}.parameters.argumentLocals`).entries()) {
    if (local !== null) natural(local, `${description}.parameters.argumentLocals[${index}]`);
  }
  for (const [index, local] of array(
    region.parameters.resultLocals, `${description}.parameters.resultLocals`).entries()) {
    natural(local, `${description}.parameters.resultLocals[${index}]`);
  }
  if (!["locals", "stack", "function-results"].includes(
    region.parameters.resultPlacement)) {
    fail(`${description}.parameters.resultPlacement is unsupported`);
  }
  if (!["fallthrough", "function-return"].includes(region.parameters.continuation)) {
    fail(`${description}.parameters.continuation is unsupported`);
  }
  for (const [index, generator] of array(
    region.generatedBy, `${description}.generatedBy`).entries()) {
    string(generator, `${description}.generatedBy[${index}]`);
  }
}

function validateFixedArrayLengthDispatch(region, description) {
  exactKeys(region, ["generatedBy", "id", "kind", "location", "parameters"], description);
  string(region.id, `${description}.id`);
  if (region.kind !== "leanexe.array.length-dispatch.v1") {
    fail(`${description}.kind is unsupported`);
  }
  exactKeys(region.location, ["endIndex", "listPath", "startIndex"],
    `${description}.location`);
  natural(region.location.startIndex, `${description}.location.startIndex`);
  natural(region.location.endIndex, `${description}.location.endIndex`);
  if (region.location.startIndex >= region.location.endIndex) {
    fail(`${description}.location must be nonempty`);
  }
  for (const [index, step] of array(
    region.location.listPath, `${description}.location.listPath`).entries()) {
    exactKeys(step, ["field", "instructionIndex"],
      `${description}.location.listPath[${index}]`);
    natural(step.instructionIndex,
      `${description}.location.listPath[${index}].instructionIndex`);
    if (!["block", "loop", "then", "else"].includes(step.field)) {
      fail(`${description}.location.listPath[${index}].field is unsupported`);
    }
  }
  exactKeys(region.parameters, [
    "continuation", "encoding", "expectedSize", "inputLocal", "invalidBranch",
    "validBranch",
  ], `${description}.parameters`);
  natural(region.parameters.inputLocal, `${description}.parameters.inputLocal`);
  natural(region.parameters.expectedSize, `${description}.parameters.expectedSize`);
  if (!["eq-normalized-v1", "ne-normalized-v1"].includes(region.parameters.encoding)) {
    fail(`${description}.parameters.encoding is unsupported`);
  }
  const expectedBranches = region.parameters.encoding === "eq-normalized-v1"
    ? { invalidBranch: "else", validBranch: "then" }
    : { invalidBranch: "then", validBranch: "else" };
  if (region.parameters.invalidBranch !== expectedBranches.invalidBranch ||
      region.parameters.validBranch !== expectedBranches.validBranch ||
      region.parameters.continuation !== "fallthrough") {
    fail(`${description}.parameters has invalid branch roles or continuation`);
  }
  for (const [index, generator] of array(
    region.generatedBy, `${description}.generatedBy`).entries()) {
    string(generator, `${description}.generatedBy[${index}]`);
  }
}

function validateFixedArraySearchKey(region, description) {
  exactKeys(region, ["generatedBy", "id", "kind", "location", "parameters"], description);
  string(region.id, `${description}.id`);
  if (region.kind !== "leanexe.array.search-key.v1") {
    fail(`${description}.kind is unsupported`);
  }
  exactKeys(region.location, ["endIndex", "listPath", "startIndex"],
    `${description}.location`);
  natural(region.location.startIndex, `${description}.location.startIndex`);
  natural(region.location.endIndex, `${description}.location.endIndex`);
  if (region.location.endIndex - region.location.startIndex !== 11) {
    fail(`${description}.location must contain the exact search-key region`);
  }
  for (const [index, step] of array(
    region.location.listPath, `${description}.location.listPath`).entries()) {
    exactKeys(step, ["field", "instructionIndex"],
      `${description}.location.listPath[${index}]`);
    natural(step.instructionIndex,
      `${description}.location.listPath[${index}].instructionIndex`);
    if (!["block", "loop", "then", "else"].includes(step.field)) {
      fail(`${description}.location.listPath[${index}].field is unsupported`);
    }
  }
  exactKeys(region.parameters, ["continuation", "index", "keyLocal", "offset"],
    `${description}.parameters`);
  natural(region.parameters.offset, `${description}.parameters.offset`);
  natural(region.parameters.index, `${description}.parameters.index`);
  natural(region.parameters.keyLocal, `${description}.parameters.keyLocal`);
  if (region.parameters.keyLocal >= region.parameters.offset + 5 ||
      region.parameters.continuation !== "fallthrough") {
    fail(`${description}.parameters has an invalid key local or continuation`);
  }
  for (const [index, generator] of array(
    region.generatedBy, `${description}.generatedBy`).entries()) {
    string(generator, `${description}.generatedBy[${index}]`);
  }
}

function validateFixedArrayEqNode(region, description) {
  exactKeys(region, ["generatedBy", "id", "kind", "location", "parameters"], description);
  string(region.id, `${description}.id`);
  if (region.kind !== "leanexe.array.eq-node.v1") {
    fail(`${description}.kind is unsupported`);
  }
  exactKeys(region.location, ["endIndex", "listPath", "startIndex"],
    `${description}.location`);
  natural(region.location.startIndex, `${description}.location.startIndex`);
  natural(region.location.endIndex, `${description}.location.endIndex`);
  if (region.location.endIndex - region.location.startIndex !== 17) {
    fail(`${description}.location must contain the exact equality-node region`);
  }
  for (const [index, step] of array(
    region.location.listPath, `${description}.location.listPath`).entries()) {
    exactKeys(step, ["field", "instructionIndex"],
      `${description}.location.listPath[${index}]`);
    natural(step.instructionIndex,
      `${description}.location.listPath[${index}].instructionIndex`);
    if (!["block", "loop", "then", "else"].includes(step.field)) {
      fail(`${description}.location.listPath[${index}].field is unsupported`);
    }
  }
  exactKeys(region.parameters, [
    "continuation", "equalBranch", "index", "keyLocal", "offset", "operandOrder",
    "unequalBranch",
  ], `${description}.parameters`);
  natural(region.parameters.offset, `${description}.parameters.offset`);
  natural(region.parameters.index, `${description}.parameters.index`);
  natural(region.parameters.keyLocal, `${description}.parameters.keyLocal`);
  if (region.parameters.keyLocal >= region.parameters.offset + 5 ||
      !["loaded-first", "key-first"].includes(region.parameters.operandOrder) ||
      region.parameters.equalBranch !== "then" ||
      region.parameters.unequalBranch !== "else" ||
      region.parameters.continuation !== "fallthrough") {
    fail(`${description}.parameters has an invalid node shape`);
  }
  for (const [index, generator] of array(
    region.generatedBy, `${description}.generatedBy`).entries()) {
    string(generator, `${description}.generatedBy[${index}]`);
  }
}

function validateFixedArrayLtNode(region, description) {
  exactKeys(region, ["generatedBy", "id", "kind", "location", "parameters"], description);
  string(region.id, `${description}.id`);
  if (region.kind !== "leanexe.array.lt-node.v1") {
    fail(`${description}.kind is unsupported`);
  }
  exactKeys(region.location, ["endIndex", "listPath", "startIndex"],
    `${description}.location`);
  natural(region.location.startIndex, `${description}.location.startIndex`);
  natural(region.location.endIndex, `${description}.location.endIndex`);
  if (region.location.endIndex - region.location.startIndex !== 13) {
    fail(`${description}.location must contain the exact less-than-node region`);
  }
  for (const [index, step] of array(
    region.location.listPath, `${description}.location.listPath`).entries()) {
    exactKeys(step, ["field", "instructionIndex"],
      `${description}.location.listPath[${index}]`);
    natural(step.instructionIndex,
      `${description}.location.listPath[${index}].instructionIndex`);
    if (!["block", "loop", "then", "else"].includes(step.field)) {
      fail(`${description}.location.listPath[${index}].field is unsupported`);
    }
  }
  exactKeys(region.parameters, [
    "comparison", "continuation", "index", "keyLocal", "lessBranch",
    "notLessBranch", "offset", "operandOrder",
  ], `${description}.parameters`);
  natural(region.parameters.offset, `${description}.parameters.offset`);
  natural(region.parameters.index, `${description}.parameters.index`);
  natural(region.parameters.keyLocal, `${description}.parameters.keyLocal`);
  if (region.parameters.keyLocal >= region.parameters.offset + 5 ||
      region.parameters.operandOrder !== "key-first" ||
      region.parameters.comparison !== "key-lt-element-v1" ||
      region.parameters.lessBranch !== "then" ||
      region.parameters.notLessBranch !== "else" ||
      region.parameters.continuation !== "fallthrough") {
    fail(`${description}.parameters has an invalid less-than-node shape`);
  }
  for (const [index, generator] of array(
    region.generatedBy, `${description}.generatedBy`).entries()) {
    string(generator, `${description}.generatedBy[${index}]`);
  }
}

function validateFixedArrayPairResult(region, description) {
  exactKeys(region, ["generatedBy", "id", "kind", "location", "parameters"], description);
  string(region.id, `${description}.id`);
  if (region.kind !== "leanexe.array.pair-result.v1") {
    fail(`${description}.kind is unsupported`);
  }
  exactKeys(region.location, ["endIndex", "listPath", "startIndex"],
    `${description}.location`);
  natural(region.location.startIndex, `${description}.location.startIndex`);
  natural(region.location.endIndex, `${description}.location.endIndex`);
  if (region.location.startIndex >= region.location.endIndex) {
    fail(`${description}.location must be nonempty`);
  }
  for (const [index, step] of array(
    region.location.listPath, `${description}.location.listPath`).entries()) {
    exactKeys(step, ["field", "instructionIndex"],
      `${description}.location.listPath[${index}]`);
    natural(step.instructionIndex,
      `${description}.location.listPath[${index}].instructionIndex`);
    if (!["block", "loop", "then", "else"].includes(step.field)) {
      fail(`${description}.location.listPath[${index}].field is unsupported`);
    }
  }
  exactKeys(region.parameters, [
    "continuation", "destination", "firstValue", "inputIndex", "mode", "offset",
    "secondValue",
  ], `${description}.parameters`);
  natural(region.parameters.offset, `${description}.parameters.offset`);
  natural(region.parameters.destination, `${description}.parameters.destination`);
  uint64String(region.parameters.secondValue, `${description}.parameters.secondValue`);
  if (region.parameters.offset !== 10 || region.parameters.destination === 0 ||
      region.parameters.destination >= 25 ||
      region.parameters.continuation !== "fallthrough") {
    fail(`${description}.parameters has an unsupported result frame`);
  }
  if (region.parameters.mode === "constants-v1") {
    uint64String(region.parameters.firstValue, `${description}.parameters.firstValue`);
    if (region.parameters.inputIndex !== null) {
      fail(`${description}.parameters.inputIndex must be null for constants-v1`);
    }
  } else if (region.parameters.mode === "input-index-and-one-v1") {
    if (region.parameters.firstValue !== null || region.parameters.secondValue !== "1") {
      fail(`${description}.parameters has an invalid input-index-and-one value shape`);
    }
    natural(region.parameters.inputIndex, `${description}.parameters.inputIndex`);
  } else {
    fail(`${description}.parameters.mode is unsupported`);
  }
  for (const [index, generator] of array(
    region.generatedBy, `${description}.generatedBy`).entries()) {
    string(generator, `${description}.generatedBy[${index}]`);
  }
}

function validateAnnotationDocument(document, wasmBytes) {
  exactKeys(document, ["artifact", "functions", "schemaVersion"], "annotations");
  if (document.schemaVersion !== 1) fail("unsupported annotation schema");
  exactKeys(document.artifact, ["byteLength"], "annotations.artifact");
  if (natural(document.artifact.byteLength, "annotations.artifact.byteLength") !==
      wasmBytes.length) {
    fail("annotation byte length differs from the WASM artifact");
  }
  const functionIndices = new Set();
  const regionIds = new Set();
  const functions = new Map();
  for (const [functionPosition, function_] of array(
    document.functions, "annotations.functions").entries()) {
    const description = `annotations.functions[${functionPosition}]`;
    exactKeys(function_, [
      "definedFunction", "exports", "locals", "parameters", "regions", "results",
      "sourceName", "wasmIndex",
    ], description);
    natural(function_.wasmIndex, `${description}.wasmIndex`);
    natural(function_.definedFunction, `${description}.definedFunction`);
    natural(function_.locals, `${description}.locals`);
    natural(function_.parameters, `${description}.parameters`);
    natural(function_.results, `${description}.results`);
    string(function_.sourceName, `${description}.sourceName`);
    if (functionIndices.has(function_.wasmIndex)) {
      fail(`duplicate annotated function ${function_.wasmIndex}`);
    }
    functionIndices.add(function_.wasmIndex);
    functions.set(function_.wasmIndex, function_);
    for (const [index, exportName] of array(
      function_.exports, `${description}.exports`).entries()) {
      string(exportName, `${description}.exports[${index}]`);
    }
    for (const [regionIndex, region] of array(
      function_.regions, `${description}.regions`).entries()) {
      if (region?.kind === "leanexe.call.direct.v1") {
        validateDirectCall(region, `${description}.regions[${regionIndex}]`);
      } else if (region?.kind === "leanexe.array.length-dispatch.v1") {
        validateFixedArrayLengthDispatch(region, `${description}.regions[${regionIndex}]`);
      } else if (region?.kind === "leanexe.array.search-key.v1") {
        validateFixedArraySearchKey(region, `${description}.regions[${regionIndex}]`);
      } else if (region?.kind === "leanexe.array.eq-node.v1") {
        validateFixedArrayEqNode(region, `${description}.regions[${regionIndex}]`);
      } else if (region?.kind === "leanexe.array.lt-node.v1") {
        validateFixedArrayLtNode(region, `${description}.regions[${regionIndex}]`);
      } else if (region?.kind === "leanexe.array.pair-result.v1") {
        validateFixedArrayPairResult(region, `${description}.regions[${regionIndex}]`);
      } else {
        fail(`${description}.regions[${regionIndex}].kind is unsupported`);
      }
      if (regionIds.has(region.id)) fail(`duplicate annotation region ${region.id}`);
      regionIds.add(region.id);
    }
  }
  for (const function_ of document.functions) {
    for (const region of function_.regions) {
      if (region.kind !== "leanexe.call.direct.v1") continue;
      const target = functions.get(region.parameters.calleeIndex);
      if (target === undefined) {
        fail(`${region.id}: callee is outside the annotated user functions`);
      }
      if (region.parameters.argumentLocals.length !== target.parameters) {
        fail(`${region.id}: argument count differs from the annotated callee`);
      }
      if (region.parameters.resultPlacement === "locals" &&
          region.parameters.resultLocals.length !== target.results) {
        fail(`${region.id}: local result count differs from the annotated callee`);
      }
    }
  }
  return document;
}

function programFunctionBody(program, functionIndex) {
  const marker = `def func${functionIndex} : Wasm.Program :=\n`;
  const start = program.indexOf(marker);
  if (start < 0) fail(`Talos program has no func${functionIndex}`);
  const bodyStart = start + marker.length;
  const end = program.indexOf(`\n\ndef func${functionIndex}Def : Wasm.Function :=`, bodyStart);
  if (end < 0) fail(`Talos program has no func${functionIndex} definition`);
  return program.slice(bodyStart, end);
}

function indentation(line) {
  return line.length - line.trimStart().length;
}

function instructionPositions(lines, start, end, level) {
  const positions = [];
  for (let index = start; index < end; index += 1) {
    if (indentation(lines[index]) === level && lines[index].trimStart().startsWith(".")) {
      positions.push(index);
    }
  }
  return positions;
}

function resolveInstructionList(body, listPath) {
  const lines = body.split("\n");
  const allInstructions = lines.filter((line) => /^\s+\./.test(line));
  if (allInstructions.length === 0) fail("Talos function body has no instructions");
  let level = Math.min(...allInstructions.map(indentation));
  let start = 0;
  let end = lines.length;
  for (const [pathIndex, step] of listPath.entries()) {
    const positions = instructionPositions(lines, start, end, level);
    const parent = positions[step.instructionIndex];
    if (parent === undefined) {
      fail(`instruction path ${pathIndex} selects a missing instruction`);
    }
    const parentText = lines[parent].trim();
    const expectedPrefix = step.field === "then" || step.field === "else" ? ".iff " :
      step.field === "block" ? ".block " : ".loop ";
    if (!parentText.startsWith(expectedPrefix) || !parentText.endsWith("[")) {
      fail(`instruction path ${pathIndex} selects ${parentText} for ${step.field}`);
    }
    const delimiters = [];
    for (let index = parent + 1; index < end; index += 1) {
      if (indentation(lines[index]) === level && lines[index].trimStart().startsWith("]")) {
        delimiters.push(index);
        if (step.field === "block" || step.field === "loop" || delimiters.length === 2) break;
      }
    }
    if (delimiters.length === 0 ||
        ((step.field === "then" || step.field === "else") && delimiters.length < 2)) {
      fail(`instruction path ${pathIndex} has incomplete ${step.field} delimiters`);
    }
    if (step.field === "then") {
      start = parent + 1;
      end = delimiters[0];
    } else if (step.field === "else") {
      if (!lines[delimiters[0]].trim().startsWith("] [")) {
        fail(`instruction path ${pathIndex} selects a missing else branch`);
      }
      start = delimiters[0] + 1;
      end = delimiters[1];
    } else {
      start = parent + 1;
      end = delimiters[0];
    }
    level += 2;
  }
  return instructionPositions(lines, start, end, level).map((index) => lines[index].trim());
}

function matchDirectCallRegion(program, function_, region) {
  const instructions = resolveInstructionList(
    programFunctionBody(program, function_.wasmIndex), region.location.listPath);
  const selected = instructions.slice(region.location.startIndex, region.location.endIndex);
  if (selected.length !== region.location.endIndex - region.location.startIndex) {
    fail(`${region.id}: instruction interval exceeds func${function_.wasmIndex}`);
  }
  const parameters = region.parameters;
  const localArguments = parameters.argumentLocals.some((local) => local === null) ? [] :
    parameters.argumentLocals;
  const expected = [
    ...localArguments.map((local) => `.localGet ${local},`),
    `.call ${parameters.calleeIndex},`,
    ...[...parameters.resultLocals].reverse().map((local) => `.localSet ${local},`),
  ];
  if (JSON.stringify(normalizeInstructions(selected)) !==
      JSON.stringify(normalizeInstructions(expected))) {
    fail(`${region.id}: decoded instructions do not match the direct-call annotation: ` +
      `expected ${JSON.stringify(expected)}, found ${JSON.stringify(selected)}`);
  }
  return {
    functionIndex: function_.wasmIndex,
    regionId: region.id,
    regionKind: region.kind,
    parameters,
  };
}

function normalizeInstructions(instructions) {
  return instructions.map((instruction) =>
    instruction.endsWith(",") ? instruction.slice(0, -1) : instruction);
}

function matchFixedArrayLengthDispatchRegion(program, function_, region) {
  const body = programFunctionBody(program, function_.wasmIndex);
  const instructions = resolveInstructionList(body, region.location.listPath);
  const selected = instructions.slice(region.location.startIndex, region.location.endIndex);
  const parameters = region.parameters;
  const common = [
    ".localGet 0,",
    `.localSet ${parameters.inputLocal},`,
    `.localGet ${parameters.inputLocal},`,
    ".wrapI64,",
    ".load64 (0 : UInt32),",
    `.constI64 (${parameters.expectedSize} : UInt64),`,
    ".eqI64,",
    ".iff 0 1 [",
  ];
  const expected = parameters.encoding === "eq-normalized-v1" ? [
    ...common,
    ".constI64 (1 : UInt64),",
    ".eqI64,",
    ".iff 0 1 [",
    ".constI64 (0 : UInt64),",
    ".eqI64,",
    ".eqz,",
    ".iff 0 0 [",
  ] : [
    ...common,
    ".constI64 (0 : UInt64),",
    ".eqI64,",
    ".eqz,",
    ".eqz,",
    ".iff 0 1 [",
    ".constI64 (1 : UInt64),",
    ".eqI64,",
    ".iff 0 1 [",
    ".constI64 (0 : UInt64),",
    ".eqI64,",
    ".eqz,",
    ".iff 0 0 [",
  ];
  if (JSON.stringify(normalizeInstructions(selected)) !==
      JSON.stringify(normalizeInstructions(expected))) {
    fail(`${region.id}: decoded instructions do not match the length-dispatch annotation`);
  }
  const booleanIfs = parameters.encoding === "eq-normalized-v1" ? [7, 10] : [7, 12, 15];
  for (const instructionIndex of booleanIfs) {
    for (const [field, value] of [["then", 1], ["else", 0]]) {
      const branch = resolveInstructionList(body, [
        ...region.location.listPath,
        {
          instructionIndex: region.location.startIndex + instructionIndex,
          field,
        },
      ]);
      if (JSON.stringify(normalizeInstructions(branch)) !==
          JSON.stringify([`.constI64 (${value} : UInt64)`])) {
        fail(`${region.id}: Boolean-normalization ${field} branch does not match`);
      }
    }
  }
  return {
    functionIndex: function_.wasmIndex,
    regionId: region.id,
    regionKind: region.kind,
    parameters,
  };
}

function fixedArrayTraversalInstructions(parameters) {
  const pointerLocal = parameters.offset + 5;
  const indexLocal = parameters.offset + 6;
  return [
    ".localGet 0,",
    `.localSet ${pointerLocal},`,
    `.constI64 (${parameters.index} : UInt64),`,
    `.localSet ${indexLocal},`,
    `.localGet ${indexLocal},`,
    `.localGet ${pointerLocal},`,
    ".wrapI64,",
    ".load64 (0 : UInt32),",
    ".ltUI64,",
    ".iff 0 1 [",
  ];
}

function matchFixedArrayTraversalBranches(body, listPath, instructionIndex, parameters,
  regionId) {
  const pointerLocal = parameters.offset + 5;
  const indexLocal = parameters.offset + 6;
  const thenBranch = resolveInstructionList(body, [
    ...listPath,
    { instructionIndex, field: "then" },
  ]);
  const expectedThen = [
    `.localGet ${pointerLocal},`,
    `.localGet ${indexLocal},`,
    ".constI64 (1 : UInt64),",
    ".mulI64,",
    ".constI64 (1 : UInt64),",
    ".addI64,",
    ".constI64 (8 : UInt64),",
    ".mulI64,",
    ".addI64,",
    ".wrapI64,",
    ".load64 (0 : UInt32)",
  ];
  const elseBranch = resolveInstructionList(body, [
    ...listPath,
    { instructionIndex, field: "else" },
  ]);
  if (JSON.stringify(normalizeInstructions(thenBranch)) !==
        JSON.stringify(normalizeInstructions(expectedThen)) ||
      JSON.stringify(normalizeInstructions(elseBranch)) !==
        JSON.stringify([".unreachable"])) {
    fail(`${regionId}: checked traversal branches do not match`);
  }
}

function matchFixedArraySearchKeyRegion(program, function_, region) {
  const body = programFunctionBody(program, function_.wasmIndex);
  const instructions = resolveInstructionList(body, region.location.listPath);
  const selected = instructions.slice(region.location.startIndex, region.location.endIndex);
  const expected = [
    ...fixedArrayTraversalInstructions(region.parameters),
    `.localSet ${region.parameters.keyLocal},`,
  ];
  if (JSON.stringify(normalizeInstructions(selected)) !==
      JSON.stringify(normalizeInstructions(expected))) {
    fail(`${region.id}: decoded instructions do not match the search-key annotation`);
  }
  matchFixedArrayTraversalBranches(body, region.location.listPath,
    region.location.startIndex + 9, region.parameters, region.id);
  return {
    functionIndex: function_.wasmIndex,
    regionId: region.id,
    regionKind: region.kind,
    parameters: region.parameters,
  };
}

function matchFixedArrayEqNodeRegion(program, function_, region) {
  const body = programFunctionBody(program, function_.wasmIndex);
  const instructions = resolveInstructionList(body, region.location.listPath);
  const selected = instructions.slice(region.location.startIndex, region.location.endIndex);
  const loader = fixedArrayTraversalInstructions(region.parameters);
  const expected = region.parameters.operandOrder === "loaded-first" ? [
    ...loader,
    `.localGet ${region.parameters.keyLocal},`,
    ".eqI64,",
    ".iff 0 1 [",
    ".constI64 (0 : UInt64),",
    ".eqI64,",
    ".eqz,",
    ".iff 0 0 [",
  ] : [
    `.localGet ${region.parameters.keyLocal},`,
    ...loader,
    ".eqI64,",
    ".iff 0 1 [",
    ".constI64 (0 : UInt64),",
    ".eqI64,",
    ".eqz,",
    ".iff 0 0 [",
  ];
  if (JSON.stringify(normalizeInstructions(selected)) !==
      JSON.stringify(normalizeInstructions(expected))) {
    fail(`${region.id}: decoded instructions do not match the equality-node annotation`);
  }
  const loaderIf = region.location.startIndex +
    (region.parameters.operandOrder === "loaded-first" ? 9 : 10);
  matchFixedArrayTraversalBranches(body, region.location.listPath,
    loaderIf, region.parameters, region.id);
  const normalizationIf = region.location.startIndex + 12;
  for (const [field, value] of [["then", 1], ["else", 0]]) {
    const branch = resolveInstructionList(body, [
      ...region.location.listPath,
      { instructionIndex: normalizationIf, field },
    ]);
    if (JSON.stringify(normalizeInstructions(branch)) !==
        JSON.stringify([`.constI64 (${value} : UInt64)`])) {
      fail(`${region.id}: equality normalization ${field} branch does not match`);
    }
  }
  return {
    functionIndex: function_.wasmIndex,
    regionId: region.id,
    regionKind: region.kind,
    parameters: region.parameters,
  };
}

function matchFixedArrayLtNodeRegion(program, function_, region) {
  const body = programFunctionBody(program, function_.wasmIndex);
  const instructions = resolveInstructionList(body, region.location.listPath);
  const selected = instructions.slice(region.location.startIndex, region.location.endIndex);
  const expected = [
    `.localGet ${region.parameters.keyLocal},`,
    ...fixedArrayTraversalInstructions(region.parameters),
    ".ltUI64,",
    ".iff 0 0 [",
  ];
  if (JSON.stringify(normalizeInstructions(selected)) !==
      JSON.stringify(normalizeInstructions(expected))) {
    fail(`${region.id}: decoded instructions do not match the less-than-node annotation`);
  }
  matchFixedArrayTraversalBranches(body, region.location.listPath,
    region.location.startIndex + 10, region.parameters, region.id);
  return {
    functionIndex: function_.wasmIndex,
    regionId: region.id,
    regionKind: region.kind,
    parameters: region.parameters,
  };
}

function matchFixedArrayPairResultRegion(program, function_, region) {
  const body = programFunctionBody(program, function_.wasmIndex);
  const instructions = resolveInstructionList(body, region.location.listPath);
  const selected = instructions.slice(region.location.startIndex, region.location.endIndex);
  if (selected.length !== region.location.endIndex - region.location.startIndex) {
    fail(`${region.id}: decoded pair-result region is truncated`);
  }
  if (normalizeInstructions(selected)[0] !== ".constI64 (8 : UInt64)" ||
      normalizeInstructions(selected).at(-1) !== `.localSet 14`) {
    fail(`${region.id}: decoded pair-result boundary does not match`);
  }
  return {
    functionIndex: function_.wasmIndex,
    regionId: region.id,
    regionKind: region.kind,
    parameters: region.parameters,
  };
}

function directCallRecipe(match, selectedSections = [], tacticEligible = false) {
  const guidance = ["strategy.calls", "strategy.frames"]
    .filter((section) => selectedSections.includes(section));
  const direct = {
    module: "Project.ProofKit.Control",
    theorem: "Wasm.wp_call_tw",
  };
  if (tacticEligible) {
    direct.tactic = "wp_entry_single_call";
    direct.invocation = `wp_entry_single_call func${match.functionIndex}Def ` +
      `unfolding func${match.functionIndex} as initial' using <callee-theorem>`;
  }
  return {
    recipeVersion: 1,
    functionIndex: match.functionIndex,
    regionId: match.regionId,
    regionKind: match.regionKind,
    applicability: "exact decoded instruction match",
    direct,
    supporting: [
      {
        declaration: "Wasm.wp_call_tw",
        purpose: "apply the callee theorem to the exact direct call",
      },
      {
        declaration: "Project.ProofKit.wp_entry",
        purpose: "establish the entry frame before the call",
      },
    ],
    expectedPostcondition: "the callee result restored into the caller continuation",
    guidance,
  };
}

function fixedArrayLengthDispatchRecipe(match, selectedSections = []) {
  const equality = match.parameters.encoding === "eq-normalized-v1";
  return {
    recipeVersion: 1,
    functionIndex: match.functionIndex,
    regionId: match.regionId,
    regionKind: match.regionKind,
    applicability: "exact decoded instruction match",
    direct: {
      module: "Project.ProofKit.FixedArrayLengthDispatch",
      theorem: equality
        ? "Project.ProofKit.FixedArrayLengthDispatch.eqProgram_spec"
        : "Project.ProofKit.FixedArrayLengthDispatch.program_spec",
      tactic: equality
        ? "wp_fixed_array_length_eq_dispatch"
        : "wp_fixed_array_length_dispatch",
      invocation: equality
        ? `wp_fixed_array_length_eq_dispatch ${match.parameters.inputLocal}, ` +
          `${match.parameters.expectedSize}`
        : `wp_fixed_array_length_dispatch ${match.parameters.inputLocal}, ` +
          `${match.parameters.expectedSize}`,
    },
    supporting: [
      {
        declaration: "Project.ProofKit.UInt64Array.At.lengthRead",
        purpose: "identify the represented input length",
      },
      {
        declaration: "Project.ProofKit.UInt64Array.At.encodedSize_eq",
        purpose: "relate the encoded length word to the fixed logical size",
      },
      {
        declaration: "Project.ProofKit.FixedArrayEqNode.branchPost",
        purpose: "preserve the enclosing branch continuation",
      },
    ],
    expectedPostcondition: "valid and invalid input-size branch obligations",
    guidance: ["strategy.arrays", "strategy.frames"]
      .filter((section) => selectedSections.includes(section)),
  };
}

function fixedArraySearchKeyRecipe(match, selectedSections = []) {
  return {
    recipeVersion: 1,
    functionIndex: match.functionIndex,
    regionId: match.regionId,
    regionKind: match.regionKind,
    applicability: "exact decoded instruction match",
    direct: {
      module: "Project.ProofKit.FixedArrayEqNode",
      theorem: "Project.ProofKit.FixedArrayEqNode.loadKeyProgram_spec",
      tactic: "wp_fixed_array_search_key",
      invocation: `wp_fixed_array_search_key ${match.parameters.offset}, ` +
        `${match.parameters.index}, ${match.parameters.keyLocal}`,
    },
    supporting: [
      {
        declaration: "Project.ProofKit.FixedArrayEqNode.SearchFrame",
        purpose: "record the input pointer, local shape, empty stack, and saved key",
      },
      {
        declaration: "Project.ProofKit.FixedArrayEqNode.SearchFrame.afterLoad",
        purpose: "preserve the saved key across a checked traversal load",
      },
      {
        declaration: "Project.ProofKit.FixedArrayEqNode.SearchFrame.branch",
        purpose: "preserve the search frame at either equality-node branch",
      },
    ],
    expectedPostcondition: "the comparison key saved in the annotated local",
    guidance: ["strategy.arrays", "strategy.frames"]
      .filter((section) => selectedSections.includes(section)),
  };
}

function fixedArrayEqNodeRecipe(match, selectedSections = []) {
  const keyFirst = match.parameters.operandOrder === "key-first";
  return {
    recipeVersion: 1,
    functionIndex: match.functionIndex,
    regionId: match.regionId,
    regionKind: match.regionKind,
    applicability: "exact decoded instruction match",
    direct: {
      module: "Project.ProofKit.FixedArrayEqNode",
      theorem: keyFirst
        ? "Project.ProofKit.FixedArrayEqNode.keyFirstProgram_spec"
        : "Project.ProofKit.FixedArrayEqNode.program_spec",
      tactic: keyFirst ? "wp_fixed_array_key_eq_node" : "wp_fixed_array_eq_node",
      invocation: `${keyFirst ? "wp_fixed_array_key_eq_node" : "wp_fixed_array_eq_node"} ` +
        `${match.parameters.offset}, ${match.parameters.index}, ` +
        `${match.parameters.keyLocal}`,
    },
    supporting: [
      {
        declaration: "Project.ProofKit.FixedArrayEqNode.SearchFrame.afterLoad",
        purpose: "discharge the saved-key premise without expanding local updates",
      },
      {
        declaration: "Project.ProofKit.FixedArrayEqNode.SearchFrame.branch",
        purpose: "carry the shared search-frame invariant into either branch",
      },
      {
        declaration: "Project.ProofKit.FixedArrayEqNode.branchN",
        purpose: "represent the nested branch continuations by a branch count",
      },
      {
        declaration: "Project.ProofKit.FixedArraySearch.pairPost_branchN_conseq",
        purpose: "compose a pair-result theorem through the remaining branch continuations",
      },
    ],
    expectedPostcondition: "equal and unequal branch obligations with a preserved search frame",
    guidance: ["strategy.arrays", "strategy.frames"]
      .filter((section) => selectedSections.includes(section)),
  };
}

function fixedArrayLtNodeRecipe(match, selectedSections = []) {
  return {
    recipeVersion: 1,
    functionIndex: match.functionIndex,
    regionId: match.regionId,
    regionKind: match.regionKind,
    applicability: "exact decoded instruction match",
    direct: {
      module: "Project.ProofKit.FixedArrayLtNode",
      theorem: "Project.ProofKit.FixedArrayLtNode.program_spec",
      tactic: "wp_fixed_array_lt_node",
      invocation: `wp_fixed_array_lt_node ${match.parameters.offset}, ` +
        `${match.parameters.index}, ${match.parameters.keyLocal}`,
    },
    supporting: [
      {
        declaration: "Project.ProofKit.FixedArrayEqNode.SearchFrame",
        purpose: "supply the saved key and shared frame facts",
      },
      {
        declaration: "Project.ProofKit.FixedArrayEqNode.SearchFrame.branch",
        purpose: "carry the search frame into either ordering branch",
      },
      {
        declaration: "Project.ProofKit.FixedArrayEqNode.branchN",
        purpose: "represent nested equality and ordering continuations by a branch count",
      },
    ],
    expectedPostcondition: "key-less-than-element and not-less-than branch obligations",
    guidance: ["strategy.arrays", "strategy.frames"]
      .filter((section) => selectedSections.includes(section)),
  };
}

function annotationMatchTheoremName(
    regionId, annotationNamespace = "Project.AnnotationMatches") {
  return `${annotationNamespace}.${regionId.replace(/[^A-Za-z0-9_]/g, "_")}_eq`;
}

function fixedArrayPairResultRecipe(
    match, selectedSections = [], annotationNamespace = "Project.AnnotationMatches") {
  const constants = match.parameters.mode === "constants-v1";
  const theorem = constants
    ? "Project.ProofKit.FixedArrayPairResult.constResultProgram_spec"
    : "Project.ProofKit.FixedArrayPairResult.inputResultProgram_spec";
  const program = constants
    ? `Project.ProofKit.FixedArrayPairResult.constResultProgram ` +
      `${match.parameters.firstValue} ${match.parameters.secondValue} ` +
      `${match.parameters.destination}`
    : `Project.ProofKit.FixedArrayPairResult.inputResultProgram ` +
      `${match.parameters.inputIndex} ${match.parameters.destination}`;
  return {
    recipeVersion: 1,
    functionIndex: match.functionIndex,
    regionId: match.regionId,
    regionKind: match.regionKind,
    applicability: "Lean-checked equality over the decoded instruction region",
    direct: {
      module: "Project.ProofKit.FixedArrayPairResult",
      theorem,
      regionEquality: annotationMatchTheoremName(match.regionId, annotationNamespace),
      program,
    },
    supporting: [
      {
        declaration: "Project.ProofKit.Annotation.region",
        purpose: "select the exact structured instruction region",
      },
      {
        declaration: "Project.ProofKit.FixedArrayPairResult.pairPost_conseq",
        purpose: "connect the represented pair to the public result continuation",
      },
    ],
    expectedPostcondition: "a represented two-word Array UInt64 result",
    guidance: ["strategy.arrays", "strategy.allocation", "strategy.frames"]
      .filter((section) => selectedSections.includes(section)),
  };
}

function locationFieldOrder(field) {
  return field === "else" ? 1 : 0;
}

function compareRegionLocations(left, right) {
  const leftPath = left.location.listPath;
  const rightPath = right.location.listPath;
  let index = 0;
  while (index < leftPath.length && index < rightPath.length) {
    if (leftPath[index].instructionIndex !== rightPath[index].instructionIndex) {
      return leftPath[index].instructionIndex - rightPath[index].instructionIndex;
    }
    const fieldDifference = locationFieldOrder(leftPath[index].field) -
      locationFieldOrder(rightPath[index].field);
    if (fieldDifference !== 0) return fieldDifference;
    index += 1;
  }
  if (index === leftPath.length && index === rightPath.length) {
    return left.location.startIndex - right.location.startIndex ||
      left.location.endIndex - right.location.endIndex || left.id.localeCompare(right.id);
  }
  if (index === leftPath.length) {
    const difference = left.location.startIndex - rightPath[index].instructionIndex;
    return difference === 0 ? -1 : difference;
  }
  const difference = leftPath[index].instructionIndex - right.location.startIndex;
  return difference === 0 ? 1 : difference;
}

function proofRecipePlan(
    document, program, selectedSections = [],
    annotationNamespace = "Project.AnnotationMatches") {
  const matches = new Map(matchAnnotationDocument(document, program)
    .map((match) => [match.regionId, match]));
  const recipes = [];
  for (const function_ of document.functions) {
    const body = programFunctionBody(program, function_.wasmIndex);
    const decodedCallCount = (body.match(/^\s*\.call [0-9]+,?$/gm) || []).length;
    const orderedRegions = [...function_.regions].sort(compareRegionLocations);
    for (const region of orderedRegions) {
      if (region.kind === "leanexe.call.direct.v1") {
        const directCalls = function_.regions.filter(
          (candidate) => candidate.kind === "leanexe.call.direct.v1");
        const tacticEligible = directCalls.length === 1 && directCalls[0].id === region.id &&
          region.location.listPath.length === 0 && decodedCallCount === 1;
        recipes.push(directCallRecipe(
          matches.get(region.id), selectedSections, tacticEligible));
      } else if (region.kind === "leanexe.array.length-dispatch.v1") {
        recipes.push(fixedArrayLengthDispatchRecipe(
          matches.get(region.id), selectedSections));
      } else if (region.kind === "leanexe.array.search-key.v1") {
        recipes.push(fixedArraySearchKeyRecipe(
          matches.get(region.id), selectedSections));
      } else if (region.kind === "leanexe.array.eq-node.v1") {
        recipes.push(fixedArrayEqNodeRecipe(
          matches.get(region.id), selectedSections));
      } else if (region.kind === "leanexe.array.lt-node.v1") {
        recipes.push(fixedArrayLtNodeRecipe(
          matches.get(region.id), selectedSections));
      } else {
        recipes.push(fixedArrayPairResultRecipe(
          matches.get(region.id), selectedSections, annotationNamespace));
      }
    }
  }
  const compositionPlan = (composition, kind, moduleName, typeName) => {
    const result = {
      compositionVersion: composition.wrapper === null ? 1 : 2,
      kind,
      functionIndex: composition.functionIndex,
      descriptor: `${annotationNamespace}.${composition.name}`,
      regionEquality: `${annotationNamespace}.${composition.name}_eq`,
      direct: {
        module: moduleName,
        theorem: `${moduleName}.${typeName}.` +
          `${composition.wrapper === null ? "program_spec" : "wrapperProgram_spec"}`,
      },
    };
    if (composition.wrapper !== null) result.wrapper = composition.wrapper;
    return result;
  };
  return {
    schemaVersion: 1,
    attemptOrder: ["direct", "composition", "tactic", "focused-guidance"],
    compositions: [
      ...fixedArraySearchTreeCompositions(document, program).map((composition) =>
        compositionPlan(composition, "fixed-array-search-tree-v1",
          "Project.ProofKit.FixedArraySearchTree", "Tree")),
      ...fixedArraySearchChainCompositions(document, program).map((composition) =>
        compositionPlan(composition, "fixed-array-search-chain-v1",
          "Project.ProofKit.FixedArraySearchChain", "Chain")),
    ],
    recipes,
  };
}

function matchAnnotationDocument(document, program) {
  const matches = [];
  const userFunctions = new Set(document.functions.map((function_) => function_.wasmIndex));
  for (const function_ of document.functions) {
    const body = programFunctionBody(program, function_.wasmIndex);
    const decodedCallees = [...body.matchAll(/^\s*\.call ([0-9]+),?$/gm)]
      .map((match) => Number(match[1])).filter((callee) => userFunctions.has(callee));
    const annotatedCallees = function_.regions
      .filter((region) => region.kind === "leanexe.call.direct.v1")
      .map((region) => region.parameters.calleeIndex);
    if (JSON.stringify(decodedCallees) !== JSON.stringify(annotatedCallees)) {
      fail(`func${function_.wasmIndex}: annotations do not cover its decoded user calls`);
    }
    for (const region of function_.regions) {
      if (region.kind === "leanexe.call.direct.v1") {
        matches.push(matchDirectCallRegion(program, function_, region));
      } else if (region.kind === "leanexe.array.length-dispatch.v1") {
        matches.push(matchFixedArrayLengthDispatchRegion(program, function_, region));
      } else if (region.kind === "leanexe.array.search-key.v1") {
        matches.push(matchFixedArraySearchKeyRegion(program, function_, region));
      } else if (region.kind === "leanexe.array.eq-node.v1") {
        matches.push(matchFixedArrayEqNodeRegion(program, function_, region));
      } else if (region.kind === "leanexe.array.lt-node.v1") {
        matches.push(matchFixedArrayLtNodeRegion(program, function_, region));
      } else {
        matches.push(matchFixedArrayPairResultRegion(program, function_, region));
      }
    }
  }
  return matches;
}

function validateProofRecipePlan(plan, document) {
  const planKeys = Object.keys(plan).sort();
  const legacyKeys = ["attemptOrder", "recipes", "schemaVersion"];
  const currentKeys = ["attemptOrder", "compositions", "recipes", "schemaVersion"];
  if (JSON.stringify(planKeys) !== JSON.stringify(legacyKeys) &&
      JSON.stringify(planKeys) !== JSON.stringify(currentKeys)) {
    fail("proof recipes has unsupported fields");
  }
  if (plan.schemaVersion !== 1) fail("unsupported proof-recipe schema");
  const expectedOrder = ["direct", "composition", "tactic", "focused-guidance"];
  if (JSON.stringify(plan.attemptOrder) !== JSON.stringify(expectedOrder)) {
    fail("proof recipes have an unsupported attempt order");
  }
  const annotatedFunctions = new Set(document.functions.map((function_) =>
    function_.wasmIndex));
  const compositionDescriptors = new Set();
  for (const [index, composition] of array(
    plan.compositions ?? [], "proof recipes.compositions").entries()) {
    const description = `proof recipes.compositions[${index}]`;
    const compositionKeys = [
      "compositionVersion", "descriptor", "direct", "functionIndex", "kind",
      "regionEquality",
    ];
    if (composition.compositionVersion === 2) compositionKeys.push("wrapper");
    exactKeys(composition, compositionKeys, description);
    if (![1, 2].includes(composition.compositionVersion) ||
        !["fixed-array-search-chain-v1", "fixed-array-search-tree-v1"].includes(
          composition.kind)) {
      fail(`${description} has an unsupported identity`);
    }
    natural(composition.functionIndex, `${description}.functionIndex`);
    string(composition.descriptor, `${description}.descriptor`);
    string(composition.regionEquality, `${description}.regionEquality`);
    if (!annotatedFunctions.has(composition.functionIndex) ||
        compositionDescriptors.has(composition.descriptor) ||
        composition.regionEquality !== `${composition.descriptor}_eq`) {
      fail(`${description} has an invalid artifact identity`);
    }
    compositionDescriptors.add(composition.descriptor);
    exactKeys(composition.direct, ["module", "theorem"], `${description}.direct`);
    const chain = composition.kind === "fixed-array-search-chain-v1";
    const expectedModule = chain
      ? "Project.ProofKit.FixedArraySearchChain"
      : "Project.ProofKit.FixedArraySearchTree";
    const expectedTheorem = `${expectedModule}.${chain ? "Chain" : "Tree"}.` +
      `${composition.compositionVersion === 1 ? "program_spec" : "wrapperProgram_spec"}`;
    if (composition.direct.module !== expectedModule ||
        composition.direct.theorem !== expectedTheorem) {
      fail(`${description}.direct is unsupported`);
    }
    if (composition.compositionVersion === 2) {
      exactKeys(composition.wrapper, [
        "expectedSize", "inputLocal", "invalidDestination", "keyIndex", "keyLocal",
        "offset",
      ], `${description}.wrapper`);
      for (const field of [
        "expectedSize", "inputLocal", "invalidDestination", "keyIndex", "keyLocal",
        "offset",
      ]) natural(composition.wrapper[field], `${description}.wrapper.${field}`);
      if (composition.wrapper.offset + 14 !== 24 ||
          composition.wrapper.keyLocal >= composition.wrapper.offset + 5 ||
          composition.wrapper.invalidDestination === 0 ||
          composition.wrapper.invalidDestination >= 25) {
        fail(`${description}.wrapper has invalid fixed-array parameters`);
      }
    }
  }
  const regions = new Map(document.functions.flatMap((function_) =>
    function_.regions.map((region) => [region.id, {
      functionIndex: function_.wasmIndex,
      kind: region.kind,
      parameters: region.parameters,
    }])));
  const found = new Set();
  for (const [index, recipe] of array(plan.recipes, "proof recipes.recipes").entries()) {
    const description = `proof recipes.recipes[${index}]`;
    exactKeys(recipe, [
      "applicability", "direct", "expectedPostcondition", "functionIndex", "guidance",
      "recipeVersion", "regionId", "regionKind", "supporting",
    ], description);
    natural(recipe.functionIndex, `${description}.functionIndex`);
    if (recipe.recipeVersion !== 1 ||
        !regions.has(recipe.regionId) || found.has(recipe.regionId) ||
        recipe.functionIndex !== regions.get(recipe.regionId).functionIndex ||
        recipe.regionKind !== regions.get(recipe.regionId).kind) {
      fail(`${description} has an invalid identity`);
    }
    const region = regions.get(recipe.regionId);
    const expectedApplicability = region.kind === "leanexe.array.pair-result.v1"
      ? "Lean-checked equality over the decoded instruction region"
      : "exact decoded instruction match";
    if (recipe.applicability !== expectedApplicability) {
      fail(`${description} has an invalid applicability check`);
    }
    found.add(recipe.regionId);
    if (recipe.direct === null || typeof recipe.direct !== "object" ||
        Array.isArray(recipe.direct)) {
      fail(`${description}.direct must be an object`);
    }
    const directKeys = Object.keys(recipe.direct).sort();
    if (JSON.stringify(directKeys) !== JSON.stringify(["module", "theorem"]) &&
        JSON.stringify(directKeys) !==
          JSON.stringify(["invocation", "module", "tactic", "theorem"]) &&
        JSON.stringify(directKeys) !==
          JSON.stringify(["module", "program", "regionEquality", "theorem"])) {
      fail(`${description}.direct has unsupported fields`);
    }
    if (region.kind === "leanexe.call.direct.v1") {
      if (recipe.direct.module !== "Project.ProofKit.Control" ||
          recipe.direct.theorem !== "Wasm.wp_call_tw" ||
          (recipe.direct.tactic !== undefined &&
            (recipe.direct.tactic !== "wp_entry_single_call" ||
              typeof recipe.direct.invocation !== "string"))) {
        fail(`${description}.direct is unsupported`);
      }
    } else if (region.kind === "leanexe.array.length-dispatch.v1") {
      const equality = region.parameters.encoding === "eq-normalized-v1";
      const theorem = equality
        ? "Project.ProofKit.FixedArrayLengthDispatch.eqProgram_spec"
        : "Project.ProofKit.FixedArrayLengthDispatch.program_spec";
      const tactic = equality
        ? "wp_fixed_array_length_eq_dispatch"
        : "wp_fixed_array_length_dispatch";
      if (recipe.direct.module !== "Project.ProofKit.FixedArrayLengthDispatch" ||
          recipe.direct.theorem !== theorem || recipe.direct.tactic !== tactic ||
          typeof recipe.direct.invocation !== "string") {
        fail(`${description}.direct is unsupported`);
      }
    } else if (region.kind === "leanexe.array.search-key.v1") {
      if (recipe.direct.module !== "Project.ProofKit.FixedArrayEqNode" ||
          recipe.direct.theorem !==
            "Project.ProofKit.FixedArrayEqNode.loadKeyProgram_spec" ||
          recipe.direct.tactic !== "wp_fixed_array_search_key" ||
          typeof recipe.direct.invocation !== "string") {
        fail(`${description}.direct is unsupported`);
      }
    } else if (region.kind === "leanexe.array.eq-node.v1") {
      const keyFirst = region.parameters.operandOrder === "key-first";
      const theorem = keyFirst
        ? "Project.ProofKit.FixedArrayEqNode.keyFirstProgram_spec"
        : "Project.ProofKit.FixedArrayEqNode.program_spec";
      const tactic = keyFirst ? "wp_fixed_array_key_eq_node" : "wp_fixed_array_eq_node";
      if (recipe.direct.module !== "Project.ProofKit.FixedArrayEqNode" ||
          recipe.direct.theorem !== theorem || recipe.direct.tactic !== tactic ||
          typeof recipe.direct.invocation !== "string") {
        fail(`${description}.direct is unsupported`);
      }
    } else if (region.kind === "leanexe.array.lt-node.v1") {
      if (recipe.direct.module !== "Project.ProofKit.FixedArrayLtNode" ||
          recipe.direct.theorem !== "Project.ProofKit.FixedArrayLtNode.program_spec" ||
          recipe.direct.tactic !== "wp_fixed_array_lt_node" ||
          typeof recipe.direct.invocation !== "string") {
        fail(`${description}.direct is unsupported`);
      }
    } else if (recipe.direct.module !== "Project.ProofKit.FixedArrayPairResult" ||
        ![
          "Project.ProofKit.FixedArrayPairResult.constResultProgram_spec",
          "Project.ProofKit.FixedArrayPairResult.inputResultProgram_spec",
        ].includes(recipe.direct.theorem) ||
        !recipe.direct.regionEquality.endsWith(
          `.${recipe.regionId.replace(/[^A-Za-z0-9_]/g, "_")}_eq`) ||
        typeof recipe.direct.program !== "string") {
      fail(`${description}.direct is unsupported`);
    }
    for (const [supportingIndex, supporting] of array(
      recipe.supporting, `${description}.supporting`).entries()) {
      exactKeys(supporting, ["declaration", "purpose"],
        `${description}.supporting[${supportingIndex}]`);
      string(supporting.declaration,
        `${description}.supporting[${supportingIndex}].declaration`);
      string(supporting.purpose,
        `${description}.supporting[${supportingIndex}].purpose`);
    }
    for (const [guidanceIndex, guidance] of array(
      recipe.guidance, `${description}.guidance`).entries()) {
      string(guidance, `${description}.guidance[${guidanceIndex}]`);
    }
    if (typeof recipe.expectedPostcondition !== "string" ||
        recipe.expectedPostcondition.length === 0) {
      fail(`${description} has invalid supporting guidance`);
    }
  }
  if (found.size !== regions.size) {
    fail("proof recipes do not cover every annotated region");
  }
  return plan;
}

function leanAnnotationPath(listPath) {
  const fields = {
    block: "block",
    loop: "loop",
    then: "thenBranch",
    else: "elseBranch",
  };
  return `[${listPath.map((step) =>
    `{ instructionIndex := ${step.instructionIndex}, field := .${fields[step.field]} }`)
    .join(", ")}]`;
}

function annotationPathKey(listPath) {
  return JSON.stringify(listPath.map((step) => [step.instructionIndex, step.field]));
}

function annotationChildPath(listPath, instructionIndex, field) {
  return [...listPath, { instructionIndex, field }];
}

function annotationPathStartsWith(listPath, prefix) {
  return prefix.length <= listPath.length && prefix.every((step, index) =>
    step.instructionIndex === listPath[index].instructionIndex &&
      step.field === listPath[index].field);
}

function fixedArraySearchWrapper(function_, root, program) {
  if (program === null) return null;
  const length = function_.regions.find((region) =>
    region.kind === "leanexe.array.length-dispatch.v1" &&
    region.parameters.encoding === "ne-normalized-v1" &&
    region.location.listPath.length === 0 && region.location.startIndex === 0);
  if (length === undefined) return null;
  const branchIndex = length.location.endIndex - 1;
  const validPath = annotationChildPath([], branchIndex,
    length.parameters.validBranch);
  const invalidPath = annotationChildPath([], branchIndex,
    length.parameters.invalidBranch);
  const searchKey = function_.regions.find((region) =>
    region.kind === "leanexe.array.search-key.v1" &&
    annotationPathKey(region.location.listPath) === annotationPathKey(validPath) &&
    region.location.startIndex === 0 &&
    region.location.endIndex === root.location.startIndex &&
    region.parameters.offset === root.parameters.offset &&
    region.parameters.keyLocal === root.parameters.keyLocal);
  const invalidResult = function_.regions.find((region) =>
    region.kind === "leanexe.array.pair-result.v1" &&
    annotationPathKey(region.location.listPath) === annotationPathKey(invalidPath) &&
    region.location.startIndex === 0 &&
    region.parameters.mode === "constants-v1" &&
    region.parameters.firstValue === "0" &&
    region.parameters.secondValue === "0" &&
    region.parameters.offset === root.parameters.offset);
  const body = programFunctionBody(program, function_.wasmIndex);
  const topInstructions = resolveInstructionList(body, []);
  const validInstructions = resolveInstructionList(body, validPath);
  const invalidInstructions = resolveInstructionList(body, invalidPath);
  if (searchKey === undefined || invalidResult === undefined ||
      root.location.listPath.length !== 1 ||
      annotationPathKey(root.location.listPath) !== annotationPathKey(validPath) ||
      root.location.endIndex !== validInstructions.length ||
      invalidResult.location.endIndex !== invalidInstructions.length ||
      length.location.endIndex !== topInstructions.length - 1 ||
      normalizeInstructions(topInstructions).at(-1) !== ".localGet 14") return null;
  return {
    expectedSize: length.parameters.expectedSize,
    inputLocal: length.parameters.inputLocal,
    invalidDestination: invalidResult.parameters.destination,
    keyIndex: searchKey.parameters.index,
    keyLocal: searchKey.parameters.keyLocal,
    offset: searchKey.parameters.offset,
  };
}

function fixedArraySearchTreeCompositions(document, program = null) {
  const compositions = [];
  for (const function_ of document.functions) {
    const equalityNodes = function_.regions.filter((region) =>
      region.kind === "leanexe.array.eq-node.v1" &&
      region.parameters.operandOrder === "key-first");
    const equalityByPath = new Map(equalityNodes.map((region) =>
      [annotationPathKey(region.location.listPath), region]));
    const lessThanByPath = new Map(function_.regions.filter((region) =>
      region.kind === "leanexe.array.lt-node.v1").map((region) =>
      [annotationPathKey(region.location.listPath), region]));
    const resultByPath = new Map(function_.regions.filter((region) =>
      region.kind === "leanexe.array.pair-result.v1").map((region) =>
      [annotationPathKey(region.location.listPath), region]));

    const build = (equality, visiting) => {
      if (visiting.has(equality.id)) return null;
      const nextVisiting = new Set(visiting);
      nextVisiting.add(equality.id);
      const branchIndex = equality.location.startIndex + 16;
      const equalPath = annotationChildPath(
        equality.location.listPath, branchIndex, "then");
      const unequalPath = annotationChildPath(
        equality.location.listPath, branchIndex, "else");
      const found = resultByPath.get(annotationPathKey(equalPath));
      if (found === undefined || found.parameters.mode !== "input-index-and-one-v1" ||
          found.parameters.secondValue !== "1" ||
          found.parameters.offset !== equality.parameters.offset) return null;
      const lessThan = lessThanByPath.get(annotationPathKey(unequalPath));
      if (lessThan === undefined) {
        const missing = resultByPath.get(annotationPathKey(unequalPath));
        if (missing === undefined || missing.parameters.mode !== "constants-v1" ||
            missing.parameters.firstValue !== "0" ||
            missing.parameters.secondValue !== "0" ||
            missing.parameters.offset !== equality.parameters.offset) return null;
        return `.leaf ${equality.parameters.index} ${found.parameters.inputIndex} ` +
          `${found.parameters.destination} ${missing.parameters.destination}`;
      }
      if (lessThan.parameters.offset !== equality.parameters.offset ||
          lessThan.parameters.index !== equality.parameters.index ||
          lessThan.parameters.keyLocal !== equality.parameters.keyLocal) return null;
      const leftPath = annotationChildPath(
        unequalPath, lessThan.location.startIndex + 12, "then");
      const rightPath = annotationChildPath(
        unequalPath, lessThan.location.startIndex + 12, "else");
      const left = equalityByPath.get(annotationPathKey(leftPath));
      const right = equalityByPath.get(annotationPathKey(rightPath));
      if (left === undefined || right === undefined) return null;
      const leftTree = build(left, nextVisiting);
      const rightTree = build(right, nextVisiting);
      if (leftTree === null || rightTree === null) return null;
      return `.branch ${equality.parameters.index} ${found.parameters.inputIndex} ` +
        `${found.parameters.destination} (${leftTree}) (${rightTree})`;
    };

    const roots = equalityNodes.filter((candidate) => !equalityNodes.some((parent) => {
      if (candidate.id === parent.id) return false;
      const thenPath = annotationChildPath(parent.location.listPath,
        parent.location.startIndex + 16, "then");
      const elsePath = annotationChildPath(parent.location.listPath,
        parent.location.startIndex + 16, "else");
      return annotationPathStartsWith(candidate.location.listPath, thenPath) ||
        annotationPathStartsWith(candidate.location.listPath, elsePath);
    }));
    let compositionIndex = 0;
    for (const root of roots) {
      const tree = build(root, new Set());
      if (tree === null || root.parameters.offset + 14 !== 24) continue;
      const wrapper = fixedArraySearchWrapper(function_, root, program);
      const name = `function_${function_.wasmIndex}_search_tree_${compositionIndex}`;
      compositionIndex += 1;
      compositions.push({
        functionIndex: function_.wasmIndex,
        keyLocal: root.parameters.keyLocal,
        location: root.location,
        name,
        offset: root.parameters.offset,
        tree,
        wrapper,
      });
    }
  }
  return compositions;
}

function fixedArraySearchChainCompositions(document, program = null) {
  const compositions = [];
  for (const function_ of document.functions) {
    const equalityNodes = function_.regions.filter((region) =>
      region.kind === "leanexe.array.eq-node.v1" &&
      region.parameters.operandOrder === "loaded-first");
    const equalityByPath = new Map(equalityNodes.map((region) =>
      [annotationPathKey(region.location.listPath), region]));
    const resultByPath = new Map(function_.regions.filter((region) =>
      region.kind === "leanexe.array.pair-result.v1").map((region) =>
      [annotationPathKey(region.location.listPath), region]));

    const build = (equality, visiting) => {
      if (visiting.has(equality.id)) return null;
      const nextVisiting = new Set(visiting);
      nextVisiting.add(equality.id);
      const branchIndex = equality.location.startIndex + 16;
      const equalPath = annotationChildPath(
        equality.location.listPath, branchIndex, "then");
      const unequalPath = annotationChildPath(
        equality.location.listPath, branchIndex, "else");
      const found = resultByPath.get(annotationPathKey(equalPath));
      if (found === undefined || found.parameters.mode !== "input-index-and-one-v1" ||
          found.parameters.secondValue !== "1" ||
          found.parameters.offset !== equality.parameters.offset) return null;
      const next = equalityByPath.get(annotationPathKey(unequalPath));
      if (next !== undefined) {
        const tail = build(next, nextVisiting);
        if (tail === null) return null;
        return `.next ${equality.parameters.index} ${found.parameters.inputIndex} ` +
          `${found.parameters.destination} (${tail})`;
      }
      const missing = resultByPath.get(annotationPathKey(unequalPath));
      if (missing === undefined || missing.parameters.mode !== "constants-v1" ||
          missing.parameters.firstValue !== "0" ||
          missing.parameters.secondValue !== "0" ||
          missing.parameters.offset !== equality.parameters.offset) return null;
      return `.last ${equality.parameters.index} ${found.parameters.inputIndex} ` +
        `${found.parameters.destination} ${missing.parameters.destination}`;
    };

    const roots = equalityNodes.filter((candidate) => !equalityNodes.some((parent) => {
      if (candidate.id === parent.id) return false;
      const elsePath = annotationChildPath(parent.location.listPath,
        parent.location.startIndex + 16, "else");
      return annotationPathStartsWith(candidate.location.listPath, elsePath);
    }));
    let compositionIndex = 0;
    for (const root of roots) {
      const chain = build(root, new Set());
      if (chain === null || root.parameters.offset + 14 !== 24) continue;
      const name = `function_${function_.wasmIndex}_search_chain_${compositionIndex}`;
      compositionIndex += 1;
      compositions.push({
        chain,
        functionIndex: function_.wasmIndex,
        keyLocal: root.parameters.keyLocal,
        location: root.location,
        name,
        offset: root.parameters.offset,
        wrapper: fixedArraySearchWrapper(function_, root, program),
      });
    }
  }
  return compositions;
}

function annotationMatchesSource(document, job) {
  const declarations = [];
  for (const function_ of document.functions) {
    for (const region of function_.regions) {
      if (region.kind !== "leanexe.array.pair-result.v1") continue;
      const parameters = region.parameters;
      const expected = parameters.mode === "constants-v1"
        ? `Project.ProofKit.FixedArrayPairResult.constResultProgram ` +
          `${parameters.firstValue} ${parameters.secondValue} ${parameters.destination}`
        : `Project.ProofKit.FixedArrayPairResult.inputResultProgram ` +
          `${parameters.inputIndex} ${parameters.destination}`;
      declarations.push(`theorem ${region.id.replace(/[^A-Za-z0-9_]/g, "_")}_eq :
    Project.ProofKit.Annotation.region ${job.namespace}.func${function_.wasmIndex}
      ${leanAnnotationPath(region.location.listPath)} ${region.location.startIndex}
      ${region.location.endIndex} = some (${expected}) := by
  rfl`);
    }
  }
  const treeCompositions = fixedArraySearchTreeCompositions(document);
  for (const composition of treeCompositions) {
    declarations.push(`def ${composition.name} :
    Project.ProofKit.FixedArraySearchTree.Tree :=
  ${composition.tree}

theorem ${composition.name}_eq :
    Project.ProofKit.Annotation.region ${job.namespace}.func${composition.functionIndex}
      ${leanAnnotationPath(composition.location.listPath)}
      ${composition.location.startIndex} ${composition.location.endIndex} =
        some (${composition.name}.program ${composition.offset} ${composition.keyLocal}) := by
  rfl`);
  }
  const chainCompositions = fixedArraySearchChainCompositions(document);
  for (const composition of chainCompositions) {
    declarations.push(`def ${composition.name} :
    Project.ProofKit.FixedArraySearchChain.Chain :=
  ${composition.chain}

theorem ${composition.name}_eq :
    Project.ProofKit.Annotation.region ${job.namespace}.func${composition.functionIndex}
      ${leanAnnotationPath(composition.location.listPath)}
      ${composition.location.startIndex} ${composition.location.endIndex} =
        some (${composition.name}.program ${composition.offset} ${composition.keyLocal}) := by
  rfl`);
  }
  return {
    module: `${job.namespace}.AnnotationMatches`,
    source: `import ${job.programModule}
import Project.ProofKit.Annotation
import Project.ProofKit.FixedArrayPairResult
${chainCompositions.length > 0 ? "import Project.ProofKit.FixedArraySearchChain\n" : ""}
${treeCompositions.length > 0 ? "import Project.ProofKit.FixedArraySearchTree\n" : ""}
set_option maxRecDepth 1048576

namespace ${job.namespace}.AnnotationMatches

${declarations.join("\n\n")}

end ${job.namespace}.AnnotationMatches
`,
  };
}

module.exports = {
  annotationMatchesSource,
  directCallRecipe,
  fixedArrayEqNodeRecipe,
  fixedArrayLengthDispatchRecipe,
  fixedArrayLtNodeRecipe,
  fixedArrayPairResultRecipe,
  fixedArraySearchKeyRecipe,
  fixedArraySearchChainCompositions,
  fixedArraySearchTreeCompositions,
  matchAnnotationDocument,
  matchDirectCallRegion,
  matchFixedArrayEqNodeRegion,
  matchFixedArrayLengthDispatchRegion,
  matchFixedArrayLtNodeRegion,
  matchFixedArrayPairResultRegion,
  matchFixedArraySearchKeyRegion,
  proofRecipePlan,
  resolveInstructionList,
  validateAnnotationDocument,
  validateProofRecipePlan,
};
