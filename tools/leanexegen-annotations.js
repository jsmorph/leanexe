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
  if (!["eq-normalized-v1", "ne-normalized-v1", "le-unsigned-v1"]
    .includes(region.parameters.encoding)) {
    fail(`${description}.parameters.encoding is unsupported`);
  }
  const expectedBranches = region.parameters.encoding === "ne-normalized-v1"
    ? { invalidBranch: "then", validBranch: "else" }
    : { invalidBranch: "else", validBranch: "then" };
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

function validateFixedArrayFindIdxEq(region, description) {
  exactKeys(region, ["generatedBy", "id", "kind", "location", "parameters"], description);
  string(region.id, `${description}.id`);
  if (region.kind !== "leanexe.array.find-idx-eq.v1") {
    fail(`${description}.kind is unsupported`);
  }
  validateRegionLocation(region, description);
  if (region.location.endIndex - region.location.startIndex !== 12) {
    fail(`${description}.location must contain the exact find-index expression region`);
  }
  exactKeys(region.parameters, [
    "continuation", "inputLocal", "itemLocal", "key", "resultEncoding",
    "scratchStart", "sourceWidth",
  ], `${description}.parameters`);
  const parameters = region.parameters;
  natural(parameters.scratchStart, `${description}.parameters.scratchStart`);
  natural(parameters.sourceWidth, `${description}.parameters.sourceWidth`);
  natural(parameters.inputLocal, `${description}.parameters.inputLocal`);
  natural(parameters.itemLocal, `${description}.parameters.itemLocal`);
  uint64String(parameters.key, `${description}.parameters.key`);
  if (parameters.scratchStart < 2 || parameters.sourceWidth !== 1 ||
      parameters.inputLocal !== 0 || parameters.itemLocal !== 1 ||
      parameters.resultEncoding !== "none-zero-some-index-plus-one-v1" ||
      parameters.continuation !== "fallthrough") {
    fail(`${description}.parameters has an unsupported find-index expression`);
  }
  for (const [index, generator] of array(
    region.generatedBy, `${description}.generatedBy`).entries()) {
    string(generator, `${description}.generatedBy[${index}]`);
  }
}

function validateEncodedIndexDecoder(region, description) {
  exactKeys(region, ["generatedBy", "id", "kind", "location", "parameters"], description);
  string(region.id, `${description}.id`);
  if (region.kind !== "leanexe.option.encoded-index.v1") {
    fail(`${description}.kind is unsupported`);
  }
  validateRegionLocation(region, description);
  if (region.location.endIndex - region.location.startIndex !== 6) {
    fail(`${description}.location must contain the exact encoded-index decoder region`);
  }
  exactKeys(region.parameters, [
    "decodedLocal", "encodedLocal", "encoding", "scratchStart",
  ], `${description}.parameters`);
  const parameters = region.parameters;
  natural(parameters.encodedLocal, `${description}.parameters.encodedLocal`);
  natural(parameters.scratchStart, `${description}.parameters.scratchStart`);
  natural(parameters.decodedLocal, `${description}.parameters.decodedLocal`);
  if (parameters.scratchStart === Number.MAX_SAFE_INTEGER ||
      parameters.encoding !== "none-zero-some-index-plus-one-v1") {
    fail(`${description}.parameters has an unsupported encoded-index decoder`);
  }
  for (const [index, generator] of array(
    region.generatedBy, `${description}.generatedBy`).entries()) {
    string(generator, `${description}.generatedBy[${index}]`);
  }
}

function validateFixedArrayEraseCopy(region, description) {
  exactKeys(region, ["generatedBy", "id", "kind", "location", "parameters"], description);
  string(region.id, `${description}.id`);
  if (region.kind !== "leanexe.array.erase-copy.v1") {
    fail(`${description}.kind is unsupported`);
  }
  validateRegionLocation(region, description);
  if (region.location.endIndex - region.location.startIndex !== 6) {
    fail(`${description}.location must contain the exact erase-copy region`);
  }
  exactKeys(region.parameters, [
    "continuation", "counterLocal", "prefixCellsLocal", "sourceLocal", "sourceWidth",
    "suffixCellsLocal", "targetLocal",
  ], `${description}.parameters`);
  const parameters = region.parameters;
  for (const key of [
    "sourceWidth", "sourceLocal", "targetLocal", "prefixCellsLocal",
    "suffixCellsLocal", "counterLocal",
  ]) {
    natural(parameters[key], `${description}.parameters.${key}`);
  }
  if (parameters.sourceWidth === 0 || parameters.continuation !== "fallthrough") {
    fail(`${description}.parameters has an unsupported erase-copy region`);
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

function validateFixedArrayMapAdd(region, description) {
  exactKeys(region, ["generatedBy", "id", "kind", "location", "parameters"], description);
  string(region.id, `${description}.id`);
  if (region.kind !== "leanexe.array.map-add.v1") {
    fail(`${description}.kind is unsupported`);
  }
  exactKeys(region.location, ["endIndex", "listPath", "startIndex"],
    `${description}.location`);
  if (array(region.location.listPath, `${description}.location.listPath`).length !== 0 ||
      natural(region.location.startIndex, `${description}.location.startIndex`) !== 0 ||
      natural(region.location.endIndex, `${description}.location.endIndex`) === 0) {
    fail(`${description}.location must cover a nonempty top-level function body`);
  }
  exactKeys(region.parameters, ["addend", "continuation", "maximumSize"],
    `${description}.parameters`);
  natural(region.parameters.maximumSize, `${description}.parameters.maximumSize`);
  uint64String(region.parameters.addend, `${description}.parameters.addend`);
  if (region.parameters.continuation !== "function-return") {
    fail(`${description}.parameters has an unsupported continuation`);
  }
  for (const [index, generator] of array(
    region.generatedBy, `${description}.generatedBy`).entries()) {
    string(generator, `${description}.generatedBy[${index}]`);
  }
}

function validateFixedArrayFilterLt(region, description) {
  exactKeys(region, ["generatedBy", "id", "kind", "location", "parameters"], description);
  string(region.id, `${description}.id`);
  if (region.kind !== "leanexe.array.filter-lt.v1") {
    fail(`${description}.kind is unsupported`);
  }
  exactKeys(region.location, ["endIndex", "listPath", "startIndex"],
    `${description}.location`);
  if (array(region.location.listPath, `${description}.location.listPath`).length !== 0 ||
      natural(region.location.startIndex, `${description}.location.startIndex`) !== 0 ||
      natural(region.location.endIndex, `${description}.location.endIndex`) === 0) {
    fail(`${description}.location must cover a nonempty top-level function body`);
  }
  exactKeys(region.parameters, ["continuation", "maximumSize", "threshold"],
    `${description}.parameters`);
  natural(region.parameters.maximumSize, `${description}.parameters.maximumSize`);
  uint64String(region.parameters.threshold, `${description}.parameters.threshold`);
  if (region.parameters.continuation !== "function-return") {
    fail(`${description}.parameters has an unsupported continuation`);
  }
  for (const [index, generator] of array(
    region.generatedBy, `${description}.generatedBy`).entries()) {
    string(generator, `${description}.generatedBy[${index}]`);
  }
}

function validateRegionLocation(region, description) {
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
}

function validateScalarExpr(expression, description) {
  if (expression === null || typeof expression !== "object" || Array.isArray(expression)) {
    fail(`${description} must be an object`);
  }
  string(expression.kind, `${description}.kind`);
  if (expression.kind === "get") {
    exactKeys(expression, ["index", "kind"], description);
    natural(expression.index, `${description}.index`);
  } else if (expression.kind === "const") {
    exactKeys(expression, ["kind", "value"], description);
    uint64String(expression.value, `${description}.value`);
  } else if (expression.kind === "bin") {
    exactKeys(expression, ["kind", "left", "operation", "right"], description);
    if (!["add", "sub", "mul", "div-u", "rem-u", "bit-and", "bit-or", "bit-xor",
      "shift-left", "shift-right"].includes(expression.operation)) {
      fail(`${description}.operation is unsupported`);
    }
    validateScalarExpr(expression.left, `${description}.left`);
    validateScalarExpr(expression.right, `${description}.right`);
  } else if (expression.kind === "ite") {
    exactKeys(expression, ["condition", "else", "kind", "then"], description);
    validateScalarCond(expression.condition, `${description}.condition`);
    validateScalarExpr(expression.then, `${description}.then`);
    validateScalarExpr(expression.else, `${description}.else`);
  } else {
    fail(`${description}.kind is unsupported`);
  }
}

function validateScalarCond(condition, description) {
  if (condition === null || typeof condition !== "object" || Array.isArray(condition)) {
    fail(`${description} must be an object`);
  }
  string(condition.kind, `${description}.kind`);
  if (["true", "false"].includes(condition.kind)) {
    exactKeys(condition, ["kind"], description);
  } else if (["eq", "ne", "lt-u", "le-u"].includes(condition.kind)) {
    exactKeys(condition, ["kind", "left", "right"], description);
    validateScalarExpr(condition.left, `${description}.left`);
    validateScalarExpr(condition.right, `${description}.right`);
  } else if (condition.kind === "not") {
    exactKeys(condition, ["condition", "kind"], description);
    validateScalarCond(condition.condition, `${description}.condition`);
  } else if (["and", "or"].includes(condition.kind)) {
    exactKeys(condition, ["kind", "left", "right"], description);
    validateScalarCond(condition.left, `${description}.left`);
    validateScalarCond(condition.right, `${description}.right`);
  } else {
    fail(`${description}.kind is unsupported`);
  }
}

function validateScalarStmt(statement, description) {
  if (statement === null || typeof statement !== "object" || Array.isArray(statement)) {
    fail(`${description} must be an object`);
  }
  string(statement.kind, `${description}.kind`);
  if (statement.kind === "skip") {
    exactKeys(statement, ["kind"], description);
  } else if (statement.kind === "assign") {
    exactKeys(statement, ["index", "kind", "value"], description);
    natural(statement.index, `${description}.index`);
    validateScalarExpr(statement.value, `${description}.value`);
  } else if (statement.kind === "seq") {
    exactKeys(statement, ["first", "kind", "second"], description);
    validateScalarStmt(statement.first, `${description}.first`);
    validateScalarStmt(statement.second, `${description}.second`);
  } else if (statement.kind === "ite") {
    exactKeys(statement, ["condition", "else", "kind", "then"], description);
    validateScalarCond(statement.condition, `${description}.condition`);
    validateScalarStmt(statement.then, `${description}.then`);
    validateScalarStmt(statement.else, `${description}.else`);
  } else {
    fail(`${description}.kind is unsupported`);
  }
}

function validateLoopFold(region, description) {
  exactKeys(region, ["generatedBy", "id", "kind", "location", "parameters"], description);
  string(region.id, `${description}.id`);
  if (region.kind !== "leanexe.loop.fold.v1") fail(`${description}.kind is unsupported`);
  validateRegionLocation(region, description);
  if (region.location.listPath.length !== 0 || region.location.startIndex !== 0) {
    fail(`${description}.location must begin at the top-level function body`);
  }
  exactKeys(region.parameters, [
    "accumulatorLocals", "accumulatorStart", "bodyLets", "bodyValues",
    "continuation", "doneLocal", "doneValue", "initialValues", "releaseOffsets",
    "releaseReadyLocal", "resultLocals", "resultWidth", "scratchStart",
    "stagedValueStart",
  ], `${description}.parameters`);
  const parameters = region.parameters;
  natural(parameters.resultWidth, `${description}.parameters.resultWidth`);
  if (parameters.resultWidth === 0) fail(`${description}.parameters.resultWidth must be positive`);
  natural(parameters.accumulatorStart, `${description}.parameters.accumulatorStart`);
  natural(parameters.scratchStart, `${description}.parameters.scratchStart`);
  natural(parameters.doneLocal, `${description}.parameters.doneLocal`);
  natural(parameters.stagedValueStart, `${description}.parameters.stagedValueStart`);
  natural(parameters.releaseReadyLocal, `${description}.parameters.releaseReadyLocal`);
  const accumulatorLocals = array(
    parameters.accumulatorLocals, `${description}.parameters.accumulatorLocals`);
  const initialValues = array(parameters.initialValues, `${description}.parameters.initialValues`);
  const bodyValues = array(parameters.bodyValues, `${description}.parameters.bodyValues`);
  const resultLocals = array(parameters.resultLocals, `${description}.parameters.resultLocals`);
  if ([accumulatorLocals, initialValues, bodyValues, resultLocals]
    .some((values) => values.length !== parameters.resultWidth)) {
    fail(`${description}.parameters result-width arrays differ in length`);
  }
  accumulatorLocals.forEach((local, index) => {
    if (natural(local, `${description}.parameters.accumulatorLocals[${index}]`) !==
        parameters.accumulatorStart + index) {
      fail(`${description}.parameters.accumulatorLocals must be consecutive`);
    }
  });
  initialValues.forEach((value, index) =>
    string(value, `${description}.parameters.initialValues[${index}]`));
  bodyValues.forEach((value, index) =>
    string(value, `${description}.parameters.bodyValues[${index}]`));
  array(parameters.bodyLets, `${description}.parameters.bodyLets`).forEach((value, index) =>
    string(value, `${description}.parameters.bodyLets[${index}]`));
  string(parameters.doneValue, `${description}.parameters.doneValue`);
  array(parameters.releaseOffsets, `${description}.parameters.releaseOffsets`)
    .forEach((offset, index) => {
      if (natural(offset, `${description}.parameters.releaseOffsets[${index}]`) >=
          parameters.resultWidth) {
        fail(`${description}.parameters.releaseOffsets[${index}] exceeds the result width`);
      }
    });
  resultLocals.forEach((local, index) =>
    natural(local, `${description}.parameters.resultLocals[${index}]`));
  if (parameters.doneLocal < parameters.scratchStart ||
      parameters.stagedValueStart !== parameters.doneLocal + 1 ||
      parameters.releaseReadyLocal !== parameters.stagedValueStart + parameters.resultWidth ||
      parameters.continuation !== "function-results") {
    fail(`${description}.parameters has an invalid scratch layout or continuation`);
  }
  array(region.generatedBy, `${description}.generatedBy`).forEach((generator, index) =>
    string(generator, `${description}.generatedBy[${index}]`));
}

function validateArrayFold(region, description) {
  exactKeys(region, ["generatedBy", "id", "kind", "location", "parameters"], description);
  string(region.id, `${description}.id`);
  if (region.kind !== "leanexe.array.fold.v1") fail(`${description}.kind is unsupported`);
  validateRegionLocation(region, description);
  const parameters = region.parameters;
  const hasDescriptor = Object.hasOwn(parameters, "descriptor") ||
    Object.hasOwn(parameters, "descriptorVersion");
  exactKeys(parameters, [
    "accumulatorLocals", "accumulatorStart", "array", "arrayLocal", "bodyLets",
    "bodyValues", "continuation", "doneLocal", "doneValue", "effectiveStopLocal",
    "indexLocal", "initialValues", "itemLocals", "itemStart", "lengthLocal",
    "releaseOffsets", "releaseReadyLocal", "resultLocals", "resultSlots", "resultWidth",
    "reverse", "scratchStart", "sourceWidth", "stagedValueStart", "start", "stop",
    "stopLocal", ...(hasDescriptor ? ["descriptor", "descriptorVersion"] : []),
  ], `${description}.parameters`);
  if (hasDescriptor && (!Object.hasOwn(parameters, "descriptor") ||
      !Object.hasOwn(parameters, "descriptorVersion"))) {
    fail(`${description}.parameters descriptor fields must appear together`);
  }
  if (hasDescriptor) {
    if (parameters.descriptorVersion !== 1) {
      fail(`${description}.parameters.descriptorVersion is unsupported`);
    }
    if (parameters.descriptor !== null) {
      exactKeys(parameters.descriptor, ["body", "condition"],
        `${description}.parameters.descriptor`);
      validateScalarCond(parameters.descriptor.condition,
        `${description}.parameters.descriptor.condition`);
      validateScalarStmt(parameters.descriptor.body,
        `${description}.parameters.descriptor.body`);
    }
  }
  natural(parameters.sourceWidth, `${description}.parameters.sourceWidth`);
  natural(parameters.resultWidth, `${description}.parameters.resultWidth`);
  if (parameters.sourceWidth === 0 || parameters.resultWidth === 0) {
    fail(`${description}.parameters fold widths must be positive`);
  }
  if (typeof parameters.reverse !== "boolean") {
    fail(`${description}.parameters.reverse must be a Boolean`);
  }
  ["array", "start", "stop", "doneValue"].forEach((field) =>
    string(parameters[field], `${description}.parameters.${field}`));
  [
    "accumulatorStart", "itemStart", "scratchStart", "arrayLocal", "lengthLocal",
    "indexLocal", "stopLocal", "effectiveStopLocal", "doneLocal", "stagedValueStart",
    "releaseReadyLocal",
  ].forEach((field) => natural(parameters[field], `${description}.parameters.${field}`));
  const accumulatorLocals = array(
    parameters.accumulatorLocals, `${description}.parameters.accumulatorLocals`);
  const itemLocals = array(parameters.itemLocals, `${description}.parameters.itemLocals`);
  const initialValues = array(
    parameters.initialValues, `${description}.parameters.initialValues`);
  const bodyValues = array(parameters.bodyValues, `${description}.parameters.bodyValues`);
  if (accumulatorLocals.length !== parameters.resultWidth ||
      itemLocals.length !== parameters.sourceWidth ||
      initialValues.length !== parameters.resultWidth ||
      bodyValues.length !== parameters.resultWidth) {
    fail(`${description}.parameters width-indexed arrays differ in length`);
  }
  accumulatorLocals.forEach((local, index) => {
    if (natural(local, `${description}.parameters.accumulatorLocals[${index}]`) !==
        parameters.accumulatorStart + index) {
      fail(`${description}.parameters.accumulatorLocals must be consecutive`);
    }
  });
  itemLocals.forEach((local, index) => {
    if (natural(local, `${description}.parameters.itemLocals[${index}]`) !==
        parameters.itemStart + index) {
      fail(`${description}.parameters.itemLocals must be consecutive`);
    }
  });
  initialValues.forEach((value, index) =>
    string(value, `${description}.parameters.initialValues[${index}]`));
  bodyValues.forEach((value, index) =>
    string(value, `${description}.parameters.bodyValues[${index}]`));
  array(parameters.bodyLets, `${description}.parameters.bodyLets`).forEach((value, index) =>
    string(value, `${description}.parameters.bodyLets[${index}]`));
  array(parameters.releaseOffsets, `${description}.parameters.releaseOffsets`)
    .forEach((offset, index) => {
      if (natural(offset, `${description}.parameters.releaseOffsets[${index}]`) >=
          parameters.resultWidth) {
        fail(`${description}.parameters.releaseOffsets[${index}] exceeds the result width`);
      }
    });
  const resultSlots = array(parameters.resultSlots, `${description}.parameters.resultSlots`);
  const resultLocals = array(parameters.resultLocals, `${description}.parameters.resultLocals`);
  if (resultSlots.length !== resultLocals.length ||
      (resultSlots.length !== 1 && resultSlots.length !== parameters.resultWidth)) {
    fail(`${description}.parameters result placement has an unsupported width`);
  }
  resultSlots.forEach((slot, index) => {
    if (natural(slot, `${description}.parameters.resultSlots[${index}]`) >=
        parameters.resultWidth) {
      fail(`${description}.parameters.resultSlots[${index}] exceeds the result width`);
    }
  });
  resultLocals.forEach((local, index) =>
    natural(local, `${description}.parameters.resultLocals[${index}]`));
  if (resultSlots.length === parameters.resultWidth &&
      resultSlots.some((slot, index) => slot !== index)) {
    fail(`${description}.parameters full result placement must preserve slot order`);
  }
  if (parameters.arrayLocal !== parameters.scratchStart ||
      parameters.lengthLocal !== parameters.scratchStart + 1 ||
      parameters.indexLocal !== parameters.scratchStart + 2 ||
      parameters.stopLocal !== parameters.scratchStart + 3 ||
      parameters.effectiveStopLocal !== parameters.scratchStart + 4 ||
      parameters.doneLocal < parameters.scratchStart + 5 ||
      parameters.stagedValueStart !== parameters.doneLocal + 1 ||
      parameters.releaseReadyLocal !== parameters.stagedValueStart + parameters.resultWidth ||
      parameters.continuation !== "fallthrough") {
    fail(`${description}.parameters has an invalid scratch layout or continuation`);
  }
  array(region.generatedBy, `${description}.generatedBy`).forEach((generator, index) =>
    string(generator, `${description}.generatedBy[${index}]`));
}

function validateWhileLoop(region, description) {
  exactKeys(region, ["generatedBy", "id", "kind", "location", "parameters"], description);
  string(region.id, `${description}.id`);
  if (region.kind !== "leanexe.loop.while.v1") fail(`${description}.kind is unsupported`);
  validateRegionLocation(region, description);
  exactKeys(region.parameters, [
    "body", "condition", "continuation", "descriptor", "descriptorVersion", "scratchStart",
  ], `${description}.parameters`);
  string(region.parameters.condition, `${description}.parameters.condition`);
  string(region.parameters.body, `${description}.parameters.body`);
  if (region.parameters.descriptorVersion !== 1) {
    fail(`${description}.parameters.descriptorVersion is unsupported`);
  }
  if (region.parameters.descriptor !== null) {
    exactKeys(region.parameters.descriptor, ["body", "condition"],
      `${description}.parameters.descriptor`);
    validateScalarCond(region.parameters.descriptor.condition,
      `${description}.parameters.descriptor.condition`);
    validateScalarStmt(region.parameters.descriptor.body,
      `${description}.parameters.descriptor.body`);
  }
  natural(region.parameters.scratchStart, `${description}.parameters.scratchStart`);
  if (region.parameters.continuation !== "fallthrough") {
    fail(`${description}.parameters has an unsupported continuation`);
  }
  array(region.generatedBy, `${description}.generatedBy`).forEach((generator, index) =>
    string(generator, `${description}.generatedBy[${index}]`));
}

function validateScalarPostTestLoop(region, description) {
  exactKeys(region, ["generatedBy", "id", "kind", "location", "parameters"], description);
  string(region.id, `${description}.id`);
  if (region.kind !== "leanexe.loop.scalar-post-test.v1") {
    fail(`${description}.kind is unsupported`);
  }
  validateRegionLocation(region, description);
  if (region.location.listPath.length !== 0 ||
      region.location.endIndex !== region.location.startIndex + 1) {
    fail(`${description}.location must select one top-level block`);
  }
  exactKeys(region.parameters, [
    "accumulatorLocals", "accumulatorStart", "continuation", "descriptor",
    "descriptorVersion", "destination", "initialValues", "releaseOffsets",
    "resultSlot", "resultWidth", "scratchStart",
  ], `${description}.parameters`);
  const parameters = region.parameters;
  natural(parameters.resultWidth, `${description}.parameters.resultWidth`);
  if (parameters.resultWidth === 0) {
    fail(`${description}.parameters.resultWidth must be positive`);
  }
  natural(parameters.accumulatorStart, `${description}.parameters.accumulatorStart`);
  natural(parameters.resultSlot, `${description}.parameters.resultSlot`);
  natural(parameters.destination, `${description}.parameters.destination`);
  natural(parameters.scratchStart, `${description}.parameters.scratchStart`);
  if (parameters.resultSlot >= parameters.resultWidth) {
    fail(`${description}.parameters.resultSlot exceeds the result width`);
  }
  const accumulatorLocals = array(
    parameters.accumulatorLocals, `${description}.parameters.accumulatorLocals`);
  const initialValues = array(
    parameters.initialValues, `${description}.parameters.initialValues`);
  if (accumulatorLocals.length !== parameters.resultWidth ||
      initialValues.length !== parameters.resultWidth) {
    fail(`${description}.parameters result-width arrays differ in length`);
  }
  accumulatorLocals.forEach((local, index) => {
    if (natural(local, `${description}.parameters.accumulatorLocals[${index}]`) !==
        parameters.accumulatorStart + index) {
      fail(`${description}.parameters.accumulatorLocals must be consecutive`);
    }
  });
  initialValues.forEach((value, index) =>
    string(value, `${description}.parameters.initialValues[${index}]`));
  if (array(parameters.releaseOffsets,
    `${description}.parameters.releaseOffsets`).length !== 0) {
    fail(`${description}.parameters.releaseOffsets must be empty`);
  }
  if (parameters.descriptorVersion !== 1 || parameters.descriptor === null) {
    fail(`${description}.parameters descriptor is unsupported`);
  }
  exactKeys(parameters.descriptor, ["body", "condition"],
    `${description}.parameters.descriptor`);
  validateScalarCond(parameters.descriptor.condition,
    `${description}.parameters.descriptor.condition`);
  validateScalarStmt(parameters.descriptor.body,
    `${description}.parameters.descriptor.body`);
  if (parameters.continuation !== "fallthrough") {
    fail(`${description}.parameters has an unsupported continuation`);
  }
  array(region.generatedBy, `${description}.generatedBy`).forEach((generator, index) =>
    string(generator, `${description}.generatedBy[${index}]`));
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
      } else if (region?.kind === "leanexe.array.find-idx-eq.v1") {
        validateFixedArrayFindIdxEq(region, `${description}.regions[${regionIndex}]`);
      } else if (region?.kind === "leanexe.option.encoded-index.v1") {
        validateEncodedIndexDecoder(region, `${description}.regions[${regionIndex}]`);
      } else if (region?.kind === "leanexe.array.erase-copy.v1") {
        validateFixedArrayEraseCopy(region, `${description}.regions[${regionIndex}]`);
      } else if (region?.kind === "leanexe.array.search-key.v1") {
        validateFixedArraySearchKey(region, `${description}.regions[${regionIndex}]`);
      } else if (region?.kind === "leanexe.array.eq-node.v1") {
        validateFixedArrayEqNode(region, `${description}.regions[${regionIndex}]`);
      } else if (region?.kind === "leanexe.array.lt-node.v1") {
        validateFixedArrayLtNode(region, `${description}.regions[${regionIndex}]`);
      } else if (region?.kind === "leanexe.array.pair-result.v1") {
        validateFixedArrayPairResult(region, `${description}.regions[${regionIndex}]`);
      } else if (region?.kind === "leanexe.array.map-add.v1") {
        validateFixedArrayMapAdd(region, `${description}.regions[${regionIndex}]`);
      } else if (region?.kind === "leanexe.array.filter-lt.v1") {
        validateFixedArrayFilterLt(region, `${description}.regions[${regionIndex}]`);
      } else if (region?.kind === "leanexe.loop.fold.v1") {
        validateLoopFold(region, `${description}.regions[${regionIndex}]`);
      } else if (region?.kind === "leanexe.array.fold.v1") {
        validateArrayFold(region, `${description}.regions[${regionIndex}]`);
      } else if (region?.kind === "leanexe.loop.while.v1") {
        validateWhileLoop(region, `${description}.regions[${regionIndex}]`);
      } else if (region?.kind === "leanexe.loop.scalar-post-test.v1") {
        validateScalarPostTestLoop(region, `${description}.regions[${regionIndex}]`);
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

function resolveInstructionSelection(body, listPath) {
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
        if ((step.field === "then" || step.field === "else") &&
            /^\]\s+\[\],?$/.test(lines[index].trim())) {
          delimiters.push(index);
          break;
        }
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
  return { lines, start, end, level };
}

function resolveInstructionList(body, listPath) {
  const { lines, start, end, level } = resolveInstructionSelection(body, listPath);
  return instructionPositions(lines, start, end, level).map((index) => lines[index].trim());
}

function resolveInstructionIntervalSource(body, listPath, startIndex, endIndex) {
  const selection = resolveInstructionSelection(body, listPath);
  const positions = instructionPositions(
    selection.lines, selection.start, selection.end, selection.level);
  if (startIndex > endIndex || endIndex > positions.length) {
    fail("instruction source interval exceeds the selected list");
  }
  if (startIndex === endIndex) return "";
  const lineStart = positions[startIndex];
  const lineEnd = endIndex === positions.length ? selection.end : positions[endIndex];
  return selection.lines.slice(lineStart, lineEnd)
    .map((line) => line.slice(selection.level)).join("\n");
}

function leanProgramLiteral(source) {
  const trimmed = source.trimEnd();
  if (trimmed === "") return "[]";
  return `[\n${trimmed.split("\n").map((line) => `  ${line}`).join("\n")}\n]`;
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

function matchFixedArrayConstantCapacity(body, listPath) {
  const instructions = normalizeInstructions(resolveInstructionList(body, listPath));
  if (instructions.length < 18) return null;
  const length = instructions[1]?.match(/^\.constI64 \(([0-9]+) : UInt64\)$/);
  const stride = instructions[2]?.match(/^\.constI64 \(([0-9]+) : UInt64\)$/);
  const capacitySet = instructions[13]?.match(/^\.localSet ([0-9]+)$/);
  const capacityGet = instructions[14]?.match(/^\.localGet ([0-9]+)$/);
  if (length === null || stride === null || capacitySet === null ||
      capacityGet === null || capacitySet[1] !== capacityGet[1]) return null;
  const expected = [
    ".constI64 (8 : UInt64)",
    `.constI64 (${length[1]} : UInt64)`,
    `.constI64 (${stride[1]} : UInt64)`,
    ".mulI64",
    ".constI64 (8 : UInt64)",
    ".mulI64",
    ".addI64",
    ".constI64 (7 : UInt64)",
    ".addI64",
    ".constI64 (8 : UInt64)",
    ".divUI64",
    ".constI64 (8 : UInt64)",
    ".mulI64",
    `.localSet ${capacitySet[1]}`,
    `.localGet ${capacitySet[1]}`,
    ".constI64 (8 : UInt64)",
    ".ltUI64",
    ".iff 0 0 [",
  ];
  if (JSON.stringify(instructions.slice(0, expected.length)) !==
      JSON.stringify(expected)) return null;
  const thenBranch = normalizeInstructions(resolveInstructionList(body, [
    ...listPath, { instructionIndex: 17, field: "then" },
  ]));
  const elseBranch = normalizeInstructions(resolveInstructionList(body, [
    ...listPath, { instructionIndex: 17, field: "else" },
  ]));
  if (JSON.stringify(thenBranch) !== JSON.stringify([
    ".constI64 (8 : UInt64)", `.localSet ${capacitySet[1]}`,
  ]) || elseBranch.length !== 0) return null;
  return {
    capacityLocal: Number(capacitySet[1]),
    endIndex: expected.length,
    length: length[1],
    listPath,
    startIndex: 0,
    stride: stride[1],
  };
}

function matchFixedArrayLengthDispatchRegion(program, function_, region) {
  const body = programFunctionBody(program, function_.wasmIndex);
  const instructions = resolveInstructionList(body, region.location.listPath);
  const selected = instructions.slice(region.location.startIndex, region.location.endIndex);
  const parameters = region.parameters;
  const prefix = [
    ".localGet 0,",
    `.localSet ${parameters.inputLocal},`,
    `.localGet ${parameters.inputLocal},`,
    ".wrapI64,",
    ".load64 (0 : UInt32),",
    `.constI64 (${parameters.expectedSize} : UInt64),`,
  ];
  const expected = parameters.encoding === "le-unsigned-v1" ? [
    ...prefix,
    ".leUI64,",
    ".iff 0 0 [",
  ] : parameters.encoding === "eq-normalized-v1" ? [
    ...prefix,
    ".eqI64,",
    ".iff 0 1 [",
    ".constI64 (1 : UInt64),",
    ".eqI64,",
    ".iff 0 1 [",
    ".constI64 (0 : UInt64),",
    ".eqI64,",
    ".eqz,",
    ".iff 0 0 [",
  ] : [
    ...prefix,
    ".eqI64,",
    ".iff 0 1 [",
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
  const booleanIfs = parameters.encoding === "le-unsigned-v1" ? [] :
    parameters.encoding === "eq-normalized-v1" ? [7, 10] : [7, 12, 15];
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
  const dispatchIndex = region.location.startIndex + selected.length - 1;
  const capacityPrefixes = [];
  const branchPrograms = [];
  for (const role of ["valid", "invalid"]) {
    const branch = parameters[`${role}Branch`];
    const listPath = [
      ...region.location.listPath,
      { instructionIndex: dispatchIndex, field: branch },
    ];
    const branchInstructions = resolveInstructionList(body, listPath);
    branchPrograms.push({
      branch,
      listPath,
      role,
      source: resolveInstructionIntervalSource(
        body, listPath, 0, branchInstructions.length),
    });
    const capacity = matchFixedArrayConstantCapacity(body, listPath);
    if (capacity !== null) capacityPrefixes.push({ ...capacity, branch, role });
  }
  const topLevelInstructions = resolveInstructionList(body, []);
  const functionPrefixEligible = region.location.listPath.length === 0 &&
    region.location.startIndex === 0;
  return {
    functionIndex: function_.wasmIndex,
    regionId: region.id,
    regionKind: region.kind,
    parameters,
    capacityPrefixes,
    branchPrograms,
    functionPrefixEligible,
    suffixSource: functionPrefixEligible
      ? resolveInstructionIntervalSource(
        body, [], region.location.endIndex, topLevelInstructions.length)
      : null,
  };
}

function matchFixedArrayFindIdxEqRegion(program, function_, region) {
  const body = programFunctionBody(program, function_.wasmIndex);
  const instructions = resolveInstructionList(body, region.location.listPath);
  const selected = instructions.slice(region.location.startIndex, region.location.endIndex);
  const parameters = region.parameters;
  const scratch = parameters.scratchStart;
  const expected = [
    `.localGet ${parameters.inputLocal}`,
    `.localSet ${scratch}`,
    `.localGet ${scratch}`,
    ".wrapI64",
    ".load64 (0 : UInt32)",
    `.localSet ${scratch + 1}`,
    ".constI64 (0 : UInt64)",
    `.localSet ${scratch + 2}`,
    ".constI64 (0 : UInt64)",
    `.localSet ${scratch + 3}`,
    ".block 0 0 [",
    `.localGet ${scratch + 3}`,
  ];
  if (JSON.stringify(normalizeInstructions(selected)) !== JSON.stringify(expected)) {
    fail(`${region.id}: decoded instructions do not match the find-index annotation`);
  }
  if (!/^\.localSet [0-9]+,?$/.test(
    instructions[region.location.endIndex] ?? "")) {
    fail(`${region.id}: find-index expression is not followed by its destination local`);
  }
  const blockPath = [
    ...region.location.listPath,
    { instructionIndex: region.location.startIndex + 10, field: "block" },
  ];
  const block = normalizeInstructions(resolveInstructionList(body, blockPath));
  if (JSON.stringify(block) !== JSON.stringify([".loop 0 0 ["])) {
    fail(`${region.id}: decoded find-index block does not match`);
  }
  const loopPath = [...blockPath, { instructionIndex: 0, field: "loop" }];
  const loop = normalizeInstructions(resolveInstructionList(body, loopPath));
  const expectedLoop = [
    `.localGet ${scratch + 2}`,
    `.localGet ${scratch + 1}`,
    ".geUI64",
    ".br_if 1",
    `.localGet ${scratch}`,
    `.localGet ${scratch + 2}`,
    ".constI64 (1 : UInt64)",
    ".mulI64",
    ".constI64 (1 : UInt64)",
    ".addI64",
    ".constI64 (8 : UInt64)",
    ".mulI64",
    ".addI64",
    ".wrapI64",
    ".load64 (0 : UInt32)",
    `.localSet ${parameters.itemLocal}`,
    `.localGet ${parameters.itemLocal}`,
    `.constI64 (${parameters.key} : UInt64)`,
    ".eqI64",
    ".iff 0 1 [",
    ".constI64 (0 : UInt64)",
    ".neI64",
    ".iff 0 0 [",
    `.localGet ${scratch + 2}`,
    ".constI64 (1 : UInt64)",
    ".addI64",
    `.localSet ${scratch + 2}`,
    ".br 0",
  ];
  if (JSON.stringify(loop) !== JSON.stringify(expectedLoop)) {
    fail(`${region.id}: decoded find-index loop does not match`);
  }
  for (const [field, value] of [["then", 1], ["else", 0]]) {
    const branch = normalizeInstructions(resolveInstructionList(body, [
      ...loopPath, { instructionIndex: 19, field },
    ]));
    if (JSON.stringify(branch) !==
        JSON.stringify([`.constI64 (${value} : UInt64)`])) {
      fail(`${region.id}: find-index predicate ${field} branch does not match`);
    }
  }
  const found = normalizeInstructions(resolveInstructionList(body, [
    ...loopPath, { instructionIndex: 22, field: "then" },
  ]));
  const notFound = normalizeInstructions(resolveInstructionList(body, [
    ...loopPath, { instructionIndex: 22, field: "else" },
  ]));
  if (JSON.stringify(found) !== JSON.stringify([
    `.localGet ${scratch + 2}`,
    ".constI64 (1 : UInt64)",
    ".addI64",
    `.localSet ${scratch + 3}`,
    ".br 2",
  ]) || notFound.length !== 0) {
    fail(`${region.id}: find-index result branches do not match`);
  }
  return {
    functionIndex: function_.wasmIndex,
    regionId: region.id,
    regionKind: region.kind,
    parameters,
  };
}

function matchEncodedIndexDecoderRegion(program, function_, region) {
  const body = programFunctionBody(program, function_.wasmIndex);
  const instructions = resolveInstructionList(body, region.location.listPath);
  const selected = normalizeInstructions(
    instructions.slice(region.location.startIndex, region.location.endIndex));
  const parameters = region.parameters;
  const expected = [
    `.localGet ${parameters.encodedLocal}`,
    ".constI64 (0 : UInt64)",
    ".eqI64",
    ".eqz",
    ".iff 0 1 [",
    `.localSet ${parameters.decodedLocal}`,
  ];
  if (JSON.stringify(selected) !== JSON.stringify(expected)) {
    fail(`${region.id}: decoded instructions do not match the encoded-index annotation`);
  }
  const outerPath = [
    ...region.location.listPath,
    { instructionIndex: region.location.startIndex + 4, field: "then" },
  ];
  const scratch = parameters.scratchStart;
  const outerThen = normalizeInstructions(resolveInstructionList(body, outerPath));
  const expectedThen = [
    `.localGet ${parameters.encodedLocal}`,
    `.localSet ${scratch}`,
    ".constI64 (1 : UInt64)",
    `.localSet ${scratch + 1}`,
    `.localGet ${scratch}`,
    `.localGet ${scratch + 1}`,
    ".ltUI64",
    ".iff 0 1 [",
  ];
  if (JSON.stringify(outerThen) !== JSON.stringify(expectedThen)) {
    fail(`${region.id}: encoded-index nonzero branch does not match`);
  }
  const outerElse = normalizeInstructions(resolveInstructionList(body, [
    ...region.location.listPath,
    { instructionIndex: region.location.startIndex + 4, field: "else" },
  ]));
  if (JSON.stringify(outerElse) !== JSON.stringify([".constI64 (0 : UInt64)"])) {
    fail(`${region.id}: encoded-index zero branch does not match`);
  }
  const innerThen = normalizeInstructions(resolveInstructionList(body, [
    ...outerPath, { instructionIndex: 7, field: "then" },
  ]));
  const innerElse = normalizeInstructions(resolveInstructionList(body, [
    ...outerPath, { instructionIndex: 7, field: "else" },
  ]));
  if (JSON.stringify(innerThen) !== JSON.stringify([".constI64 (0 : UInt64)"]) ||
      JSON.stringify(innerElse) !== JSON.stringify([
        `.localGet ${scratch}`, `.localGet ${scratch + 1}`, ".subI64",
      ])) {
    fail(`${region.id}: encoded-index subtraction branch does not match`);
  }
  return {
    functionIndex: function_.wasmIndex,
    regionId: region.id,
    regionKind: region.kind,
    parameters,
  };
}

function matchFixedArrayEraseCopyRegion(program, function_, region) {
  const body = programFunctionBody(program, function_.wasmIndex);
  const instructions = resolveInstructionList(body, region.location.listPath);
  const selected = normalizeInstructions(
    instructions.slice(region.location.startIndex, region.location.endIndex));
  const parameters = region.parameters;
  const expected = [
    ".constI64 (0 : UInt64)",
    `.localSet ${parameters.counterLocal}`,
    ".block 0 0 [",
    ".constI64 (0 : UInt64)",
    `.localSet ${parameters.counterLocal}`,
    ".block 0 0 [",
  ];
  if (JSON.stringify(selected) !== JSON.stringify(expected)) {
    fail(`${region.id}: decoded instructions do not match the erase-copy annotation`);
  }
  const prefixBlockPath = [
    ...region.location.listPath,
    { instructionIndex: region.location.startIndex + 2, field: "block" },
  ];
  const suffixBlockPath = [
    ...region.location.listPath,
    { instructionIndex: region.location.startIndex + 5, field: "block" },
  ];
  for (const [name, blockPath] of [
    ["prefix", prefixBlockPath], ["suffix", suffixBlockPath],
  ]) {
    if (JSON.stringify(normalizeInstructions(resolveInstructionList(body, blockPath))) !==
        JSON.stringify([".loop 0 0 ["])) {
      fail(`${region.id}: decoded erase-copy ${name} block does not match`);
    }
  }
  const prefixLoop = normalizeInstructions(resolveInstructionList(body, [
    ...prefixBlockPath, { instructionIndex: 0, field: "loop" },
  ]));
  const suffixLoop = normalizeInstructions(resolveInstructionList(body, [
    ...suffixBlockPath, { instructionIndex: 0, field: "loop" },
  ]));
  const counterStep = [
    `.localGet ${parameters.counterLocal}`,
    ".constI64 (1 : UInt64)",
    ".addI64",
    `.localSet ${parameters.counterLocal}`,
    ".br 0",
  ];
  const expectedPrefixLoop = [
    `.localGet ${parameters.counterLocal}`,
    `.localGet ${parameters.prefixCellsLocal}`,
    ".geUI64",
    ".br_if 1",
    `.localGet ${parameters.targetLocal}`,
    `.localGet ${parameters.counterLocal}`,
    ".constI64 (1 : UInt64)",
    ".addI64",
    ".constI64 (8 : UInt64)",
    ".mulI64",
    ".addI64",
    ".wrapI64",
    `.localGet ${parameters.sourceLocal}`,
    `.localGet ${parameters.counterLocal}`,
    ".constI64 (1 : UInt64)",
    ".addI64",
    ".constI64 (8 : UInt64)",
    ".mulI64",
    ".addI64",
    ".wrapI64",
    ".load64 (0 : UInt32)",
    ".store64 (0 : UInt32)",
    ...counterStep,
  ];
  const expectedSuffixLoop = [
    `.localGet ${parameters.counterLocal}`,
    `.localGet ${parameters.suffixCellsLocal}`,
    ".geUI64",
    ".br_if 1",
    `.localGet ${parameters.targetLocal}`,
    `.localGet ${parameters.prefixCellsLocal}`,
    `.localGet ${parameters.counterLocal}`,
    ".addI64",
    ".constI64 (1 : UInt64)",
    ".addI64",
    ".constI64 (8 : UInt64)",
    ".mulI64",
    ".addI64",
    ".wrapI64",
    `.localGet ${parameters.sourceLocal}`,
    `.localGet ${parameters.prefixCellsLocal}`,
    `.constI64 (${parameters.sourceWidth} : UInt64)`,
    ".addI64",
    `.localGet ${parameters.counterLocal}`,
    ".addI64",
    ".constI64 (1 : UInt64)",
    ".addI64",
    ".constI64 (8 : UInt64)",
    ".mulI64",
    ".addI64",
    ".wrapI64",
    ".load64 (0 : UInt32)",
    ".store64 (0 : UInt32)",
    ...counterStep,
  ];
  if (JSON.stringify(prefixLoop) !== JSON.stringify(expectedPrefixLoop)) {
    fail(`${region.id}: decoded erase-copy prefix loop does not match`);
  }
  if (JSON.stringify(suffixLoop) !== JSON.stringify(expectedSuffixLoop)) {
    fail(`${region.id}: decoded erase-copy suffix loop does not match`);
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

function matchFixedArrayMapAddRegion(program, function_, region) {
  const body = programFunctionBody(program, function_.wasmIndex);
  const instructions = resolveInstructionList(body, region.location.listPath);
  const selected = instructions.slice(region.location.startIndex, region.location.endIndex);
  if (selected.length !== instructions.length ||
      selected.length !== region.location.endIndex - region.location.startIndex ||
      normalizeInstructions(selected)[0] !== ".localGet 0" ||
      normalizeInstructions(selected).at(-1) !== ".localGet 4") {
    fail(`${region.id}: decoded map-add wrapper boundary does not match`);
  }
  return {
    functionIndex: function_.wasmIndex,
    regionId: region.id,
    regionKind: region.kind,
    parameters: region.parameters,
  };
}

function matchFixedArrayFilterLtRegion(program, function_, region) {
  const body = programFunctionBody(program, function_.wasmIndex);
  const instructions = resolveInstructionList(body, region.location.listPath);
  const selected = instructions.slice(region.location.startIndex, region.location.endIndex);
  if (selected.length !== instructions.length ||
      selected.length !== region.location.endIndex - region.location.startIndex ||
      normalizeInstructions(selected)[0] !== ".localGet 0" ||
      normalizeInstructions(selected).at(-1) !== ".localGet 4") {
    fail(`${region.id}: decoded filter-lt wrapper boundary does not match`);
  }
  return {
    functionIndex: function_.wasmIndex,
    regionId: region.id,
    regionKind: region.kind,
    parameters: region.parameters,
  };
}

function matchLoopFoldRegion(program, function_, region) {
  const body = programFunctionBody(program, function_.wasmIndex);
  const instructions = resolveInstructionList(body, region.location.listPath);
  const selected = instructions.slice(region.location.startIndex, region.location.endIndex);
  if (selected.length !== region.location.endIndex - region.location.startIndex) {
    fail(`${region.id}: decoded loop-fold region is truncated`);
  }
  const normalized = normalizeInstructions(selected);
  const blockIndex = normalized.findIndex((instruction) => instruction.startsWith(".block "));
  if (blockIndex < 2 || normalized.slice(0, blockIndex)
    .slice(-2).join("\n") !==
      `.constI64 (0 : UInt64)\n.localSet ${region.parameters.releaseReadyLocal}`) {
    fail(`${region.id}: decoded loop-fold initialization boundary does not match`);
  }
  const expectedTargets = region.parameters.accumulatorLocals.flatMap((local, index) => [
    `.localGet ${local}`,
    `.localSet ${region.parameters.resultLocals[index]}`,
  ]);
  if (JSON.stringify(normalized.slice(blockIndex + 1)) !== JSON.stringify(expectedTargets)) {
    fail(`${region.id}: decoded loop-fold result copies do not match`);
  }
  const blockPath = [
    ...region.location.listPath,
    { instructionIndex: region.location.startIndex + blockIndex, field: "block" },
  ];
  const block = normalizeInstructions(resolveInstructionList(body, blockPath));
  if (block.length !== 1 || !block[0].startsWith(".loop ")) {
    fail(`${region.id}: decoded loop-fold block does not contain one loop`);
  }
  const loop = normalizeInstructions(resolveInstructionList(body, [
    ...blockPath,
    { instructionIndex: 0, field: "loop" },
  ]));
  const expectedSuffix = [
    ...region.parameters.accumulatorLocals.flatMap((local, index) => [
      `.localGet ${region.parameters.stagedValueStart + index}`,
      `.localSet ${local}`,
    ]),
    ".constI64 (1 : UInt64)",
    `.localSet ${region.parameters.releaseReadyLocal}`,
    `.localGet ${region.parameters.doneLocal}`,
    ".constI64 (0 : UInt64)",
    ".eqI64",
    ".eqz",
    ".br_if 1",
    ".br 0",
  ];
  if (JSON.stringify(loop.slice(-expectedSuffix.length)) !== JSON.stringify(expectedSuffix)) {
    fail(`${region.id}: decoded loop-fold back edge does not match`);
  }
  return {
    functionIndex: function_.wasmIndex,
    regionId: region.id,
    regionKind: region.kind,
    parameters: region.parameters,
  };
}

function matchArrayFoldRegion(program, function_, region) {
  const body = programFunctionBody(program, function_.wasmIndex);
  const instructions = resolveInstructionList(body, region.location.listPath);
  const selected = instructions.slice(region.location.startIndex, region.location.endIndex);
  if (selected.length !== region.location.endIndex - region.location.startIndex) {
    fail(`${region.id}: decoded array-fold region is truncated`);
  }
  const parameters = region.parameters;
  const normalized = normalizeInstructions(selected);
  const boundaryLocal = parameters.reverse
    ? parameters.indexLocal : parameters.effectiveStopLocal;
  const blockIndex = normalized.findIndex((instruction, index) =>
    instruction.startsWith(".block ") &&
      normalized[index - 1] === `.localSet ${boundaryLocal}`);
  const releaseInitialization = normalized.findIndex((instruction, index) =>
    instruction === ".constI64 (0 : UInt64)" &&
      normalized[index + 1] === `.localSet ${parameters.releaseReadyLocal}`);
  if (blockIndex < 2 || releaseInitialization < 0) {
    fail(`${region.id}: decoded array-fold initialization boundary does not match`);
  }
  const initializedLocals = [
    parameters.arrayLocal,
    parameters.lengthLocal,
    parameters.indexLocal,
    parameters.stopLocal,
    ...parameters.accumulatorLocals,
    parameters.effectiveStopLocal,
    parameters.releaseReadyLocal,
  ];
  const prefix = new Set(normalized.slice(0, blockIndex));
  if (initializedLocals.some((local) => !prefix.has(`.localSet ${local}`))) {
    fail(`${region.id}: decoded array-fold initialization locals do not match`);
  }
  const expectedResults = parameters.resultSlots.flatMap((slot, index) => [
    `.localGet ${parameters.accumulatorStart + slot}`,
    `.localSet ${parameters.resultLocals[index]}`,
  ]);
  if (JSON.stringify(normalized.slice(blockIndex + 1)) !== JSON.stringify(expectedResults)) {
    fail(`${region.id}: decoded array-fold result placement does not match`);
  }
  const blockPath = [
    ...region.location.listPath,
    { instructionIndex: region.location.startIndex + blockIndex, field: "block" },
  ];
  const block = normalizeInstructions(resolveInstructionList(body, blockPath));
  if (block.length !== 1 || !block[0].startsWith(".loop ")) {
    fail(`${region.id}: decoded array-fold block does not contain one loop`);
  }
  const loopPath = [
    ...blockPath,
    { instructionIndex: 0, field: "loop" },
  ];
  const loop = normalizeInstructions(resolveInstructionList(body, loopPath));
  const expectedGuard = parameters.reverse ? [
    `.localGet ${parameters.indexLocal}`,
    `.localGet ${parameters.stopLocal}`,
    ".leUI64",
    ".br_if 1",
    `.localGet ${parameters.indexLocal}`,
    ".constI64 (1 : UInt64)",
    ".subI64",
    `.localSet ${parameters.indexLocal}`,
  ] : [
    `.localGet ${parameters.indexLocal}`,
    `.localGet ${parameters.effectiveStopLocal}`,
    ".geUI64",
    ".br_if 1",
  ];
  if (JSON.stringify(loop.slice(0, expectedGuard.length)) !== JSON.stringify(expectedGuard)) {
    fail(`${region.id}: decoded array-fold guard does not match`);
  }
  const dynamicPrefix = [
    `.localGet ${parameters.arrayLocal}`,
    `.localGet ${parameters.indexLocal}`,
    ".constI64 (1 : UInt64)",
    ".mulI64",
    ".constI64 (1 : UInt64)",
    ".addI64",
    ".constI64 (8 : UInt64)",
    ".mulI64",
    ".addI64",
    ".wrapI64",
    ".load64 (0 : UInt32)",
    `.localSet ${parameters.itemLocals[0]}`,
  ];
  const dynamicTraversalEligible = !parameters.reverse &&
    parameters.sourceWidth === 1 &&
    JSON.stringify(loop.slice(expectedGuard.length,
      expectedGuard.length + dynamicPrefix.length)) === JSON.stringify(dynamicPrefix);
  const transitionSuffix = [
    ...parameters.accumulatorLocals.flatMap((local, index) => [
      `.localGet ${parameters.stagedValueStart + index}`,
      `.localSet ${local}`,
    ]),
    ".constI64 (1 : UInt64)",
    `.localSet ${parameters.releaseReadyLocal}`,
    `.localGet ${parameters.doneLocal}`,
    ".constI64 (0 : UInt64)",
    ".neI64",
    ".br_if 1",
    ...(!parameters.reverse ? [
      `.localGet ${parameters.indexLocal}`,
      ".constI64 (1 : UInt64)",
      ".addI64",
      `.localSet ${parameters.indexLocal}`,
    ] : []),
    ".br 0",
  ];
  if (JSON.stringify(loop.slice(-transitionSuffix.length)) !==
      JSON.stringify(transitionSuffix)) {
    fail(`${region.id}: decoded array-fold transition does not match`);
  }
  const setupInitial = normalized[14]?.match(/^\.constI64 \(([0-9]+) : UInt64\)$/);
  const forwardSetupCandidate = parameters.resultWidth === 1 &&
    parameters.accumulatorLocals.length === 1 && !parameters.reverse &&
    blockIndex === 23 && normalized[21] === ".iff 0 1 [";
  const forwardSetupExpected = forwardSetupCandidate ? [
      ".localGet 0",
      `.localSet ${parameters.arrayLocal}`,
      `.localGet ${parameters.arrayLocal}`,
      ".wrapI64",
      ".load64 (0 : UInt32)",
      `.localSet ${parameters.lengthLocal}`,
      ".constI64 (0 : UInt64)",
      `.localSet ${parameters.indexLocal}`,
      ".localGet 0",
      `.localSet ${parameters.doneLocal}`,
      `.localGet ${parameters.doneLocal}`,
      ".wrapI64",
      ".load64 (0 : UInt32)",
      `.localSet ${parameters.stopLocal}`,
      setupInitial === null ? "" : `.constI64 (${setupInitial[1]} : UInt64)`,
      `.localSet ${parameters.accumulatorLocals[0]}`,
      ".constI64 (0 : UInt64)",
      `.localSet ${parameters.releaseReadyLocal}`,
      `.localGet ${parameters.stopLocal}`,
      `.localGet ${parameters.lengthLocal}`,
      ".ltUI64",
      ".iff 0 1 [",
      `.localSet ${parameters.effectiveStopLocal}`,
    ] : [];
  const forwardSetupThen = forwardSetupCandidate
    ? normalizeInstructions(resolveInstructionList(body, [
      ...region.location.listPath,
      {
        instructionIndex: region.location.startIndex + 21,
        field: "then",
      },
    ])) : [];
  const forwardSetupElse = forwardSetupCandidate
    ? normalizeInstructions(resolveInstructionList(body, [
      ...region.location.listPath,
      {
        instructionIndex: region.location.startIndex + 21,
        field: "else",
      },
    ])) : [];
  const forwardSetupEligible = forwardSetupCandidate && setupInitial !== null &&
    JSON.stringify(normalized.slice(0, blockIndex)) ===
      JSON.stringify(forwardSetupExpected) &&
    JSON.stringify(forwardSetupThen) ===
      JSON.stringify([`.localGet ${parameters.stopLocal}`]) &&
    JSON.stringify(forwardSetupElse) ===
      JSON.stringify([`.localGet ${parameters.lengthLocal}`]);
  const resultPlacementEligible = parameters.resultSlots.length === 1;
  const resultTail = normalizeInstructions(
    instructions.slice(region.location.endIndex));
  const resultRoot = resultTail[0]?.match(/^\.localGet ([0-9]+)$/);
  const resultValue = resultTail[10]?.match(/^\.localGet ([0-9]+)$/);
  const finishRoot = resultTail[12]?.match(/^\.localGet ([0-9]+)$/);
  const finishDestination = resultTail[13]?.match(/^\.localSet ([0-9]+)$/);
  const finishDestinationGet = resultTail[14]?.match(/^\.localGet ([0-9]+)$/);
  const finishReturn = resultTail[15]?.match(/^\.localSet ([0-9]+)$/);
  const singletonResultEligible = resultPlacementEligible &&
    resultTail.length === 16 && resultRoot !== null && resultValue !== null &&
    finishRoot !== null && finishDestination !== null &&
    finishDestinationGet !== null && finishReturn !== null &&
    resultValue[1] === `${parameters.resultLocals[0]}` &&
    finishRoot[1] === resultRoot[1] &&
    finishDestinationGet[1] === finishDestination[1] &&
    JSON.stringify(resultTail.slice(1, 10)) === JSON.stringify([
      ".constI64 (0 : UInt64)",
      ".constI64 (1 : UInt64)",
      ".mulI64",
      ".constI64 (1 : UInt64)",
      ".addI64",
      ".constI64 (8 : UInt64)",
      ".mulI64",
      ".addI64",
      ".wrapI64",
    ]) && resultTail[11] === ".store64 (0 : UInt32)";
  const guardedBackEdgeEligible = dynamicTraversalEligible && !parameters.reverse &&
    parameters.descriptorVersion === 1 && parameters.descriptor !== null &&
    typeof parameters.descriptor === "object";
  return {
    functionIndex: function_.wasmIndex,
    frameWidth: function_.parameters + function_.locals,
    regionId: region.id,
    regionKind: region.kind,
    parameters,
    dynamicTraversalEligible,
    forwardSetupEligible,
    guardedBackEdgeEligible,
    resultPlacementEligible,
    singletonResultEligible,
    ...(dynamicTraversalEligible ? {
      continuingEndIndex: expectedGuard.length + dynamicPrefix.length,
      loopPath,
    } : {}),
    ...(forwardSetupEligible ? {
      setupEndIndex: region.location.startIndex + blockIndex,
      setupInitialValue: setupInitial[1],
    } : {}),
    ...(guardedBackEdgeEligible ? {
      stepEndIndex: loop.length,
      stepStartIndex: expectedGuard.length + dynamicPrefix.length,
    } : {}),
    ...(resultPlacementEligible ? {
      resultAccumulatorLocal:
        parameters.accumulatorStart + parameters.resultSlots[0],
      resultEndIndex: region.location.endIndex,
      resultLocal: parameters.resultLocals[0],
      resultStartIndex: region.location.startIndex + blockIndex + 1,
    } : {}),
    ...(singletonResultEligible ? {
      singletonResultDestinationLocal: Number(finishDestination[1]),
      singletonResultEndIndex: instructions.length,
      singletonResultReturnLocal: Number(finishReturn[1]),
      singletonResultRootLocal: Number(resultRoot[1]),
    } : {}),
  };
}

function matchWhileLoopRegion(program, function_, region) {
  const body = programFunctionBody(program, function_.wasmIndex);
  const instructions = resolveInstructionList(body, region.location.listPath);
  const selected = normalizeInstructions(
    instructions.slice(region.location.startIndex, region.location.endIndex));
  if (selected.length !== 1 || !selected[0].startsWith(".block ")) {
    fail(`${region.id}: decoded while-loop region is not one structured block`);
  }
  const blockPath = [
    ...region.location.listPath,
    { instructionIndex: region.location.startIndex, field: "block" },
  ];
  const block = normalizeInstructions(resolveInstructionList(body, blockPath));
  if (block.length !== 1 || !block[0].startsWith(".loop ")) {
    fail(`${region.id}: decoded while-loop block does not contain one loop`);
  }
  const loop = normalizeInstructions(resolveInstructionList(body, [
    ...blockPath,
    { instructionIndex: 0, field: "loop" },
  ]));
  const exitIndex = loop.indexOf(".br_if 1");
  if (exitIndex < 1 || loop[exitIndex - 1] !== ".eqz" || loop.at(-1) !== ".br 0") {
    fail(`${region.id}: decoded while-loop guard or back edge does not match`);
  }
  return {
    functionIndex: function_.wasmIndex,
    regionId: region.id,
    regionKind: region.kind,
    parameters: region.parameters,
    entryEligible: scalarEntryState(function_, region, program) !== null,
  };
}

function matchScalarPostTestLoopRegion(program, function_, region) {
  const body = programFunctionBody(program, function_.wasmIndex);
  const instructions = resolveInstructionList(body, region.location.listPath);
  const selected = normalizeInstructions(
    instructions.slice(region.location.startIndex, region.location.endIndex));
  if (selected.length !== 1 || !selected[0].startsWith(".block ")) {
    fail(`${region.id}: decoded scalar post-test region is not one structured block`);
  }
  const blockPath = [
    ...region.location.listPath,
    { instructionIndex: region.location.startIndex, field: "block" },
  ];
  const block = normalizeInstructions(resolveInstructionList(body, blockPath));
  if (block.length !== 1 || !block[0].startsWith(".loop ")) {
    fail(`${region.id}: decoded scalar post-test block does not contain one loop`);
  }
  const loop = normalizeInstructions(resolveInstructionList(body, [
    ...blockPath,
    { instructionIndex: 0, field: "loop" },
  ]));
  if (loop.length < 2 || loop.at(-2) !== ".br_if 1" || loop.at(-1) !== ".br 0") {
    fail(`${region.id}: decoded scalar post-test back edge does not match`);
  }
  return {
    functionIndex: function_.wasmIndex,
    regionId: region.id,
    regionKind: region.kind,
    parameters: region.parameters,
    entryEligible: scalarEntryState(function_, region, program) !== null,
    counterTransferIdentityEligible:
      scalarCounterTransferSummary(function_, region, program) !== null,
  };
}

function scalarDescriptorHasUnitOperation(value, operation) {
  if (value === null || typeof value !== "object") return false;
  if (Array.isArray(value)) {
    return value.some((item) => scalarDescriptorHasUnitOperation(item, operation));
  }
  if (value.kind === "bin" && value.operation === operation &&
      ((value.left?.kind === "const" && value.left.value === "1") ||
       (value.right?.kind === "const" && value.right.value === "1"))) {
    return true;
  }
  return Object.values(value)
    .some((item) => scalarDescriptorHasUnitOperation(item, operation));
}

function scalarDescriptorHasBinaryOperation(value) {
  if (value === null || typeof value !== "object") return false;
  if (Array.isArray(value)) return value.some(scalarDescriptorHasBinaryOperation);
  if (value.kind === "bin") return true;
  return Object.values(value).some(scalarDescriptorHasBinaryOperation);
}

function arrayFoldFrameRoleLabels(parameters) {
  const labels = new Map();
  const add = (local, label) => {
    if (!labels.has(local)) labels.set(local, []);
    labels.get(local).push(label);
  };
  add(parameters.arrayLocal, "arrayLocal");
  add(parameters.lengthLocal, "lengthLocal");
  add(parameters.indexLocal, "indexLocal");
  add(parameters.stopLocal, "stopLocal");
  add(parameters.effectiveStopLocal, "effectiveStopLocal");
  add(parameters.doneLocal, "doneLocal");
  add(parameters.releaseReadyLocal, "releaseReadyLocal");
  parameters.accumulatorLocals.forEach((local, index) =>
    add(local, `accumulatorLocals[${index}]`));
  parameters.itemLocals.forEach((local, index) =>
    add(local, `itemLocals[${index}]`));
  parameters.resultLocals.forEach((local, index) =>
    add(local, `resultLocals[${index}]`));
  for (let index = 0; index < parameters.resultWidth; index += 1) {
    add(parameters.stagedValueStart + index, `stagedValueStart+${index}`);
  }
  return labels;
}

function loopRecipe(
    match, selectedSections = [], annotationNamespace = "Project.AnnotationMatches") {
  const checkedScalarLoop = [
    "leanexe.loop.while.v1", "leanexe.loop.scalar-post-test.v1",
  ].includes(match.regionKind) && match.parameters.descriptor !== null;
  if (checkedScalarLoop) {
    const name = match.regionId.replace(/[^A-Za-z0-9_]/g, "_");
    const postTest = match.regionKind === "leanexe.loop.scalar-post-test.v1";
    const hasUnitDecrement = scalarDescriptorHasUnitOperation(
      match.parameters.descriptor.body, "sub");
    const hasUnitIncrement = scalarDescriptorHasUnitOperation(
      match.parameters.descriptor.body, "add");
    const hasBinaryOperation = scalarDescriptorHasBinaryOperation(
      match.parameters.descriptor.body);
    return {
      recipeVersion: 2,
      functionIndex: match.functionIndex,
      regionId: match.regionId,
      regionKind: match.regionKind,
      applicability: "Lean-checked equality over the decoded instruction region",
      direct: {
        module: "Project.ProofKit.ScalarTransition",
        theorem: postTest
          ? "Project.ProofKit.ScalarTransition.postTestProgram_spec"
          : "Project.ProofKit.ScalarTransition.whileProgram_spec",
        regionEquality: annotationMatchTheoremName(match.regionId, annotationNamespace),
        tailEquality: annotationTailTheoremName(match.regionId, annotationNamespace),
        program: exactRecipeProgram(match, annotationNamespace),
      },
      supporting: [
        ...(match.counterTransferIdentityEligible ? [{
          declaration:
            `${annotationNamespace}.${name}_terminates_with_counter_transfer_identity`,
          purpose: "prove the complete store-preserving identity function from its checked counter-transfer loop",
        }] : []),
        ...(match.entryEligible ? [{
          declaration: `${annotationNamespace}.${name}_terminates_with_of_loop`,
          purpose: "enter the checked loop from TerminatesWith with the exact WebAssembly argument order",
        }, {
          declaration: `${annotationNamespace}.${name}_entry_to_loop`,
          purpose: "carry arbitrary i64 arguments through the checked function-entry prefix",
        }] : []),
        {
          declaration: `${annotationNamespace}.${name}_condition_eval`,
          purpose: "use the checked condition transition without reducing the scalar evaluator",
        },
        {
          declaration: `${annotationNamespace}.${name}_body_eval`,
          purpose: "use the checked body transition without exposing scratch-local updates",
        },
        {
          declaration: "Project.ProofKit.ScalarTransition.Expr.program_spec",
          purpose: "prove each typed scalar guard expression",
        },
        {
          declaration: "Project.ProofKit.ScalarTransition.Stmt.program_spec",
          purpose: "prove each typed scalar loop-body transition",
        },
        {
          declaration: "Project.ProofKit.ScalarTransition.Stmt.eval_preserves_below",
          purpose: "preserve each application local below scratch that the body does not write",
        },
        {
          declaration: "Project.ProofKit.ScalarTransition.State.localU64ToNat",
          purpose: "define a natural-number loop measure from an i64 local without a Value pattern",
        },
        ...(hasBinaryOperation ? [{
          declaration: "Project.ProofKit.ScalarTransition.U64Op.apply",
          purpose: "reduce descriptor operations to ordinary UInt64 operations after a generated transition equation",
        }] : []),
        ...(hasUnitDecrement ? [{
          declaration:
            "Project.ProofKit.ScalarTransition.CounterTransition.decrement_toNat_lt",
          purpose: "prove strict natural-number decrease for a nonzero UInt64 decrement",
        }] : []),
        ...(hasUnitDecrement && hasUnitIncrement ? [{
          declaration:
            "Project.ProofKit.ScalarTransition.CounterTransition.decrement_add_increment",
          purpose: "preserve a wrapping sum when one UInt64 counter decreases and another increases",
        }] : []),
        {
          declaration: postTest
            ? "Project.ProofKit.ScalarTransition.postTestProgram_spec"
            : "Project.ProofKit.ScalarTransition.whileProgram_spec",
          purpose: postTest
            ? "compose a checked post-test transition with the invariant and measure"
            : "compose the checked transition with the invariant and measure",
        },
      ],
      expectedPostcondition: "an invariant-preserving transition with a decreasing measure",
      guidance: ["strategy.loops", "strategy.frames", "strategy.arithmetic"]
        .filter((section) => selectedSections.includes(section)),
    };
  }
  const arrayFold = match.regionKind === "leanexe.array.fold.v1";
  const frameRoleLabels = arrayFold
    ? arrayFoldFrameRoleLabels(match.parameters) : new Map();
  const name = match.regionId.replace(/[^A-Za-z0-9_]/g, "_");
  return {
    recipeVersion: arrayFold ? 2 : 1,
    functionIndex: match.functionIndex,
    regionId: match.regionId,
    regionKind: match.regionKind,
    applicability: arrayFold
      ? "Lean-checked equality over the decoded instruction region"
      : "exact decoded instruction match",
    direct: {
      module: "Project.ProofKit.Control",
      theorem: "Wasm.wp_loop_cons",
      ...(arrayFold ? {
        regionEquality: annotationMatchTheoremName(match.regionId, annotationNamespace),
        tailEquality: annotationTailTheoremName(match.regionId, annotationNamespace),
        program: exactRecipeProgram(match, annotationNamespace),
      } : {}),
    },
    supporting: [
      ...(arrayFold ? [{
        declaration: `${annotationNamespace}.${name}_eq`,
        purpose: "rewrite the selected decoded interval to its named exact program",
      }, {
        declaration: `${annotationNamespace}.${name}_program`,
        purpose: "name the complete checked fold interval, including initialization and result placement",
      }, ...(match.forwardSetupEligible ? [{
        declaration: `${annotationNamespace}.${name}_setup_eq`,
        purpose: "rewrite the exact forward full-array setup interval",
      }, {
        declaration: `${annotationNamespace}.${name}_setup_program`,
        purpose: "name the compiler-matched setup through effective-stop selection",
      }, {
        declaration: "Project.ProofKit.FixedArrayFold.forwardSetupProgram_spec",
        purpose: "execute the checked length loads and fold-local initialization",
      }, {
        declaration: "Project.ProofKit.FixedArrayFold.forwardSetupFrame",
        purpose: "state the exact initialized frame at loop entry",
      }, ...(match.dynamicTraversalEligible ? [{
        declaration: `${annotationNamespace}.${name}_setup_frame_eq`,
        purpose: "normalize setup into the generated continuing-frame representation",
      }] : [])] : []), ...(match.resultPlacementEligible ? [{
        declaration: `${annotationNamespace}.${name}_result_eq`,
        purpose: "rewrite the exact accumulator result-placement interval",
      }, {
        declaration: `${annotationNamespace}.${name}_result_program`,
        purpose: "name the compiler-matched accumulator-to-result transfer",
      }, {
        declaration: "Project.ProofKit.FixedArrayFold.resultProgram_spec",
        purpose: "execute result placement from one accumulator getter",
      }, {
        declaration: "Project.ProofKit.FixedArrayFold.resultFrame",
        purpose: "state the exact result-placement frame",
      }, {
        declaration: "Project.ProofKit.FixedArrayFold.resultFrame_params",
        purpose: "preserve parameters across result placement",
      }, {
        declaration: "Project.ProofKit.FixedArrayFold.resultFrame_locals_length",
        purpose: "preserve the internal-local length across result placement",
      }, {
        declaration: "Project.ProofKit.FixedArrayFold.resultFrame_values",
        purpose: "preserve the operand-stack projection across result placement",
      }] : []), ...(match.singletonResultEligible ? [{
        declaration: `${annotationNamespace}.${name}_singleton_result_eq`,
        purpose: "rewrite the complete accumulator-placement, singleton payload-store, and root-transfer suffix",
      }, {
        declaration: `${annotationNamespace}.${name}_singleton_result_program`,
        purpose: "name the compiler-matched complete singleton fold-result suffix",
      }, ...(match.guardedBackEdgeEligible ? [{
        declaration: `${annotationNamespace}.${name}_singleton_result_spec`,
        purpose: "execute the exact singleton fold-result suffix to a caller-supplied postcondition",
      }] : []), {
        declaration: "Project.ProofKit.FixedArrayFold.singletonResultProgram_spec_to",
        purpose: "execute a singleton fold-result suffix to an arbitrary exact final-state postcondition",
      }, {
        declaration: "Project.ProofKit.FixedArrayFold.singletonResultProgram_spec",
        purpose: "execute the complete singleton fold-result suffix to a compact represented-output assertion",
      }, {
        declaration: "Project.ProofKit.FixedArrayFold.singletonResultPost",
        purpose: "state the compact represented singleton result and return-local endpoint",
      }] : []), {
        declaration: "Project.ProofKit.ArrayFold.foldPrefix",
        purpose: "state the loop invariant as the fold over the consumed input prefix",
      }, {
        declaration: "Project.ProofKit.ArrayFold.foldPrefix_succ",
        purpose: "rewrite the continuing branch as one fold step at the current element",
      }, {
        declaration: "Project.ProofKit.ArrayFold.foldPrefix_size",
        purpose: "rewrite the exit accumulator as the complete Array.foldl result",
      }, ...(match.dynamicTraversalEligible ? [{
        declaration: `${annotationNamespace}.${name}_continuing_eq`,
        purpose: "rewrite the exact continuing guard and indexed element-load prefix",
      }, {
        declaration: `${annotationNamespace}.${name}_continuing_program`,
        purpose: "name the compiler-matched continuing guard and indexed element-load prefix",
      }, {
        declaration: "Project.ProofKit.FixedArrayTraversalInput.continuingProgram_spec",
        purpose: "execute the continuing guard and indexed element load from the annotated local roles",
      }, ...(match.guardedBackEdgeEligible ? [{
        declaration: `${annotationNamespace}.${name}_continuing_spec`,
        purpose: "execute the prefix from the generated scalar frame with only semantic input, index, and continuation premises",
      }, {
        declaration: `${annotationNamespace}.${name}_continuing_loaded_frame_eq`,
        purpose: "identify the generated scalar frame after the checked indexed element load",
      }, {
        declaration: `${annotationNamespace}.${name}_continuing_frame_params`,
        purpose: "expose the exact parameter list of the generated continuing frame",
      }, {
        declaration: `${annotationNamespace}.${name}_continuing_frame_locals_length`,
        purpose: "expose the exact local-list length of the generated continuing frame",
      }, {
        declaration: `${annotationNamespace}.${name}_continuing_frame_values`,
        purpose: "expose the empty operand stack of the generated continuing frame",
      }, ...Array.from({ length: match.frameWidth }, (_, index) => {
        const roles = frameRoleLabels.get(index);
        return {
          declaration: `${annotationNamespace}.${name}_continuing_frame_get_${index}`,
          purpose: `read generated continuing-frame index ${index}` +
            (roles === undefined ? "" : ` (${roles.join(", ")})`),
        };
      }), {
        declaration: "Project.ProofKit.FixedArrayFold.resultFrame_get_result",
        purpose: "read the value placed in a valid nonparameter result local",
      }, {
        declaration: "Project.ProofKit.FixedArrayFold.resultFrame_get_of_ne",
        purpose: "preserve a distinct valid nonparameter local across result placement",
      }, {
        declaration: "Project.ProofKit.FixedArrayFoldBody.continuingGuardedProgram_spec",
        purpose: "compose the continuing traversal guard and load with the compiler-described guarded back edge",
      }] : []), {
        declaration: "Project.ProofKit.FixedArrayTraversalInput.continuingProgram_exit_spec",
        purpose: "execute the same checked guard through Break 1 when the index equals the effective stop",
      }, {
        declaration: "Project.ProofKit.FixedArrayTraversalInput.dynamicProgram_spec",
        purpose: "execute an indexed element load after a separate loop-guard reduction",
      }, {
        declaration: "Project.ProofKit.Frame.internal_getElem?_of_get",
        purpose: "project an invariant getter to the internal local list used by a dependent continuation",
      }, {
        declaration: "Project.ProofKit.Frame.internal_getElem_of_get",
        purpose: "project an invariant getter to a bounded internal local value",
      }] : []), ...(match.guardedBackEdgeEligible ? [{
        declaration: `${annotationNamespace}.${name}_step_eq`,
        purpose: "rewrite the exact scalar fold update, conditional exit, index increment, and back edge",
      }, {
        declaration: `${annotationNamespace}.${name}_step_program`,
        purpose: "name the compiler-matched guarded back-edge interval",
      }, {
        declaration: `${annotationNamespace}.${name}_body_eval`,
        purpose: "use the compiler-derived scalar body transition in the loop invariant step",
      }, {
        declaration: `${annotationNamespace}.${name}_condition_eval`,
        purpose: "use the compiler-derived done-condition transition after the scalar body",
      }, {
        declaration: `${annotationNamespace}.${name}_step_continuing_eval`,
        purpose: "use the generated compact transition for the continuing index update",
      }, {
        declaration: "Project.ProofKit.ScalarTransition.guardedBackEdgeProgram_spec",
        purpose: "execute the descriptor body and condition through exit or the indexed back edge",
      }] : [])] : []),
      {
        declaration: "Project.ProofKit.wp_block_loop",
        purpose: "apply the block and loop rules after reaching the annotated region",
      },
      {
        declaration: "Project.ProofKit.wp_entry_to_loop",
        purpose: "reach a block-wrapped loop from a matching function entry",
      },
    ],
    expectedPostcondition: "an invariant-preserving transition with a decreasing measure",
    guidance: [
      ...(arrayFold ? ["strategy.arrays"] : []),
      "strategy.loops", "strategy.frames", "strategy.arithmetic",
    ]
      .filter((section) => selectedSections.includes(section)),
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

function fixedArrayLengthDispatchRecipe(
    match, selectedSections = [], annotationNamespace = "Project.AnnotationMatches") {
  const equality = match.parameters.encoding === "eq-normalized-v1";
  const bounded = match.parameters.encoding === "le-unsigned-v1";
  return {
    recipeVersion: 1,
    functionIndex: match.functionIndex,
    regionId: match.regionId,
    regionKind: match.regionKind,
    applicability: "exact decoded instruction match",
    direct: {
      module: "Project.ProofKit.FixedArrayLengthDispatch",
      theorem: bounded
        ? "Project.ProofKit.FixedArrayLengthDispatch.leProgram_spec"
        : equality
          ? "Project.ProofKit.FixedArrayLengthDispatch.eqProgram_spec"
          : "Project.ProofKit.FixedArrayLengthDispatch.program_spec",
      tactic: bounded
        ? "wp_fixed_array_length_le_dispatch_from"
        : equality
          ? "wp_fixed_array_length_eq_dispatch_from"
          : "wp_fixed_array_length_dispatch_from",
      invocation: bounded
        ? `wp_fixed_array_length_le_dispatch_from hArray at ` +
          `${match.parameters.inputLocal}, ${match.parameters.expectedSize}`
        : equality
          ? `wp_fixed_array_length_eq_dispatch_from hArray at ` +
            `${match.parameters.inputLocal}, ${match.parameters.expectedSize}`
          : `wp_fixed_array_length_dispatch_from hArray at ` +
            `${match.parameters.inputLocal}, ${match.parameters.expectedSize}`,
    },
    supporting: [
      {
        declaration: "Wasm.TerminatesWith.of_wp_entry_for",
        purpose: "specialize public entry execution to the represented input store before invoking the region tactic",
      },
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
      ...(match.functionPrefixEligible ? [
        {
          declaration: `${annotationNamespace}.${match.regionId.replace(
            /[^A-Za-z0-9_]/g, "_")}_function_eq`,
          purpose: "rewrite the decoded function to the named dispatch and suffix programs",
        },
        {
          declaration: `${annotationNamespace}.${match.regionId.replace(
            /[^A-Za-z0-9_]/g, "_")}_dispatch_eq`,
          purpose: "check the named dispatch program against the exact decoded prefix",
        },
      ] : []),
      ...match.capacityPrefixes.flatMap((capacity) => {
        const name = match.regionId.replace(/[^A-Za-z0-9_]/g, "_");
        const prefix = `${name}_${capacity.role}_capacity`;
        return [{
          declaration: `${annotationNamespace}.${prefix}_eq`,
          purpose: `rewrite the exact ${capacity.role}-branch capacity prefix`,
        }, {
          declaration: `${annotationNamespace}.${prefix}_program`,
          purpose: `name the compiler-matched ${capacity.role}-branch capacity prefix`,
        }, {
          declaration: "Project.ProofKit.FixedArrayCapacity.constantProgram_spec",
          purpose: "execute constant result-capacity normalization into its destination local",
        }, {
          declaration: "Project.ProofKit.FixedArrayCapacity.normalizedCapacity",
          purpose: "name the computed aligned capacity passed to allocation",
        }, {
          declaration: "Project.ProofKit.FixedArrayCapacity.capacityFrame",
          purpose: "state the exact post-capacity local frame",
        }, {
          declaration: "Project.ProofKit.FixedArrayCapacity.capacityFrame_get_capacity",
          purpose: "read the normalized capacity through the selected combined local",
        }, {
          declaration: "Project.ProofKit.FixedArrayCapacity.capacityFrame_internal_get_capacity",
          purpose: "supply the normalized capacity to an allocator's internal-local premise",
        }, {
          declaration: "Project.ProofKit.FixedArrayCapacity.normalizedCapacity_toNat_ge_eight",
          purpose: "derive the allocator's minimum-capacity premise from normalization",
        }, {
          declaration: "Project.ProofKit.FixedArrayAllocatorWindow.constantCapacityRegion_spec_withTail",
          purpose: "compose this prefix with an immediately following standard shifted allocator when its capacity local is offset plus nine",
        }];
      }),
    ],
    expectedPostcondition: "valid and invalid input-size branch obligations",
    guidance: ["strategy.arrays", "strategy.allocation", "strategy.frames"]
      .filter((section) => selectedSections.includes(section)),
  };
}

function fixedArrayFindIdxEqRecipe(
    match, selectedSections = [], annotationNamespace = "Project.AnnotationMatches") {
  const name = match.regionId.replace(/[^A-Za-z0-9_]/g, "_");
  return {
    recipeVersion: 2,
    functionIndex: match.functionIndex,
    regionId: match.regionId,
    regionKind: match.regionKind,
    applicability: "Lean-checked equality over the decoded instruction region",
    direct: {
      module: "Project.ProofKit.FixedArrayFindIdxEq",
      theorem: "Project.ProofKit.FixedArrayFindIdxEq.program_spec",
      regionEquality: `${annotationNamespace}.${name}_eq`,
      tailEquality: annotationTailTheoremName(match.regionId, annotationNamespace),
      program: exactRecipeProgram(match, annotationNamespace),
    },
    supporting: [
      {
        declaration: "Project.ProofKit.Annotation.region",
        purpose: "select the exact array search expression without its destination local update",
      },
      {
        declaration: "Project.ProofKit.FixedArrayFindIdxEq.predicate",
        purpose: "state the first-match predicate for the annotated constant key",
      },
      {
        declaration: "Project.ProofKit.FixedArrayFindIdxEq.noneFrame",
        purpose: "describe the encoded none result and continuation frame",
      },
      {
        declaration: "Project.ProofKit.FixedArrayFindIdxEq.someFrame",
        purpose: "describe the encoded first matching index and continuation frame",
      },
      {
        declaration: "Project.ProofKit.FixedArrayFindIdxEq.encodedIndex",
        purpose: "name the compiler's index-plus-one result encoding",
      },
      {
        declaration: "Project.ProofKit.FixedArrayFindIdxEq.encodedIndex_eq_ofNat_succ",
        purpose: "normalize the emitted index-plus-one word under its checked UInt64 bound",
      },
      {
        declaration: "Project.ProofKit.FixedArrayFindIdxEq.encodedIndex_ne_zero",
        purpose: "select the successful option branch without reducing modular arithmetic",
      },
      {
        declaration: "Project.ProofKit.FixedArrayFindIdxEq.encodedIndex_sub_one",
        purpose: "decode the successful result word back to the represented index",
      },
      {
        declaration: "Project.ProofKit.FixedArrayFindIdxEq.someFrame_params",
        purpose: "project the unchanged parameters without unfolding the search frames",
      },
      {
        declaration: "Project.ProofKit.FixedArrayFindIdxEq.someFrame_locals_length",
        purpose: "project the unchanged local-list length without unfolding the search frames",
      },
      {
        declaration: "Project.ProofKit.FixedArrayFindIdxEq.someFrame_values",
        purpose: "project the encoded result operand without unfolding the search frames",
      },
    ],
    expectedPostcondition: "none encoded as zero or the first matching index encoded by encodedIndex",
    guidance: ["strategy.arrays", "strategy.loops", "strategy.frames"]
      .filter((section) => selectedSections.includes(section)),
  };
}

function fixedArrayEraseCopyRecipe(
    match, selectedSections = [], annotationNamespace = "Project.AnnotationMatches") {
  const name = match.regionId.replace(/[^A-Za-z0-9_]/g, "_");
  return {
    recipeVersion: 2,
    functionIndex: match.functionIndex,
    regionId: match.regionId,
    regionKind: match.regionKind,
    applicability: "Lean-checked equality over the decoded instruction region",
    direct: {
      module: "Project.ProofKit.FixedArrayCopy",
      theorem: "Project.ProofKit.FixedArrayCopy.program_spec",
      regionEquality: `${annotationNamespace}.${name}_eq`,
      tailEquality: annotationTailTheoremName(match.regionId, annotationNamespace),
      program: exactRecipeProgram(match, annotationNamespace),
    },
    supporting: [
      {
        declaration: "Project.ProofKit.Annotation.region",
        purpose: "select the two exact copy loops after allocation and the result-length store",
      },
      {
        declaration: `${annotationNamespace}.${name}_prefix_eq`,
        purpose: "check the prefix-copy half of the selected region",
      },
      {
        declaration: `${annotationNamespace}.${name}_suffix_eq`,
        purpose: "check the shifted-suffix half of the selected region",
      },
      {
        declaration: "Project.ProofKit.FixedArrayCopy.prefixProgram_spec",
        purpose: "copy the cells before the removed element",
      },
      {
        declaration: "Project.ProofKit.FixedArrayCopy.suffixProgram_spec",
        purpose: "copy later cells after skipping one source element",
      },
      {
        declaration: "Project.ProofKit.FixedArrayCopy.eraseIdxProgram_spec",
        purpose: "specialize the one-word copy pair to an in-bounds Array.eraseIdx! result",
      },
      {
        declaration: "Project.ProofKit.UInt64Array.At.eraseIdx!_of_reads",
        purpose: "reconstruct the one-word result representation from prefix and shifted-suffix reads",
      },
      {
        declaration: "Project.ProofKit.FixedArrayCopy.cellRead",
        purpose: "state source and target cell facts at the program theorem boundary",
      },
      {
        declaration: "Project.ProofKit.FixedArrayCopy.counterFrame",
        purpose: "state the loop pair's final combined-local frame",
      },
    ],
    expectedPostcondition: "prefix cells copied unchanged and suffix cells shifted by sourceWidth",
    guidance: ["strategy.arrays", "strategy.loops", "strategy.memory", "strategy.frames"]
      .filter((section) => selectedSections.includes(section)),
  };
}

function encodedIndexDecoderRecipe(
    match, selectedSections = [], annotationNamespace = "Project.AnnotationMatches") {
  const name = match.regionId.replace(/[^A-Za-z0-9_]/g, "_");
  return {
    recipeVersion: 2,
    functionIndex: match.functionIndex,
    regionId: match.regionId,
    regionKind: match.regionKind,
    applicability: "Lean-checked equality over the decoded instruction region",
    direct: {
      module: "Project.ProofKit.EncodedIndexDecoder",
      theorem: "Project.ProofKit.EncodedIndexDecoder.program_spec",
      regionEquality: `${annotationNamespace}.${name}_eq`,
      tailEquality: annotationTailTheoremName(match.regionId, annotationNamespace),
      program: exactRecipeProgram(match, annotationNamespace),
    },
    supporting: [
      {
        declaration: "Project.ProofKit.Annotation.region",
        purpose: "select the exact encoded-index decoder and destination-local update",
      },
      {
        declaration: "Project.ProofKit.EncodedIndexDecoder.resultFrame",
        purpose: "name the decoder's exact local frame",
      },
      {
        declaration: "Project.ProofKit.EncodedIndexDecoder.resultFrame_decoded",
        purpose: "read zero or the decoded predecessor through the destination local",
      },
      {
        declaration: "Project.ProofKit.EncodedIndexDecoder.resultFrame_params",
        purpose: "preserve the parameter list at the decoder boundary",
      },
      {
        declaration: "Project.ProofKit.EncodedIndexDecoder.resultFrame_locals_length",
        purpose: "preserve the combined-local bound at the decoder boundary",
      },
      {
        declaration: "Project.ProofKit.EncodedIndexDecoder.resultFrame_values",
        purpose: "preserve the operand stack at the decoder boundary",
      },
    ],
    expectedPostcondition: "zero when the encoded word is zero, otherwise the encoded word minus one",
    guidance: ["strategy.arithmetic", "strategy.frames"]
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

function annotationTailTheoremName(
    regionId, annotationNamespace = "Project.AnnotationMatches") {
  return `${annotationNamespace}.` +
    `${regionId.replace(/[^A-Za-z0-9_]/g, "_")}_tail_eq`;
}

function exactRecipeProgram(
    match, annotationNamespace = "Project.AnnotationMatches") {
  const name = match.regionId.replace(/[^A-Za-z0-9_]/g, "_");
  if ([
    "leanexe.array.find-idx-eq.v1", "leanexe.option.encoded-index.v1",
    "leanexe.array.erase-copy.v1", "leanexe.array.fold.v1",
    "leanexe.loop.while.v1", "leanexe.loop.scalar-post-test.v1",
  ].includes(match.regionKind)) return `${annotationNamespace}.${name}_program`;
  if (match.regionKind === "leanexe.array.pair-result.v1") {
    return match.parameters.mode === "constants-v1"
      ? `Project.ProofKit.FixedArrayPairResult.constResultProgram ` +
        `${match.parameters.firstValue} ${match.parameters.secondValue} ` +
        `${match.parameters.destination}`
      : `Project.ProofKit.FixedArrayPairResult.inputResultProgram ` +
        `${match.parameters.inputIndex} ${match.parameters.destination}`;
  }
  if (match.regionKind === "leanexe.array.map-add.v1") {
    return `Project.ProofKit.FixedArrayMapAdd.wrapperProgram ` +
      `${match.parameters.maximumSize} ${match.parameters.addend}`;
  }
  if (match.regionKind === "leanexe.array.filter-lt.v1") {
    return `Project.ProofKit.FixedArrayFilterLt.wrapperProgram ` +
      `${match.parameters.maximumSize} ${match.parameters.threshold}`;
  }
  fail(`${match.regionId}: no exact semantic recipe program`);
}

function fixedArrayPairResultRecipe(
    match, selectedSections = [], annotationNamespace = "Project.AnnotationMatches") {
  const constants = match.parameters.mode === "constants-v1";
  const theorem = constants
    ? "Project.ProofKit.FixedArrayPairResult.constResultProgram_spec"
    : "Project.ProofKit.FixedArrayPairResult.inputResultProgram_spec";
  return {
    recipeVersion: 2,
    functionIndex: match.functionIndex,
    regionId: match.regionId,
    regionKind: match.regionKind,
    applicability: "Lean-checked equality over the decoded instruction region",
    direct: {
      module: "Project.ProofKit.FixedArrayPairResult",
      theorem,
      regionEquality: annotationMatchTheoremName(match.regionId, annotationNamespace),
      tailEquality: annotationTailTheoremName(match.regionId, annotationNamespace),
      program: exactRecipeProgram(match, annotationNamespace),
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

function fixedArrayMapAddRecipe(
    match, selectedSections = [], annotationNamespace = "Project.AnnotationMatches") {
  return {
    recipeVersion: 2,
    functionIndex: match.functionIndex,
    regionId: match.regionId,
    regionKind: match.regionKind,
    applicability: "Lean-checked equality over the decoded instruction region",
    direct: {
      module: "Project.ProofKit.FixedArrayMapAdd",
      theorem: "Project.ProofKit.FixedArrayMapAdd.wrapperProgram_spec",
      regionEquality: annotationMatchTheoremName(match.regionId, annotationNamespace),
      tailEquality: annotationTailTheoremName(match.regionId, annotationNamespace),
      program: exactRecipeProgram(match, annotationNamespace),
    },
    supporting: [
      {
        declaration: "Project.ProofKit.FixedArrayLengthDispatch.leProgram_spec",
        purpose: "select the bounded input-length branch",
      },
      {
        declaration: "Project.ProofKit.FixedArrayAllocatorWindow.region_spec_withTail",
        purpose: "prove both canonical result allocations",
      },
      {
        declaration: "Project.ProofKit.FixedArrayMapAdd.wrapperProgram_spec",
        purpose: "prove the map loop and public array result",
      },
    ],
    expectedPostcondition: "the bounded wrapping-add map result",
    guidance: ["strategy.arrays", "strategy.loops", "strategy.allocation", "strategy.frames"]
      .filter((section) => selectedSections.includes(section)),
  };
}

function fixedArrayFilterLtRecipe(
    match, selectedSections = [], annotationNamespace = "Project.AnnotationMatches") {
  return {
    recipeVersion: 2,
    functionIndex: match.functionIndex,
    regionId: match.regionId,
    regionKind: match.regionKind,
    applicability: "Lean-checked equality over the decoded instruction region",
    direct: {
      module: "Project.ProofKit.FixedArrayFilterLt",
      theorem: "Project.ProofKit.FixedArrayFilterLt.wrapperProgram_spec",
      regionEquality: annotationMatchTheoremName(match.regionId, annotationNamespace),
      tailEquality: annotationTailTheoremName(match.regionId, annotationNamespace),
      program: exactRecipeProgram(match, annotationNamespace),
    },
    supporting: [
      {
        declaration: "Project.ProofKit.FixedArrayLengthDispatch.leProgram_spec",
        purpose: "select the bounded input-length branch",
      },
      {
        declaration: "Project.ProofKit.FixedArrayAllocatorWindow.region_spec_withTail",
        purpose: "prove the empty-result allocation",
      },
      {
        declaration: "Project.ProofKit.FixedArrayFilterLt.wrapperProgram_spec",
        purpose: "prove allocation, filtering, dynamic length, and the public result",
      },
    ],
    expectedPostcondition: "the bounded stable filter result",
    guidance: ["strategy.arrays", "strategy.loops", "strategy.allocation", "strategy.frames"]
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
          matches.get(region.id), selectedSections, annotationNamespace));
      } else if (region.kind === "leanexe.array.find-idx-eq.v1") {
        recipes.push(fixedArrayFindIdxEqRecipe(
          matches.get(region.id), selectedSections, annotationNamespace));
      } else if (region.kind === "leanexe.option.encoded-index.v1") {
        recipes.push(encodedIndexDecoderRecipe(
          matches.get(region.id), selectedSections, annotationNamespace));
      } else if (region.kind === "leanexe.array.erase-copy.v1") {
        recipes.push(fixedArrayEraseCopyRecipe(
          matches.get(region.id), selectedSections, annotationNamespace));
      } else if (region.kind === "leanexe.array.search-key.v1") {
        recipes.push(fixedArraySearchKeyRecipe(
          matches.get(region.id), selectedSections));
      } else if (region.kind === "leanexe.array.eq-node.v1") {
        recipes.push(fixedArrayEqNodeRecipe(
          matches.get(region.id), selectedSections));
      } else if (region.kind === "leanexe.array.lt-node.v1") {
        recipes.push(fixedArrayLtNodeRecipe(
          matches.get(region.id), selectedSections));
      } else if (region.kind === "leanexe.array.map-add.v1") {
        recipes.push(fixedArrayMapAddRecipe(
          matches.get(region.id), selectedSections, annotationNamespace));
      } else if (region.kind === "leanexe.array.filter-lt.v1") {
        recipes.push(fixedArrayFilterLtRecipe(
          matches.get(region.id), selectedSections, annotationNamespace));
      } else if ([
        "leanexe.array.fold.v1", "leanexe.loop.fold.v1", "leanexe.loop.while.v1",
        "leanexe.loop.scalar-post-test.v1",
      ].includes(region.kind)) {
        recipes.push(loopRecipe(
          matches.get(region.id), selectedSections, annotationNamespace));
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
      ...fixedArraySingletonWrapperCompositions(document, program).map((composition) => ({
        compositionVersion: 1,
        kind: "fixed-array-singleton-wrapper-v1",
        functionIndex: composition.functionIndex,
        calleeIndex: composition.calleeIndex,
        descriptor: `${annotationNamespace}.${composition.name}`,
        regionEquality: `${annotationNamespace}.${composition.name}_eq`,
        direct: {
          module: "Project.ProofKit.FixedArraySingletonWrapper",
          theorem: "Project.ProofKit.FixedArraySingletonWrapper.wrapperProgram_spec",
        },
      })),
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
      } else if (region.kind === "leanexe.array.find-idx-eq.v1") {
        matches.push(matchFixedArrayFindIdxEqRegion(program, function_, region));
      } else if (region.kind === "leanexe.option.encoded-index.v1") {
        matches.push(matchEncodedIndexDecoderRegion(program, function_, region));
      } else if (region.kind === "leanexe.array.erase-copy.v1") {
        matches.push(matchFixedArrayEraseCopyRegion(program, function_, region));
      } else if (region.kind === "leanexe.array.search-key.v1") {
        matches.push(matchFixedArraySearchKeyRegion(program, function_, region));
      } else if (region.kind === "leanexe.array.eq-node.v1") {
        matches.push(matchFixedArrayEqNodeRegion(program, function_, region));
      } else if (region.kind === "leanexe.array.lt-node.v1") {
        matches.push(matchFixedArrayLtNodeRegion(program, function_, region));
      } else if (region.kind === "leanexe.array.map-add.v1") {
        matches.push(matchFixedArrayMapAddRegion(program, function_, region));
      } else if (region.kind === "leanexe.array.filter-lt.v1") {
        matches.push(matchFixedArrayFilterLtRegion(program, function_, region));
      } else if (region.kind === "leanexe.loop.fold.v1") {
        matches.push(matchLoopFoldRegion(program, function_, region));
      } else if (region.kind === "leanexe.array.fold.v1") {
        matches.push(matchArrayFoldRegion(program, function_, region));
      } else if (region.kind === "leanexe.loop.while.v1") {
        matches.push(matchWhileLoopRegion(program, function_, region));
      } else if (region.kind === "leanexe.loop.scalar-post-test.v1") {
        matches.push(matchScalarPostTestLoopRegion(program, function_, region));
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
    if (composition.kind === "fixed-array-singleton-wrapper-v1" &&
        composition.calleeIndex !== undefined) compositionKeys.push("calleeIndex");
    if (composition.compositionVersion === 2) compositionKeys.push("wrapper");
    exactKeys(composition, compositionKeys, description);
    if (![1, 2].includes(composition.compositionVersion) ||
        ![
          "fixed-array-search-chain-v1", "fixed-array-search-tree-v1",
          "fixed-array-singleton-wrapper-v1",
        ].includes(composition.kind) ||
        (composition.kind === "fixed-array-singleton-wrapper-v1" &&
          composition.compositionVersion !== 1)) {
      fail(`${description} has an unsupported identity`);
    }
    natural(composition.functionIndex, `${description}.functionIndex`);
    if (composition.calleeIndex !== undefined) {
      natural(composition.calleeIndex, `${description}.calleeIndex`);
    }
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
    const singleton = composition.kind === "fixed-array-singleton-wrapper-v1";
    const expectedModule = singleton
      ? "Project.ProofKit.FixedArraySingletonWrapper"
      : chain
        ? "Project.ProofKit.FixedArraySearchChain"
        : "Project.ProofKit.FixedArraySearchTree";
    const expectedTheorem = singleton
      ? `${expectedModule}.wrapperProgram_spec`
      : `${expectedModule}.${chain ? "Chain" : "Tree"}.` +
        `${composition.compositionVersion === 1 ? "program_spec" : "wrapperProgram_spec"}`;
    if (composition.direct.module !== expectedModule ||
        composition.direct.theorem !== expectedTheorem) {
      fail(`${description}.direct is unsupported`);
    }
    if (singleton && composition.calleeIndex !== undefined) {
      const function_ = document.functions.find((candidate) =>
        candidate.wasmIndex === composition.functionIndex);
      const callees = function_.regions.filter((region) =>
        region.kind === "leanexe.call.direct.v1").map((region) =>
        region.parameters.calleeIndex);
      if (callees.length !== 1 || callees[0] !== composition.calleeIndex) {
        fail(`${description}.calleeIndex does not identify the checked wrapper call`);
      }
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
    if (![1, 2].includes(recipe.recipeVersion) ||
        !regions.has(recipe.regionId) || found.has(recipe.regionId) ||
        recipe.functionIndex !== regions.get(recipe.regionId).functionIndex ||
        recipe.regionKind !== regions.get(recipe.regionId).kind) {
      fail(`${description} has an invalid identity`);
    }
    const region = regions.get(recipe.regionId);
    const checkedScalarLoop = [
      "leanexe.loop.while.v1", "leanexe.loop.scalar-post-test.v1",
    ].includes(region.kind) && region.parameters.descriptor !== null;
    const checkedArrayFold = region.kind === "leanexe.array.fold.v1" &&
      recipe.direct.regionEquality !== undefined &&
      recipe.direct.program !== undefined;
    const exactSemanticRecipe = [
      "leanexe.array.find-idx-eq.v1", "leanexe.array.erase-copy.v1",
      "leanexe.option.encoded-index.v1",
      "leanexe.array.pair-result.v1",
      "leanexe.array.map-add.v1",
      "leanexe.array.filter-lt.v1",
    ].includes(region.kind) || checkedScalarLoop || checkedArrayFold;
    const expectedApplicability = exactSemanticRecipe
      ? "Lean-checked equality over the decoded instruction region"
      : "exact decoded instruction match";
    if (recipe.applicability !== expectedApplicability) {
      fail(`${description} has an invalid applicability check`);
    }
    if (recipe.recipeVersion === 2 && !exactSemanticRecipe) {
      fail(`${description} has an unsupported recipe version`);
    }
    found.add(recipe.regionId);
    if (recipe.direct === null || typeof recipe.direct !== "object" ||
        Array.isArray(recipe.direct)) {
      fail(`${description}.direct must be an object`);
    }
    const directKeys = Object.keys(recipe.direct).sort();
    const legacyDirect =
      JSON.stringify(directKeys) === JSON.stringify(["module", "theorem"]) ||
      JSON.stringify(directKeys) ===
        JSON.stringify(["invocation", "module", "tactic", "theorem"]) ||
      JSON.stringify(directKeys) ===
        JSON.stringify(["module", "program", "regionEquality", "theorem"]);
    const exactDirect = JSON.stringify(directKeys) === JSON.stringify([
      "module", "program", "regionEquality", "tailEquality", "theorem",
    ]);
    if ((recipe.recipeVersion === 1 && !legacyDirect) ||
        (recipe.recipeVersion === 2 && !exactDirect)) {
      fail(`${description}.direct has unsupported fields`);
    }
    if (recipe.recipeVersion === 2) {
      string(recipe.direct.tailEquality, `${description}.direct.tailEquality`);
      const name = recipe.regionId.replace(/[^A-Za-z0-9_]/g, "_");
      if (!recipe.direct.tailEquality.endsWith(`.${name}_tail_eq`)) {
        fail(`${description}.direct.tailEquality is unsupported`);
      }
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
      const bounded = region.parameters.encoding === "le-unsigned-v1";
      const theorem = bounded
        ? "Project.ProofKit.FixedArrayLengthDispatch.leProgram_spec"
        : equality
          ? "Project.ProofKit.FixedArrayLengthDispatch.eqProgram_spec"
          : "Project.ProofKit.FixedArrayLengthDispatch.program_spec";
      const tactics = bounded
        ? ["wp_fixed_array_length_le_dispatch_from",
          "wp_fixed_array_length_le_dispatch"]
        : equality
          ? ["wp_fixed_array_length_eq_dispatch_from",
            "wp_fixed_array_length_eq_dispatch"]
          : ["wp_fixed_array_length_dispatch_from",
            "wp_fixed_array_length_dispatch"];
      if (recipe.direct.module !== "Project.ProofKit.FixedArrayLengthDispatch" ||
          recipe.direct.theorem !== theorem ||
          !tactics.includes(recipe.direct.tactic) ||
          typeof recipe.direct.invocation !== "string") {
        fail(`${description}.direct is unsupported`);
      }
    } else if (region.kind === "leanexe.array.find-idx-eq.v1") {
      const name = recipe.regionId.replace(/[^A-Za-z0-9_]/g, "_");
      if (recipe.direct.module !== "Project.ProofKit.FixedArrayFindIdxEq" ||
          recipe.direct.theorem !== "Project.ProofKit.FixedArrayFindIdxEq.program_spec" ||
          !recipe.direct.regionEquality.endsWith(`.${name}_eq`) ||
          !recipe.direct.program.endsWith(`.${name}_program`)) {
        fail(`${description}.direct is unsupported`);
      }
    } else if (region.kind === "leanexe.option.encoded-index.v1") {
      const name = recipe.regionId.replace(/[^A-Za-z0-9_]/g, "_");
      if (recipe.direct.module !== "Project.ProofKit.EncodedIndexDecoder" ||
          recipe.direct.theorem !== "Project.ProofKit.EncodedIndexDecoder.program_spec" ||
          !recipe.direct.regionEquality.endsWith(`.${name}_eq`) ||
          !recipe.direct.program.endsWith(`.${name}_program`)) {
        fail(`${description}.direct is unsupported`);
      }
    } else if (region.kind === "leanexe.array.erase-copy.v1") {
      const name = recipe.regionId.replace(/[^A-Za-z0-9_]/g, "_");
      if (recipe.direct.module !== "Project.ProofKit.FixedArrayCopy" ||
          recipe.direct.theorem !== "Project.ProofKit.FixedArrayCopy.program_spec" ||
          !recipe.direct.regionEquality.endsWith(`.${name}_eq`) ||
          !recipe.direct.program.endsWith(`.${name}_program`)) {
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
    } else if (region.kind === "leanexe.array.map-add.v1") {
      if (recipe.direct.module !== "Project.ProofKit.FixedArrayMapAdd" ||
          recipe.direct.theorem !==
            "Project.ProofKit.FixedArrayMapAdd.wrapperProgram_spec" ||
          !recipe.direct.regionEquality.endsWith(
            `.${recipe.regionId.replace(/[^A-Za-z0-9_]/g, "_")}_eq`) ||
          recipe.direct.program !== `Project.ProofKit.FixedArrayMapAdd.wrapperProgram ` +
            `${region.parameters.maximumSize} ${region.parameters.addend}`) {
        fail(`${description}.direct is unsupported`);
      }
    } else if (region.kind === "leanexe.array.filter-lt.v1") {
      if (recipe.direct.module !== "Project.ProofKit.FixedArrayFilterLt" ||
          recipe.direct.theorem !==
            "Project.ProofKit.FixedArrayFilterLt.wrapperProgram_spec" ||
          !recipe.direct.regionEquality.endsWith(
            `.${recipe.regionId.replace(/[^A-Za-z0-9_]/g, "_")}_eq`) ||
          recipe.direct.program !== `Project.ProofKit.FixedArrayFilterLt.wrapperProgram ` +
            `${region.parameters.maximumSize} ${region.parameters.threshold}`) {
        fail(`${description}.direct is unsupported`);
      }
    } else if (checkedScalarLoop) {
      const name = recipe.regionId.replace(/[^A-Za-z0-9_]/g, "_");
      const expectedTheorem = region.kind === "leanexe.loop.scalar-post-test.v1"
        ? "Project.ProofKit.ScalarTransition.postTestProgram_spec"
        : "Project.ProofKit.ScalarTransition.whileProgram_spec";
      if (recipe.direct.module !== "Project.ProofKit.ScalarTransition" ||
          recipe.direct.theorem !== expectedTheorem ||
          !recipe.direct.regionEquality.endsWith(`.${name}_eq`) ||
          !recipe.direct.program.endsWith(`.${name}_program`)) {
        fail(`${description}.direct is unsupported`);
      }
    } else if ([
      "leanexe.array.fold.v1", "leanexe.loop.fold.v1", "leanexe.loop.while.v1",
      "leanexe.loop.scalar-post-test.v1",
    ].includes(region.kind)) {
      const arrayFoldDirectInvalid = region.kind === "leanexe.array.fold.v1" &&
        checkedArrayFold &&
        (!recipe.direct.regionEquality.endsWith(
          `.${recipe.regionId.replace(/[^A-Za-z0-9_]/g, "_")}_eq`) ||
         !recipe.direct.program.endsWith(
           `.${recipe.regionId.replace(/[^A-Za-z0-9_]/g, "_")}_program`));
      if (recipe.direct.module !== "Project.ProofKit.Control" ||
          recipe.direct.theorem !== "Wasm.wp_loop_cons" ||
          arrayFoldDirectInvalid) {
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

function sameInstructions(found, expected) {
  return JSON.stringify(normalizeInstructions(found)) ===
    JSON.stringify(normalizeInstructions(expected));
}

function fixedArraySingletonWrapperCompositions(document, program = null) {
  if (program === null) return [];
  const compositions = [];
  for (const function_ of document.functions) {
    const calls = function_.regions.filter((region) =>
      region.kind === "leanexe.call.direct.v1");
    if (function_.parameters !== 1 || function_.results !== 1 ||
        function_.locals !== 14 || calls.length !== 1) continue;
    const call = calls[0];
    if (call.location.listPath.length !== 1 ||
        call.location.listPath[0].instructionIndex !== 14 ||
        call.location.listPath[0].field !== "then" ||
        call.location.startIndex !== 11 || call.location.endIndex !== 14 ||
        JSON.stringify(call.parameters.argumentLocals) !== "[1]" ||
        JSON.stringify(call.parameters.resultLocals) !== "[2]" ||
        call.parameters.resultPlacement !== "locals") continue;
    const body = programFunctionBody(program, function_.wasmIndex);
    const top = resolveInstructionList(body, []);
    const validPath = [{ instructionIndex: 14, field: "then" }];
    const invalidPath = [{ instructionIndex: 14, field: "else" }];
    const valid = resolveInstructionList(body, validPath);
    const invalid = resolveInstructionList(body, invalidPath);
    const expectedTop = [
      ".localGet 0", ".localSet 5", ".localGet 5", ".wrapI64",
      ".load64 (0 : UInt32)", ".constI64 (1 : UInt64)", ".eqI64",
      ".iff 0 1 [", ".constI64 (1 : UInt64)", ".eqI64", ".iff 0 1 [",
      ".constI64 (0 : UInt64)", ".eqI64", ".eqz", ".iff 0 0 [",
      ".localGet 4",
    ];
    const expectedPrefix = [
      ".localGet 0", ".localSet 5", ".constI64 (0 : UInt64)", ".localSet 6",
      ".localGet 6", ".localGet 5", ".wrapI64", ".load64 (0 : UInt32)",
      ".ltUI64", ".iff 0 1 [", ".localSet 1", ".localGet 1",
      `.call ${call.parameters.calleeIndex}`, ".localSet 2",
      ".constI64 (8 : UInt64)", ".constI64 (1 : UInt64)",
      ".constI64 (1 : UInt64)", ".mulI64", ".constI64 (8 : UInt64)",
      ".mulI64", ".addI64", ".constI64 (7 : UInt64)", ".addI64",
      ".constI64 (8 : UInt64)", ".divUI64", ".constI64 (8 : UInt64)",
      ".mulI64", ".localSet 9", ".localGet 9", ".constI64 (8 : UInt64)",
      ".ltUI64", ".iff 0 0 [",
    ];
    const expectedTail = [
      ".constI64 (0 : UInt64)", ".localSet 14", ".constI64 (0 : UInt64)",
      ".localSet 10", ".globalGet 1", ".localSet 11", ".block 0 0 [",
      ".localGet 14", ".constI64 (0 : UInt64)", ".eqI64", ".iff 0 0 [",
      ".globalGet 2", ".constI64 (1 : UInt64)", ".addI64", ".globalSet 2",
      ".localGet 14", ".localSet 5", ".localGet 5", ".wrapI64",
      ".constI64 (1 : UInt64)", ".store64 (0 : UInt32)", ".localGet 2",
      ".localSet 8", ".localGet 5", ".constI64 (0 : UInt64)",
      ".constI64 (1 : UInt64)", ".mulI64", ".constI64 (1 : UInt64)",
      ".addI64", ".constI64 (8 : UInt64)", ".mulI64", ".addI64", ".wrapI64",
      ".localGet 8", ".store64 (0 : UInt32)", ".localGet 5", ".localSet 3",
      ".localGet 3", ".localSet 4",
    ];
    const loadThen = resolveInstructionList(body,
      [...validPath, { instructionIndex: 9, field: "then" }]);
    const loadElse = resolveInstructionList(body,
      [...validPath, { instructionIndex: 9, field: "else" }]);
    if (!sameInstructions(top, expectedTop) ||
        !sameInstructions(invalid, [".localGet 0", ".localSet 4"]) ||
        valid.length !== expectedPrefix.length + expectedTail.length ||
        !sameInstructions(valid.slice(0, expectedPrefix.length), expectedPrefix) ||
        !sameInstructions(valid.slice(expectedPrefix.length), expectedTail) ||
        !sameInstructions(loadThen, [
          ".localGet 5", ".localGet 6", ".constI64 (1 : UInt64)", ".mulI64",
          ".constI64 (1 : UInt64)", ".addI64", ".constI64 (8 : UInt64)",
          ".mulI64", ".addI64", ".wrapI64", ".load64 (0 : UInt32)",
        ]) || !sameInstructions(loadElse, [".unreachable"])) continue;
    compositions.push({
      functionIndex: function_.wasmIndex,
      name: `function_${function_.wasmIndex}_singleton_wrapper_0`,
      calleeIndex: call.parameters.calleeIndex,
    });
  }
  return compositions;
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

function scalarOperationLean(operation) {
  return ({
    "add": ".add",
    "sub": ".sub",
    "mul": ".mul",
    "div-u": ".divU",
    "rem-u": ".remU",
    "bit-and": ".bitAnd",
    "bit-or": ".bitOr",
    "bit-xor": ".bitXor",
    "shift-left": ".shiftLeft",
    "shift-right": ".shiftRight",
  })[operation];
}

function scalarExprLean(expression) {
  if (expression.kind === "get") return `.get ${expression.index}`;
  if (expression.kind === "const") return `.const (${expression.value} : UInt64)`;
  if (expression.kind === "bin") {
    return `.bin ${scalarOperationLean(expression.operation)} ` +
      `(${scalarExprLean(expression.left)}) (${scalarExprLean(expression.right)})`;
  }
  return `.ite (${scalarCondLean(expression.condition)}) ` +
    `(${scalarExprLean(expression.then)}) (${scalarExprLean(expression.else)})`;
}

function scalarCondLean(condition) {
  if (condition.kind === "true") return ".bconst true";
  if (condition.kind === "false") return ".bconst false";
  if (["eq", "ne", "lt-u", "le-u"].includes(condition.kind)) {
    const constructor = ({ "eq": ".eq", "ne": ".ne", "lt-u": ".ltU", "le-u": ".leU" })[
      condition.kind];
    return `${constructor} (${scalarExprLean(condition.left)}) ` +
      `(${scalarExprLean(condition.right)})`;
  }
  if (condition.kind === "not") return `.not (${scalarCondLean(condition.condition)})`;
  const constructor = condition.kind === "and" ? ".and" : ".or";
  return `${constructor} (${scalarCondLean(condition.left)}) ` +
    `(${scalarCondLean(condition.right)})`;
}

function scalarStmtLean(statement) {
  if (statement.kind === "skip") return ".skip";
  if (statement.kind === "assign") {
    return `.assign ${statement.index} (${scalarExprLean(statement.value)})`;
  }
  if (statement.kind === "seq") {
    return `.seq (${scalarStmtLean(statement.first)}) (${scalarStmtLean(statement.second)})`;
  }
  return `.ite (${scalarCondLean(statement.condition)}) ` +
    `(${scalarStmtLean(statement.then)}) (${scalarStmtLean(statement.else)})`;
}

function scalarTransitionLeaf(value) {
  return { kind: "leaf", value };
}

function scalarTransitionIte(condition, thenTree, elseTree) {
  return { kind: "ite", condition, thenTree, elseTree };
}

function scalarValue(type, value, known = null) {
  return { type, value, known };
}

function scalarValueIte(condition, thenTree, elseTree) {
  if (condition.known === true) return thenTree;
  if (condition.known === false) return elseTree;
  return scalarTransitionIte(condition.value, thenTree, elseTree);
}

function scalarTransitionBind(tree, next) {
  if (tree.kind === "leaf") return next(tree.value);
  return scalarTransitionIte(
    tree.condition,
    scalarTransitionBind(tree.thenTree, next),
    scalarTransitionBind(tree.elseTree, next),
  );
}

function scalarStateSet(state, index, value) {
  if (!Number.isInteger(index) || index < 0 || index >= state.length) {
    fail(`scalar transition writes unavailable combined local ${index}`);
  }
  const next = [...state];
  next[index] = value;
  return next;
}

function scalarOperationTerm(operation, left, right) {
  const constructor = ({
    "add": ".add",
    "sub": ".sub",
    "mul": ".mul",
    "div-u": ".divU",
    "rem-u": ".remU",
    "bit-and": ".bitAnd",
    "bit-or": ".bitOr",
    "bit-xor": ".bitXor",
    "shift-left": ".shiftLeft",
    "shift-right": ".shiftRight",
  })[operation];
  return `Project.ProofKit.ScalarTransition.U64Op.apply ${constructor} ` +
    `(${left}) (${right})`;
}

function scalarExpressionTransition(expression, scratch, state) {
  if (expression.kind === "get") {
    if (expression.index >= state.length) {
      fail(`scalar transition reads unavailable combined local ${expression.index}`);
    }
    return scalarTransitionLeaf({
      value: scalarValue("u64", state[expression.index]), state,
    });
  }
  if (expression.kind === "const") {
    return scalarTransitionLeaf({
      value: scalarValue("u64", `(${expression.value} : UInt64)`, BigInt(expression.value)),
      state,
    });
  }
  if (expression.kind === "bin") {
    const staged = ["div-u", "rem-u"].includes(expression.operation);
    const childScratch = staged ? scratch + 2 : scratch;
    return scalarTransitionBind(
      scalarExpressionTransition(expression.left, childScratch, state),
      (left) => {
        const afterLeft = staged
          ? scalarStateSet(left.state, scratch, left.value.value)
          : left.state;
        return scalarTransitionBind(
          scalarExpressionTransition(expression.right, childScratch, afterLeft),
          (right) => scalarTransitionLeaf({
            value: scalarValue("u64", scalarOperationTerm(
              expression.operation, left.value.value, right.value.value)),
            state: staged
              ? scalarStateSet(right.state, scratch + 1, right.value.value)
              : right.state,
          }),
        );
      },
    );
  }
  if (["eq", "ne", "lt-u", "le-u"].includes(expression.kind)) {
    return scalarTransitionBind(
      scalarExpressionTransition(expression.left, scratch, state),
      (left) => scalarTransitionBind(
        scalarExpressionTransition(expression.right, scratch, left.state),
        (right) => {
          let known = null;
          if (typeof left.value.known === "bigint" &&
              typeof right.value.known === "bigint") {
            known = expression.kind === "eq"
              ? left.value.known === right.value.known
              : expression.kind === "ne"
                ? left.value.known !== right.value.known
              : expression.kind === "lt-u"
                ? left.value.known < right.value.known
                : left.value.known <= right.value.known;
          }
          return scalarTransitionLeaf({
            value: scalarValue("bool", expression.kind === "eq"
              ? `((${left.value.value}) == (${right.value.value}))`
              : expression.kind === "ne"
                ? `((${left.value.value}) != (${right.value.value}))`
              : expression.kind === "lt-u"
                ? `(decide ((${left.value.value}) < (${right.value.value})))`
                : `(decide ((${left.value.value}) ≤ (${right.value.value})))`, known),
            state: right.state,
          });
        },
      ),
    );
  }
  if (expression.kind === "true" || expression.kind === "false") {
    const known = expression.kind === "true";
    return scalarTransitionLeaf({
      value: scalarValue("bool", expression.kind, known), state,
    });
  }
  if (expression.kind === "not") {
    return scalarTransitionBind(
      scalarExpressionTransition(expression.condition, scratch, state),
      (result) => scalarTransitionLeaf({
        value: scalarValue("bool", `(!(${result.value.value}))`,
          typeof result.value.known === "boolean" ? !result.value.known : null),
        state: result.state,
      }),
    );
  }
  if (expression.kind === "and" || expression.kind === "or") {
    return scalarTransitionBind(
      scalarExpressionTransition(expression.left, scratch, state),
      (left) => {
        if (expression.kind === "and" && left.value.known === false) {
          return scalarTransitionLeaf({
            value: scalarValue("bool", "false", false), state: left.state,
          });
        }
        if (expression.kind === "or" && left.value.known === true) {
          return scalarTransitionLeaf({
            value: scalarValue("bool", "true", true), state: left.state,
          });
        }
        const right = scalarExpressionTransition(expression.right, scratch, left.state);
        return expression.kind === "and"
          ? scalarValueIte(
            left.value, right,
            scalarTransitionLeaf({
              value: scalarValue("bool", "false", false), state: left.state,
            }),
          )
          : scalarValueIte(
            left.value,
            scalarTransitionLeaf({
              value: scalarValue("bool", "true", true), state: left.state,
            }), right,
          );
      },
    );
  }
  if (expression.kind === "ite") {
    return scalarTransitionBind(
      scalarExpressionTransition(expression.condition, scratch, state),
      (condition) => scalarValueIte(
        condition.value,
        scalarExpressionTransition(expression.then, scratch, condition.state),
        scalarExpressionTransition(expression.else, scratch, condition.state),
      ),
    );
  }
  fail(`unsupported scalar transition expression ${expression.kind}`);
}

function scalarStatementTransition(statement, scratch, state) {
  if (statement.kind === "skip") return scalarTransitionLeaf(state);
  if (statement.kind === "assign") {
    return scalarTransitionBind(
      scalarExpressionTransition(statement.value, scratch, state),
      (result) => scalarTransitionLeaf(
        scalarStateSet(result.state, statement.index, result.value.value)),
    );
  }
  if (statement.kind === "seq") {
    return scalarTransitionBind(
      scalarStatementTransition(statement.first, scratch, state),
      (afterFirst) => scalarStatementTransition(statement.second, scratch, afterFirst),
    );
  }
  if (statement.kind === "ite") {
    return scalarTransitionBind(
      scalarExpressionTransition(statement.condition, scratch, state),
      (condition) => scalarValueIte(
        condition.value,
        scalarStatementTransition(statement.then, scratch, condition.state),
        scalarStatementTransition(statement.else, scratch, condition.state),
      ),
    );
  }
  fail(`unsupported scalar transition statement ${statement.kind}`);
}

function scalarStateTerm(stateName, state) {
  return `${stateName} ${state.map((value) => `(${value})`).join(" ")}`;
}

function scalarTransitionTerm(tree, leaf) {
  if (tree.kind === "leaf") return leaf(tree.value);
  return `(if ${tree.condition} then\n      ${scalarTransitionTerm(tree.thenTree, leaf)} ` +
    `else\n      ${scalarTransitionTerm(tree.elseTree, leaf)})`;
}

function scalarTransitionProof(tree, simpDeclarations, depth = 0, hypotheses = []) {
  if (tree.kind === "leaf") {
    return `simp (config := { maxSteps := 1000000 }) only [` +
      `${[...simpDeclarations, ...hypotheses].join(", ")}]`;
  }
  const hypothesis = `h${depth}`;
  const branchHypotheses = [...hypotheses, hypothesis];
  const thenProof = scalarTransitionProof(
    tree.thenTree, simpDeclarations, depth + 1, branchHypotheses)
    .replaceAll("\n", "\n  ");
  const elseProof = scalarTransitionProof(
    tree.elseTree, simpDeclarations, depth + 1, branchHypotheses)
    .replaceAll("\n", "\n  ");
  return `by_cases ${hypothesis} : (${tree.condition}) = true\n` +
    `· ${thenProof}\n` +
    `· ${elseProof}`;
}

function scalarTransitionSimpDeclarations(base, transition, syntax, statement = false) {
  const encoded = JSON.stringify(syntax);
  const declarations = [
    `${base}_${statement ? "body" : "condition"}`,
    `${base}_state`,
    transition,
    ...(statement ? ["Project.ProofKit.ScalarTransition.Stmt.evalU64"] : []),
    "Project.ProofKit.ScalarTransition.Expr.evalU64",
  ];
  declarations.push("Project.ProofKit.ScalarTransition.U64State.get");
  if (encoded.includes('"operation":"div-u"') ||
      encoded.includes('"operation":"rem-u"') || statement) {
    declarations.push("Project.ProofKit.ScalarTransition.U64State.set?");
  }
  declarations.push(
    "Option.bind",
    "Option.pure_def",
    "Option.bind_eq_bind",
    "Option.bind_some",
    "Option.bind_none",
    "Option.map",
    "List.length",
    "List.getElem?_cons_zero",
    "List.getElem?_cons_succ",
    "List.set",
    "Nat.reduceAdd",
    "Nat.reduceLT",
    "Nat.reduceSub",
    "reduceCtorEq",
    "or_true",
    "true_or",
    "or_false",
    "false_or",
    "Bool.false_eq_true",
    "Bool.not_eq_true'",
    "Bool.not_true",
    "Bool.not_false",
    "beq_self_eq_true",
    "Project.ProofKit.ScalarTransition.u64_one_beq_zero",
    "Project.ProofKit.ScalarTransition.u64_zero_beq_one",
    "decide_true",
    "decide_false",
    "if_true",
    "if_false",
  );
  return declarations;
}

function scalarTransitionDeclarations(function_, region) {
  const descriptor = region.parameters.descriptor;
  if (descriptor === null) return null;
  const count = function_.parameters + function_.locals;
  const variables = Array.from({ length: count }, (_, index) => `v${index}`);
  const stateName = `${region.id.replace(/[^A-Za-z0-9_]/g, "_")}_state`;
  const conditionName = `${region.id.replace(/[^A-Za-z0-9_]/g, "_")}_conditionTransition`;
  const bodyName = `${region.id.replace(/[^A-Za-z0-9_]/g, "_")}_bodyTransition`;
  const initial = [...variables];
  const condition = scalarExpressionTransition(
    descriptor.condition, region.parameters.scratchStart, initial);
  const body = scalarStatementTransition(
    descriptor.body, region.parameters.scratchStart, initial);
  const stateTerm = (state) => scalarStateTerm(stateName, state);
  const conditionTerm = scalarTransitionTerm(condition, (result) =>
    `some (${result.value.value}, ${stateTerm(result.state)})`);
  const bodyTerm = scalarTransitionTerm(body, (state) => `some (${stateTerm(state)})`);
  const binders = `(${variables.join(" ")} : UInt64)`;
  const stateArguments = variables.join(" ");
  const parameters = variables.slice(0, function_.parameters).join(", ");
  const locals = variables.slice(function_.parameters).join(", ");
  const base = region.id.replace(/[^A-Za-z0-9_]/g, "_");
  const conditionProof = scalarTransitionProof(condition,
    scalarTransitionSimpDeclarations(
      base, conditionName, descriptor.condition));
  const bodyProof = scalarTransitionProof(body,
    scalarTransitionSimpDeclarations(base, bodyName, descriptor.body, true));
  return {
    conditionTheorem: `${base}_condition_eval`,
    bodyTheorem: `${base}_body_eval`,
    source: `def ${stateName} ${binders} :
    Project.ProofKit.ScalarTransition.U64State :=
  { params := [${parameters}], locals := [${locals}] }

def ${conditionName} ${binders} :
    Option (Bool × Project.ProofKit.ScalarTransition.U64State) :=
  ${conditionTerm}

def ${bodyName} ${binders} :
    Option Project.ProofKit.ScalarTransition.U64State :=
  ${bodyTerm}

set_option linter.unusedSimpArgs false in
theorem ${base}_condition_evalU64 ${binders} :
    ${base}_condition.evalU64 ${region.parameters.scratchStart}
      (${stateName} ${stateArguments}) = ${conditionName} ${stateArguments} := by
  ${conditionProof.replaceAll("\n", "\n  ")}

set_option linter.unusedSimpArgs false in
theorem ${base}_body_evalU64 ${binders} :
    ${base}_body.evalU64 ${region.parameters.scratchStart}
      (${stateName} ${stateArguments}) = ${bodyName} ${stateArguments} := by
  ${bodyProof.replaceAll("\n", "\n  ")}

theorem ${base}_condition_eval ${binders} :
    ${base}_condition.eval ${region.parameters.scratchStart}
      (${stateName} ${stateArguments}).toState =
        (${conditionName} ${stateArguments}).map fun result =>
          (result.1, result.2.toState) := by
  rw [Project.ProofKit.ScalarTransition.Expr.eval_toState,
    ${base}_condition_evalU64]

theorem ${base}_body_eval ${binders} :
    ${base}_body.eval ${region.parameters.scratchStart}
      (${stateName} ${stateArguments}).toState =
        (${bodyName} ${stateArguments}).map
          Project.ProofKit.ScalarTransition.U64State.toState := by
  rw [Project.ProofKit.ScalarTransition.Stmt.eval_toState,
    ${base}_body_evalU64]`,
  };
}

function scalarStatementTransitionDeclarations(function_, region, suffix, statement) {
  const count = function_.parameters + function_.locals;
  const variables = Array.from({ length: count }, (_, index) => `v${index}`);
  const base = region.id.replace(/[^A-Za-z0-9_]/g, "_");
  const stateName = `${base}_state`;
  const statementName = `${base}_${suffix}`;
  const transitionName = `${statementName}Transition`;
  const transition = scalarStatementTransition(
    statement, region.parameters.scratchStart, [...variables]);
  const stateTerm = (state) => scalarStateTerm(stateName, state);
  const transitionTerm = scalarTransitionTerm(
    transition, (state) => `some (${stateTerm(state)})`);
  const binders = `(${variables.join(" ")} : UInt64)`;
  const stateArguments = variables.join(" ");
  const simpDeclarations = scalarTransitionSimpDeclarations(
    base, transitionName, statement, true);
  simpDeclarations[0] = statementName;
  const proof = scalarTransitionProof(transition, simpDeclarations);
  return {
    theorem: `${statementName}_eval`,
    source: `def ${transitionName} ${binders} :
    Option Project.ProofKit.ScalarTransition.U64State :=
  ${transitionTerm}

set_option linter.unusedSimpArgs false in
theorem ${statementName}_evalU64 ${binders} :
    ${statementName}.evalU64 ${region.parameters.scratchStart}
      (${stateName} ${stateArguments}) = ${transitionName} ${stateArguments} := by
  ${proof.replaceAll("\n", "\n  ")}

theorem ${statementName}_eval ${binders} :
    ${statementName}.eval ${region.parameters.scratchStart}
      (${stateName} ${stateArguments}).toState =
        (${transitionName} ${stateArguments}).map
          Project.ProofKit.ScalarTransition.U64State.toState := by
  rw [Project.ProofKit.ScalarTransition.Stmt.eval_toState,
    ${statementName}_evalU64]`,
  };
}

function arrayFoldTraversalDeclarations(function_, region, match) {
  const count = function_.parameters + function_.locals;
  const variables = Array.from({ length: count }, (_, index) => `v${index}`);
  const binders = `(${variables.join(" ")} : UInt64)`;
  const stateArguments = variables.join(" ");
  const base = region.id.replace(/[^A-Za-z0-9_]/g, "_");
  const stateName = `${base}_state`;
  const frameName = `${base}_continuing_frame`;
  const itemValidName = `${base}_continuing_item_valid`;
  const loadedFrameName = `${base}_continuing_loaded_frame_eq`;
  const theoremName = `${base}_continuing_spec`;
  const arrayLocal = region.parameters.arrayLocal;
  const indexLocal = region.parameters.indexLocal;
  const stopLocal = region.parameters.effectiveStopLocal;
  const itemLocal = region.parameters.itemLocals[0];
  const loadedArguments = variables.map((variable, index) =>
    index === itemLocal ? "value" : variable).join(" ");
  const parameterValues = variables.slice(0, function_.parameters)
    .map((variable) => `.i64 ${variable}`).join(", ");
  const stateDeclaration = match.guardedBackEdgeEligible ? "" :
    `def ${stateName} ${binders} :
    Project.ProofKit.ScalarTransition.U64State :=
  { params := [${variables.slice(0, function_.parameters).join(", ")}],
    locals := [${variables.slice(function_.parameters).join(", ")}] }

`;
  const frameAccessors = [
    `@[simp] theorem ${frameName}_params ${binders} :\n` +
      `    (${frameName} ${stateArguments}).params = [${parameterValues}] := by\n` +
      `  rfl`,
    `@[simp] theorem ${frameName}_locals_length ${binders} :\n` +
      `    (${frameName} ${stateArguments}).locals.length = ${function_.locals} := by\n` +
      `  rfl`,
    `@[simp] theorem ${frameName}_values ${binders} :\n` +
      `    (${frameName} ${stateArguments}).values = [] := by\n` +
      `  rfl`,
    ...variables.map((variable, index) =>
      `@[simp] theorem ${frameName}_get_${index} ${binders} :\n` +
      `    (${frameName} ${stateArguments}).get ${index} = ` +
      `some (.i64 ${variable}) := by\n` +
      `  rfl`),
  ].join("\n\n");
  const setupValues = new Map([
    [region.parameters.arrayLocal, variables[0]],
    [region.parameters.lengthLocal, "(UInt64.ofNat inputSize)"],
    [region.parameters.indexLocal, "0"],
    [region.parameters.doneLocal, variables[0]],
    [region.parameters.stopLocal, "(UInt64.ofNat inputSize)"],
    [region.parameters.accumulatorLocals[0], `${match.setupInitialValue}`],
    [region.parameters.releaseReadyLocal, "0"],
    [region.parameters.effectiveStopLocal, "(UInt64.ofNat inputSize)"],
  ]);
  const setupArguments = variables.map(
    (variable, index) => setupValues.get(index) ?? variable).join(" ");
  const setupFrameEquality = match.forwardSetupEligible ? `

theorem ${base}_setup_frame_eq ${binders} (inputSize : Nat) :
    Project.ProofKit.FixedArrayFold.forwardSetupFrame
      (${frameName} ${stateArguments}) ${variables[0]} inputSize
      ${region.parameters.arrayLocal} ${region.parameters.lengthLocal}
      ${region.parameters.indexLocal} ${region.parameters.doneLocal}
      ${region.parameters.stopLocal} ${region.parameters.accumulatorLocals[0]}
      ${region.parameters.releaseReadyLocal} ${region.parameters.effectiveStopLocal}
      ${match.setupInitialValue} =
        ${frameName} ${setupArguments} := by
  simp [Project.ProofKit.FixedArrayFold.forwardSetupFrame,
    ${frameName}, ${stateName},
    Project.ProofKit.ScalarTransition.U64State.toState]` : "";
  return {
    theorem: theoremName,
    source: `${stateDeclaration}def ${frameName} ${binders} : Wasm.Locals :=
  (${stateName} ${stateArguments}).toState.toLocals []

${frameAccessors}
${setupFrameEquality}

theorem ${itemValidName} ${binders} :
    (${frameName} ${stateArguments}).validIndex ${itemLocal} := by
  norm_num [Wasm.Locals.validIndex, ${frameName}, ${stateName},
    Project.ProofKit.ScalarTransition.U64State.toState]

theorem ${loadedFrameName} ${binders} (value : UInt64) :
    Project.ProofKit.FixedArrayTraversalInput.dynamicResultFrame
      (${frameName} ${stateArguments}) ${itemLocal} value
      (${itemValidName} ${stateArguments}) =
        ${frameName} ${loadedArguments} := by
  simp [Project.ProofKit.FixedArrayTraversalInput.dynamicResultFrame,
    ${frameName}, ${stateName},
    Project.ProofKit.ScalarTransition.U64State.toState, Wasm.Locals.set]

theorem ${theoremName} ${binders}
    (module_ : Wasm.Module) (env : Wasm.HostEnv Unit) (st : Wasm.Store Unit)
    (input : Array UInt64) (index : Nat)
    (hIndexValue : v${indexLocal} = UInt64.ofNat index)
    (hContinue : v${indexLocal} < v${stopLocal})
    (hInput : Project.ProofKit.UInt64Array.At st v${arrayLocal} input)
    (hIndex : index < input.size)
    (Q : Wasm.Assertion Unit) (rest : Wasm.Program)
    (hNext : Wasm.wp module_ rest Q st
      (Project.ProofKit.FixedArrayTraversalInput.dynamicResultFrame
        (${frameName} ${stateArguments}) ${itemLocal} input[index]
        (${itemValidName} ${stateArguments})) env) :
    Wasm.wp module_ (${base}_continuing_program ++ rest) Q st
      (${frameName} ${stateArguments}) env := by
  apply Project.ProofKit.FixedArrayTraversalInput.continuingProgram_spec
    (inputPtr := v${arrayLocal}) (indexValue := v${indexLocal})
    (stopValue := v${stopLocal}) (input := input) (index := index)
    (hValues := rfl) (hArrayLocal := rfl) (hIndexLocal := rfl)
    (hStopLocal := rfl) (hIndexValue := hIndexValue)
    (hContinue := hContinue) (hItem := ${itemValidName} ${stateArguments})
    (hInput := hInput) (hIndex := hIndex)
  exact hNext`,
  };
}

function arrayFoldSingletonResultDeclarations(function_, region, match) {
  if (!match.singletonResultEligible || !match.guardedBackEdgeEligible) {
    return null;
  }
  const count = function_.parameters + function_.locals;
  const variables = Array.from({ length: count }, (_, index) => `v${index}`);
  const binders = `(${variables.join(" ")} : UInt64)`;
  const stateArguments = variables.join(" ");
  const base = region.id.replace(/[^A-Za-z0-9_]/g, "_");
  const frameName = `${base}_continuing_frame`;
  const theoremName = `${base}_singleton_result_spec`;
  const accumulatorLocal = match.resultAccumulatorLocal;
  const resultLocal = match.resultLocal;
  const rootLocal = match.singletonResultRootLocal;
  const destinationLocal = match.singletonResultDestinationLocal;
  const returnLocal = match.singletonResultReturnLocal;
  const value = variables[accumulatorLocal];
  const root = variables[rootLocal];
  return {
    theorem: theoremName,
    source: `theorem ${theoremName} ${binders}
    (module_ : Wasm.Module) (env : Wasm.HostEnv Unit) (st : Wasm.Store Unit)
    (hPayloadBound :
      (Project.ProofKit.FixedArrayResult.payloadAddress ${root} 0).toUInt32.toNat + 8 ≤
        st.mem.pages * 65536)
    (Q : Wasm.Assertion Unit)
    (hNext : Q (.Fallthrough
      (Project.ProofKit.FixedArrayResult.writePayload st ${root} 0 ${value})
      (Project.ProofKit.FixedArrayResult.finishFrame
        (Project.ProofKit.FixedArrayFold.resultFrame
          (${frameName} ${stateArguments}) ${resultLocal} ${value})
        ${destinationLocal} ${returnLocal} ${root}))) :
    Wasm.wp module_ ${base}_singleton_result_program Q st
      (${frameName} ${stateArguments}) env := by
  change Wasm.wp module_
    (Project.ProofKit.FixedArrayFold.singletonResultProgram
      ${accumulatorLocal} ${resultLocal} ${rootLocal} ${destinationLocal}
      ${returnLocal}) Q st (${frameName} ${stateArguments}) env
  apply Project.ProofKit.FixedArrayFold.singletonResultProgram_spec_to
    (root := ${root}) (value := ${value})
  · exact ${frameName}_values ${stateArguments}
  · exact ${frameName}_get_${accumulatorLocal} ${stateArguments}
  · simp only [${frameName}_params]
    norm_num
  · simp [Wasm.Locals.validIndex, ${frameName}_params,
      ${frameName}_locals_length]
  · apply Project.ProofKit.FixedArrayFold.resultFrame_get_of_ne
    · simp only [${frameName}_params]
      norm_num
    · simp only [${frameName}_params]
      norm_num
    · simp [Wasm.Locals.validIndex, ${frameName}_params,
        ${frameName}_locals_length]
    · norm_num
    · exact ${frameName}_get_${rootLocal} ${stateArguments}
  · apply Project.ProofKit.FixedArrayFold.resultFrame_get_result
    · simp only [${frameName}_params]
      norm_num
    · simp [Wasm.Locals.validIndex, ${frameName}_params,
        ${frameName}_locals_length]
  · exact hPayloadBound
  · simp only [Project.ProofKit.FixedArrayFold.resultFrame_params,
      ${frameName}_params]
    norm_num
  · simp [Wasm.Locals.validIndex,
      Project.ProofKit.FixedArrayFold.resultFrame_params,
      Project.ProofKit.FixedArrayFold.resultFrame_locals_length,
      ${frameName}_params, ${frameName}_locals_length]
  · simp only [Project.ProofKit.FixedArrayFold.resultFrame_params,
      ${frameName}_params]
    norm_num
  · simp [Wasm.Locals.validIndex,
      Project.ProofKit.FixedArrayFold.resultFrame_params,
      Project.ProofKit.FixedArrayFold.resultFrame_locals_length,
      ${frameName}_params, ${frameName}_locals_length]
  · exact hNext`,
  };
}

function programFunctionDefinition(program, functionIndex) {
  const marker = `def func${functionIndex}Def : Wasm.Function :=\n`;
  const start = program.indexOf(marker);
  if (start < 0) return null;
  const bodyStart = start + marker.length;
  const end = program.indexOf("\n\ndef ", bodyStart);
  return program.slice(bodyStart, end < 0 ? program.length : end);
}

function functionI64Types(program, function_) {
  const definition = programFunctionDefinition(program, function_.wasmIndex);
  if (definition === null) return false;
  const types = (field) => {
    const match = definition.match(new RegExp(`${field} := \\[([^\\]]*)\\]`));
    if (match === null) return null;
    const contents = match[1].trim();
    return contents === "" ? [] : contents.split(",").map((type) => type.trim());
  };
  const parameters = types("params");
  const locals = types("locals");
  return parameters !== null && locals !== null &&
    parameters.length === function_.parameters && locals.length === function_.locals &&
    [...parameters, ...locals].every((type) => type === ".i64");
}

function scalarEntryState(function_, region, program) {
  if (region.location.listPath.length !== 0 || !functionI64Types(program, function_)) {
    return null;
  }
  const instructions = normalizeInstructions(resolveInstructionList(
    programFunctionBody(program, function_.wasmIndex), []));
  const prefix = instructions.slice(0, region.location.startIndex);
  if (prefix.length !== region.location.startIndex) return null;
  const state = Array.from(
    { length: function_.parameters + function_.locals },
    (_, index) => index < function_.parameters ? `v${index}` : "(0 : UInt64)");
  const stack = [];
  for (const instruction of prefix) {
    let match = instruction.match(/^\.constI64 \(([0-9]+) : UInt64\)$/);
    if (match !== null) {
      stack.unshift(`(${match[1]} : UInt64)`);
      continue;
    }
    match = instruction.match(/^\.constI64 ([0-9]+)$/);
    if (match !== null) {
      stack.unshift(`(${match[1]} : UInt64)`);
      continue;
    }
    match = instruction.match(/^\.localGet ([0-9]+)$/);
    if (match !== null && Number(match[1]) < state.length) {
      stack.unshift(state[Number(match[1])]);
      continue;
    }
    match = instruction.match(/^\.localSet ([0-9]+)$/);
    if (match !== null && Number(match[1]) < state.length && stack.length > 0) {
      state[Number(match[1])] = stack.shift();
      continue;
    }
    return null;
  }
  return stack.length === 0 ? state : null;
}

function scalarTransitionUnder(tree, condition, result) {
  if (tree.kind === "leaf") return tree.value;
  if (tree.condition !== condition) return null;
  return scalarTransitionUnder(result ? tree.thenTree : tree.elseTree, condition, result);
}

function scalarKnownU64(expression, state) {
  if (expression.kind === "const") return BigInt(expression.value);
  if (expression.kind !== "get") return null;
  const match = /^\(([0-9]+) : UInt64\)$/.exec(state[expression.index] ?? "");
  return match === null ? null : BigInt(match[1]);
}

function scalarKnownCondition(condition, state) {
  if (condition.kind === "true") return true;
  if (condition.kind === "false") return false;
  if (["eq", "ne", "lt-u", "le-u"].includes(condition.kind)) {
    const left = scalarKnownU64(condition.left, state);
    const right = scalarKnownU64(condition.right, state);
    if (left === null || right === null) return null;
    if (condition.kind === "eq") return left === right;
    if (condition.kind === "ne") return left !== right;
    if (condition.kind === "lt-u") return left < right;
    return left <= right;
  }
  if (condition.kind === "not") {
    const result = scalarKnownCondition(condition.condition, state);
    return result === null ? null : !result;
  }
  const left = scalarKnownCondition(condition.left, state);
  if (left === null) return null;
  if (condition.kind === "and") {
    return left ? scalarKnownCondition(condition.right, state) : false;
  }
  return left ? true : scalarKnownCondition(condition.right, state);
}

function scalarCounterTransferSummary(function_, region, program) {
  if (program === null || region.kind !== "leanexe.loop.scalar-post-test.v1" ||
      function_.parameters !== 1 || function_.results !== 1 ||
      region.parameters.resultWidth < 2 ||
      region.parameters.accumulatorLocals.length !== region.parameters.resultWidth ||
      region.parameters.resultSlot < 0 ||
      region.parameters.resultSlot >= region.parameters.accumulatorLocals.length ||
      region.parameters.releaseOffsets.length !== 0 ||
      region.parameters.continuation !== "fallthrough") {
    return null;
  }
  const accumulatorLocals = region.parameters.accumulatorLocals;
  const resultIndex = accumulatorLocals[region.parameters.resultSlot];
  const count = function_.parameters + function_.locals;
  if (accumulatorLocals.some((index) => index >= count)) {
    return null;
  }
  const entryState = scalarEntryState(function_, region, program);
  if (entryState === null || entryState[0] !== "v0" ||
      entryState[resultIndex] !== "(0 : UInt64)") {
    return null;
  }
  const instructions = normalizeInstructions(resolveInstructionList(
    programFunctionBody(program, function_.wasmIndex), []));
  const expectedSuffix = [
    `.localGet ${resultIndex}`,
    `.localSet ${region.parameters.destination}`,
    `.localGet ${region.parameters.destination}`,
  ];
  if (JSON.stringify(instructions.slice(region.location.endIndex)) !==
      JSON.stringify(expectedSuffix)) {
    return null;
  }
  const summaries = accumulatorLocals
    .filter((index) => index !== resultIndex && entryState[index] === "v0")
    .map((remainingIndex) => {
      const variables = Array.from({ length: count }, (_, index) => `v${index}`);
      variables[0] = "input";
      variables[remainingIndex] = "remaining";
      variables[resultIndex] = "result";
      const body = scalarStatementTransition(
        region.parameters.descriptor.body, region.parameters.scratchStart, variables);
      const zeroTest = "((remaining) == ((0 : UInt64)))";
      const zero = scalarTransitionUnder(body, zeroTest, true);
      const next = scalarTransitionUnder(body, zeroTest, false);
      const nextRemaining = scalarOperationTerm(
        "sub", "remaining", "(1 : UInt64)");
      const nextResult = scalarOperationTerm("add", "result", "(1 : UInt64)");
      if (zero === null || next === null ||
          !Array.isArray(zero) || !Array.isArray(next) ||
          zero[0] !== "input" || next[0] !== "input" ||
          zero[remainingIndex] !== "remaining" || zero[resultIndex] !== "result" ||
          next[remainingIndex] !== nextRemaining || next[resultIndex] !== nextResult) {
        return null;
      }
      const zeroCondition = scalarExpressionTransition(
        region.parameters.descriptor.condition, region.parameters.scratchStart, zero);
      const nextCondition = scalarExpressionTransition(
        region.parameters.descriptor.condition, region.parameters.scratchStart, next);
      if (zeroCondition.kind !== "leaf" || nextCondition.kind !== "leaf" ||
          scalarKnownCondition(region.parameters.descriptor.condition, zero) !== true ||
          scalarKnownCondition(region.parameters.descriptor.condition, next) !== false ||
          JSON.stringify(zeroCondition.value.state) !== JSON.stringify(zero) ||
          JSON.stringify(nextCondition.value.state) !== JSON.stringify(next)) {
        return null;
      }
      return {
        remainingIndex,
        resultIndex,
        entryState: entryState.map((value) => value === "v0" ? "input" : value),
        variables,
        zeroState: zero,
        nextState: next,
        nextRemaining,
        nextResult,
      };
    })
    .filter((summary) => summary !== null);
  return summaries.length === 1 ? summaries[0] : null;
}

function scalarCounterTransferDeclaration(function_, region, job, program) {
  const summary = scalarCounterTransferSummary(function_, region, program);
  if (summary === null) return null;
  const base = region.id.replace(/[^A-Za-z0-9_]/g, "_");
  const stateName = `${base}_state`;
  const indices = Array.from(
    { length: function_.parameters + function_.locals }, (_, index) => index);
  const existentialIndices = indices.filter((index) =>
    ![0, summary.remainingIndex, summary.resultIndex].includes(index));
  if (existentialIndices.length === 0) return null;
  const existentialNames = existentialIndices.map((index) => `v${index}`);
  const state = (values) => scalarStateTerm(stateName, values);
  const replace = (term, substitutions) => Object.entries(substitutions)
    .reduce((result, [from, to]) => result.replaceAll(from, to), term);
  const replaceState = (values, substitutions) =>
    values.map((value) => replace(value, substitutions));
  const zeroState = replaceState(summary.zeroState, {
    remaining: "(0 : UInt64)",
    result: "input",
  });
  const nextState = replaceState(summary.nextState, {
    [summary.nextRemaining]: "remaining'",
    [summary.nextResult]: "result'",
  });
  const initialWitnesses = existentialIndices.map((index) => summary.entryState[index]);
  const nextWitnesses = existentialIndices.map((index) => nextState[index]);
  const localIndex = summary.remainingIndex - function_.parameters;
  const viewTerm = state(summary.variables);
  const zeroTerm = state(zeroState);
  const nextTerm = state(nextState);
  return {
    theorem: `${base}_terminates_with_counter_transfer_identity`,
    source: `theorem ${base}_terminates_with_counter_transfer_identity {α : Type}
    (env : Wasm.HostEnv α) (initial : Wasm.Store α) (input : UInt64) :
    Wasm.TerminatesWith env ${job.namespace}.«module» ${function_.wasmIndex}
      initial [.i64 input]
      (fun final results => final = initial ∧ results = [.i64 input]) := by
  apply ${base}_terminates_with_of_loop
  let View : Project.ProofKit.ScalarTransition.State → UInt64 → UInt64 → Prop :=
    fun current remaining result =>
      ∃ ${existentialNames.join(" ")} : UInt64,
        current = (${viewTerm}).toState
  let remainingOf : Project.ProofKit.ScalarTransition.State → UInt64 := fun current =>
    match current.locals[${localIndex}]? with
    | some (Wasm.Value.i64 remaining) => remaining
    | _ => 0
  unfold ${base}_program
  apply Project.ProofKit.ScalarTransition.CounterTransition.postTestProgram_spec
    (remainingOf := remainingOf) (View := View)
    (initialRemaining := input) (initialResult := 0) (expected := input)
  · intro current remaining result hView
    rcases hView with ⟨${existentialNames.join(", ")}, rfl⟩
    simp [remainingOf, ${stateName},
      Project.ProofKit.ScalarTransition.U64State.toState]
  · dsimp [View]
    exact ⟨${initialWitnesses.join(", ")}, rfl⟩
  · simp
  · intro current remaining result hView hZero hResult
    rcases hView with ⟨${existentialNames.join(", ")}, rfl⟩
    subst remaining
    subst result
    let after := (${zeroTerm}).toState
    refine ⟨after, after, ?_, ?_, ?_⟩
    · rw [${base}_body_eval]
      simp [${base}_bodyTransition,
        Project.ProofKit.ScalarTransition.U64Op.apply, after]
    · rw [${base}_condition_eval]
      simp [${base}_conditionTransition, after]
    · unfold ${job.namespace}.func${function_.wasmIndex}
      wp_run
      simp [after, ${stateName},
        Project.ProofKit.ScalarTransition.U64State.toState,
        Project.ProofKit.ScalarTransition.State.toLocals]
  · intro current remaining result hView hZero
    rcases hView with ⟨${existentialNames.join(", ")}, rfl⟩
    let remaining' := Project.ProofKit.ScalarTransition.U64Op.apply .sub remaining 1
    let result' := Project.ProofKit.ScalarTransition.U64Op.apply .add result 1
    let after := (${nextTerm}).toState
    refine ⟨after, after, ?_, ?_, ?_⟩
    · rw [${base}_body_eval]
      simp [${base}_bodyTransition,
        Project.ProofKit.ScalarTransition.U64Op.apply,
        hZero, remaining', result', after]
    · rw [${base}_condition_eval]
      simp [${base}_conditionTransition, after]
    · dsimp [View]
      exact ⟨${nextWitnesses.join(", ")}, rfl⟩`,
  };
}

function scalarEntryDeclaration(function_, region, job, program) {
  if (program === null) return null;
  const state = scalarEntryState(function_, region, program);
  if (state === null) return null;
  const base = region.id.replace(/[^A-Za-z0-9_]/g, "_");
  const variables = Array.from(
    { length: function_.parameters }, (_, index) => `v${index}`);
  const binders = variables.length === 0 ? "" : ` (${variables.join(" ")} : UInt64)`;
  const argumentValues = `[${variables.map((variable) => `.i64 ${variable}`).join(", ")}]`;
  const callArguments =
    `[${variables.slice().reverse().map((variable) => `.i64 ${variable}`).join(", ")}]`;
  const stateArguments = state.map((value) => `(${value})`).join(" ");
  return {
    theorem: `${base}_entry_to_loop`,
    source: `theorem ${base}_loop_tail_eq :
    ${job.namespace}.func${function_.wasmIndex}.drop ${region.location.startIndex} =
      ${base}_program ++
        ${job.namespace}.func${function_.wasmIndex}.drop ${region.location.endIndex} := by
  rfl

theorem ${base}_entry_to_loop {α : Type}
    (module : Wasm.Module) (Q : Wasm.Assertion α)
    (initial : Wasm.Store α) (env : Wasm.HostEnv α)${binders} :
    Wasm.wp module ${job.namespace}.func${function_.wasmIndex} Q initial
      (${job.namespace}.func${function_.wasmIndex}Def.toLocals ${argumentValues}) env ↔
    Wasm.wp module
      (${base}_program ++
        ${job.namespace}.func${function_.wasmIndex}.drop ${region.location.endIndex})
      Q initial
      ((${base}_state ${stateArguments}).toState.toLocals []) env := by
  rw [← ${base}_loop_tail_eq]
  unfold ${job.namespace}.func${function_.wasmIndex}Def
  unfold ${job.namespace}.func${function_.wasmIndex}
  unfold ${base}_state
  wp_run
  simp [Project.ProofKit.ScalarTransition.U64State.toState,
    Project.ProofKit.ScalarTransition.State.toLocals]

theorem ${base}_terminates_with_of_loop {α : Type}
    (env : Wasm.HostEnv α) (initial : Wasm.Store α)
    (P : Wasm.Store α → List Wasm.Value → Prop)${binders}
    (hLoop : Wasm.wp ${job.namespace}.«module»
      (${base}_program ++
        ${job.namespace}.func${function_.wasmIndex}.drop ${region.location.endIndex})
      (fun c => match c with
        | .Fallthrough st' s' => P st' (s'.values.take ${function_.results})
        | .Return st' vs => P st' (vs.take ${function_.results})
        | _ => False)
      initial
      ((${base}_state ${stateArguments}).toState.toLocals []) env) :
    Wasm.TerminatesWith env ${job.namespace}.«module» ${function_.wasmIndex}
      initial ${callArguments} P := by
  apply Wasm.TerminatesWith.of_wp_entry_for
    (f := ${job.namespace}.func${function_.wasmIndex}Def) rfl
  unfold ${job.namespace}.func${function_.wasmIndex}Def
  simp only [Wasm.Function.numParams, List.length, List.take, List.reverse_cons,
    List.reverse_nil, List.drop, Nat.zero_add, List.append_nil]
  change Wasm.wp ${job.namespace}.«module» ${job.namespace}.func${function_.wasmIndex}
    _ initial (${job.namespace}.func${function_.wasmIndex}Def.toLocals ${argumentValues}) env
  rw [${base}_entry_to_loop]
  exact hLoop`,
  };
}

function exactRecipeTailEqualitySource(function_, region, job) {
  const annotationNamespace = `${job.namespace}.AnnotationMatches`;
  const program = exactRecipeProgram({
    regionId: region.id,
    regionKind: region.kind,
    parameters: region.parameters,
  }, annotationNamespace);
  const name = region.id.replace(/[^A-Za-z0-9_]/g, "_");
  const resolved = `(Project.ProofKit.Annotation.resolve ` +
    `${job.namespace}.func${function_.wasmIndex} ` +
    `${leanAnnotationPath(region.location.listPath)}).getD []`;
  return `

theorem ${name}_tail_eq :
    (${resolved}).drop ${region.location.startIndex} =
      ${program} ++ (${resolved}).drop ${region.location.endIndex} := by
  rfl`;
}

function annotationMatchesSource(document, job, program = null) {
  const declarations = [];
  for (const function_ of document.functions) {
    for (const region of function_.regions) {
      if (region.kind === "leanexe.array.length-dispatch.v1") {
        const match = program === null
          ? null : matchFixedArrayLengthDispatchRegion(program, function_, region);
        const name = region.id.replace(/[^A-Za-z0-9_]/g, "_");
        if (match?.functionPrefixEligible) {
          for (const branch of match.branchPrograms) {
            declarations.push(`def ${name}_${branch.role}_branch_program : Wasm.Program :=
  ${leanProgramLiteral(branch.source)}`);
          }
          const constructor = match.parameters.encoding === "le-unsigned-v1"
            ? "leProgram" : match.parameters.encoding === "eq-normalized-v1"
              ? "eqProgram" : "program";
          const branchArguments = match.parameters.encoding === "le-unsigned-v1"
            ? `${name}_valid_branch_program ${name}_invalid_branch_program`
            : `${name}_invalid_branch_program ${name}_valid_branch_program`;
          declarations.push(`def ${name}_dispatch_program : Wasm.Program :=
  Project.ProofKit.FixedArrayLengthDispatch.${constructor}
    ${match.parameters.inputLocal} ${match.parameters.expectedSize}
    ${branchArguments}

def ${name}_suffix_program : Wasm.Program :=
  ${leanProgramLiteral(match.suffixSource)}

theorem ${name}_dispatch_eq :
    Project.ProofKit.Annotation.region ${job.namespace}.func${function_.wasmIndex}
      ${leanAnnotationPath(region.location.listPath)} ${region.location.startIndex}
      ${region.location.endIndex} = some ${name}_dispatch_program := by
  rfl

theorem ${name}_function_eq :
    ${job.namespace}.func${function_.wasmIndex} =
      ${name}_dispatch_program ++ ${name}_suffix_program := by
  rfl`);
        }
        for (const capacity of match?.capacityPrefixes ?? []) {
          const prefix = `${name}_${capacity.role}_capacity`;
          declarations.push(`def ${prefix}_program : Wasm.Program :=
  Project.ProofKit.FixedArrayCapacity.constantProgram
    ${capacity.length} ${capacity.stride} ${capacity.capacityLocal}

theorem ${prefix}_eq :
    Project.ProofKit.Annotation.region ${job.namespace}.func${function_.wasmIndex}
      ${leanAnnotationPath(capacity.listPath)} ${capacity.startIndex}
      ${capacity.endIndex} = some ${prefix}_program := by
  rfl`);
        }
        continue;
      }
      if (region.kind === "leanexe.array.find-idx-eq.v1") {
        const parameters = region.parameters;
        const name = region.id.replace(/[^A-Za-z0-9_]/g, "_");
        declarations.push(`def ${name}_program : Wasm.Program :=
  Project.ProofKit.FixedArrayFindIdxEq.program
    ${parameters.scratchStart} ${parameters.key}

theorem ${name}_eq :
    Project.ProofKit.Annotation.region ${job.namespace}.func${function_.wasmIndex}
      ${leanAnnotationPath(region.location.listPath)} ${region.location.startIndex}
      ${region.location.endIndex} = some ${name}_program := by
  rfl${exactRecipeTailEqualitySource(function_, region, job)}`);
        continue;
      }
      if (region.kind === "leanexe.option.encoded-index.v1") {
        const parameters = region.parameters;
        const name = region.id.replace(/[^A-Za-z0-9_]/g, "_");
        declarations.push(`def ${name}_program : Wasm.Program :=
  Project.ProofKit.EncodedIndexDecoder.program
    ${parameters.encodedLocal} ${parameters.scratchStart} ${parameters.decodedLocal}

theorem ${name}_eq :
    Project.ProofKit.Annotation.region ${job.namespace}.func${function_.wasmIndex}
      ${leanAnnotationPath(region.location.listPath)} ${region.location.startIndex}
      ${region.location.endIndex} = some ${name}_program := by
  rfl${exactRecipeTailEqualitySource(function_, region, job)}`);
        continue;
      }
      if (region.kind === "leanexe.array.erase-copy.v1") {
        const parameters = region.parameters;
        const name = region.id.replace(/[^A-Za-z0-9_]/g, "_");
        declarations.push(`def ${name}_prefix_program : Wasm.Program :=
  Project.ProofKit.FixedArrayCopy.prefixProgram
    ${parameters.sourceLocal} ${parameters.targetLocal}
    ${parameters.prefixCellsLocal} ${parameters.counterLocal}

def ${name}_suffix_program : Wasm.Program :=
  Project.ProofKit.FixedArrayCopy.suffixProgram
    ${parameters.sourceWidth} ${parameters.sourceLocal} ${parameters.targetLocal}
    ${parameters.prefixCellsLocal} ${parameters.suffixCellsLocal}
    ${parameters.counterLocal}

def ${name}_program : Wasm.Program :=
  Project.ProofKit.FixedArrayCopy.program
    ${parameters.sourceWidth} ${parameters.sourceLocal} ${parameters.targetLocal}
    ${parameters.prefixCellsLocal} ${parameters.suffixCellsLocal}
    ${parameters.counterLocal}

theorem ${name}_prefix_eq :
    Project.ProofKit.Annotation.region ${job.namespace}.func${function_.wasmIndex}
      ${leanAnnotationPath(region.location.listPath)} ${region.location.startIndex}
      ${region.location.startIndex + 3} = some ${name}_prefix_program := by
  rfl

theorem ${name}_suffix_eq :
    Project.ProofKit.Annotation.region ${job.namespace}.func${function_.wasmIndex}
      ${leanAnnotationPath(region.location.listPath)} ${region.location.startIndex + 3}
      ${region.location.endIndex} = some ${name}_suffix_program := by
  rfl

theorem ${name}_eq :
    Project.ProofKit.Annotation.region ${job.namespace}.func${function_.wasmIndex}
      ${leanAnnotationPath(region.location.listPath)} ${region.location.startIndex}
      ${region.location.endIndex} = some ${name}_program := by
  rfl${exactRecipeTailEqualitySource(function_, region, job)}`);
        continue;
      }
      if ([
        "leanexe.loop.while.v1", "leanexe.loop.scalar-post-test.v1",
      ].includes(region.kind) && region.parameters.descriptor !== null) {
        const descriptor = region.parameters.descriptor;
        const name = region.id.replace(/[^A-Za-z0-9_]/g, "_");
        const programConstructor = region.kind === "leanexe.loop.scalar-post-test.v1"
          ? "postTestProgram"
          : "whileProgram";
        declarations.push(`def ${name}_condition :
    Project.ProofKit.ScalarTransition.Expr .bool :=
  ${scalarCondLean(descriptor.condition)}

def ${name}_body : Project.ProofKit.ScalarTransition.Stmt :=
  ${scalarStmtLean(descriptor.body)}

def ${name}_program : Wasm.Program :=
  Project.ProofKit.ScalarTransition.${programConstructor}
    ${region.parameters.scratchStart} ${name}_condition ${name}_body

theorem ${name}_eq :
    Project.ProofKit.Annotation.region ${job.namespace}.func${function_.wasmIndex}
      ${leanAnnotationPath(region.location.listPath)} ${region.location.startIndex}
      ${region.location.endIndex} = some ${name}_program := by
  rfl${exactRecipeTailEqualitySource(function_, region, job)}`);
        const transitions = scalarTransitionDeclarations(function_, region);
        declarations.push(transitions.source);
        const entry = scalarEntryDeclaration(function_, region, job, program);
        if (entry !== null) declarations.push(entry.source);
        const counterTransfer = scalarCounterTransferDeclaration(
          function_, region, job, program);
        if (counterTransfer !== null) declarations.push(counterTransfer.source);
        continue;
      }
      if (region.kind === "leanexe.array.map-add.v1") {
        const parameters = region.parameters;
        declarations.push(`theorem ${region.id.replace(/[^A-Za-z0-9_]/g, "_")}_eq :
    Project.ProofKit.Annotation.region ${job.namespace}.func${function_.wasmIndex}
      ${leanAnnotationPath(region.location.listPath)} ${region.location.startIndex}
      ${region.location.endIndex} = some
        (Project.ProofKit.FixedArrayMapAdd.wrapperProgram
          ${parameters.maximumSize} ${parameters.addend}) := by
  rfl${exactRecipeTailEqualitySource(function_, region, job)}`);
        continue;
      }
      if (region.kind === "leanexe.array.filter-lt.v1") {
        const parameters = region.parameters;
        declarations.push(`theorem ${region.id.replace(/[^A-Za-z0-9_]/g, "_")}_eq :
    Project.ProofKit.Annotation.region ${job.namespace}.func${function_.wasmIndex}
      ${leanAnnotationPath(region.location.listPath)} ${region.location.startIndex}
      ${region.location.endIndex} = some
        (Project.ProofKit.FixedArrayFilterLt.wrapperProgram
          ${parameters.maximumSize} ${parameters.threshold}) := by
  rfl${exactRecipeTailEqualitySource(function_, region, job)}`);
        continue;
      }
      if (region.kind === "leanexe.array.fold.v1") {
        const name = region.id.replace(/[^A-Za-z0-9_]/g, "_");
        const selected = `Project.ProofKit.Annotation.region ` +
          `${job.namespace}.func${function_.wasmIndex} ` +
          `${leanAnnotationPath(region.location.listPath)} ` +
          `${region.location.startIndex} ${region.location.endIndex}`;
        const match = program === null
          ? null : matchArrayFoldRegion(program, function_, region);
        const continuing = match?.dynamicTraversalEligible ? `

def ${name}_continuing_program : Wasm.Program :=
  Project.ProofKit.FixedArrayTraversalInput.continuingProgram
    ${region.parameters.arrayLocal} ${region.parameters.indexLocal}
    ${region.parameters.effectiveStopLocal} ${region.parameters.itemLocals[0]}

theorem ${name}_continuing_eq :
    Project.ProofKit.Annotation.region ${job.namespace}.func${function_.wasmIndex}
      ${leanAnnotationPath(match.loopPath)} 0 ${match.continuingEndIndex} =
        some ${name}_continuing_program := by
  rfl` : "";
        const setup = match?.forwardSetupEligible ? `

def ${name}_setup_program : Wasm.Program :=
  Project.ProofKit.FixedArrayFold.forwardSetupProgram
    ${region.parameters.arrayLocal} ${region.parameters.lengthLocal}
    ${region.parameters.indexLocal} ${region.parameters.doneLocal}
    ${region.parameters.stopLocal} ${region.parameters.accumulatorLocals[0]}
    ${region.parameters.releaseReadyLocal} ${region.parameters.effectiveStopLocal}
    ${match.setupInitialValue}

theorem ${name}_setup_eq :
    Project.ProofKit.Annotation.region ${job.namespace}.func${function_.wasmIndex}
      ${leanAnnotationPath(region.location.listPath)} ${region.location.startIndex}
      ${match.setupEndIndex} = some ${name}_setup_program := by
  rfl` : "";
        const result = match?.resultPlacementEligible ? `

def ${name}_result_program : Wasm.Program :=
  Project.ProofKit.FixedArrayFold.resultProgram
    ${match.resultAccumulatorLocal} ${match.resultLocal}

theorem ${name}_result_eq :
    Project.ProofKit.Annotation.region ${job.namespace}.func${function_.wasmIndex}
      ${leanAnnotationPath(region.location.listPath)} ${match.resultStartIndex}
      ${match.resultEndIndex} = some ${name}_result_program := by
  rfl` : "";
        const singletonResult = match?.singletonResultEligible ? `

def ${name}_singleton_result_program : Wasm.Program :=
  Project.ProofKit.FixedArrayFold.singletonResultProgram
    ${match.resultAccumulatorLocal} ${match.resultLocal}
    ${match.singletonResultRootLocal} ${match.singletonResultDestinationLocal}
    ${match.singletonResultReturnLocal}

theorem ${name}_singleton_result_eq :
    Project.ProofKit.Annotation.region ${job.namespace}.func${function_.wasmIndex}
      ${leanAnnotationPath(region.location.listPath)} ${match.resultStartIndex}
      ${match.singletonResultEndIndex} = some
        ${name}_singleton_result_program := by
  rfl` : "";
        const continuingStatement = match?.guardedBackEdgeEligible ? {
          kind: "assign",
          index: region.parameters.indexLocal,
          value: {
            kind: "bin",
            operation: "add",
            left: { kind: "get", index: region.parameters.indexLocal },
            right: { kind: "const", value: "1" },
          },
        } : null;
        const guardedBackEdge = match?.guardedBackEdgeEligible ? `

def ${name}_condition : Project.ProofKit.ScalarTransition.Expr .bool :=
  ${scalarCondLean(region.parameters.descriptor.condition)}

def ${name}_body : Project.ProofKit.ScalarTransition.Stmt :=
  ${scalarStmtLean(region.parameters.descriptor.body)}

def ${name}_step_continuing : Project.ProofKit.ScalarTransition.Stmt :=
  ${scalarStmtLean(continuingStatement)}

def ${name}_step_program : Wasm.Program :=
  Project.ProofKit.ScalarTransition.guardedBackEdgeProgram
    ${region.parameters.scratchStart} ${name}_body ${name}_condition
    ${name}_step_continuing

theorem ${name}_step_eq :
    Project.ProofKit.Annotation.region ${job.namespace}.func${function_.wasmIndex}
      ${leanAnnotationPath(match.loopPath)} ${match.stepStartIndex}
      ${match.stepEndIndex} = some ${name}_step_program := by
  rfl` : "";
        const transitions = match?.guardedBackEdgeEligible
          ? scalarTransitionDeclarations(function_, region).source : "";
        const continuingTransition = match?.guardedBackEdgeEligible
          ? scalarStatementTransitionDeclarations(
            function_, region, "step_continuing", continuingStatement).source
          : "";
        const traversal = match?.dynamicTraversalEligible
          ? arrayFoldTraversalDeclarations(function_, region, match).source
          : "";
        const singletonResultSpec = match?.singletonResultEligible &&
            match?.guardedBackEdgeEligible
          ? arrayFoldSingletonResultDeclarations(function_, region, match).source
          : "";
        declarations.push(`def ${name}_program : Wasm.Program :=
  (${selected}).getD []

theorem ${name}_eq :
    ${selected} = some ${name}_program := by
  rfl${exactRecipeTailEqualitySource(function_, region, job)}${setup}${continuing}${guardedBackEdge}${result}${singletonResult}

${transitions}

${continuingTransition}

${traversal}

${singletonResultSpec}`);
        continue;
      }
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
  rfl${exactRecipeTailEqualitySource(function_, region, job)}`);
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
  const singletonCompositions = fixedArraySingletonWrapperCompositions(document, program);
  for (const composition of singletonCompositions) {
    declarations.push(`def ${composition.name} : Wasm.Program :=
  Project.ProofKit.FixedArraySingletonWrapper.wrapperProgram
    ${composition.calleeIndex}

theorem ${composition.name}_eq :
    ${job.namespace}.func${composition.functionIndex} = ${composition.name} := by
  rfl`);
  }
  const needsScalarTransition = document.functions.some((function_) =>
    function_.regions.some((region) => {
      if (["leanexe.loop.while.v1", "leanexe.loop.scalar-post-test.v1"].includes(
        region.kind) && region.parameters.descriptor !== null) return true;
      if (program === null || region.kind !== "leanexe.array.fold.v1") return false;
      const match = matchArrayFoldRegion(program, function_, region);
      return match.guardedBackEdgeEligible || match.dynamicTraversalEligible;
    }));
  return {
    module: `${job.namespace}.AnnotationMatches`,
    source: `import ${job.programModule}
import Project.ProofKit.Annotation
import Project.ProofKit.FixedArrayPairResult
${document.functions.some((function_) => function_.regions.some((region) =>
    region.kind === "leanexe.array.find-idx-eq.v1"))
    ? "import Project.ProofKit.FixedArrayFindIdxEq\n" : ""}
${document.functions.some((function_) => function_.regions.some((region) =>
    region.kind === "leanexe.option.encoded-index.v1"))
    ? "import Project.ProofKit.EncodedIndexDecoder\n" : ""}
${document.functions.some((function_) => function_.regions.some((region) =>
    region.kind === "leanexe.array.erase-copy.v1"))
    ? "import Project.ProofKit.FixedArrayCopy\n" : ""}
${needsScalarTransition ? "import Project.ProofKit.ScalarTransition\n" +
  "import Project.ProofKit.ScalarTransitionU64\n" : ""}
${program !== null && document.functions.some((function_) => function_.regions.some((region) =>
    region.kind === "leanexe.array.fold.v1" &&
      matchArrayFoldRegion(program, function_, region).guardedBackEdgeEligible))
    ? "import Project.ProofKit.GuardedBackEdge\n" : ""}
${document.functions.some((function_) => function_.regions.some((region) =>
    region.kind === "leanexe.array.map-add.v1"))
    ? "import Project.ProofKit.FixedArrayMapAdd\n" : ""}
${document.functions.some((function_) => function_.regions.some((region) =>
    region.kind === "leanexe.array.filter-lt.v1"))
    ? "import Project.ProofKit.FixedArrayFilterLt\n" : ""}
${program !== null && document.functions.some((function_) => function_.regions.some((region) =>
    region.kind === "leanexe.array.length-dispatch.v1" &&
      matchFixedArrayLengthDispatchRegion(program, function_, region).functionPrefixEligible))
    ? "import Project.ProofKit.FixedArrayLengthDispatch\n" : ""}
${program !== null && document.functions.some((function_) => function_.regions.some((region) =>
    region.kind === "leanexe.array.length-dispatch.v1" &&
      matchFixedArrayLengthDispatchRegion(program, function_, region)
        .capacityPrefixes.length > 0))
    ? "import Project.ProofKit.FixedArrayCapacity\n" : ""}
${program !== null && document.functions.some((function_) => function_.regions.some((region) =>
    region.kind === "leanexe.array.fold.v1" &&
      matchArrayFoldRegion(program, function_, region).dynamicTraversalEligible))
    ? "import Project.ProofKit.FixedArrayTraversalInput\n" : ""}
${program !== null && document.functions.some((function_) => function_.regions.some((region) => {
    if (region.kind !== "leanexe.array.fold.v1") return false;
    const match = matchArrayFoldRegion(program, function_, region);
    return match.forwardSetupEligible || match.resultPlacementEligible;
  })) ? "import Project.ProofKit.FixedArrayFold\n" : ""}
${chainCompositions.length > 0 ? "import Project.ProofKit.FixedArraySearchChain\n" : ""}
${treeCompositions.length > 0 ? "import Project.ProofKit.FixedArraySearchTree\n" : ""}
${singletonCompositions.length > 0
    ? "import Project.ProofKit.FixedArraySingletonWrapper\n" : ""}
set_option maxRecDepth 1048576
set_option maxHeartbeats 8000000

namespace ${job.namespace}.AnnotationMatches

${declarations.join("\n\n")}

end ${job.namespace}.AnnotationMatches
`,
  };
}

module.exports = {
  annotationMatchesSource,
  directCallRecipe,
  encodedIndexDecoderRecipe,
  fixedArrayEraseCopyRecipe,
  fixedArrayEqNodeRecipe,
  fixedArrayFindIdxEqRecipe,
  fixedArrayLengthDispatchRecipe,
  fixedArrayLtNodeRecipe,
  fixedArrayFilterLtRecipe,
  fixedArrayMapAddRecipe,
  fixedArrayPairResultRecipe,
  fixedArraySearchKeyRecipe,
  fixedArraySingletonWrapperCompositions,
  fixedArraySearchChainCompositions,
  fixedArraySearchTreeCompositions,
  loopRecipe,
  matchAnnotationDocument,
  matchArrayFoldRegion,
  matchDirectCallRegion,
  matchEncodedIndexDecoderRegion,
  matchFixedArrayEraseCopyRegion,
  matchFixedArrayEqNodeRegion,
  matchFixedArrayFindIdxEqRegion,
  matchFixedArrayLengthDispatchRegion,
  matchFixedArrayLtNodeRegion,
  matchFixedArrayFilterLtRegion,
  matchFixedArrayMapAddRegion,
  matchFixedArrayPairResultRegion,
  matchFixedArraySearchKeyRegion,
  matchLoopFoldRegion,
  matchScalarPostTestLoopRegion,
  matchWhileLoopRegion,
  proofRecipePlan,
  resolveInstructionList,
  validateAnnotationDocument,
  validateProofRecipePlan,
};
