import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';

const directory = process.argv[2];
const suite = process.argv[3] || 'all';
const groups = JSON.parse(readFileSync(new URL('./arithmetic-engine-groups.json', import.meta.url), 'utf8'));
if (!directory || process.argv.length > 4 || (!['all', 'range'].includes(suite) && !Object.hasOwn(groups, suite))) {
  throw new Error('usage: node test/arithmetic_engine.mjs <artifact-directory> [all|range|checked-group]');
}
const rangeEntries = JSON.parse(readFileSync(new URL('./arithmetic-range-cases.json', import.meta.url), 'utf8'));
const cases = readFileSync(resolve(directory, 'expected.jsonl'), 'utf8').trim().split('\n').map(JSON.parse);
const allEntries = ['constant', 'wrapping', 'quotient', 'remainder', 'shifts', 'nested', 'order',
  'bindings', 'shadowed', 'nestedBindings', 'unusedBinding', 'boundConstant',
  'compareEq', 'compareLt', 'compareLe', 'compareBEq', 'compareBNe',
  'nestedChoice', 'choiceBindings', 'choiceOperands',
  'doReturn', 'doBind', 'doUpdates', 'doEarly', 'doNested', 'doBranches', 'doConstant',
  'localFunction', 'capturedShadow', 'chainedFunctions', 'nestedFunctions',
  'unusedFunction', 'doJoined', 'doBranchUpdates',
  'compareNe', 'negatedEq', 'negatedLt', 'negatedLe', 'negatedGt', 'negatedGe', 'negatedBool', 'doubleNegation', 'negatedBindings', 'binaryOrder', 'binaryCapture', 'binaryChained', 'binaryUnused', 'binaryDo', 'binaryNested', 'binaryChoice', 'binaryArguments', 'binaryWrapped', 'boolNotEqual', 'boolNotUnequal', 'boolNotTwice', 'boolNotThrice', 'boolNotNested', 'boolNotFunction', 'boolNotDo', 'boolNotProposition', 'complementDirect', 'complementOperator', 'complementTwice', 'complementMixed', 'complementChoice', 'complementFunction', 'complementDo', 'complementOperand', 'compoundAnd', 'compoundOr', 'compoundNested', 'compoundNegatedLeaves', 'compoundZeroDivisor', 'compoundFunction', 'compoundDo', 'compoundOperand', 'compoundNotAnd', 'compoundNotOr', 'compoundNotTwice', 'compoundNotThrice', 'compoundNotNested', 'compoundNotFunction', 'compoundNotDo', 'compoundNotOperand', 'boolAndTruth', 'boolOrTruth', 'boolCompoundNot', 'boolCompoundTwice', 'boolCompoundNested', 'boolCompoundFunction', 'boolCompoundDo', 'boolCompoundOperand', 'mixedGuardAnd', 'mixedGuardOr', 'mixedGuardNot', 'mixedGuardNegations', 'mixedGuardNested', 'mixedGuardFunction', 'mixedGuardDo', 'mixedGuardOperand', 'minimumOrder', 'maximumOrder', 'extremaNested', 'extremaClamped', 'extremaFunction', 'extremaDo', 'extremaGuard', 'extremaWrapped', 'literalBoolTrue', 'literalBoolFalse', 'literalPropTrue', 'literalPropFalse', 'literalNegations', 'literalCompound', 'literalFunction', 'literalDo', 'punitExplicit', 'punitCapture', 'punitChain', 'punitUnused', 'punitDo', 'punitNested', 'idReturnedHelper', 'idPureNested', 'idRunNested', 'idBindInput', 'idBindOutput', 'idConditional', 'idFunctions', 'idUnused', 'manyOrder', 'manyFour', 'manySix', 'manyCapture', 'manyChained', 'manyDo', 'manyId', 'manyUnused', 'dependentCompare', 'dependentMixed', 'dependentLiteral', 'dependentNested', 'dependentCapture', 'dependentDo', 'dependentOperand', 'dependentMany', 'booleanLet', 'booleanAlias', 'booleanShadow', 'booleanCompound', 'booleanNestedOperand', 'booleanUnused', 'booleanMany', 'booleanDo', 'booleanDependentLet', 'booleanDependentAlias', 'booleanDependentShadow', 'booleanDependentCompound', 'booleanDependentNestedOperand', 'booleanDependentUnused', 'booleanDependentMany', 'booleanDependentDo', 'instanceDependentMany', 'instanceLet', 'instanceApplied', 'instanceNested', 'instanceShadow', 'instanceProof', 'instanceOverflow', 'instanceDo', 'naturalConverted', 'naturalConvertedOverflow', 'naturalExplicitLet', 'naturalExplicitApplied', 'naturalExplicitNested', 'naturalDependentMany', 'naturalDo', 'naturalOperand', 'boolBindLet', 'boolBindAlias', 'boolBindWrapped', 'boolBindShadow', 'boolBindCapture', 'boolBindDependent', 'boolBindDo', 'boolBindUnused', 'boolChoiceLet', 'boolChoiceNested', 'boolChoiceClosed', 'boolChoiceShadow', 'boolChoiceCapture', 'boolChoiceDependent', 'boolChoiceDo', 'boolChoiceUnused', 'propChoiceLet', 'propChoiceNested', 'propChoiceClosed', 'propChoiceShadow', 'propChoiceCapture', 'propChoiceDependent', 'propChoiceDo', 'propChoiceUnused', 'boolFnConditional', 'boolFnLocalGuard', 'boolFnNested', 'boolFnDirect', 'boolFnShadow', 'boolFnCapture', 'boolFnAnnotation', 'boolFnUnused', 'decideLet', 'decideImplicit', 'decideCompound', 'decideBoolean', 'decideChoices', 'decideCapture', 'decideDo', 'decideUnused', 'boolWordDirect', 'boolWordCaptured', 'boolWordAction', 'boolWordLiterals', 'boolWordChoice', 'boolWordNested', 'boolWordDependent', 'boolWordUnused', 'boolEqDirect', 'boolEqCalls', 'boolEqConditional', 'boolEqCapture', 'boolEqLiterals', 'boolEqChoices', 'boolEqNested', 'boolEqDo', 'boolPropEqual', 'boolPropUnequal', 'boolPropLiterals', 'boolPropDependent', 'boolPropTruth', 'boolPropChoices', 'boolPropDo', 'boolPropEarly', ...rangeEntries];
const entries = suite === 'all' ? allEntries : suite === 'range' ? rangeEntries : groups[suite];
if (!Array.isArray(entries) || entries.length === 0 || new Set(entries).size !== entries.length ||
    entries.some(name => !allEntries.includes(name))) {
  throw new Error(`invalid checked execution group: ${suite}`);
}
const constants = new Set(['constant', 'boundConstant', 'doConstant', 'rangeConstant']);
const ranges = new Set(rangeEntries);
const counts = new Map(entries.map(name => [name, new Set()]));
const uint64 = value => typeof value === 'string' && /^(0|[1-9][0-9]*)$/.test(value) &&
  BigInt(value) < (1n << 64n);
for (const row of cases) {
  if (!counts.has(row.name) || !Array.isArray(row.args) ||
      row.args.length !== (constants.has(row.name) ? 0 : 2) ||
      !row.args.every(uint64) || !uint64(row.expected)) {
    throw new Error(`invalid native result: ${JSON.stringify(row)}`);
  }
  const key = row.args.join(',');
  if (counts.get(row.name).has(key)) throw new Error(`duplicate input for ${row.name}: ${key}`);
  counts.get(row.name).add(key);
}
for (const [name, inputs] of counts) {
  if (inputs.size !== (constants.has(name) ? 1 : ranges.has(name) ? 24 : 14)) {
    throw new Error(`incomplete native results for ${name}: ${inputs.size} inputs`);
  }
}
const modules = new Map();
for (const row of cases) {
  if (!modules.has(row.name)) {
    const bytes = readFileSync(resolve(directory, `${row.name}.wasm`));
    if (!WebAssembly.validate(bytes)) throw new Error(`invalid module: ${row.name}`);
    modules.set(row.name, new WebAssembly.Instance(new WebAssembly.Module(bytes)).exports);
  }
  const invoke = modules.get(row.name)[row.name];
  if (typeof invoke !== 'function') throw new Error(`missing export: ${row.name}`);
  const actual = BigInt.asUintN(64, invoke(...row.args.map(BigInt))).toString();
  if (actual !== row.expected) {
    throw new Error(`${row.name}(${row.args.join(', ')}): expected ${row.expected}, received ${actual}`);
  }
}
console.log(`Passed ${cases.length} native Lean / independent Wasm engine comparisons across ${modules.size} declarations.`);
