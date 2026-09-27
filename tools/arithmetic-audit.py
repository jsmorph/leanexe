#!/usr/bin/env python3
"""Check every public arithmetic compiler theorem's printed dependencies."""
import re
import sys
from pathlib import Path

ADMISSION = 'LeanExe.Extract.Arithmetic.'
MODULE = 'Project.Compiler.ArithmeticModule.'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
AUDITS = {
    'LeanExe.Extract.Core.booleanSequencePrefix_accepts': STANDARD,
    'LeanExe.Extract.Core.booleanSequencePrefix_sound': STANDARD,
    'LeanExe.Extract.Core.booleanSequencePrefix_body_size': STANDARD,
    'LeanExe.Extract.Core.SequenceBindingsMatch.booleanResult': STANDARD,

    'LeanExe.Source.Scalar.BooleanSequence.Supported.evaluates': STANDARD,
    'LeanExe.Extract.Core.extractScalarBooleanSequenceWith_accepts': STANDARD,
    'LeanExe.Extract.Core.extractScalarBooleanSequenceWith_correct': STANDARD,
    'LeanExe.Extract.Core.extractScalarBooleanSequenceWith_admitted': STANDARD,

    'LeanExe.IR.Stmt.ScalarEval.append': STANDARD,
    'LeanExe.Extract.Core.extractScalarSequenceWith_accepts': STANDARD,
    'LeanExe.Extract.Core.extractScalarSequenceWith_correct': STANDARD,
    'Project.ProofKit.ScalarTransition.WhileTrace.program_spec': STANDARD,
    'Project.Compiler.ScalarLowering.program_eval': STANDARD,
    'Project.Compiler.ScalarLowering.sequence_function_execution': STANDARD,
    'Project.Compiler.ArithmeticValidation.loop_sequence_function_sequence': STANDARD,
    'Project.Compiler.ArithmeticEncoding.sequence_function_body_bytes': STANDARD,

    'LeanExe.Source.Scalar.BooleanStep.UnitBooleanFunction.apply': set(),
    'LeanExe.Extract.Core.booleanStepUnitTypes_sound': STANDARD,
    'LeanExe.Extract.Core.booleanStepUnitTypes_accepts': STANDARD,
    'LeanExe.Extract.Core.booleanStepUnitValue_sound': STANDARD,
    'LeanExe.Extract.Core.booleanStepUnitValue_accepts': STANDARD,
    'LeanExe.Extract.Core.booleanUnitStepFunction_sound': STANDARD,
    'LeanExe.Extract.Core.booleanUnitStepFunction_accepts': STANDARD,
    'LeanExe.Source.Scalar.BooleanBinaryFunctionBinding.apply': set(),
    'LeanExe.Extract.Core.booleanBinaryHelper_sound': STANDARD,
    'LeanExe.Extract.Core.booleanBinaryHelper_accepts': STANDARD,
    'LeanExe.Extract.Core.booleanBinaryCall_sound': STANDARD,
    'LeanExe.Extract.Core.booleanBinaryCall_accepts': STANDARD,
    'LeanExe.Source.Scalar.BooleanScopeBindingForm.application_apply': set(),
    'LeanExe.Source.Scalar.BooleanScopeBindingForm.monadic_apply': set(),
    'LeanExe.Extract.Core.booleanScopeBinding_sound': STANDARD,
    'LeanExe.Extract.Core.booleanScopeBinding_accepts': STANDARD,
    'LeanExe.Source.Scalar.StepMatcher.denote_cases': set(),
    'LeanExe.Extract.Core.findStepMatcher_sound': STANDARD,
    'LeanExe.Extract.Core.findStepMatcher_accepts': STANDARD,
    'LeanExe.Extract.Core.expandStepMatchers_normalizes': STANDARD,
    'LeanExe.Extract.Core.expandStepMatchers_accepts': STANDARD,
    'LeanExe.Extract.Core.extractScalarEnvironmentFunc_accepts': STANDARD,
    'LeanExe.Extract.Core.extractScalarEnvironmentFunc_correct': STANDARD,
    'LeanExe.Extract.Arithmetic.compileEnvironment_environment_accepts': STANDARD,
    'Project.Compiler.ArithmeticModule.environment_extracted_correct': STANDARD,
    'Project.Compiler.ArithmeticModule.compileEnvironment_environment_correct': STANDARD,

    'LeanExe.Extract.Core.extractScalarFunc_boolean_correct': STANDARD,
    'LeanExe.Extract.Core.predicateInputTypes_sound': STANDARD,
    'LeanExe.Extract.Core.predicateInputTypes_accepts': STANDARD,
    'LeanExe.Extract.Core.booleanFunctionApplication_sound': STANDARD,
    'LeanExe.Extract.Core.booleanFunctionApplication_accepts': STANDARD,
    'LeanExe.Extract.Core.guardDecision_sound': STANDARD,
    'LeanExe.Extract.Core.guardDecision_accepts': STANDARD,
    'LeanExe.Source.Scalar.Reannotates.eval_iff': STANDARD,
    'LeanExe.Extract.Core.reannotation_sound': STANDARD,
    'LeanExe.Extract.Core.reannotation_accepts': STANDARD,
    ADMISSION + 'compileEnvironment_accepts': STANDARD,
    ADMISSION + 'compileEnvironment_success': STANDARD,
    **{MODULE + name: {'propext'} for name in
       ('retain_valid', 'alloc_valid', 'release_valid')},
    **{MODULE + name: STANDARD for name in
       ('extracted_module_valid', 'extracted_correct',
        'compileEnvironment_correct', 'compileEnvironment_sound')},
}


def audit(output):
    found = {}
    pattern = r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
    for match in re.finditer(pattern, output):
        name, body = match.groups()
        if name not in AUDITS:
            continue
        axioms = {x.strip() for x in (body or '').split(',') if x.strip()}
        unexpected = axioms - AUDITS[name]
        if unexpected:
            raise ValueError(f'{name}: unapproved axioms {sorted(unexpected)}')
        if name in found and found[name] != sorted(axioms):
            raise ValueError(f'inconsistent repeated axiom audit: {name}')
        found[name] = sorted(axioms)
    missing = AUDITS.keys() - found.keys()
    if missing:
        raise ValueError(f'missing axiom audits: {sorted(missing)}')
    for name, axioms in found.items():
        print(f'{name}: {", ".join(axioms) or "none"}')
    print(f'Passed all {len(found)} arithmetic axiom audits.')
    return found


if __name__ == '__main__':
    try:
        if len(sys.argv) != 2:
            raise ValueError('usage: tools/arithmetic-audit.py <proof-log>')
        audit(Path(sys.argv[1]).read_text())
    except (OSError, ValueError) as error:
        sys.exit(str(error))
