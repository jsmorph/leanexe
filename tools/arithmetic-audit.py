#!/usr/bin/env python3
"""Check every public arithmetic compiler theorem's printed dependencies."""
import re
import sys
from pathlib import Path

ADMISSION = 'LeanExe.Extract.Arithmetic.'
MODULE = 'Project.Compiler.ArithmeticModule.'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
AUDITS = {
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
