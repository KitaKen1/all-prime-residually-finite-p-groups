"""Validate the exact declarations requested by a Lean axiom audit."""
from collections import Counter
import re

ALLOWED_AXIOMS = frozenset({'propext', 'Classical.choice', 'Quot.sound'})
MAIN_THEOREM = 'AllPrimeGroups.all_prime_groups'


def audit_axioms(source, output, required=()):
    expected = re.findall(r'^#print axioms (\S+)\s*$', source, re.M)
    if not expected or len(expected) != len(set(expected)):
        raise ValueError('The audit must request distinct declarations.')
    entries = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", output)
    entries += [(name, '') for name in re.findall(
        r"'([^']+)' does not depend on any axioms", output)]
    if Counter(name for name, _ in entries) != Counter(expected):
        raise ValueError('The axiom report does not match the requested declarations.')
    if not set(required) <= set(expected):
        raise ValueError(f'Required declarations are missing: {set(required) - set(expected)}')
    result = {}
    for name, axioms in entries:
        dependencies = {item.strip() for item in axioms.split(',') if item.strip()}
        if not dependencies <= ALLOWED_AXIOMS:
            raise ValueError(f'Unexpected axiom dependency: {name}: '
                             f'{dependencies - ALLOWED_AXIOMS}')
        result[name] = sorted(dependencies)
    return result
