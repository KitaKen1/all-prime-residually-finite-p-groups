"""Read the controlled FC proposal format without importing Lean or the proof project."""
import re

PROOF_URL = ('https://github.com/KitaKen1/all-prime-residually-finite-p-groups/'
             'blob/main/lean/FCSolution.lean')
REFERENCE_NAMES = {
    'finitely_presented_burnside_problem': 'MainStatement',
    'variants.finitely_presented_burnside_problem_residually_finite': 'ResiduallyFinitePeriodicStatement',
    'variants.finitely_presented_burnside_problem_all_primes': 'Statement',
}


def without_comments(source):
    return re.sub(r'/-.*?-/', '', source, flags=re.S)


def proposal_statements(source):
    text = without_comments(source)
    declarations = re.findall(r'^\s*(theorem|lemma|def|abbrev|axiom)\s+(\w+)', text, re.M)
    if declarations != [('theorem', name.rsplit('.', 1)[-1]) for name in REFERENCE_NAMES]:
        raise ValueError('The FC proposal must contain the named Burnside problem and its two variants.')
    attributes = (r'@\[\s*category research solved,\s*AMS 20,\s*'
                  r'formal_proof using lean4 at "' + re.escape(PROOF_URL) + r'"\s*\]')
    def theorem(name, index):
        return (attributes + r'\s*theorem ' + re.escape(name.rsplit('.', 1)[-1]) +
                r'\s*:\s*(?P<statement_' + str(index) + r'>.*?)\s*:=\s*by\s+sorry\s*')
    names = list(REFERENCE_NAMES)
    match = re.fullmatch(
        r'\s*module\s+public import FormalConjecturesUtil\s+'
        r'@\[expose\] public section\s+namespace AllPrimeGroupsFC\s*' +
        theorem(names[0], 0) + r'namespace variants\s*' +
        ''.join(theorem(name, index) for index, name in enumerate(names[1:], 1)) +
        r'end variants\s*' +
        r'end AllPrimeGroupsFC\s*', text, re.S)
    if not match:
        raise ValueError('The FC proposal metadata, proof references or placeholders differ.')
    return {name: match[f'statement_{index}'].strip() for index, name in enumerate(names)}


def check_proposal(root):
    statements = proposal_statements((root / 'FClikelean/AllPrimeGroups.lean').read_text())
    reference = without_comments((root / 'lean/Challenge.lean').read_text())
    for name, reference_name in REFERENCE_NAMES.items():
        match = re.search(r'def ' + reference_name + r'\s*:\s*Prop\s*:=\s*(.*?)'
                          r'(?=^\s*(?:def|end)\b)', reference, re.M | re.S)
        if not match or re.sub(r'\s+', '', statements[name]) != re.sub(r'\s+', '', match[1]):
            raise ValueError(f'The FC proposal statement differs from the independent reference: {name}.')
    return statements
