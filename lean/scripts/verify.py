#!/usr/bin/env python3
"""Check every new module and audit the axioms of all milestone theorems."""
import hashlib
import json
import subprocess
import sys
from build_env import ROOT
from axiom_audit import audit_axioms, MAIN_THEOREM

files = ['Target', 'PrimePeriods', 'Symmetrization', 'CongruencePGroup',
    'RootCalculus', 'Separation', 'FinitePerfect', 'SteinbergCore',
    'MatrixModel', 'FaithfulStrip', 'Stabilization', 'NilAugmentation', 'ChainLimit',
    'StableGroup', 'FiniteStage', 'HierarchyGrowth', 'Candidate',
    'FiniteIndexPresentation', 'StableMap', 'Assembly',
    'MonomialPresentation', 'SteinbergPresentation',
    'KernelExtras', 'BlockEmbeddings', 'BandFactorization', 'SpecialLinearLift',
    'SpecialLinearRealization', 'NumericalSimilarity', 'CyclicTriangularization',
    'StablePermutation', 'PolynomialTorsion', 'RelativeTorsion',
    'PhaseCommutators', 'SeparationCriterion', 'LongRepresentatives',
    'OffsetCollection', 'PhaseSeparation', 'RelocationFrames', 'RelocationMoves', 'CorrectionSubgroup',
    'CorrectionFaithful', 'Relocation', 'PrimeCancellation',
    'PrimeMatrixNil', 'PrimeAlgebra', 'PrimeReduction', 'WordBasis', 'PhaseConstruction',
    'HierarchyPhases', 'HierarchyGrading', 'PrimeSeparation', 'ColumnComplex', 'CosetTransport',
    'LocalColumns', 'GLPresentation', 'GLTransport', 'GLSection', 'GLLift',
    'GLSwap', 'GLInduction', 'GLAction', 'GLRelabel', 'K1Stability',
    'CentralClosed', 'FrameComplex', 'FrameExactness', 'FrameSplit', 'FrameLemma',
    'FrameTheorem', 'RowStabilizer', 'MultiRowStabilizer', 'StabilityCharacters',
    'CocycleExtension', 'ExtensionOperations', 'ExtensionFactorSet', 'ExtensionCohomology',
    'CocycleProducts', 'PrimeCharacterReduction',
    'MatrixGeometry', 'CoordinateStability', 'FrameBlockMatrices', 'BlockFaceMaps', 'FrameFaceGeometry',
    'ScaledFrameFaces', 'SignedFacePair', 'FrameActions', 'FrameActionStabilizers', 'FrameRepresentations',
    'NilMatrixLift', 'FieldFrameCompletion', 'SplitFrameCompletion', 'FrameTransitivity', 'FrameCosets',
    'PrimeFrameTransitivity',
    'FunctionCoinduction', 'HomologyUnop', 'ProjectiveComparison', 'BarRestriction', 'CohomologyComparison', 'ExplicitShapiro', 'HomogeneousShapiro', 'FrameCochains', 'FrameShapiro', 'FrameLowDegree', 'PrimeFrameShapiro',
    'CohomologyConjugation', 'SignedFrameShapiro', 'FactorSetPullback', 'CentralExtensionCharacters', 'FrameCharacterClasses', 'FrameCharacterCocycle', 'PrimeFrameCharacterClasses',
    'InjectiveDualExact', 'FrameChainDuality', 'FrameCoefficientComplex', 'FrameCochainRows', 'FrameCoefficientH0', 'CochainExactness', 'LowDegreeChase', 'FrameLowDegreeLift', 'FrameAugmentation', 'FrameH2Lift', 'PrimeFrameH2Lift',
    'CentralClassLifts', 'OneRowFrameCover', 'PrimeCharacterRealization', 'PrimeCharacterExtensions',
    'FiniteLocal', 'PrimeGroups', 'FinitePQuotients', 'PrimePQuotients', 'NilCongruence', 'NilMatrixCongruence', 'PrimeNilUnits']
sources = [*[f'AllPrimeGroups/{name}.lean' for name in files], 'AllPrimeGroups.lean', 'Audit.lean']
if set(sys.argv[1:]) - {'--audit-only'}:
    raise SystemExit('Usage: verify.py [--audit-only]')
actual = {p.stem for p in (ROOT / 'AllPrimeGroups').glob('*.lean')}
if actual != set(files) or len(files) != len(set(files)):
    raise SystemExit('The verification module list does not match AllPrimeGroups/.')
if '--audit-only' not in sys.argv:
    subprocess.run([sys.executable, str(ROOT / 'scripts/check.py'), *sources], cwd=ROOT, check=True)
report = json.loads((ROOT / 'reports/local-checks.json').read_text())
for name in sources:
    checked = report['files'].get(name, {})
    digest = hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
    artifact = ROOT / '.lake/build/lib/lean' / name.replace('.lean', '.olean')
    if checked.get('exit_code') != 0 or checked.get('source_sha256') != digest:
        raise SystemExit(f'Run the checker first: {name}')
    if not artifact.exists() or checked.get('olean_sha256') != hashlib.sha256(artifact.read_bytes()).hexdigest():
        raise SystemExit(f'Build artifact changed or missing: {name}')
audit_log = ROOT / 'reports/Audit.log'
if report['files']['Audit.lean'].get('log_sha256') != hashlib.sha256(audit_log.read_bytes()).hexdigest():
    raise SystemExit('Audit log changed or has no recorded hash; recheck Audit.lean.')
try:
    result = audit_axioms((ROOT / 'Audit.lean').read_text(), audit_log.read_text(), [MAIN_THEOREM])
except ValueError as error:
    raise SystemExit(str(error)) from error
(ROOT / 'reports/local-axioms.json').write_text(json.dumps(result, indent=2) + '\n')
print(f'PASS: {len(files)} modules, {len(result)} theorem axiom audits.')
print(f'Main theorem {MAIN_THEOREM} : Target is proved and audited.')
