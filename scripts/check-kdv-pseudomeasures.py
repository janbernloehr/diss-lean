"""Focused pinned Lean checks with read-only reference imports and private outputs."""
from pathlib import Path
import os, re, subprocess, sys
def declaration_names(text):
    """Inventory declarations, including those inside nested namespaces."""
    stack, names = [], []
    for line in text.splitlines():
        ns = re.match(r'^namespace (\S+)\s*$', line)
        end = re.match(r'^end(?: (\S+))?\s*$', line)
        decl = re.match(r'^(?:@\[[^\n]*\]\s*)?(?:def|theorem)\s+([\w.]+)', line)
        if ns:
            stack.append(ns.group(1))
        elif end and stack and end.group(1) == stack[-1]:
            stack.pop()
        elif decl:
            assert stack, decl.group(1)
            names.append('.'.join(stack + [decl.group(1)]))
    return names

def axiom_reports(text):
    """Lean prints a separate sentence for declarations with an empty axiom set."""
    reports = re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]", text, re.S)
    reports += [(name, '') for name in re.findall(r"'([^']+)' does not depend on any axioms", text)]
    return reports

root = Path(__file__).resolve().parent.parent
repo = Path(os.environ.get('DISS_LEAN_REFERENCE_ROOT', '/home/janbernloehr/Documents/Codex/2026-09-11/test-01-5-2-test-02/outputs/dnls'))
elan = Path(os.environ.get('DISS_LEAN_ELAN_HOME', str(repo.parent.parent / 'work/tooling/elan')))
lean = elan / 'toolchains/leanprover--lean4---v4.33.1/bin/lean'
check_dir = root / os.environ.get('DISS_LEAN_CHECK_DIR', '.lake/article-check')
view = check_dir / 'lib/lean'
logs = check_dir / 'logs'
logs.mkdir(parents=True, exist_ok=True)
modules = [
    'NLS.SequenceSpaces.WeightedFiniteCoefficients',
    'NLS.Fourier.PeriodicEndpointBounds',
    'NLS.RealAnalysis.SplitRootGap',
    'NLS.Fourier.PeriodicWeightCongruence',
    'NLS.SequenceSpaces.ConjugateReflection',
    'NLS.SequenceSpaces.WeightedAnalyticRealization',
    'NLS.SequenceSpaces.EvenTailReplacement',
    'NLS.SequenceSpaces.EvenTailConjugation',
    'NLS.ComplexAnalysis.JointSpectralDerivative',
    'NLS.ComplexAnalysis.AnalyticImplicitRoot',
    'NLS.ComplexAnalysis.AnalyticImplicitBanachRoot',
    'NLS.ComplexAnalysis.NearIdentityAnalyticInverse',
    'NLS.ComplexAnalysis.NearIdentityBallInverse',
    'NLS.ComplexAnalysis.AnalyticOpenInverse',
    'NLS.ComplexAnalysis.AnalyticInjectiveImage',
    'NLS.ComplexAnalysis.NearIdentityImageInverse',
    'NLS.FunctionalAnalysis.ContractingSelection',
    'NLS.ComplexAnalysis.LexicographicOrder',
    'NLS.SequenceSpaces.OrderedOneSidedEnumeration',
    'NLS.ComplexAnalysis.CircleOpenCollar',
    'NLS.ComplexAnalysis.RealDiameterDisc',
    'NLS.FunctionalAnalysis.CircleResolventProjection',
    'NLS.FunctionalAnalysis.FiniteInvariantSpectrum',
    'NLS.FunctionalAnalysis.PencilRootChains',
    'NLS.FunctionalAnalysis.PencilRootSemisimple',
    'NLS.FunctionalAnalysis.EquivalentNormNeumann',
    'NLS.ComplexAnalysis.PoweredAnalyticJet',
    'NLS.ComplexAnalysis.BanachFiniteJets',
    'NLS.ComplexAnalysis.AffinePencilJets',
    'NLS.FunctionalAnalysis.ResolventRootSpace',
    'NLS.FunctionalAnalysis.IdempotentRootSpaces',
    'NLS.FunctionalAnalysis.TwoDimensionalDeterminant',
    'NLS.ComplexAnalysis.MatrixAnalyticJetAction',
    'NLS.SequenceSpaces.SobolevConvolutionBounds',
    'NLS.SequenceSpaces.HilbertProductTame',
    'NLS.Fourier.PeriodicH1Multiplication',
    'NLS.Fourier.PeriodicSingularMultiplicationFamily',
    'NLS.Fourier.PeriodicSobolevConjugation',
    'NLS.Fourier.PeriodicH1FormBound',
    'NLS.SequenceSpaces.HillMixedKernel',
    'NLS.SequenceSpaces.InfinityMatrix',
    'NLS.SequenceSpaces.NegativeSpectralWeight',
    'NLS.SequenceSpaces.ScaledSobolevApproximation',
    'NLS.SequenceSpaces.NegativeModulation',
    'NLS.SequenceSpaces.SignedSobolevConvolution',
    'NLS.SequenceSpaces.ShiftReflection',
    'NLS.KdV.FreeHill',
    'NLS.KdV.FreeHillWideGeometry',
    'NLS.KdV.HillComplement',
    'NLS.KdV.HillReduction',
    'NLS.KdV.FreeHillRegularity',
    'NLS.KdV.FreeHillAnalytic',
    'NLS.KdV.SingularHillPhysical',
    'NLS.KdV.SingularHillFreeIsomorphism',
    'NLS.KdV.SingularHillOperatorDomain',
    'NLS.KdV.SingularHillRootSpace',
    'NLS.KdV.SingularHillBilinear',
    'NLS.KdV.SingularHillSesquilinear',
    'NLS.KdV.SingularHillEnergy',
    'NLS.KdV.SingularHillSemibounded',
    'NLS.KdV.SingularHillRealSpectrum',
    'NLS.KdV.SingularHillFreeSpectrum',
    'NLS.KdV.PseudomeasureKernel',
    'NLS.KdV.PseudomeasurePerturbation',
    'NLS.SequenceSpaces.WienerWeakStar',
    'NLS.SequenceSpaces.WeightedWienerWeakStar',
    'NLS.SequenceSpaces.WeightedWeakStarCompactness',
    'NLS.SequenceSpaces.WeightedWeakStarLowerTopology',
    'NLS.SequenceSpaces.EndpointCompactInclusion',
    'NLS.KdV.PseudomeasureRegularity',
    'NLS.KdV.PseudomeasureMultiplication',
    'NLS.KdV.PseudomeasureWideComparison',
    'NLS.KdV.PseudomeasureFredholm',
    'NLS.KdV.PseudomeasureEllipticRegularity',
    'NLS.KdV.PseudomeasureTailInverse',
    'NLS.KdV.PseudomeasureWideTail',
    'NLS.KdV.PseudomeasureReduction',
    'NLS.KdV.PseudomeasureAnalytic',
    'NLS.KdV.PseudomeasureH1Analytic',
    'NLS.KdV.PseudomeasureBilinearSymmetry',
    'NLS.KdV.PseudomeasureLocalization',
    'NLS.KdV.PseudomeasureCoefficients',
    'NLS.KdV.PseudomeasureConjugation',
    'NLS.KdV.PseudomeasureWeightInclusion',
    'NLS.KdV.PseudomeasureWeightedCoefficients',
    'NLS.KdV.PseudomeasureReconstructionAnalytic',
    'NLS.KdV.PseudomeasureInhomogeneousReduction',
    'NLS.KdV.PseudomeasureZeroCount',
    'NLS.KdV.PseudomeasureResolvent',
    'NLS.KdV.PseudomeasureSpectrum',
    'NLS.KdV.PseudomeasureRootSpaces',
    'NLS.KdV.PseudomeasureRieszProjection',
    'NLS.KdV.SingularHillResolventFamily',
    'NLS.KdV.SingularHillFredholm',
    'NLS.KdV.SingularHillSpectrum',
    'NLS.KdV.SingularHillAlgebraicMultiplicity',
    'NLS.KdV.SingularHillChains',
    'NLS.KdV.PseudomeasureChainJets',
    'NLS.KdV.PseudomeasureTaylorKernel',
    'NLS.KdV.PseudomeasureMultiplicityOrder',
    'NLS.KdV.PseudomeasureRealSpectrum',
    'NLS.KdV.PseudomeasureRieszRange',
    'NLS.KdV.SingularHillSpectralProjection',
    'NLS.KdV.PseudomeasureComplexRiesz',
    'NLS.KdV.PseudomeasureComplexCounting',
    'NLS.KdV.PseudomeasureSpectralLipschitz',
    'NLS.KdV.PseudomeasureCouplingLipschitz',
    'NLS.KdV.PseudomeasureDiagonalRoot',
    'NLS.KdV.PseudomeasureDiagonalRootConjugation',
    'NLS.KdV.PseudomeasureDiagonalRootAnalytic',
    'NLS.KdV.PseudomeasureRootSeparation',
    'NLS.KdV.PseudomeasureRealPairs',
    'NLS.KdV.PseudomeasureRealGapComparison',
    'NLS.KdV.PseudomeasureComplexPairs',
    'NLS.KdV.PseudomeasureWeightedGaps',
    'NLS.KdV.PseudomeasureWideLocalization',
    'NLS.KdV.PseudomeasureLowerSpectrum',
    'NLS.Fourier.PeriodicPseudomeasureWeakStar',
    'NLS.Fourier.PeriodicWeightedWeakStar',
    'NLS.Fourier.PeriodicDistributionParity',
    'NLS.Fourier.RealMeanZeroPeriodOne',
    'NLS.Fourier.PeriodicEndpointLowerInclusion',
    'NLS.Fourier.PeriodicWeakStarLowerTopology',
    'NLS.Dynamics.ActionDependentWeightedPhaseFlow',
    'NLS.Dynamics.WeightedWeakStarPhaseFlow',
    'NLS.SequenceSpaces.OrderedNatEnumerationUnique',
    'NLS.SequenceSpaces.OrderedFiniteContinuity',
    'NLS.Articles.KdVPseudomeasures.WeakStarEndpoint',
    'NLS.Articles.KdVPseudomeasures.WeightedWeakStarEndpoint',
    'NLS.Articles.KdVPseudomeasures.PeriodicWeakStarEndpoint',
    'NLS.Articles.KdVPseudomeasures.AppendixBWeakStar',
    'NLS.Articles.KdVPseudomeasures.AppendixBLowerTopology',
    'NLS.Articles.KdVPseudomeasures.TrajectoryTopology',
    'NLS.Articles.KdVPseudomeasures.SourceSpaces',
    'NLS.Articles.KdVPseudomeasures.RealPredualTopology',
    'NLS.Articles.KdVPseudomeasures.SourceWeakStarTopology',
    'NLS.Articles.KdVPseudomeasures.SourceWeakStarLimits',
    'NLS.Articles.KdVPseudomeasures.SourceWeakStarNets',
    'NLS.Articles.KdVPseudomeasures.SourceWeakStarCompactSets',
    'NLS.Articles.KdVPseudomeasures.SourceWeakStarTrajectories',
    'NLS.Articles.KdVPseudomeasures.SpectralEndpoint',
    'NLS.Articles.KdVPseudomeasures.SpectralReduction',
    'NLS.Articles.KdVPseudomeasures.SpectralAnalytic',
    'NLS.Articles.KdVPseudomeasures.SpectralCoefficients',
    'NLS.Articles.KdVPseudomeasures.SpectralResolvent',
    'NLS.Articles.KdVPseudomeasures.SpectralReconstruction',
    'NLS.Articles.KdVPseudomeasures.SpectralMultiplicity',
    'NLS.Articles.KdVPseudomeasures.SpectralChainJets',
    'NLS.Articles.KdVPseudomeasures.SpectralMultiplicityOrder',
    'NLS.Articles.KdVPseudomeasures.SpectralReality',
    'NLS.Articles.KdVPseudomeasures.SpectralPairs',
    'NLS.Articles.KdVPseudomeasures.SpectralGapTail',
    'NLS.Articles.KdVPseudomeasures.SpectralWideLocalization',
    'NLS.Articles.KdVPseudomeasures.SpectralLowerBound',
    'NLS.Articles.KdVPseudomeasures.SpectralCentralWindow',
    'NLS.Articles.KdVPseudomeasures.SpectralFreeCount',
    'NLS.Articles.KdVPseudomeasures.SpectralComplexCounting',
    'NLS.Articles.KdVPseudomeasures.SpectralComplexCentral',
    'NLS.Articles.KdVPseudomeasures.SpectralComplexPairs',
    'NLS.Articles.KdVPseudomeasures.SpectralComplexRoots',
    'NLS.Articles.KdVPseudomeasures.SpectralComplexGlobal',
    'NLS.Articles.KdVPseudomeasures.SpectralComplexUniqueness',
    'NLS.Articles.KdVPseudomeasures.SpectralCentralProjection',
    'NLS.Articles.KdVPseudomeasures.SpectralCentralCounting',
    'NLS.Articles.KdVPseudomeasures.SpectralCentralRoots',
    'NLS.Articles.KdVPseudomeasures.SpectralGlobalLabels',
    'NLS.Articles.KdVPseudomeasures.SpectralLabelUniqueness',
    'NLS.Articles.KdVPseudomeasures.SpectralCanonicalLabels',
    'NLS.Articles.KdVPseudomeasures.SpectralCanonicalGaps',
    'NLS.Articles.KdVPseudomeasures.SpectralComplexCanonical',
    'NLS.Articles.KdVPseudomeasures.SpectralComplexGaps',
    'NLS.Articles.KdVPseudomeasures.SourceWeightedSpectral',
    'NLS.Articles.KdVPseudomeasures.SpectralDiagonalRoot',
    'NLS.Articles.KdVPseudomeasures.SpectralAdaptedCoefficients',
    'NLS.Articles.KdVPseudomeasures.SpectralAdaptedFourier',
    'NLS.Articles.KdVPseudomeasures.SpectralAdaptedInverse',
    'NLS.Articles.KdVPseudomeasures.SpectralRealAdapted',
    'NLS.Articles.KdVPseudomeasures.SpectralInverseRestriction',
    'NLS.Articles.KdVPseudomeasures.SpectralInverseGapComparison',
    'NLS.Articles.KdVPseudomeasures.SpectralEndpointBootstrap',
    'NLS.Articles.KdVPseudomeasures.SpectralCrossOrder',
    'NLS.Articles.KdVPseudomeasures.SpectralWeakStarResolvent',
    'NLS.Articles.KdVPseudomeasures.SpectralCumulativeCounts',
    'NLS.Articles.KdVPseudomeasures.SpectralLabelContinuity',
    'NLS.Articles.KdVPseudomeasures.SpectralClosedFibers',
    'NLS.Articles.KdVPseudomeasures.OriginalHillSpectrum',
    'NLS.Articles.KdVPseudomeasures.SpectralEndpointCompactness',
    'NLS.Articles.KdVPseudomeasures.SpectralAdaptedDiffeomorphism',
    'NLS.Articles.KdVPseudomeasures.SpectralWeightedGaps',
    'NLS.KdV.HillSobolev',
    'NLS.KdV.HillPhysical',
    'NLS.KdV.HillFirstOrderReduction',
    'NLS.KdV.HillAnalytic',
    'NLS.KdV.HillWeightedCoefficients',
    'NLS.KdV.HillBilinearSymmetry',
    'NLS.KdV.HillSpectralLipschitz',
    'NLS.KdV.HillRootSeparation',
    'NLS.SequenceSpaces.WeightedInsertion',
    'NLS.KdV.HillPeriodOnePotential',
    'NLS.KdV.HillL2SpectralCriterion',
    'NLS.KdV.ConstantUpperSpectralBridge',
    'NLS.KdV.ClassicalSpectralSymmetry',
    'NLS.KdV.ClassicalDiscriminant',
    'NLS.KdV.ClassicalHillFlow',
    'NLS.KdV.HillClassicalIdentification',
    'NLS.FunctionalAnalysis.AbsoluteContinuityTranslation',
    'NLS.KdV.HillFullPeriod',
    'NLS.FunctionalAnalysis.LinearVolterraLinearity',
    'NLS.KdV.ClassicalHillMultipliers',
    'NLS.KdV.HillDiscriminantNecessity',
    'NLS.KdV.HillDiscriminantComparison',
    'NLS.ComplexAnalysis.EntireEvenSquareDescent',
    'NLS.KdV.HillL2EnergyDiscriminant',
    'NLS.KdV.SingularHillL2Domain',
    'NLS.KdV.SingularHillL2Characteristic',
    'NLS.Articles.KdVPseudomeasures.OriginalL2Characteristic',
    'NLS.FunctionalAnalysis.CompactClosedGraph',
    'NLS.Articles.KdVPseudomeasures.SourceWeakStarClosedGraph',
    'NLS.Articles.KdVPseudomeasures.SourceWeakStarIntersections',
    'NLS.Articles.KdVPseudomeasures.Audit',
]
# Expand only directories that need local compiled outputs. All reference
# imports remain symlinks; no compiler output may traverse those symlinks.
def local_directory(path):
    if path.is_symlink():
        reference = path.resolve(strict=True)
        path.unlink()
        path.mkdir()
        for child in reference.iterdir():
            (path / child.name).symlink_to(child, target_is_directory=child.is_dir())
    else:
        path.mkdir(parents=True, exist_ok=True)
(view / 'NLS').mkdir(parents=True, exist_ok=True)
for child in (repo / '.lake/build/lib/lean/NLS').iterdir():
    target = view / 'NLS' / child.name
    if not target.exists():
        target.symlink_to(child, target_is_directory=child.is_dir())
for module in modules:
    rel = Path(*module.split('.'))
    for parent in reversed(rel.parents):
        local_directory(view / parent)
    target = (view / rel).with_suffix('.olean')
    if target.is_symlink():
        target.unlink()
paths = [view] + list((repo / '.lake/packages').glob('*/.lake/build/lib/lean'))
env = dict(os.environ, LEAN_PATH=':'.join(map(str, paths)), ELAN_HOME=str(elan),
           PATH=str(elan / 'bin') + os.pathsep + os.environ.get('PATH', ''),
           MATHLIB_CACHE_DIR=str(repo.parent.parent / 'work/cache/mathlib'))
requested = sys.argv[1:]
selected = [m if m.startswith('NLS.') else 'NLS.Articles.KdVPseudomeasures.' + m for m in requested] if requested else modules
for module in selected:
    rel = Path(*module.split('.'))
    source = (root / rel).with_suffix('.lean')
    output = (view / rel).with_suffix('.olean')
    assert not output.is_symlink() and output.parent.resolve().is_relative_to(view), output
    result = subprocess.run([str(lean), '-DautoImplicit=false', '-R', str(root), '-o', str(output), str(source)],
                            env=env, capture_output=True, text=True)
    (logs / ('check-' + module.split('.')[-1] + '.log')).write_text(result.stdout + result.stderr)
    print(module, 'exit:', result.returncode)
    if result.returncode or module.endswith('.Audit'):
        print(result.stdout + result.stderr, end='')
    elif result.stdout or result.stderr:
        print(result.stdout + result.stderr, end='')
    if result.returncode:
        sys.exit(result.returncode)
    if module.endswith('.Audit'):
        reports = axiom_reports(result.stdout)
        expected = re.findall(r'^#print axioms (\S+)', source.read_text(), re.M)
        inventory = []
        for checked in modules:
            if checked.endswith('.Audit'):
                continue
            text = (root / Path(*checked.split('.'))).with_suffix('.lean').read_text()
            inventory += declaration_names(text)
        assert len(inventory) == len(set(inventory)), inventory
        assert set(expected) == set(inventory), (set(expected) ^ set(inventory))
        assert len(reports) == len(expected) and {d for d, _ in reports} == set(expected), (set(expected) ^ {d for d, _ in reports})
        for declaration, axioms in reports:
            assert {a.strip() for a in axioms.split(',') if a.strip()} <= {'propext', 'Classical.choice', 'Quot.sound'}, (declaration, axioms)
print('All requested isolated checks passed.')
