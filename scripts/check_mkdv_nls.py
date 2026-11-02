#!/usr/bin/env python3
"""Compile article changes using read-only cached imports and private outputs.

Pass --imports-from the pinned canonical checkout. This never invokes lake or
writes a dependency artifact. It is a focused check, not a fresh full build.
"""
from pathlib import Path
import argparse
from contextlib import nullcontext
import fcntl
import os
import shutil
import subprocess
import sys

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--imports-from", type=Path, required=True)
parser.add_argument("--lean", default=shutil.which("lean"))
parser.add_argument("--full-audit", action="store_true")
parser.add_argument("--module-only", action="append", metavar="PATH",
                    help="Check only this module, without aggregate compilation or audit (repeatable).")
parser.add_argument("--resume-from", metavar="PATH",
                    help="Resume a failed check here, reusing prior private validated module outputs.")
args = parser.parse_args()
if not args.lean:
    parser.error("Set PATH to the pinned toolchain or pass --lean.")
root = Path(__file__).resolve().parent.parent
canonical = args.imports_from.resolve()
build = root / ".lake/build"
lib = build / "lib/lean"
logs = build / "article-logs/mkdv-nls-hierarchies"
logs.mkdir(parents=True, exist_ok=True)
version = subprocess.check_output([args.lean, "--version"], text=True).strip()
if not version.startswith("Lean (version 4.33.1,"):
    parser.error(f"Expected pinned Lean 4.33.1, got {version}")
modules = [
    "NLS/ComplexAnalysis/SourceDiscriminantPrimitive.lean",
    "NLS/KdV/FreeHill.lean",
    "NLS/KdV/HillComplement.lean",
    "NLS/KdV/HillReduction.lean",
    "NLS/KdV/HillSobolev.lean",
    "NLS/KdV/HillPhysical.lean",
    "NLS/KdV/HillFirstOrderReduction.lean",
    "NLS/KdV/HillAnalytic.lean",
    "NLS/KdV/HillWeightedCoefficients.lean",
    "NLS/KdV/HillBilinearSymmetry.lean",
    "NLS/KdV/HillSpectralLipschitz.lean",
    "NLS/FunctionalAnalysis/TwoDimensionalDeterminant.lean",
    "NLS/KdV/HillRootSeparation.lean",
    "NLS/SequenceSpaces/WeightedInsertion.lean",
    "NLS/KdV/HillPeriodOnePotential.lean",
    "NLS/KdV/HillL2SpectralCriterion.lean",
    "NLS/KdV/ConstantUpperSpectralBridge.lean",
    "NLS/KdV/ClassicalSpectralSymmetry.lean",
    "NLS/KdV/ClassicalDiscriminant.lean",
    "NLS/KdV/ClassicalHillFlow.lean",
    "NLS/KdV/HillClassicalIdentification.lean",
    "NLS/FunctionalAnalysis/AbsoluteContinuityTranslation.lean",
    "NLS/KdV/HillFullPeriod.lean",
    "NLS/FunctionalAnalysis/LinearVolterraLinearity.lean",
    "NLS/KdV/ClassicalHillMultipliers.lean",
    "NLS/KdV/HillDiscriminantNecessity.lean",
    "NLS/KdV/HillDiscriminantComparison.lean",
    "NLS/ComplexAnalysis/EntireEvenSquareDescent.lean",
    "NLS/KdV/HillL2EnergyDiscriminant.lean",
    "NLS/KdV/HillWeightIndependence.lean",
    "NLS/KdV/HillLocalization.lean",
    "NLS/KdV/HillZeroCount.lean",
    "NLS/ComplexAnalysis/ZeroCountHomotopy.lean",
    "NLS/ComplexAnalysis/TwoZeroOrderComparison.lean",
    "NLS/KdV/ClassicalLocalPrimitive.lean",
    "NLS/KdV/ClassicalFreePrimitive.lean",
    "NLS/KdV/HillCharacteristicZeros.lean",
    "NLS/KdV/HillFreeSpectrum.lean",
    "NLS/KdV/HillRealSpectrum.lean",
    "NLS/KdV/HillWideLocalization.lean",
    "NLS/ComplexAnalysis/RealDiameterDisc.lean",
    "NLS/KdV/HillCentralCounting.lean",
    "NLS/KdV/HillCentralRoots.lean",
    "NLS/KdV/HillRealGapPairs.lean",
    "NLS/SequenceSpaces/OrderedOneSidedEnumeration.lean",
    "NLS/KdV/HillGlobalRealLabels.lean",
    "NLS/KdV/HillRealLabelingUniqueness.lean",
    "NLS/KdV/HillCanonicalRealLabels.lean",
    "NLS/KdV/ClassicalHillSpectrum.lean",
    "NLS/ZakharovShabat/ClassicalSolutionInjectivity.lean",
    "NLS/KdV/ClassicalHillGreen.lean",
    "NLS/KdV/ClassicalSourcePrimitive.lean",
    "NLS/ZakharovShabat/ContinuousPotentialL2Bound.lean",
    "NLS/KdV/ClassicalSpectralEmbedding.lean",
    "NLS/KdV/ClassicalContourCoverage.lean",
    "NLS/KdV/ClassicalHighGapPairs.lean",
    "NLS/KdV/ClassicalHillReality.lean",
    "NLS/KdV/ClassicalHillConjugation.lean",
    "NLS/KdV/ClassicalHillPrimitiveSheets.lean",
    "NLS/KdV/ClassicalHillPrimitiveReflection.lean",
    "NLS/KdV/ClassicalHillBandNormalization.lean",
    "NLS/KdV/HillNLSPrimitivePathComparison.lean",
    "NLS/ZakharovShabat/ContinuousPotentialSource.lean",
    "NLS/FunctionalAnalysis/PeriodicIntegrationByParts.lean",
    "NLS/ZakharovShabat/ClassicalNLSHamiltonians.lean",
    "NLS/ZakharovShabat/ClassicalNLSEnergyVariation.lean",
    "NLS/ZakharovShabat/SobolevPhysicalJets.lean",
    "NLS/FunctionalAnalysis/UnitIntervalMean.lean",
    "NLS/DifferentialPolynomial/PolynomialVariation.lean",
    "NLS/DifferentialPolynomial/EulerLagrange.lean",
    "NLS/DifferentialPolynomial/EulerOrderBounds.lean",
    "NLS/DifferentialPolynomial/UngradedIntegrationByParts.lean",
    "NLS/DifferentialPolynomial/PowerSeriesDerivation.lean",
    "NLS/DifferentialPolynomial/LogarithmicDerivative.lean",
    "NLS/DifferentialPolynomial/RiccatiResolvent.lean",
    "NLS/DifferentialPolynomial/DifferentialRiccati.lean",
    "NLS/DifferentialPolynomial/MiuraRiccati.lean",
    "NLS/DifferentialPolynomial/ConstructedRiccatiResolvent.lean",
    "NLS/DifferentialPolynomial/RiccatiResolventParity.lean",
    "NLS/DifferentialPolynomial/RiccatiResolventVariation.lean",
    "NLS/ZakharovShabat/NLSRiccatiResolvent.lean",
    "NLS/DifferentialPolynomial/MultiJet.lean",
    "NLS/DifferentialPolynomial/AlgebraicPolynomialVariation.lean",
    "NLS/DifferentialPolynomial/IndependentJetVariation.lean",
    "NLS/DifferentialPolynomial/EulerScalar.lean",
    "NLS/DifferentialPolynomial/RiccatiResolventNaturality.lean",
    "NLS/Fourier/PeriodicVariationalUniqueness.lean",
    "NLS/Fourier/PeriodOneDistributionDerivative.lean",
    "NLS/Fourier/PeriodOneSobolevDistribution.lean",
    "NLS/DifferentialPolynomial/SmoothVariation.lean",
    "NLS/ZakharovShabat/ClassicalNLSHierarchyVariation.lean",
    "NLS/ZakharovShabat/NLSRiccatiResolventVariation.lean",
    "NLS/ZakharovShabat/NLSRiccatiResolventGradient.lean",
    "NLS/Fourier/CircleUnitCoefficients.lean",
    "NLS/Fourier/CircleBilinearMean.lean",
    "NLS/ZakharovShabat/SobolevPolynomialL2.lean",
    "NLS/ZakharovShabat/SobolevPolynomialEndpointMean.lean",
    "NLS/ZakharovShabat/SobolevPolynomialVariation.lean",
    "NLS/ZakharovShabat/SobolevScalarSmoothDensity.lean",
    "NLS/ZakharovShabat/SobolevOddHamiltonianAllOrders.lean",
    "NLS/ZakharovShabat/SobolevSourceCotangent.lean",
    "NLS/ZakharovShabat/SobolevSmoothFirstVariation.lean",
    "NLS/ZakharovShabat/SobolevHierarchyGradient.lean",
    "NLS/ZakharovShabat/SobolevHierarchySymmetries.lean",
    "NLS/ZakharovShabat/NLSEvenHamiltonianReducedPolynomial.lean",
    "NLS/ZakharovShabat/SobolevEvenHamiltonian.lean",
    "NLS/ZakharovShabat/SobolevEvenHierarchyGradient.lean",
    "NLS/Articles/MKdVNLSHierarchies/SharpEvenVanishing.lean",
    "NLS/ZakharovShabat/SobolevHierarchyGradientVariation.lean",
    "NLS/ZakharovShabat/SobolevHierarchyGradientSymmetries.lean",
    "NLS/MKdV/HierarchyGradientRecurrence.lean",
    "NLS/MKdV/SobolevHierarchyGradientRecurrence.lean",
    "NLS/MKdV/HierarchyRestriction.lean",
    "NLS/MKdV/MiuraHierarchyHamiltonians.lean",
    "NLS/MKdV/MiuraHierarchyFlowRestriction.lean",
    "NLS/MKdV/SobolevMiuraHillHamiltonian.lean",
    "NLS/MKdV/SobolevMiuraHillFlowRestriction.lean",
    "NLS/MKdV/MiuraHillRiccatiRemainder.lean",
    "NLS/MKdV/NativeMiuraHillHamiltonian.lean",
    "NLS/MKdV/NativeMiuraHillGradient.lean",
    "NLS/Articles/MKdVNLSHierarchies/NativeHierarchy.lean",
    "NLS/Articles/MKdVNLSHierarchies/SharpMiuraFlow.lean",
    "NLS/Articles/MKdVNLSHierarchies/SmoothHierarchy.lean",
    "NLS/Articles/MKdVNLSHierarchies/InitialChecks.lean",
    "NLS/Articles/MKdVNLSHierarchies/GradientSymmetries.lean",
    "NLS/Articles/MKdVNLSHierarchies/GradientRecurrence.lean",
    "NLS/ZakharovShabat/ClassicalNLSFourthHamiltonian.lean",
    "NLS/ZakharovShabat/ClassicalNLSFourthVariation.lean",
    "NLS/MKdV/ClassicalEnergyVariation.lean",
    "NLS/MKdV/ClassicalFourthFlowRestriction.lean",
    "NLS/Articles/MKdVNLSHierarchies/SmoothFourthFlow.lean",
    "NLS/MKdV/MiuraClassicalSolution.lean",
    "NLS/MKdV/MiuraBoundaryTransfer.lean",
    "NLS/FunctionalAnalysis/LinearVolterraFlow.lean",
    "NLS/MKdV/QuasiHillDiscriminant.lean",
    "NLS/ZakharovShabat/ClassicalVolterraTrace.lean",
    "NLS/MKdV/QuasiHillZSComparison.lean",
    "NLS/MKdV/QuasiHillJointAnalytic.lean",
    "NLS/MKdV/QuasiHillSourcePrimitive.lean",
    "NLS/MKdV/QuasiHillPhysicalEquation.lean",
    "NLS/MKdV/QuasiHillPhysicalUniqueness.lean",
    "NLS/MKdV/SobolevQuasiHill.lean",
    "NLS/MKdV/PhysicalHillDiscriminant.lean",
    "NLS/MKdV/MiuraHillHamiltonianTrace.lean",
    "NLS/MKdV/MiuraHillSpectralBridge.lean",
    "NLS/MKdV/MiuraHillPrimitiveComparison.lean",
    "NLS/MKdV/QuasiHillPrimitiveComparison.lean",
    "NLS/MKdV/SobolevMiuraPrimitive.lean",
    "NLS/Articles/MKdVNLSHierarchies/PrimitiveIdentification.lean",
    "NLS/Articles/MKdVNLSHierarchies/DiscriminantIdentity.lean",
    "NLS/Articles/MKdVNLSHierarchies/SobolevPrimitiveIdentification.lean",
    "NLS/MKdV/SobolevMiuraPotential.lean",
    "NLS/MKdV/MiuraL2HillDiscriminant.lean",
    "NLS/MKdV/MiuraHillSpectralIdentification.lean",
    "NLS/MKdV/MiuraHillRealLabels.lean",
    "NLS/Articles/MKdVNLSHierarchies/SpectralIdentification.lean",
    "NLS/SequenceSpaces/OrderedNaturalEnumerationUnique.lean",
    "NLS/ZakharovShabat/CanonicalPeriodicEvenReflection.lean",
    "NLS/MKdV/MiuraNLSPositiveEndpoints.lean",
    "NLS/MKdV/MiuraPositiveMultiplicity.lean",
    "NLS/MKdV/MiuraSquaredEndpointMultiplicity.lean",
    "NLS/MKdV/MiuraGapIdentification.lean",
    "NLS/Articles/MKdVNLSHierarchies/GapIdentification.lean",
    "NLS/ZakharovShabat/ClassicalDiagonalZeroEnergy.lean",
    "NLS/MKdV/MiuraZeroEnergy.lean",
    "NLS/MKdV/MiuraActionZeroIdentification.lean",
    "NLS/ZakharovShabat/SourceIndexedActionCosineIntegral.lean",
    "NLS/MKdV/MiuraActionReflection.lean",
    "NLS/Articles/MKdVNLSHierarchies/ActionIdentification.lean",
    "NLS/ComplexAnalysis/NonrealBoundaryExtension.lean",
    "NLS/MKdV/MiuraHillBoundaryExtension.lean",
    "NLS/MKdV/MiuraHillGapComplement.lean",
    "NLS/MKdV/MiuraCanonicalHillSheets.lean",
    "NLS/MKdV/MiuraHillPrimitiveEndpoint.lean",
    "NLS/Articles/MKdVNLSHierarchies/CanonicalPrimitiveIdentification.lean",
    "NLS/ComplexAnalysis/PiecewiseSquareContour.lean",
    "NLS/ZakharovShabat/SourceWeightedPrimitiveContour.lean",
    "NLS/ZakharovShabat/SourceLaurentActionContour.lean",
    "NLS/MKdV/MiuraLaurentContourComparison.lean",
    "NLS/ComplexAnalysis/RealCenteredPositiveDisc.lean",
    "NLS/ComplexAnalysis/PiecewiseSquareWinding.lean",
    "NLS/MKdV/MiuraActionContourFamily.lean",
    "NLS/MKdV/MiuraSpectralActions.lean",
    "NLS/ZakharovShabat/SourceLaurentActionContourPeriod.lean",
    "NLS/MKdV/MiuraSpectralActionContours.lean",
    "NLS/Articles/MKdVNLSHierarchies/SpectralActionIdentification.lean",
]
if args.full_audit:
    modules.append("NLS.lean")
if args.module_only:
    if args.full_audit:
        parser.error("--module-only cannot be combined with --full-audit")
    modules = args.module_only
check_modules = modules
if args.resume_from:
    if args.module_only:
        parser.error("--resume-from cannot be combined with --module-only")
    if args.resume_from not in modules:
        parser.error("--resume-from must name a checked module")
    index = modules.index(args.resume_from)
    for prior in modules[:index]:
        cached = lib / Path(prior).with_suffix(".olean")
        if not cached.exists() or cached.is_symlink():
            parser.error(f"Missing prior private validated output: {cached}")
    check_modules = modules[index:]
targets = {Path(module).with_suffix(".olean") for module in modules}

def overlay(source, target, prefix=Path()):
    if target.is_symlink():
        target.unlink()
    target.mkdir(parents=True, exist_ok=True)
    for item in source.iterdir():
        relative = prefix / item.name
        destination = target / item.name
        if relative in targets:
            if destination.is_symlink():
                destination.unlink()
            continue
        if item.is_dir() and any(relative in module.parents for module in targets):
            overlay(item, destination, relative)
        elif not destination.exists() and not destination.is_symlink():
            destination.symlink_to(item, target_is_directory=item.is_dir())

overlay(canonical / ".lake/build/lib/lean", lib)
paths = [lib]
paths.extend(sorted((canonical / ".lake/packages").glob("*/.lake/build/lib/lean")))
env = dict(os.environ, LEAN_PATH=":".join(map(str, paths)))

def run(source, output=None):
    command = [args.lean, "-DautoImplicit=false", "-DwarningAsError=true", "--root", str(root)]
    if output:
        if output.is_symlink() or not output.resolve().is_relative_to(build.resolve()):
            raise RuntimeError(f"Refusing to write through cached dependency link: {output}")
        output.parent.mkdir(parents=True, exist_ok=True)
        command.extend(["-o", str(output)])
    command.append(str(root / source))
    print(f"Checking {source}", flush=True)
    result = subprocess.run(command, cwd=root, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (logs / (Path(source).stem + ".log")).write_text(result.stdout)
    print(result.stdout, end="", flush=True)
    if result.returncode:
        sys.exit(result.returncode)

# Serialize aggregate compilation and larger validation with the article lock.
with (open("/tmp/diss-lean-article-build.lock", "a") if args.full_audit else
      nullcontext(None)) as lock:
    if lock is not None:
        print("Waiting for shared article build lock", flush=True)
        fcntl.flock(lock, fcntl.LOCK_EX)
    for module in check_modules:
        run(module, lib / Path(module).with_suffix(".olean"))
    if not args.module_only:
        run("scripts/CheckMKdVNLSHierarchiesAxioms.lean")
    if args.full_audit:
        combined = logs / "CombinedAxioms.lean"
        imports = "".join(f"import {str(Path(module).with_suffix('')).replace('/', '.')}\n"
                          for module in modules if module != "NLS.lean")
        combined.write_text(imports + (root / "scripts/CheckAxioms.lean").read_text())
        run(str(combined.relative_to(root)))
    print("Requested compilation and axiom checks passed.", flush=True)
