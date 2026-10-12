import NLS.ZakharovShabat.SourceLemma4_3
import NLS.ZakharovShabat.SourceBoundaryFourier
import NLS.Fourier.HalfIntervalL2Identification

/-!
# Lemma 4.3 on arbitrary physical L² input

The bounded source extension has the actual signed-reflection coefficients
for every square-integrable unit-interval pair. Fourier synthesis reconstructs
that reflection almost everywhere. All norms are the original component-sum
norms, and no boundary or endpoint matching is imposed.
-/

noncomputable section
open MeasureTheory Set NLS.Fourier
namespace NLS.ZakharovShabat
open BoundaryCondition

/-- The original unit-period Fourier coefficients of arbitrary physical L² interval data. -/
def sourceUnitIntervalL2Coefficients (f : ℝ → ℂ × ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) : CoeffPair 2 :=
  WithLp.toLp 2 (unitIntervalMemLpCoefficients (fun x => (f x).1) hf.fst,
    unitIntervalMemLpCoefficients (fun x => (f x).2) hf.snd)

/-- The completed amplitudes equal actual half-interval integrals for every L² input. -/
theorem sourceIntervalAmplitudeCLM_two_ofFunction (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) (n : ℤ) :
    sourceIntervalAmplitudeCLM b (by norm_num) (by simp) (sourceUnitIntervalL2Coefficients f hf) n =
      intervalAmplitude b f n := by
  change halfIntervalCoeffs (by norm_num) (by simp) (unitIntervalMemLpCoefficients (fun x => (f x).2) hf.snd) n +
    b.extensionSign * halfIntervalCoeffs (by norm_num) (by simp) (unitIntervalMemLpCoefficients (fun x => (f x).1) hf.fst) (-n) = _
  rw [halfIntervalCoeffs_two_ofFunction, halfIntervalCoeffs_two_ofFunction]
  rfl

/-- Remove the trivial zero-Sobolev weight isometrically in the original pair norms. -/
def sourceZeroWeightedPairEquiv : WeightedCoeffPair (Weight.sobolev 0) 2 ≃ₗᵢ[ℂ] CoeffPair 2 :=
  (WeightedCoeff.weightIsometry (Weight.sobolev 0) 2).withLpProdCongr 2
    (WeightedCoeff.weightIsometry (Weight.sobolev 0) 2)

/-- Removing the zero weight preserves the first raw coefficient. -/
theorem sourceZeroWeightedPairEquiv_fst (a : WeightedCoeffPair (Weight.sobolev 0) 2) (n : ℤ) :
    (sourceZeroWeightedPairEquiv a).fst n = a.fst.val n := by
  change (Weight.sobolev 0 n : ℂ) * a.fst.val n = _
  simp

/-- Removing the zero weight preserves the second raw coefficient. -/
theorem sourceZeroWeightedPairEquiv_snd (a : WeightedCoeffPair (Weight.sobolev 0) 2) (n : ℤ) :
    (sourceZeroWeightedPairEquiv a).snd n = a.snd.val n := by
  change (Weight.sobolev 0 n : ℂ) * a.snd.val n = _
  simp

/-- The completed extension in the original unweighted Hilbert pair spaces. -/
def sourceIntervalExtensionL2 (b : BoundaryCondition) : CoeffPair 2 →L[ℂ] CoeffPair 2 :=
  sourceZeroWeightedPairEquiv.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((sourceWeightedBoundarySubspace (p := 2) b 0).subtypeL.comp
      (sourceIntervalExtensionToBoundary b (by norm_num) (by simp)))

/-- The completed operator gives exactly the actual signed-reflection Fourier coefficients. -/
theorem sourceIntervalExtensionL2_ofFunction (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) :
    sourceIntervalExtensionL2 b (sourceUnitIntervalL2Coefficients f hf) =
      sourceIntervalExtensionCoefficients b f hf := by
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext <;> apply lp.ext <;> funext n
  · change (sourceZeroWeightedPairEquiv (sourceIntervalExtensionToBoundary b (by norm_num) (by simp) (sourceUnitIntervalL2Coefficients f hf)).val).fst n = (sourceIntervalExtensionCoefficients b f hf).fst n
    rw [sourceZeroWeightedPairEquiv_fst, sourceIntervalExtensionToBoundary_fst,
      sourceIntervalAmplitudeCLM_two_ofFunction, sourceIntervalExtensionCoefficients_fst]
  · change (sourceZeroWeightedPairEquiv (sourceIntervalExtensionToBoundary b (by norm_num) (by simp) (sourceUnitIntervalL2Coefficients f hf)).val).snd n = (sourceIntervalExtensionCoefficients b f hf).snd n
    rw [sourceZeroWeightedPairEquiv_snd, sourceIntervalExtensionToBoundary_snd,
      sourceIntervalAmplitudeCLM_two_ofFunction, sourceIntervalExtensionCoefficients_snd]

/-- The physical source extension preserves the original Hilbert pair norm. -/
theorem norm_sourceIntervalExtensionL2 (b : BoundaryCondition) (a : CoeffPair 2) :
    ‖sourceIntervalExtensionL2 b a‖ = ‖a‖ := by
  change ‖sourceZeroWeightedPairEquiv (sourceIntervalExtensionToBoundary b (by norm_num) (by simp) a).val‖ = _
  rw [sourceZeroWeightedPairEquiv.norm_map]
  exact norm_sourceIntervalExtensionToBoundary_two b a

/-- The original coefficient norm equals the ordinary unit-interval L² norm. -/
theorem norm_sourceUnitIntervalL2Coefficients (f : ℝ → ℂ × ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) :
    ‖sourceUnitIntervalL2Coefficients f hf‖ = ‖intervalL2OfFunction f hf‖ := by
  rw [← norm_sourceIntervalExtensionL2 .dirichlet, sourceIntervalExtensionL2_ofFunction,
    norm_sourceIntervalExtensionCoefficients]

/-- Fourier synthesis of the completed operator reconstructs the actual signed reflection almost everywhere. -/
theorem sourceLemma4_3_L2_physical (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) :
    sourceCircleRepresentative (sourceCircleSynthesis
      (sourceIntervalExtensionL2 b (sourceUnitIntervalL2Coefficients f hf)))
      =ᵐ[volume.restrict (Ioc 0 2)] intervalExtension b f := by
  rw [sourceIntervalExtensionL2_ofFunction]
  exact sourceCircleSynthesis_intervalExtension b f hf

end NLS.ZakharovShabat
