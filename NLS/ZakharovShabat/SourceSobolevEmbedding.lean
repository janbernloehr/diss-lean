import NLS.SequenceSpaces.SobolevPeriodDoubling
import NLS.SequenceSpaces.WeightedMultiplier
import NLS.ZakharovShabat.SourceWeightedPeriodOne

/-! # The H¹ source and its weighted physical realization

Both maps preserve original Fourier coefficients. The physical realization
inserts them at the even indices and carries the weight needed by the
spectral gap estimates.
-/
noncomputable section
namespace NLS.ZakharovShabat

/-- Forget the Sobolev weights, retaining the original period-one source coefficients. -/
def sobolevSourceInclusion : (ScalarDomain 2 × ScalarDomain 2) →L[ℂ] CoeffPair 2 :=
  (CoeffPair.toMax 2).symm.toContinuousLinearMap.comp (scalarInclusion.prodMap scalarInclusion)

@[simp] theorem sobolevSourceInclusion_fst (a : ScalarDomain 2 × ScalarDomain 2) (n : ℤ) :
    (sobolevSourceInclusion a).fst n = a.1.val n := scalarInclusion_apply _ _

@[simp] theorem sobolevSourceInclusion_snd (a : ScalarDomain 2 × ScalarDomain 2) (n : ℤ) :
    (sobolevSourceInclusion a).snd n = a.2.val n := scalarInclusion_apply _ _

private def spectralSobolevInclusion : ScalarDomain 2 →L[ℂ]
    WeightedCoeff (SpectralWeight.sobolev 1 (by norm_num)).toWeight 2 :=
  WeightedCoeff.inclusionCLM _ _ (by intro n; simp)

/-- The same H¹ source, now with physical even frequencies and their Sobolev weight. -/
def sobolevSourceWeightedPeriodOne : (ScalarDomain 2 × ScalarDomain 2) →L[ℂ]
    WeightedCoeffPair (SpectralWeight.sobolev 1 (by norm_num)).toWeight 2 :=
  (WeightedCoeffPair.toMax _ 2).symm.toContinuousLinearMap.comp
    ((spectralSobolevInclusion.comp Coeff.periodDoubleSobolevCLM).prodMap
      (spectralSobolevInclusion.comp Coeff.periodDoubleSobolevCLM))

@[simp] theorem sobolevSourceWeightedPeriodOne_fst
    (a : ScalarDomain 2 × ScalarDomain 2) (n : ℤ) :
    (sobolevSourceWeightedPeriodOne a).fst.val n = Coeff.periodDouble (scalarInclusion a.1) n := by
  change (spectralSobolevInclusion (Coeff.periodDoubleSobolev a.1)).val n = _
  rw [spectralSobolevInclusion, WeightedCoeff.inclusionCLM_apply, Coeff.periodDoubleSobolev_apply]

@[simp] theorem sobolevSourceWeightedPeriodOne_snd
    (a : ScalarDomain 2 × ScalarDomain 2) (n : ℤ) :
    (sobolevSourceWeightedPeriodOne a).snd.val n = Coeff.periodDouble (scalarInclusion a.2) n := by
  change (spectralSobolevInclusion (Coeff.periodDoubleSobolev a.2)).val n = _
  rw [spectralSobolevInclusion, WeightedCoeff.inclusionCLM_apply, Coeff.periodDoubleSobolev_apply]

/-- The weighted construction supplies exactly the original source's spectral operator. -/
theorem weightedBaseToPair_sobolevSourceWeightedPeriodOne (a : ScalarDomain 2 × ScalarDomain 2) :
    weightedBaseToPair (SpectralWeight.sobolev 1 (by norm_num)) (sobolevSourceWeightedPeriodOne a) =
      periodOnePotential (sobolevSourceInclusion a) := by
  apply Prod.ext <;> ext n
  · simp only [weightedBaseToPair_fst, sobolevSourceWeightedPeriodOne_fst, periodOnePotential_apply]
    rfl
  · simp only [weightedBaseToPair_snd, sobolevSourceWeightedPeriodOne_snd, periodOnePotential_apply]
    rfl

end NLS.ZakharovShabat
