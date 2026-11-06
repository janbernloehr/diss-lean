import NLS.ZakharovShabat.PeriodOneSobolevFourthClassical
import NLS.ZakharovShabat.SourceFiniteGapHamiltonianReality
import NLS.ZakharovShabat.SourceWeightedFiniteGapDensity
import NLS.ZakharovShabat.SourceSection14WeightedMembership

/-! # Physical H₄ on the native real H^(3/2) source

The original weighted real source is transported coefficient-for-coefficient
to the physical fractional Hamiltonian. Its independently defined finite-gap
values and reality extend in the actual H^(3/2) topology.
-/
noncomputable section
set_option autoImplicit false
open Complex Set
open scoped ENNReal
namespace NLS.ZakharovShabat

private theorem fourthHilbertExponent_ne_top : (2:ℝ≥0∞) ≠ ⊤ := by simp
private theorem fourthHilbertExponent_one_lt : (1:ℝ≥0∞) < 2 := by norm_num

/-- Half-scale spectral weight gives the exact physical H^(3/2) coefficient norm. -/
def fourthSobolevSpectralWeight : SpectralWeight :=
  sourceSobolevSpectralWeight (3/2) (by norm_num)

/-- The full original real H^(3/2) source, with its native weighted pair norm. -/
abbrev NativeFourthSobolevSource :=
  weightedRealSourceSubmodule (p := 2) fourthSobolevSpectralWeight

/-- Coefficient-preserving scalar transport from the native spectral weight. -/
def fourthNativeFieldCLM :
    WeightedCoeff (sourceFrequencyWeight fourthSobolevSpectralWeight) 2 →L[ℂ] FourthSobolevField :=
  WeightedCoeff.inclusionCLM _ _ (by intro n; simp [fourthSobolevSpectralWeight])

@[simp] theorem fourthNativeFieldCLM_apply
    (a : WeightedCoeff (sourceFrequencyWeight fourthSobolevSpectralWeight) 2) (n : ℤ) :
    (fourthNativeFieldCLM a).val n = a.val n :=
  WeightedCoeff.inclusionCLM_apply _ _ _ a n

/-- The native real source and the physical H^(3/2) polynomial use the same raw coefficients. -/
def fourthNativeSourceCLM : NativeFourthSobolevSource →L[ℝ] FourthSobolevSource :=
  ((fourthNativeFieldCLM.restrictScalars ℝ).prodMap
    (fourthNativeFieldCLM.restrictScalars ℝ)).comp
      ((WithLp.prodContinuousLinearEquiv (2:ℝ≥0∞) ℝ _ _).toContinuousLinearMap.comp
        (weightedRealSourceSubmodule (p := 2) fourthSobolevSpectralWeight).subtypeL)

@[simp] theorem fourthNativeSourceCLM_fst (a : NativeFourthSobolevSource) (n : ℤ) :
    (fourthNativeSourceCLM a).1.val n =
      (originalWeightedRealSource fourthSobolevSpectralWeight a).val.fst n := by
  change (fourthNativeFieldCLM a.val.fst).val n = _
  rw [fourthNativeFieldCLM_apply,originalWeightedRealSource_fst]

@[simp] theorem fourthNativeSourceCLM_snd (a : NativeFourthSobolevSource) (n : ℤ) :
    (fourthNativeSourceCLM a).2.val n =
      (originalWeightedRealSource fourthSobolevSpectralWeight a).val.snd n := by
  change (fourthNativeFieldCLM a.val.snd).val n = _
  rw [fourthNativeFieldCLM_apply,originalWeightedRealSource_snd]

/-- The physical H₄ Hamiltonian on the full original real fractional Sobolev source. -/
def sourceSobolevFourthHamiltonian (a : NativeFourthSobolevSource) : ℂ :=
  periodOneSobolevFourthHamiltonian (fourthNativeSourceCLM a)

/-- Real analytic dependence holds in the original H^(3/2) topology. -/
theorem analyticOnNhd_sourceSobolevFourthHamiltonian :
    AnalyticOnNhd ℝ sourceSobolevFourthHamiltonian univ := by
  intro a _
  exact (analyticAt_periodOneSobolevFourthHamiltonian _).restrictScalars.comp
    (fourthNativeSourceCLM.analyticAt a)

/-- At every real finite-gap source this is the independently defined physical H₄. -/
theorem sourceSobolevFourthHamiltonian_eq_finiteGap
    (a : NativeFourthSobolevSource)
    (hf : originalWeightedRealSource fourthSobolevSpectralWeight a ∈
      sourceFiniteGapLocus fourthHilbertExponent_ne_top fourthHilbertExponent_one_lt) :
    sourceSobolevFourthHamiltonian a = sourceFiniteGapNLSHamiltonian fourthHilbertExponent_ne_top fourthHilbertExponent_one_lt
      (originalWeightedRealSource fourthSobolevSpectralWeight a) hf 4 := by
  let φ := originalWeightedRealSource fourthSobolevSpectralWeight a
  exact periodOneSobolevFourthHamiltonian_eq_classical (fourthNativeSourceCLM a)
    (sourceFiniteGapPhysicalPair fourthHilbertExponent_ne_top fourthHilbertExponent_one_lt φ hf).1
    (sourceFiniteGapPhysicalPair fourthHilbertExponent_ne_top fourthHilbertExponent_one_lt φ hf).2
    (contDiff_sourceFiniteGapPhysicalPair fourthHilbertExponent_ne_top fourthHilbertExponent_one_lt φ hf).1
    (contDiff_sourceFiniteGapPhysicalPair fourthHilbertExponent_ne_top fourthHilbertExponent_one_lt φ hf).2
    (periodic_sourceFiniteGapPhysicalPair fourthHilbertExponent_ne_top fourthHilbertExponent_one_lt φ hf).1
    (periodic_sourceFiniteGapPhysicalPair fourthHilbertExponent_ne_top fourthHilbertExponent_one_lt φ hf).2
    (fun n => (fourthNativeSourceCLM_fst a n).trans
      (periodOneCoefficient_sourceFiniteGapPhysicalPair fourthHilbertExponent_ne_top fourthHilbertExponent_one_lt φ hf n).1.symm)
    (fun n => (fourthNativeSourceCLM_snd a n).trans
      (periodOneCoefficient_sourceFiniteGapPhysicalPair fourthHilbertExponent_ne_top fourthHilbertExponent_one_lt φ hf n).2.symm)

/-- Continuity in the full native fractional norm. -/
theorem continuous_sourceSobolevFourthHamiltonian : Continuous sourceSobolevFourthHamiltonian :=
  continuous_iff_continuousAt.mpr fun b =>
    (analyticOnNhd_sourceSobolevFourthHamiltonian b (mem_univ _)).continuousAt

private theorem im_eq_zero_of_finiteGap_value
    (z : ℂ) (φ : realTypeSourceSubmodule 2)
    (hf : φ ∈ sourceFiniteGapLocus fourthHilbertExponent_ne_top fourthHilbertExponent_one_lt)
    (hz : z = sourceFiniteGapNLSHamiltonian fourthHilbertExponent_ne_top fourthHilbertExponent_one_lt φ hf 4) : z.im = 0 :=
  (congrArg Complex.im hz).trans
    (sourceFiniteGapNLSHamiltonian_im_eq_zero fourthHilbertExponent_ne_top fourthHilbertExponent_one_lt φ hf 4)

/-- Finite-gap reality for the native physical Hamiltonian. -/
theorem sourceSobolevFourthHamiltonian_finiteGap_im_eq_zero
    (a : NativeFourthSobolevSource)
    (hf : originalWeightedRealSource fourthSobolevSpectralWeight a ∈
      sourceFiniteGapLocus fourthHilbertExponent_ne_top fourthHilbertExponent_one_lt) :
    (sourceSobolevFourthHamiltonian a).im = 0 :=
  im_eq_zero_of_finiteGap_value (sourceSobolevFourthHamiltonian a)
    (originalWeightedRealSource fourthSobolevSpectralWeight a) hf
    (sourceSobolevFourthHamiltonian_eq_finiteGap a hf)

/-- Actual spectral finite-gap sources are dense in the original fractional topology. -/
theorem dense_nativeFourthSobolev_finiteGap :
    Dense {a : NativeFourthSobolevSource |
      originalWeightedRealSource fourthSobolevSpectralWeight a ∈
        sourceFiniteGapLocus fourthHilbertExponent_ne_top fourthHilbertExponent_one_lt} :=
  dense_weightedRealSource_finiteGap fourthHilbertExponent_ne_top fourthHilbertExponent_one_lt fourthSobolevSpectralWeight

/-- H₄ is real on every original real H^(3/2) source, including infinitely many open gaps. -/
theorem sourceSobolevFourthHamiltonian_im_eq_zero (a : NativeFourthSobolevSource) :
    (sourceSobolevFourthHamiltonian a).im = 0 :=
  im_eq_zero_of_continuous_weighted_finiteGap fourthHilbertExponent_ne_top fourthHilbertExponent_one_lt
    fourthSobolevSpectralWeight sourceSobolevFourthHamiltonian
    continuous_sourceSobolevFourthHamiltonian sourceSobolevFourthHamiltonian_finiteGap_im_eq_zero a

/-- H₄ with its genuine real scalar codomain. -/
def sourceRealSobolevFourthHamiltonian (a : NativeFourthSobolevSource) : ℝ :=
  (sourceSobolevFourthHamiltonian a).re

/-- The real scalar value is exactly the physical complex construction. -/
theorem sourceRealSobolevFourthHamiltonian_complex (a : NativeFourthSobolevSource) :
    (sourceRealSobolevFourthHamiltonian a : ℂ) = sourceSobolevFourthHamiltonian a := by
  apply Complex.ext
  · rfl
  · simpa using (sourceSobolevFourthHamiltonian_im_eq_zero a).symm

/-- Real analyticity into the actual real scalar target. -/
theorem analyticOnNhd_sourceRealSobolevFourthHamiltonian :
    AnalyticOnNhd ℝ sourceRealSobolevFourthHamiltonian univ := by
  intro a ha
  exact (Complex.reCLM.analyticAt _).comp (analyticOnNhd_sourceSobolevFourthHamiltonian a ha)

end NLS.ZakharovShabat
