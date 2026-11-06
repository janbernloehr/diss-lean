import NLS.Articles.MKdVBelowL2.PhysicalFourthFrequencyReality
import NLS.ZakharovShabat.SourceSobolevFourthMomentIdentification

/-! # Full original-domain physical adapter for the H₄ extension

The fixed article family supplies actual Hamiltonian action derivatives on
every original H^(3/2) source. Their normalized values equal the previously
constructed candidate, not merely its finite-gap values. Every finite real
weighted target retains this identity, including closed actions.
-/
noncomputable section
set_option autoImplicit false
open Set
open scoped ENNReal
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat

/-- The original fractional real source as its actual period-one distributions. -/
def fourthSobolevPhysicalInput (a : NativeFourthSobolevSource) : PhysicalRealInput 2 :=
  (physicalRealCoefficientsCL (p := 2)).symm (originalWeightedRealSource fourthSobolevSpectralWeight a)

/-- The adapter preserves both original raw Fourier coefficient sequences. -/
theorem fourthSobolevPhysicalInput_coefficients (a : NativeFourthSobolevSource) :
    physicalCoefficients (fourthSobolevPhysicalInput a).val =
      (originalWeightedRealSource fourthSobolevSpectralWeight a).val := by
  rw [← physicalRealCoefficientsCL_val]
  exact congrArg Subtype.val ((physicalRealCoefficientsCL (p := 2)).apply_symm_apply _)

/-- The original-domain normalized frequency is an independent physical H₄
action derivative in the same accepted Hilbert Birkhoff family as Theorem 1.2. -/
def physicalSobolevFourthFrequency (a : NativeFourthSobolevSource) (n : ℤ) : ℂ :=
  (originalBirkhoffChart (p := 2) (by simp) (by norm_num)).data.complex.normalizedSobolevFourthFrequency a n

/-- The constructed moment candidate agrees with the actual physical H₄
action derivative throughout its original domain, including closed actions. -/
theorem physicalFourthFrequencyCandidate_eq_sobolev_actionDerivative
    (a : NativeFourthSobolevSource) (n : ℤ) :
    physicalFourthFrequencyCandidate (p := 2) (by simp) (by norm_num) n
      (fourthSobolevPhysicalInput a).val = physicalSobolevFourthFrequency a n := by
  let C := fourthMomentChart (p := 2) (by simp) (by norm_num)
  have h := (originalBirkhoffChart (p := 2) (by simp) (by norm_num)).data.complex.normalizedSobolevFourthFrequency_eq_moments
    C.atlas C.squared.toSourcePsiNormalizedComplexExtension C.domain C.real_subset C.candidate_analytic a n
  unfold physicalFourthFrequencyCandidate
  rw [fourthSobolevPhysicalInput_coefficients]
  exact h.symm

/-- The physical normalized frequency is real at every original fractional
source and index, without a finite-gap or noncollapsed-gap hypothesis. -/
theorem physicalSobolevFourthFrequency_im_eq_zero (a : NativeFourthSobolevSource) (n : ℤ) :
    (physicalSobolevFourthFrequency a n).im = 0 := by
  rw [← physicalFourthFrequencyCandidate_eq_sobolev_actionDerivative]
  exact physicalFourthFrequencyCandidate_im_eq_zero (by simp) (by norm_num) (fourthSobolevPhysicalInput a) n

/-- The genuine real weighted extension recovers every original physical
H₄ derivative, in every finite Hilbert target r>1. -/
theorem physicalRealFourthFrequencySequence_eq_sobolev_actionDerivative
    (r : ℝ≥0∞) [Fact (1 ≤ r)] (hr : r ≠ ⊤) (hr1 : 1 < r)
    (a : NativeFourthSobolevSource) (n : ℤ) :
    (physicalRealFourthFrequencySequence (p := 2) (by simp) (by norm_num) r
      (fourthSobolevPhysicalInput a)).val.val n = physicalSobolevFourthFrequency a n := by
  rw [(physicalRealFourthFrequencySequence_hilbert r hr hr1).2,
    physicalFourthFrequencyCandidate_eq_sobolev_actionDerivative]

/-- Every exponent extension has the same original-domain physical value
whenever the input represents the same two period-one distributions. -/
theorem physicalFourthFrequencyCandidate_eq_sobolev_of_same_distributions
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p)
    (u : PhysicalRealInput p) (a : NativeFourthSobolevSource)
    (h : u.val.1.val = (fourthSobolevPhysicalInput a).val.1.val ∧
      u.val.2.val = (fourthSobolevPhysicalInput a).val.2.val) (n : ℤ) :
    physicalFourthFrequencyCandidate hp hp1 n u.val = physicalSobolevFourthFrequency a n :=
  (physicalFourthFrequencyCandidate_eq_of_same_distributions hp hp1 (by simp) (by norm_num)
    u (fourthSobolevPhysicalInput a) h n).trans
      (physicalFourthFrequencyCandidate_eq_sobolev_actionDerivative a n)

end NLS.Articles.MKdVBelowL2
