import NLS.Articles.MKdVBelowL2.Theorem13
import NLS.ZakharovShabat.SourceActionPhaseFlow

/-! # The article's actual fourth-Hamiltonian frequency family for rotations

The coordinate rotation uses (2πn)^3+omega4star_n, with the verified physical
H₄ normalization and the Hamiltonian time orientation. Its continuity and
action dependence are proved from the constructed atlas on the entire real
source. Identification of the restricted source flow with mKdV remains a
separate diagonal and classical-solution obligation.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual weighted H₄ moment sum is constant on every original action
level set, at every finite source exponent greater than one. -/
theorem fourthFrequencyCandidate_eq_of_actions
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceRealActionLevelSet hp hp1 φ) (n : ℤ) :
    fourthFrequencyCandidate (fourthMomentChart hp hp1).atlas n ψ.val =
      fourthFrequencyCandidate (fourthMomentChart hp hp1).atlas n φ.val := by
  let C := fourthMomentChart hp hp1
  unfold fourthFrequencyCandidate
  congr 1
  apply tsum_congr
  intro k
  exact congrArg ((k:ℂ)*·) (C.atlas.moment_real_eq_of_actions C.atlas
    C.squared.toSourcePsiIsolatingComplexExtension C.squared.toSourcePsiIsolatingComplexExtension φ ψ h n k 2)

/-- The literal cubic-plus-normalized physical fourth frequency family,
with all continuity and action-invariance inputs discharged. -/
def fourthSourcePhaseFrequency (hp : p ≠ ⊤) (hp1 : 1 < p) : SourceActionFrequency hp hp1 where
  frequency φ n := (2*Real.pi*n)^3+(fourthFrequencyCandidate (fourthMomentChart hp hp1).atlas n φ.val).re
  continuous n := by
    apply continuous_iff_continuousAt.mpr
    intro φ
    exact continuousAt_const.add (Complex.continuous_re.continuousAt.comp
      (((fourthMomentChart hp hp1).candidate_analytic n φ.val
        ((fourthMomentChart hp hp1).real_subset φ.property)).continuousAt.comp
          (realTypeSourceSubmodule p).subtypeL.continuous.continuousAt))
  invariant φ ψ h := by
    funext n
    rw [fourthFrequencyCandidate_eq_of_actions hp hp1 φ ψ h n]

/-- The real family has the exact complex physical normalization at every
index, including zero and every closed selected action. -/
theorem fourthSourcePhaseFrequency_complex
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) (n : ℤ) :
    ((fourthSourcePhaseFrequency hp hp1).frequency φ n : ℂ) =
      (2*(n:ℂ)*Real.pi)^3+fourthFrequencyCandidate (fourthMomentChart hp hp1).atlas n φ.val := by
  have hreal : ((fourthFrequencyCandidate (fourthMomentChart hp hp1).atlas n φ.val).re : ℂ) =
      fourthFrequencyCandidate (fourthMomentChart hp hp1).atlas n φ.val := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using (fourthFrequencyCandidate_im_eq_zero
        (fourthMomentChart hp hp1).atlas (fourthMomentChart hp hp1).squared.toSourcePsiIsolatingComplexExtension φ n).symm
  change (((2*Real.pi*n)^3+(fourthFrequencyCandidate (fourthMomentChart hp hp1).atlas n φ.val).re : ℝ):ℂ) = _
  rw [Complex.ofReal_add,hreal]
  push_cast
  ring

/-- On the original H^(3/2) domain this rotation frequency is the independent
physical H₄ action derivative minus the actual momentum and mass shifts. -/
theorem fourthSourcePhaseFrequency_eq_physical_derivative
    (a : NativeFourthSobolevSource) (n : ℤ) :
    ((fourthSourcePhaseFrequency (p := 2) (by simp) (by norm_num)).frequency
      (originalWeightedRealSource fourthSobolevSpectralWeight a) n : ℂ) =
      (originalBirkhoffChart (p := 2) (by simp) (by norm_num)).data.complex.sobolevFourthFrequency a n-
        6*sourceFourthSobolevMomentum a-(12*Real.pi:ℂ)*n*sourceFourthSobolevMass a := by
  rw [fourthSourcePhaseFrequency_complex]
  have hc : fourthFrequencyCandidate (fourthMomentChart (p := 2) (by simp) (by norm_num)).atlas n
      (originalWeightedRealSource fourthSobolevSpectralWeight a).val = physicalSobolevFourthFrequency a n := by
    have h := physicalFourthFrequencyCandidate_eq_sobolev_actionDerivative a n
    unfold physicalFourthFrequencyCandidate at h
    rw [fourthSobolevPhysicalInput_coefficients] at h
    exact h
  rw [hc]
  unfold physicalSobolevFourthFrequency SourceBirkhoffMapComplexData.normalizedSobolevFourthFrequency
  ring

end NLS.Articles.MKdVBelowL2
