import NLS.ZakharovShabat.SourceSobolevFourthActionDifferential
import NLS.ZakharovShabat.SourceWeightedHolomorphicRealGerm

/-! # The full complex physical H₄ cotangent at finite gaps

The real native chain rule determines the entire complex weighted cotangent.
It is the restriction of a bounded original Hilbert cotangent, with its
coefficients given by the independent physical H₄ action derivatives.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- The real physical source derivative is the restriction of its full
independently defined complex fractional derivative. -/
theorem sourceComplexSobolevFourthHamiltonian_fderiv_real
    (a h : NativeFourthSobolevSource) :
    fderiv ℂ sourceComplexSobolevFourthHamiltonian a.val h.val =
      fderiv ℝ sourceSobolevFourthHamiltonian a h := by
  have hd := ((analyticAt_sourceComplexSobolevFourthHamiltonian a.val).differentiableAt.hasFDerivAt.restrictScalars ℝ).comp a
    (weightedRealSourceSubmodule (p := 2) fourthSobolevSpectralWeight).subtypeL.hasFDerivAt
  change HasFDerivAt sourceSobolevFourthHamiltonian _ a at hd
  exact (congrArg (fun L => L h) hd.fderiv).symm

/-- At a source with finite action-cotangent support, the entire complex
physical H₄ cotangent is the restricted original finite frequency sum. -/
theorem sourceComplexSobolevFourthHamiltonian_fderiv_eq_finite_sum
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a : NativeFourthSobolevSource) (S : Finset ℤ)
    (hS : ∀ n ∉ S, fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n)
      (originalWeightedRealSource fourthSobolevSpectralWeight a).val = 0) :
    fderiv ℂ sourceComplexSobolevFourthHamiltonian a.val =
      (∑ n ∈ S, D.sobolevFourthFrequency a n •
        fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n)
          (originalWeightedRealSource fourthSobolevSpectralWeight a).val).comp
            (originalWeightedSourceCLM fourthSobolevSpectralWeight) := by
  apply weightedSourceCLM_ext_real (by simp) fourthSobolevSpectralWeight
  intro h
  rw [sourceComplexSobolevFourthHamiltonian_fderiv_real,
    D.sourceSobolevFourthHamiltonian_fderiv_eq_finite_sum a S hS h]
  simp only [ContinuousLinearMap.comp_apply,sum_apply,smul_apply,smul_eq_mul,
    originalWeightedSourceCLM_real]

/-- Every actual finite-gap native source has an original bounded Hilbert
cotangent whose full fractional restriction is the physical H₄ derivative. -/
theorem exists_sourceSobolevFourth_finiteGap_physical_cotangent
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a : NativeFourthSobolevSource)
    (hf : originalWeightedRealSource fourthSobolevSpectralWeight a ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    ∃ L : CoeffPair 2 →L[ℂ] ℂ,
      HasFDerivAt sourceComplexSobolevFourthHamiltonian
        (L.comp (originalWeightedSourceCLM fourthSobolevSpectralWeight)) a.val := by
  obtain ⟨S,hS⟩ := exists_sourceComplexAction_fderiv_support (by simp) (by norm_num)
    (originalWeightedRealSource fourthSobolevSpectralWeight a) hf
  exact ⟨_,D.sourceComplexSobolevFourthHamiltonian_fderiv_eq_finite_sum a S hS ▸
    (analyticAt_sourceComplexSobolevFourthHamiltonian a.val).differentiableAt.hasFDerivAt⟩

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
