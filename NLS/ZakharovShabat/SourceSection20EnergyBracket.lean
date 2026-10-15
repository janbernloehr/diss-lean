import NLS.ZakharovShabat.SourceSection20Original
import NLS.ZakharovShabat.SourceFiniteGapAngleEnergy

/-!
# Section 20's original physical energy bracket on finite-gap sources

The angle, moment roots, and Birkhoff family are the original ones retained
by the Section 20 package. The actual H¹ energy derivative and its original
Poisson bivector give the same frequency, with mass and dispersion restored.
The extension to arbitrary complex H¹ sources is a separate assertion.
-/
noncomputable section
open Set NLS.Poisson
namespace NLS.ZakharovShabat.SourceSection20Data
variable {W₀ W V Wa B U : Set (CoeffPair 2)}
  {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
  {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
  {A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s}
  (Q : SourceSection20Data D A B U)
include Q

/-- The actual H¹ directional bracket recovers the original moment
frequency, including its physical mass and free dispersion. -/
theorem finiteGap_energy_bracket
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem _) n ≠ 0) :
    -(fderiv ℂ periodOneSobolevHamiltonian (sourceFiniteGapSobolevPair (by simp) (by norm_num) φ hf)
      (D.complex.finiteGapThetaSobolevVector D.previous.original_theta_common_domain φ hf n hn)) =
      A.renormalizedFrequency n φ.val +
        4*sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 1+(2*(n : ℂ)*Real.pi)^2 := by
  have he := Q.physical_frequency D φ hf n
  rw [D.complex.finiteGapFrequencyAtExponent_two,SourceBirkhoffMapComplexData.finiteGapFrequency,
    dif_neg hn,D.complex.finiteGapOpenFrequency_eq_sobolev_energy_bracket
      D.previous.original_theta_common_domain φ hf n hn] at he
  change -(fderiv ℂ periodOneSobolevHamiltonian (sourceFiniteGapSobolevPair (by simp) (by norm_num) φ hf)
      (D.complex.finiteGapThetaSobolevVector D.previous.original_theta_common_domain φ hf n hn))-
      4*sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 1-(2*(n : ℂ)*Real.pi)^2 =
      A.renormalizedFrequency n φ.val at he
  linear_combination he

/-- One actual physical cotangent gives the original Poisson identity
simultaneously for every open selected gap. -/
theorem finiteGap_energy_cotangent
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    ∃ L : CoeffPair 2 →L[ℂ] ℂ,
      HasFDerivAt periodOneSobolevHamiltonian (L.comp sobolevSourceInclusion)
        (sourceFiniteGapSobolevPair (by simp) (by norm_num) φ hf) ∧
      ∀ (n : ℤ) (hn : canonicalPeriodicGap (by simp) (by norm_num)
        (periodOnePotential φ.val) (periodOnePotential_mem _) n ≠ 0),
        sourceBivector le_rfl (sourceAngularThetaDifferential (by simp) (by norm_num) n s φ.val) L =
          A.renormalizedFrequency n φ.val +
            4*sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 1+(2*(n : ℂ)*Real.pi)^2 := by
  obtain ⟨L,hL,he⟩ := D.complex.exists_finiteGap_energy_cotangent_bracket
    D.previous.original_theta_common_domain φ hf
  refine ⟨L,hL,?_⟩
  intro n hn
  rw [he n hn,D.complex.finiteGapOpenFrequency_eq_sobolev_energy_bracket
    D.previous.original_theta_common_domain φ hf n hn]
  exact Q.finiteGap_energy_bracket φ hf n hn

end NLS.ZakharovShabat.SourceSection20Data
