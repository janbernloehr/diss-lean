import NLS.KdV.ClassicalNormalizedResolventExterior
import NLS.ZakharovShabat.SingleSpectralProductRatioExterior

/-! # Exterior normalization of the actual entire product quotient -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
namespace ClassicalAllContourPeriodData
variable {N : ℕ} {V : Set (NLS.LinearVolterra.Curve ℂ)} {A : ℝ}
variable (D : ClassicalAllContourPeriodData N V A)
include D

/-- An exact resolvent formula for the ordinary quotient on the
zero-free exterior. All factors belong to the actual selected families. -/
theorem normalizedProductQuotient_eq_signed_products
    (R : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2)) (n : ℕ+)
    (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) (ht : t ∈ classicalHillCandidateDomain V)
    (haux : ∀ j ≤ (0 : ℤ), t.1 j = 0) (z : ℂ)
    (hav : ∀ k : ℕ+, z^2 ≠ classicalHillUniformCriticalPoint N k t.2)
    (heta : entireSingleSpectralProduct (classicalHillSignedCandidate N t) z ≠ 0) :
    classicalHillNormalizedProductQuotient N R n t (z^2) =
      (entireSingleSpectralProduct (classicalHillSignedCritical N t.2) z/
        entireSingleSpectralProduct (classicalHillSignedCandidate N t) z)*
      ((n : ℂ)⁻¹*((z^2-classicalHillCandidateEnergy N n t)*
        ∑' k : ℕ+, (k : ℂ)*(R t.2 (lp.single 2 (n : ℤ) 1)) (k : ℤ)/
          (z^2-classicalHillUniformCriticalPoint N k t.2))) := by
  have hlp := D.signedCandidate_displacement_memlp t ht.2
  have hzero := classicalHillSignedCandidate_zero N t
  have hneg := classicalHillSignedCandidate_paired N t haux
  have hinj := D.signedCandidate_injective t ht
  have hfull : (2*z)*classicalHillCandidateEnergyProduct N t (z^2) =
      entireSingleSpectralProduct (classicalHillSignedCandidate N t) z :=
    pairedEnergyProduct_factor (by norm_num : (2 : ENNReal) ≠ ⊤) _ hlp hzero hneg z
  have hfactor : (z^2-classicalHillCandidateEnergy N n t)*classicalHillCandidateOmittedProduct N n t (z^2) =
      (2*(n : ℂ)*Real.pi)*classicalHillCandidateEnergyProduct N t (z^2) := by
    have hh := omittedPairedEnergyProduct_factor (by norm_num : (2 : ENNReal) ≠ ⊤)
      (by norm_num : 1 < (2 : ENNReal)) _ hlp hzero hneg hinj n (z^2)
    have he : (classicalHillSignedCandidate N t (n : ℤ))^2 = classicalHillCandidateEnergy N n t := by
      rw [classicalHillSignedCandidate_positive N t haux]
      rfl
    simpa only [he] using! hh
  have hG : classicalHillCandidateEnergyProduct N t (z^2) ≠ 0 := by
    intro he
    apply heta
    rw [← hfull,he,mul_zero]
  have hz : z ≠ 0 := by
    intro he
    apply heta
    rw [← hfull,he,mul_zero,zero_mul]
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast n.ne_zero
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hB : classicalHillCandidateOmittedProduct N n t (z^2) ≠ 0 := by
    intro he
    rw [he,mul_zero] at hfactor
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hn) hpi) hG hfactor.symm
  have hdiff : z^2-classicalHillCandidateEnergy N n t =
      (2*(n : ℂ)*Real.pi)*classicalHillCandidateEnergyProduct N t (z^2)/
        classicalHillCandidateOmittedProduct N n t (z^2) := (eq_div_iff hB).mpr hfactor
  have hrat : entireSingleSpectralProduct (classicalHillSignedCritical N t.2) z/
      entireSingleSpectralProduct (classicalHillSignedCandidate N t) z =
      deriv (classicalHillDiscriminant t.2) (z^2)/classicalHillCandidateEnergyProduct N t (z^2) := by
    rw [(D.signedCritical_product t.2 ht.2).2.2.1 z,← hfull]
    field_simp
  have hquot : classicalHillNormalizedProductQuotient N R n t (z^2) =
      classicalHillNormalizedNumerator N R n (z^2,t.2)/classicalHillCandidateOmittedProduct N n t (z^2) :=
    filledSimpleQuotient_eq_div hB
  rw [hquot,D.normalizedNumerator_resolvent R n t.2 ht.2 (z^2) hav,hrat,hdiff]
  field_simp

/-- The entire quotient has the actual residue sum as its exterior limit.
The statement uses the same constructed inverse and selected roots. -/
theorem tendsto_normalizedProductQuotient_of_separated
    {T : Type*} {l : Filter T}
    (R Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2)) (n : ℕ+)
    (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) (ht : t ∈ classicalHillCandidateDomain V)
    (haux : ∀ j ≤ (0 : ℤ), t.1 j = 0)
    (hcompat : ∀ m j : ℤ,
      NLS.Coeff.positiveIndexWeight m^2*(R t.2 (lp.single 2 j 1)) m =
        NLS.Coeff.positiveIndexWeight j^2*(Q t.2 (lp.single 2 j 1)) m)
    (z : T → ℂ) (hz : Tendsto (fun i => ‖z i‖) l atTop)
    {r : ℝ} (hr : 0 < r) (hrpi : r ≤ Real.pi/4)
    (hsep : ∀ i (j : ℤ), r ≤ ‖z i-(Real.pi : ℂ)*j‖) :
    Tendsto (fun i => classicalHillNormalizedProductQuotient N R n t (z i^2)) l
      (𝓝 (classicalHillNormalizedLeadingCoefficient Q n t.2)) := by
  have hc := (D.signedCritical_product t.2 ht.2).2.1
  have he := D.signedCandidate_displacement_memlp t ht.2
  have hratio := tendsto_entireSingleSpectralProduct_ratio_of_separated
    (by norm_num : (2 : ENNReal) ≠ ⊤) _ _ hc he z hz hr hrpi hsep
  have heta := tendsto_entireSingleSpectralProduct_div_free_of_separated
    (by norm_num : (2 : ENNReal) ≠ ⊤) _ he z hz hr hrpi hsep
  have hu := D.tendsto_normalized_resolvent_leading_of_separated R Q t.2 ht.2 hcompat n
    (classicalHillCandidateEnergy N n t) z hz hr hrpi hsep
  have hlead : Tendsto (fun i => (n : ℂ)⁻¹*((z i^2-classicalHillCandidateEnergy N n t)*
      ∑' k : ℕ+, (k : ℂ)*(R t.2 (lp.single 2 (n : ℤ) 1)) (k : ℤ)/
        (z i^2-classicalHillUniformCriticalPoint N k t.2))) l
      (𝓝 (classicalHillNormalizedLeadingCoefficient Q n t.2)) := by
    rw [classicalHillNormalizedLeadingCoefficient_eq R Q t.2 hcompat n]
    exact hu.const_mul _
  have hlimit := hratio.mul hlead
  simp only [one_mul] at hlimit
  obtain ⟨K,hK⟩ := D.exists_threshold_normalized_resolvent_leading R Q t.2 ht.2 hcompat n
    (classicalHillCandidateEnergy N n t) hr hrpi (by norm_num : (0 : ℝ) < 1)
  apply hlimit.congr'
  filter_upwards [hz.eventually_ge_atTop K,heta.eventually_ne (by norm_num : (1 : ℂ) ≠ 0)] with i hi hne
  have hzero : entireSingleSpectralProduct (classicalHillSignedCandidate N t) (z i) ≠ 0 := by
    intro hbad
    exact hne (by rw [hbad,zero_div])
  exact (D.normalizedProductQuotient_eq_signed_products R n t ht haux (z i) (hK (z i) hi (hsep i)).1 hzero).symm

end ClassicalAllContourPeriodData
end NLS.KdV
