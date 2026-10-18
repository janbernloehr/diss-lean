import NLS.ZakharovShabat.SobolevRiccatiUniformBounds
import NLS.ZakharovShabat.SobolevRiccatiClassicalAgreement
import NLS.ZakharovShabat.SobolevRealJets
import NLS.Fourier.IntervalParseval
import NLS.ComplexAnalysis.OscillatoryIntegralL2

/-! # Physical bounds for the Sobolev Riccati hierarchy

Parseval and continuous synthesis transfer the source norm bounds to actual smooth periodic representatives, including an L2 bound for the highest residual derivative.
-/

noncomputable section
open Set Complex MeasureTheory NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- Parseval identifies the actual unit-period square integral with the unweighted Fourier norm. -/
theorem integral_norm_sq_eq_sobolevToL2_norm (s : ℕ) (a : ScalarSobolev s)
    (f : ℝ → ℂ) (hf : Continuous f) (ha : ∀ j, a.val j = periodOneCoefficient f j) :
    (∫ x in (0:ℝ)..1, ‖f x‖^2) = ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg s) a‖^2 := by
  have h := hasSum_sq_fourierCoeffOn (by norm_num : (0:ℝ) < 1)
    (memLp_two_interval hf 0 1 (by norm_num))
  have hc (n : ℤ) : fourierCoeffOn (by norm_num : (0:ℝ) < 1) f n =
      WeightedCoeff.sobolevToL2 (Nat.cast_nonneg s) a n := by
    rw [WeightedCoeff.sobolevToL2_apply]
    change periodOneCoefficient f n = a.val n
    exact (ha n).symm
  change HasSum (fun n => ‖fourierCoeffOn (by norm_num : (0:ℝ) < 1) f n‖^2) _ at h
  simp only [hc,sub_zero,inv_one,one_smul] at h
  have hJ : HasSum (fun n : ℤ => ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg s) a n‖^2)
      (‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg s) a‖^2) := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
      lp.hasSum_norm (by norm_num : 0 < (2:ℝ≥0∞).toReal) (WeightedCoeff.sobolevToL2 (Nat.cast_nonneg s) a)
  exact h.unique hJ

/-- Every available classical Riccati density has a uniform physical L2 bound
on a fixed original Hs ball, including its highest derivative. -/
theorem exists_uniform_nlsRiccatiDensity_L2_bound (s n : ℕ) (hn : n ≤ s)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ f g : ℝ → ℂ,
      ContDiff ℝ ∞ f → ContDiff ℝ ∞ g →
      Function.Periodic f 1 → Function.Periodic g 1 →
      (∀ j, ab.1.val j = periodOneCoefficient f j) →
      (∀ j, ab.2.val j = periodOneCoefficient g j) →
      Real.sqrt (∫ x in (0:ℝ)..1, ‖nlsRiccatiDensity f g n x‖^2) ≤ C := by
  obtain ⟨C,hC,h⟩ := exists_uniform_sobolevRiccatiDensity_bound s n hn R hR
  refine ⟨C,hC,?_⟩
  intro ab hab f g hf hg hpf hpg ha hb
  rw [integral_norm_sq_eq_sobolevToL2_norm (s-n) (sobolevRiccatiDensity s ab n hn)
    (nlsRiccatiDensity f g n) (contDiff_nlsRiccatiDensity f g hf hg n).continuous
    (sobolevRiccatiDensity_eq_classical_coefficients s ab f g hf hg hpf hpg ha hb n hn),
    Real.sqrt_sq (norm_nonneg _)]
  exact (WeightedCoeff.norm_sobolevToL2_le _ _).trans (h ab hab)

/-- Every lower classical density is uniformly bounded pointwise on the
whole real line by the original Hs source ball. -/
theorem exists_uniform_nlsRiccatiDensity_pointwise_bound (s n : ℕ) (hn : n < s)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ f g : ℝ → ℂ,
      ContDiff ℝ ∞ f → ContDiff ℝ ∞ g →
      Function.Periodic f 1 → Function.Periodic g 1 →
      (∀ j, ab.1.val j = periodOneCoefficient f j) →
      (∀ j, ab.2.val j = periodOneCoefficient g j) →
      ∀ x : ℝ, ‖nlsRiccatiDensity f g n x‖ ≤ C := by
  obtain ⟨C,hC,h⟩ := exists_uniform_sobolevRiccatiDensity_bound s n hn.le R hR
  let K := hierarchySobolevJetContinuous (s-n) 0 (Nat.sub_pos_of_lt hn)
  refine ⟨‖K‖*C,by positivity,?_⟩
  intro ab hab f g hf hg hpf hpg ha hb x
  have he : (fun y : ℝ => K (sobolevRiccatiDensity s ab n hn.le) (y : AddCircle (2:ℝ))) =
      nlsRiccatiDensity f g n := by
    simpa only [iteratedDeriv_zero] using hierarchySobolevJetContinuous_eq_classical
      (s-n) 0 (Nat.sub_pos_of_lt hn) (sobolevRiccatiDensity s ab n hn.le)
      (nlsRiccatiDensity f g n) (contDiff_nlsRiccatiDensity f g hf hg n)
      (periodic_nlsRiccatiDensity f g 1 hpf hpg n)
      (sobolevRiccatiDensity_eq_classical_coefficients s ab f g hf hg hpf hpg ha hb n hn.le)
  rw [← he]
  exact ((K (sobolevRiccatiDensity s ab n hn.le)).norm_coe_le_norm _).trans
    ((K.le_opNorm _).trans (mul_le_mul_of_nonneg_left (h ab hab) (norm_nonneg _)))

/-- The derivative of every lower classical density has a uniform L2 bound
on the original Hs ball, including the top derivative needed in the residual. -/
theorem exists_uniform_deriv_nlsRiccatiDensity_L2_bound (s n : ℕ) (hn : n < s)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ f g : ℝ → ℂ,
      ContDiff ℝ ∞ f → ContDiff ℝ ∞ g →
      Function.Periodic f 1 → Function.Periodic g 1 →
      (∀ j, ab.1.val j = periodOneCoefficient f j) →
      (∀ j, ab.2.val j = periodOneCoefficient g j) →
      Real.sqrt (∫ x in (0:ℝ)..1, ‖deriv (nlsRiccatiDensity f g n) x‖^2) ≤ C := by
  obtain ⟨C,hC,h⟩ := exists_uniform_sobolevRiccatiDensity_bound s n hn.le R hR
  let L := hierarchySobolevDerivative (s-n) 0 (by omega)
  refine ⟨‖L‖*C,by positivity,?_⟩
  intro ab hab f g hf hg hpf hpg ha hb
  let c := L (sobolevRiccatiDensity s ab n hn.le)
  have hd := contDiff_nlsRiccatiDensity f g hf hg n
  have hp := periodic_nlsRiccatiDensity f g 1 hpf hpg n
  have hc (j : ℤ) : c.val j = periodOneCoefficient (deriv (nlsRiccatiDensity f g n)) j := by
    simp only [c,L,hierarchySobolevDerivative_apply,
      sobolevRiccatiDensity_eq_classical_coefficients s ab f g hf hg hpf hpg ha hb n hn.le,
      periodOneCoefficient_deriv_of_smooth_periodic _ hd hp]
  rw [integral_norm_sq_eq_sobolevToL2_norm 0 c _
    (contDiff_infty_iff_deriv.mp hd).2.continuous hc,Real.sqrt_sq (norm_nonneg _)]
  exact (WeightedCoeff.norm_sobolevToL2_le _ c).trans
    ((L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (h ab hab) (norm_nonneg _)))

end NLS.ZakharovShabat
