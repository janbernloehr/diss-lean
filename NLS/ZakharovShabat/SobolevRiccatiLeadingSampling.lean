import NLS.ZakharovShabat.SobolevRiccatiSmoothingUniform
import NLS.ZakharovShabat.SobolevRiccatiWeightedSampling

/-! # The original leading derivative in Riccati samples

Actual perturbed samples minus the leading Fourier derivative form a uniformly bounded H1 sequence under an inverse-index displacement budget.
-/

noncomputable section
open Set Complex MeasureTheory NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- The actual sampled density differs from the original leading Fourier
derivative by an H1 sequence, uniformly on original Sobolev balls and
inverse-index bounded complex displacements, including N=s and H0. -/
theorem exists_uniform_sobolevRiccati_leading_sampling_error_bound
    (s N : ℕ) (hNs : N ≤ s) (R : ℝ) (hR : 0 ≤ R) (D M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ab : SobolevSource s, ‖ab‖ ≤ R →
      ∀ a b : ℝ → ℂ, ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ δ : NLS.Coeff ⊤, ‖δ‖ ≤ D →
      (∀ n : ℤ, (1+|(n:ℝ)|)*‖δ n‖ ≤ M) →
      ∃ e : WeightedCoeff (Weight.sobolev 1) 2,
        (∀ n, e.val n = (∫ x in (0:ℝ)..1, nlsRiccatiDensity a b N x*
          exp (-2*I*((Real.pi:ℂ)*n+δ n)*x))+(2*I*(Real.pi:ℂ)*n)^N*ab.2.val n) ∧ ‖e‖ ≤ C := by
  obtain ⟨K,hK,h⟩ := exists_uniform_sobolevRiccati_weighted_sampling_error_bound
    s N hNs R hR D M hM (Weight.sobolev 1)
  obtain ⟨L,hL,hrem⟩ := exists_uniform_sobolevRiccatiSmoothingRemainder_bound s N hNs R hR
  refine ⟨K+L,by positivity,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb δ hδD hδM
  obtain ⟨e,he,hn⟩ := h ab hab a b ha hb hpa hpb hca hcb δ hδD (by
    intro n; simpa only [Weight.sobolev_apply,Real.rpow_one] using hδM n)
  let q : WeightedCoeff (Weight.sobolev 1) 2 := WeightedCoeff.sobolevInclusion
    (show (1:ℝ) ≤ (s-N+1:ℕ) by exact_mod_cast (show 1 ≤ s-N+1 by omega))
    (sobolevRiccatiSmoothingRemainder s ab N hNs)
  have hq : ‖q‖ ≤ L := (WeightedCoeff.norm_sobolevInclusion_le _ _).trans (hrem ab hab)
  refine ⟨e+q,?_,(norm_add_le _ _).trans (add_le_add hn hq)⟩
  intro n
  simp only [WeightedCoeff.add_val,q,WeightedCoeff.sobolevInclusion_apply,
    sobolevRiccatiSmoothingRemainder_apply,he]
  ring

end NLS.ZakharovShabat
