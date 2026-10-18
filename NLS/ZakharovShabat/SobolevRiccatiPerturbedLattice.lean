import NLS.Fourier.PerturbedLatticeFourierL2
import NLS.ZakharovShabat.SobolevRiccatiPhysicalBounds

/-! # Uniform sampling of the highest Sobolev Riccati density

The top density samples have a uniform L2 bound, including N=s and H0, when the actual displacement sequence has bounded L2 norm.
-/

noncomputable section
open Set Complex MeasureTheory NLS.Fourier NLS.ComplexAnalysis
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- The actual top-density oscillatory integrals at square-summably
perturbed pi-lattice points form an L2 sequence uniformly on source balls. -/
theorem exists_uniform_sobolevRiccati_perturbed_lattice_bound
    (s N : ℕ) (hNs : N ≤ s) (R : ℝ) (hR : 0 ≤ R) (D : ℝ) (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ δ : NLS.Coeff 2, ‖δ‖ ≤ D → ∃ c : NLS.Coeff 2,
        (∀ n, c n = ∫ x in (0:ℝ)..1, nlsRiccatiDensity a b N x*
          exp (-2*I*((Real.pi:ℂ)*n+δ n)*x)) ∧ ‖c‖ ≤ C := by
  obtain ⟨K,hK,hbound⟩ := exists_uniform_sobolevRiccatiDensity_bound s N hNs R hR
  refine ⟨K+2*Real.exp (2*D)*K*D,by positivity,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb δ hδ
  let ρ := nlsRiccatiDensity a b N
  let c := WeightedCoeff.sobolevToL2 (Nat.cast_nonneg (s-N)) (sobolevRiccatiDensity s ab N hNs)
  have hc (n : ℤ) : c n = periodOneCoefficient ρ n := by
    simpa only [c,ρ,WeightedCoeff.sobolevToL2_apply] using
      sobolevRiccatiDensity_eq_classical_coefficients s ab a b ha hb hpa hpb hca hcb N hNs n
  have hρ : Continuous ρ := (contDiff_nlsRiccatiDensity a b ha hb N).continuous
  have hcNorm : ‖c‖ ≤ K := (WeightedCoeff.norm_sobolevToL2_le _ _).trans (hbound ab hab)
  have hL : (∫ x in (0:ℝ)..1, ‖ρ x‖) ≤ K := by
    have hi := integral_norm_le_sqrt_length_mul_L2 ρ 1 (by norm_num)
      (memLp_two_interval hρ 0 1 (by norm_num))
    simp only [Real.sqrt_one,one_mul] at hi
    rw [integral_norm_sq_eq_sobolevToL2_norm (s-N) (sobolevRiccatiDensity s ab N hNs) ρ hρ
      (sobolevRiccatiDensity_eq_classical_coefficients s ab a b ha hb hpa hpb hca hcb N hNs),
      Real.sqrt_sq (norm_nonneg _)] at hi
    exact hi.trans hcNorm
  obtain ⟨d,hd,hn⟩ := exists_perturbed_lattice_coefficients ρ hρ c δ hc D hδ
  refine ⟨d,hd,hn.trans ?_⟩
  gcongr

end NLS.ZakharovShabat
