import NLS.Fourier.WeightedLatticeFourierDifference
import NLS.ZakharovShabat.SobolevRiccatiPerturbedLattice

/-! # Weighted sampling errors of the actual Riccati hierarchy

The error bounds hold uniformly on original Sobolev balls through the highest order N=s, using smooth periodic representatives with exact original coefficients.
-/

noncomputable section
open Set Complex MeasureTheory NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- The actual Riccati sampling error inherits any weighted supremum
budget on the displacement, uniformly on the original Sobolev ball.
This includes the top density N=s and the H0 endpoint. -/
theorem exists_uniform_sobolevRiccati_weighted_sampling_error_bound
    (s N : ℕ) (hNs : N ≤ s) (R : ℝ) (hR : 0 ≤ R)
    (D M : ℝ) (hM : 0 ≤ M) (w : Weight) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ δ : NLS.Coeff ⊤, ‖δ‖ ≤ D → (∀ n, w n*‖δ n‖ ≤ M) →
      ∃ e : WeightedCoeff w 2,
        (∀ n, e.val n = (∫ x in (0:ℝ)..1, nlsRiccatiDensity a b N x*
          exp (-2*I*((Real.pi:ℂ)*n+δ n)*x))-(sobolevRiccatiDensity s ab N hNs).val n) ∧
        ‖e‖ ≤ C := by
  obtain ⟨K,hK,hbound⟩ := exists_uniform_sobolevRiccatiDensity_bound s N hNs R hR
  refine ⟨M*((2*Real.exp (2*D))*K),by positivity,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb δ hδ hδw
  let ρ := nlsRiccatiDensity a b N
  have hρ : Continuous ρ := (contDiff_nlsRiccatiDensity a b ha hb N).continuous
  let c := WeightedCoeff.sobolevToL2 (Nat.cast_nonneg (s-N)) (sobolevRiccatiDensity s ab N hNs)
  have hc (n : ℤ) : c n = periodOneCoefficient ρ n := by
    simpa only [c,ρ,WeightedCoeff.sobolevToL2_apply] using
      sobolevRiccatiDensity_eq_classical_coefficients s ab a b ha hb hpa hpb hca hcb N hNs n
  have hcNorm : ‖c‖ ≤ K := (WeightedCoeff.norm_sobolevToL2_le _ _).trans (hbound ab hab)
  have hrealization : unitIntervalMemLpCoefficients ρ (memLp_two_interval hρ 0 1 (by norm_num)) = c := by
    ext n
    rw [unitIntervalMemLpCoefficients_eq_periodOneCoefficient]
    exact (hc n).symm
  obtain ⟨e,he,hn⟩ := exists_weighted_lattice_fourier_difference ρ hρ δ w M hM hδw
  refine ⟨e,?_,?_⟩
  · intro n
    rw [he n,← hc n]
    simp only [c,ρ,WeightedCoeff.sobolevToL2_apply]
  · rw [hrealization] at hn
    apply hn.trans
    gcongr

end NLS.ZakharovShabat
