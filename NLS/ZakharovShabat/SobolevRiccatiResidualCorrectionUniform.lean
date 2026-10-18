import NLS.ZakharovShabat.NLSRiccatiResidualCorrection
import NLS.ZakharovShabat.SobolevRiccatiApproximationUniform

/-! # Uniform bounds for the corrected Riccati residual

The order-(N+1) correction is uniform on original Hs balls for N <= s, without an additional source derivative.
-/

noncomputable section
open Set Complex NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- After removing the actual leading density, the residual gains an
extra power uniformly on the original Hs ball, without extra derivatives. -/
theorem exists_uniform_nlsRiccatiResidual_correction_bound
    (s N : ℕ) (hs : 1 ≤ s) (hNs : N ≤ s) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ x : ℝ, ∀ w : ℂ, ‖w‖ ≤ 1 →
        ‖(nlsRiccatiResidualPolynomial a b N).eval₂ (Pi.evalRingHom (fun _ : ℝ => ℂ) x) w+
          nlsRiccatiDensity a b N x*w^N‖ ≤ C*‖w‖^(N+1) := by
  obtain ⟨A,hA,ha⟩ := exists_uniform_first_potential_pointwise_bound s hs R hR
  have hprev (k : Fin N) := exists_uniform_nlsRiccatiDensity_pointwise_bound
    s k.val (lt_of_lt_of_le k.isLt hNs) R hR
  choose U₀ hU₀ hu using hprev
  let U := ∑ k : Fin N, U₀ k
  have hU : 0 ≤ U := Finset.sum_nonneg (fun k _ => hU₀ k)
  refine ⟨∑ k ∈ Finset.range (2*N+3), A*(k+1)*U^2,
    Finset.sum_nonneg (fun k _ => by positivity),?_⟩
  intro ab hab a b hca hcb hpa hpb hfa hfb x w hw
  apply norm_nlsRiccatiResidual_correction_le a b N A U hA hU
    (ha ab hab a b hca hcb hpa hpb hfa hfb) _ x w hw
  intro j hj y
  exact (hu ⟨j,hj⟩ ab hab a b hca hcb hpa hpb hfa hfb y).trans
    (Finset.single_le_sum (fun k _ => hU₀ k) (Finset.mem_univ (⟨j,hj⟩ : Fin N)))

end NLS.ZakharovShabat
