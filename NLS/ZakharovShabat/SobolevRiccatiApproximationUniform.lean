import NLS.ZakharovShabat.SobolevRiccatiPhysicalBounds
import NLS.ZakharovShabat.NLSRiccatiTruncation

/-! # Uniform finite Riccati approximations

Truncations of order N <= s and the physical potential are bounded uniformly on original Hs balls, using their matching Fourier coefficients.
-/

noncomputable section
open Set Complex MeasureTheory NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- Finite Riccati approximations have a uniform inverse-frequency bound on
an original Hs ball, using only lower continuous densities. -/
theorem exists_uniform_nlsRiccatiApproximation_bound (s N : ℕ) (hNs : N ≤ s)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ f g : ℝ → ℂ,
      ContDiff ℝ ∞ f → ContDiff ℝ ∞ g →
      Function.Periodic f 1 → Function.Periodic g 1 →
      (∀ j, ab.1.val j = periodOneCoefficient f j) →
      (∀ j, ab.2.val j = periodOneCoefficient g j) →
      ∀ w : ℂ, ‖w‖ ≤ 1 → ∀ x : ℝ, ‖nlsRiccatiApproximation f g N w x‖ ≤ C*‖w‖ := by
  have hprev (k : Fin N) := exists_uniform_nlsRiccatiDensity_pointwise_bound
    s k.val (lt_of_lt_of_le k.isLt hNs) R hR
  choose C hC hc using hprev
  refine ⟨∑ k : Fin N, C k,Finset.sum_nonneg (fun k _ => hC k),?_⟩
  intro ab hab f g hf hg hpf hpg ha hb w hw x
  rw [nlsRiccatiApproximation,Finset.sum_range]
  apply (norm_sum_le _ _).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k _
  rw [norm_mul,norm_pow]
  apply mul_le_mul (hc k ab hab f g hf hg hpf hpg ha hb x) _ (by positivity) (hC k)
  rw [pow_succ]
  exact mul_le_of_le_one_left (norm_nonneg w) (pow_le_one₀ (norm_nonneg w) hw)

/-- The physical first potential is pointwise bounded uniformly on an Hs ball,
for s >= 1. The smooth functions are linked to the original coefficients. -/
theorem exists_uniform_first_potential_pointwise_bound (s : ℕ) (hs : 1 ≤ s)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ f g : ℝ → ℂ,
      ContDiff ℝ ∞ f → ContDiff ℝ ∞ g →
      Function.Periodic f 1 → Function.Periodic g 1 →
      (∀ j, ab.1.val j = periodOneCoefficient f j) →
      (∀ j, ab.2.val j = periodOneCoefficient g j) →
      ∀ x : ℝ, ‖f x‖ ≤ A := by
  obtain ⟨A,hA,h⟩ := exists_uniform_nlsRiccatiDensity_pointwise_bound s 0 (by omega) R hR
  refine ⟨A,hA,?_⟩
  intro ab hab f g hf hg hpf hpg ha hb x
  have hswap : ‖(ab.2,ab.1)‖ ≤ R := by simpa only [Prod.norm_def,max_comm] using hab
  simpa only [nlsRiccatiDensity_zero,Pi.neg_apply,norm_neg] using
    h (ab.2,ab.1) hswap g f hg hf hpg hpf hb ha x

end NLS.ZakharovShabat
