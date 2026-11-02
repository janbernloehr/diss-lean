import NLS.Articles.KdVPseudomeasures.SpectralAdaptedFourier
import NLS.ComplexAnalysis.NearIdentityBallInverse

/-! The actual adapted Fourier map has a weighted analytic inverse, with
one cutoff before the weight, the source and the target. -/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue NLS.KdV
open NLS.ComplexAnalysis

/-- The complex analytic inverse and quantitative conclusions of Proposition2.18
for the actual physical adapted Fourier map, in every exact original weight.
The common cutoff precedes both weights and potentials. Real-type symmetry is
a separate assertion, not inferred from complex analyticity. -/
theorem source_uniform_adaptedFourier_inverse (r : ℝ) (hr : AdmissiblePredualOrder r)
    (m : ℝ) (hm : 0 < m) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ w : SpectralWeight,
      AnalyticOnNhd ℂ (sourceWeightedAdaptedFourier w r hr N) (ball 0 (2*m)) ∧
      (∀ q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤, ‖q‖ ≤ m →
        ‖fderiv ℂ (sourceWeightedAdaptedFourier w r hr N) q-
          ContinuousLinearMap.id ℂ _‖ ≤ (1/16 : ℝ) ∧
        (1/2 : ℝ)*‖q‖ ≤ ‖sourceWeightedAdaptedFourier w r hr N q‖ ∧
          ‖sourceWeightedAdaptedFourier w r hr N q‖ ≤ 2*‖q‖) ∧
      ∃ g : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤ →
          PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤,
        AnalyticOnNhd ℂ g (ball 0 (3*m/4)) ∧
        Set.InjOn (sourceWeightedAdaptedFourier w r hr N) (closedBall 0 m) ∧
        (∀ y, ‖y‖ ≤ 3*m/4 → g y ∈ ball 0 m ∧ sourceWeightedAdaptedFourier w r hr N (g y) = y) ∧
        (∀ q, ‖q‖ ≤ m → ‖sourceWeightedAdaptedFourier w r hr N q‖ ≤ 3*m/4 →
          g (sourceWeightedAdaptedFourier w r hr N q) = q) ∧
        ∀ y, ‖y‖ ≤ m/2 →
          (g y).val (mode 0) = y.val (mode 0) ∧
          (IsPeriodicDistribution 1 (g y).val.toTempered ↔ IsPeriodicDistribution 1 y.val.toTempered) := by
  obtain ⟨N, hN, hcut, hmap⟩ := source_uniform_adaptedFourier r hr (2*m) (by positivity)
  refine ⟨N, hN, fun w => ?_⟩
  let : CompleteSpace (PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤) :=
    PeriodicFourierLebesgue.completeSpace _ _ (w.hasTemperedInverse_negativeSobolev r)
  obtain ⟨hf, hspec⟩ := hmap w
  have hb (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤)
      (hq : q ∈ ball 0 (2*m)) : ‖sourceWeightedAdaptedFourier w r hr N q-q‖ ≤ m/32 := by
    have hh := (hspec q (mem_ball_zero_iff.mp hq).le).2
    linarith
  refine ⟨hf, ?_, ?_⟩
  · intro q hq
    have hder := norm_fderiv_sub_id_le_of_ball_error _ m hm hf hb q hq
    have hh := norm_error_sub_le_of_ball_error _ m hm hf hb q 0 hq (by simpa using hm.le)
    rw [sourceWeightedAdaptedFourier_zero, sub_zero, sub_zero, sub_zero] at hh
    refine ⟨hder, ?_, ?_⟩
    · have hl := norm_le_norm_sub_add q (sourceWeightedAdaptedFourier w r hr N q)
      rw [norm_sub_rev] at hl
      nlinarith [norm_nonneg q]
    · exact (norm_le_norm_sub_add (sourceWeightedAdaptedFourier w r hr N q) q).trans
        (by nlinarith [norm_nonneg q])
  · obtain ⟨g, hg, hinj, hright, hleft⟩ := exists_analytic_inverse_of_ball_error _ m hm hf hb
    refine ⟨g, hg, hinj, hright, hleft, ?_⟩
    intro y hy
    have hy' : ‖y‖ ≤ 3*m/4 := by linarith
    obtain ⟨hgm, he⟩ := hright y hy'
    have hgn : ‖g y‖ ≤ 2*m := by have hh := mem_ball_zero_iff.mp hgm; linarith
    have hp := sourceWeightedAdaptedFourier_preserves_complex_source w r hr N (2*m)
      (by positivity) hcut (g y) hgn
    rw [he] at hp
    exact ⟨hp.1.symm, hp.2.symm⟩

end NLS.Articles.KdVPseudomeasures
