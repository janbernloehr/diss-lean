import NLS.Fourier.PeriodicFourierLebesgueSpace

/-! Quantitative endpoint membership of the ENTIRE original periodic distribution. -/
noncomputable section
open scoped ENNReal
namespace NLS.Fourier.PeriodicFourierLebesgue
open SmoothPeriodicTest
variable {L : ℝ} [Fact (0 < L)]

/-- Exact normalized weighted coefficient bound at every Banach exponent. -/
theorem weight_mul_norm_coefficient_le (w : Weight) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (q : PeriodicFourierLebesgue L w p) (k : ℤ) : w k*‖q.val (mode (-k))‖ ≤ ‖q‖ := by
  have hh := lp.norm_apply_le_norm (ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p)))
    (WeightedCoeff.weightEquiv w p (coefficientsLM w p q)) k
  change ‖(w k:ℂ)*q.val (mode (-k))‖ ≤ ‖q‖ at hh
  simpa only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (w.positive k).le] using hh

/-- A pointwise weighted bound gives ACTUAL original-distribution membership
and the same endpoint norm bound. No synthesis or new distribution is substituted. -/
theorem exists_of_endpoint_bound (w : Weight) (u : Distribution L) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ k : ℤ, w k*‖u (mode (-k))‖ ≤ M) :
    ∃ q : PeriodicFourierLebesgue L w ⊤, q.val = u ∧ ‖q‖ ≤ M := by
  have hn (k : ℤ) : ‖(w k:ℂ)*u (mode (-k))‖ ≤ M := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (w.positive k).le] using hb k
  let q : PeriodicFourierLebesgue L w ⊤ := ⟨u, memℓp_infty ⟨M, by rintro _ ⟨k,rfl⟩; exact hn k⟩⟩
  refine ⟨q, rfl, ?_⟩
  change ‖WeightedCoeff.weightEquiv w ⊤ (coefficientsLM w ⊤ q)‖ ≤ M
  exact lp.norm_le_of_forall_le hM hn

/-- An explicit lower weight comparison gives stronger regularity of the SAME
original distribution,with its literal endpoint norm bound. -/
theorem exists_of_endpoint_weight_lower_bound (w v : Weight) (c : ℝ) (hc : 0 < c)
    (hweight : ∀ k : ℤ, c*v k ≤ w k) (q : PeriodicFourierLebesgue L w ⊤) :
    ∃ p : PeriodicFourierLebesgue L v ⊤, p.val = q.val ∧ ‖p‖ ≤ ‖q‖/c := by
  apply exists_of_endpoint_bound v q.val (‖q‖/c) (by positivity)
  intro k
  apply (le_div_iff₀ hc).mpr
  have hh := (mul_le_mul_of_nonneg_right (hweight k) (norm_nonneg (q.val (mode (-k))))).trans
    (weight_mul_norm_coefficient_le w ⊤ q k)
  nlinarith

end NLS.Fourier.PeriodicFourierLebesgue
