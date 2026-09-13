import NLS.ComplexAnalysis.DecayingDuhamelKernel

/-!
# Integrating a decaying term and a uniform error

These bounds feed the fast-coordinate estimate back into the slow equation.
-/

noncomputable section
open Set Complex MeasureTheory intervalIntegral
namespace NLS.ComplexAnalysis

theorem integral_exp_neg_mul_le (a t : ℝ) (ha : 0 < a) (ht : 0 ≤ t) :
    (∫ s in 0..t, Real.exp (-a * s)) ≤ 1 / a := by
  have h := intervalIntegral.integral_comp_sub_left (fun s => Real.exp (-a * s)) t
    (a := 0) (b := t)
  simp only [sub_self, sub_zero] at h
  rw [← h]
  exact integral_decaying_kernel_le a t ha ht

/-- A bounded coefficient times a decaying term and a constant error is integrable
with an inverse-rate bound on the decaying part. -/
theorem norm_integral_mul_le_of_decay (p v : ℝ → ℂ) (a t M D E : ℝ)
    (ha : 0 < a) (ht : t ∈ Icc (0 : ℝ) 1)
    (hM : 0 ≤ M) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hp : ∀ s ∈ Icc 0 t, ‖p s‖ ≤ M)
    (hv : ∀ s ∈ Icc 0 t, ‖v s‖ ≤ Real.exp (-a * s) * D + E) :
    ‖∫ s in 0..t, p s * v s‖ ≤ M * (D / a + E) := by
  have hi : ‖∫ s in 0..t, p s * v s‖ ≤
      ∫ s in 0..t, M * (Real.exp (-a * s) * D + E) := by
    apply norm_integral_le_of_norm_le ht.1
    · apply Filter.Eventually.of_forall
      intro s hs
      rw [norm_mul]
      exact mul_le_mul (hp s ⟨hs.1.le, hs.2⟩) (hv s ⟨hs.1.le, hs.2⟩)
        (norm_nonneg _) hM
    · exact (show Continuous (fun s => M * (Real.exp (-a * s) * D + E)) by
        fun_prop).intervalIntegrable 0 t
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
    ((show Continuous (fun s => Real.exp (-a * s) * D) by fun_prop).intervalIntegrable 0 t)
    (continuous_const.intervalIntegrable 0 t), intervalIntegral.integral_mul_const,
    intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hi
  apply hi.trans
  apply mul_le_mul_of_nonneg_left _ hM
  calc
    _ ≤ (1/a) * D + 1 * E := add_le_add
      (mul_le_mul_of_nonneg_right (integral_exp_neg_mul_le a t ha ht.1) hD)
      (mul_le_mul_of_nonneg_right ht.2 hE)
    _ = D/a + E := by ring

end NLS.ComplexAnalysis
