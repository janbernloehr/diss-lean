import NLS.SequenceSpaces.RealActionTorus

/-! # Weighted sequence membership is constant on real action tori -/
noncomputable section
open scoped ENNReal
namespace NLS.RealCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
/-- Equal quadratic actions transfer any real weight between the two
coordinate pairs. No finite-support or positive-action hypothesis enters. -/
theorem weighted_mem_of_pairAction_eq (w : ℤ → ℝ) (z v : RealCoeff p × RealCoeff p)
    (hz : Memℓp (fun n => w n*z.1 n) p ∧ Memℓp (fun n => w n*z.2 n) p)
    (ha : ∀ n, pairAction v n = pairAction z n) :
    Memℓp (fun n => w n*v.1 n) p ∧ Memℓp (fun n => w n*v.2 n) p := by
  have hmajor := hz.1.norm.add hz.2.norm
  have hc (n : ℤ) : ‖w n*v.1 n‖ ≤ ‖w n*z.1 n‖+‖w n*z.2 n‖ ∧
      ‖w n*v.2 n‖ ≤ ‖w n*z.1 n‖+‖w n*z.2 n‖ := by
    have h := abs_coordinates_le_of_pairAction_eq z v n (ha n)
    simp only [norm_mul,Real.norm_eq_abs]
    rw [← mul_add]
    exact ⟨mul_le_mul_of_nonneg_left h.1 (abs_nonneg _),mul_le_mul_of_nonneg_left h.2 (abs_nonneg _)⟩
  constructor
  · apply hmajor.mono
    intro n
    exact (hc n).1
  · apply hmajor.mono
    intro n
    exact (hc n).2

end NLS.RealCoeff
