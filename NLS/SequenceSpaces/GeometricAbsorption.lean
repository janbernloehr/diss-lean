import Mathlib.Analysis.MeanInequalities

/-! # Scaled Young absorption with an arbitrary small coefficient -/
noncomputable section
namespace NLS

/-- A sublinear geometric power of Y can be absorbed with any positive
coefficient; its companion X retains exponent one. -/
theorem exists_geometric_absorption (t K ε : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X Y : ℝ, 0 ≤ X → 0 ≤ Y →
      K*X^(1-t)*Y^t ≤ ε*Y+C*X := by
  let D := ((K+1)/ε)^((1-t)⁻¹)
  have hD : 0 < D := Real.rpow_pos_of_pos (div_pos (by linarith) hε) _
  have he : D^(1-t) = (K+1)/ε := by
    dsimp [D]
    rw [← Real.rpow_mul (by positivity),inv_mul_cancel₀ (by linarith : 1-t ≠ 0),Real.rpow_one]
  refine ⟨ε*D,mul_nonneg hε.le hD.le,?_⟩
  intro X Y hX hY
  have h := Real.geom_mean_le_arith_mean2_weighted (by linarith : 0 ≤ 1-t) ht.le
    (mul_nonneg hD.le hX) hY (by ring : 1-t+t=1)
  rw [Real.mul_rpow hD.le hX,he] at h
  have hh := mul_le_mul_of_nonneg_left h hε.le
  have hprod : 0 ≤ X^(1-t)*Y^t := mul_nonneg (Real.rpow_nonneg hX _) (Real.rpow_nonneg hY _)
  have hDX : 0 ≤ D*X := mul_nonneg hD.le hX
  have hsmall₁ : ε*((1-t)*(D*X)) ≤ ε*(D*X) := by
    apply mul_le_mul_of_nonneg_left _ hε.le
    exact mul_le_of_le_one_left hDX (by linarith)
  have hsmall₂ : ε*(t*Y) ≤ ε*Y := by
    apply mul_le_mul_of_nonneg_left _ hε.le
    exact mul_le_of_le_one_left hY ht1.le
  have hcancel : ε*((K+1)/ε*X^(1-t)*Y^t) = (K+1)*(X^(1-t)*Y^t) := by field_simp
  rw [hcancel] at hh
  nlinarith

end NLS
