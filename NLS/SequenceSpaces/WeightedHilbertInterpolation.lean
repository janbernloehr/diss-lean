import NLS.SequenceSpaces.HilbertGeometricInterpolation
import NLS.SequenceSpaces.SignedSobolevWeight

/-! Log-convexity of Hilbert norms at arbitrary real Sobolev orders.
The three vectors represent the same raw Fourier coefficients. -/
noncomputable section
open scoped ENNReal
namespace NLS.WeightedCoeff

theorem norm_le_of_weighted_coefficients (w v : Weight)
    (a : WeightedCoeff w 2) (b : WeightedCoeff v 2) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ k, w k*‖a.val k‖ ≤ C*(v k*‖b.val k‖)) : ‖a‖ ≤ C*‖b‖ := by
  have hh : ‖weightEquiv w 2 a‖ ≤ ‖(C:ℂ) • weightEquiv v 2 b‖ := by
    apply lp.norm_mono (by norm_num : (2:ℝ≥0∞) ≠ 0)
    intro k
    simpa only [weightEquiv_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
      norm_mul, Complex.norm_real, Real.norm_of_nonneg hC,
      Real.norm_of_nonneg (w.positive k).le, Real.norm_of_nonneg (v.positive k).le]
      using h k
  simpa only [norm_smul, Complex.norm_real, Real.norm_of_nonneg hC, ← norm_eq] using hh

theorem norm_le_weighted_geometric (w₀ w₁ w : Weight) (t : ℝ)
    (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hw : ∀ k, w k = (w₀ k)^(1-t)*(w₁ k)^t)
    (a : WeightedCoeff w₀ 2) (b : WeightedCoeff w₁ 2) (c : WeightedCoeff w 2)
    (ha : ∀ k, a.val k = c.val k) (hb : ∀ k, b.val k = c.val k) :
    ‖c‖ ≤ ‖a‖^(1-t)*‖b‖^t := by
  apply Coeff.norm_le_geometric (weightEquiv w₀ 2 a) (weightEquiv w₁ 2 b)
    (weightEquiv w 2 c) t ht ht1
  intro k
  simp only [weightEquiv_apply, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (w.positive k).le, Real.norm_of_nonneg (w₀.positive k).le,
    Real.norm_of_nonneg (w₁.positive k).le, ha k, hb k]
  rw [hw k, Real.mul_rpow (w₀.positive k).le (norm_nonneg _),
    Real.mul_rpow (w₁.positive k).le (norm_nonneg _)]
  rw [mul_mul_mul_comm, ← Real.rpow_add_of_nonneg (norm_nonneg _) (sub_nonneg.mpr ht1) ht]
  simp

theorem norm_signedSobolev_geometric (s₀ s₁ t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (a : WeightedCoeff (Weight.signedSobolev s₀) 2)
    (b : WeightedCoeff (Weight.signedSobolev s₁) 2)
    (c : WeightedCoeff (Weight.signedSobolev ((1-t)*s₀+t*s₁)) 2)
    (ha : ∀ k, a.val k = c.val k) (hb : ∀ k, b.val k = c.val k) :
    ‖c‖ ≤ ‖a‖^(1-t)*‖b‖^t := by
  apply norm_le_weighted_geometric _ _ _ t ht ht1 _ a b c ha hb
  intro k
  change (max 1 |(k:ℝ)|)^((1-t)*s₀+t*s₁) =
    ((max 1 |(k:ℝ)|)^s₀)^(1-t)*((max 1 |(k:ℝ)|)^s₁)^t
  rw [← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity),
    ← Real.rpow_add (by positivity)]
  congr 1
  ring

end NLS.WeightedCoeff
