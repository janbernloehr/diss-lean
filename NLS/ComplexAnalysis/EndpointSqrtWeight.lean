import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality

/-!
# The endpoint square-root weight on a finite interval

The reciprocal square root of the product of endpoint distances is
integrable on every nondegenerate real interval. This is the affine
form of the Chebyshev weight on `[-1, 1]`.
-/

noncomputable section
open MeasureTheory intervalIntegral Set
namespace NLS.ComplexAnalysis

theorem intervalIntegrable_inv_sqrt_endpoint_product
    {a b : ℝ} (hab : a < b) :
    IntervalIntegrable (fun x : ℝ => (Real.sqrt ((x-a)*(b-x)))⁻¹)
      volume a b := by
  let δ : ℝ := (b-a)/2
  let τ : ℝ := (a+b)/2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδne : δ ≠ 0 := ne_of_gt hδ
  have hbase := Polynomial.Chebyshev.intervalIntegrable_sqrt_one_sub_sq_inv
  have hscaled := hbase.comp_mul_left (c := δ⁻¹)
  have hshifted := hscaled.comp_sub_right τ
  have hleft : -1 / δ⁻¹ + τ = a := by
    rw [div_inv_eq_mul]
    dsimp [δ,τ]
    ring
  have hright : 1 / δ⁻¹ + τ = b := by
    rw [div_inv_eq_mul]
    dsimp [δ,τ]
    ring
  have hnorm : IntervalIntegrable
      (fun x : ℝ => δ⁻¹ * (Real.sqrt (1 - (δ⁻¹*(x-τ))^2))⁻¹)
      volume a b := by
    have hscaled2 := hshifted.const_mul δ⁻¹
    simpa only [hleft,hright,Real.sqrt_inv] using hscaled2
  apply hnorm.congr_uIoo
  rw [uIoo_of_le hab.le]
  intro x hx
  have hprod : 0 ≤ (x-a)*(b-x) :=
    (mul_pos (sub_pos.mpr hx.1) (sub_pos.mpr hx.2)).le
  have hid : (x-a)*(b-x) = δ^2 * (1-(δ⁻¹*(x-τ))^2) := by
    have hmul : δ * (δ⁻¹*(x-τ)) = x-τ := by
      rw [← mul_assoc, mul_inv_cancel₀ hδne, one_mul]
    calc
      _ = δ^2 - (x-τ)^2 := by dsimp [δ,τ]; ring
      _ = δ^2 - (δ*(δ⁻¹*(x-τ)))^2 := by rw [hmul]
      _ = δ^2 * (1-(δ⁻¹*(x-τ))^2) := by ring
  change δ⁻¹ * (Real.sqrt (1 - (δ⁻¹*(x-τ))^2))⁻¹ =
    (Real.sqrt ((x-a)*(b-x)))⁻¹
  rw [hid, Real.sqrt_mul (sq_nonneg δ), Real.sqrt_sq_eq_abs,
    abs_of_pos hδ]
  simp [mul_inv_rev,mul_comm]

/-- A bounded continuous numerator preserves the endpoint-weight
integrability. -/
theorem intervalIntegrable_div_sqrt_endpoint_product
    {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) :
    IntervalIntegrable (fun x : ℝ =>
      f x / Real.sqrt ((x-a)*(b-x))) volume a b := by
  have hweight := intervalIntegrable_inv_sqrt_endpoint_product hab
  have hf' : ContinuousOn f (uIcc a b) := by
    simpa only [uIcc_of_le hab.le] using hf
  have hprod := hweight.continuousOn_mul hf'
  simpa only [div_eq_mul_inv, mul_comm] using hprod

/-- If a radicand factors as the endpoint-distance product times a
strictly positive continuous factor, its square-root quotient is
interval-integrable for every continuous numerator. -/
theorem intervalIntegrable_div_sqrt_factored_endpoint_product
    {a b : ℝ} (hab : a < b) {f q G : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hG : ContinuousOn G (Icc a b))
    (hGpos : ∀ x ∈ Icc a b, 0 < G x)
    (hfactor : ∀ x ∈ Ioo a b,
      q x = (x-a)*(b-x)*G x) :
    IntervalIntegrable (fun x : ℝ => f x / Real.sqrt (q x))
      volume a b := by
  have hnum : ContinuousOn
      (fun x : ℝ => f x / Real.sqrt (G x)) (Icc a b) :=
    hf.div (Real.continuous_sqrt.comp_continuousOn hG)
      (fun x hx => ne_of_gt (Real.sqrt_pos.2 (hGpos x hx)))
  have hbase := intervalIntegrable_div_sqrt_endpoint_product hab hnum
  apply hbase.congr_uIoo
  rw [uIoo_of_le hab.le]
  intro x hx
  have hweight : 0 ≤ (x-a)*(b-x) :=
    (mul_pos (sub_pos.mpr hx.1) (sub_pos.mpr hx.2)).le
  change (f x / Real.sqrt (G x)) /
    Real.sqrt ((x-a)*(b-x)) = f x / Real.sqrt (q x)
  rw [hfactor x hx, Real.sqrt_mul hweight]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end NLS.ComplexAnalysis
