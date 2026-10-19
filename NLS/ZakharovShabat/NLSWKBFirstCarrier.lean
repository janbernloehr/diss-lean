import NLS.ZakharovShabat.SobolevWKBCarrierFreeUniform

/-! # The exact mass correction to the first WKB carrier

The signed-swap invariant physical mass primitive gives the exact first carrier, including its zero-frequency convention.
-/

noncomputable section
open Set Complex MeasureTheory
namespace NLS.ZakharovShabat

/-- The physical mass primitive in the first inverse-frequency correction. -/
def nlsWKBMassPrimitive (a b : ℝ → ℂ) (x : ℝ) : ℂ := ∫ t in (0:ℝ)..x, a t*b t

theorem continuous_nlsWKBMassPrimitive (a b : ℝ → ℂ) (ha : Continuous a) (hb : Continuous b) :
    Continuous (nlsWKBMassPrimitive a b) := by
  have hc := ha.mul hb
  apply continuous_iff_continuousAt.mpr
  intro x
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 x)
    (hc.stronglyMeasurableAtFilter volume (nhds x)) hc.continuousAt).continuousAt

@[simp] theorem nlsWKBMassPrimitive_signedSwap (a b : ℝ → ℂ) (x : ℝ) :
    nlsWKBMassPrimitive (-b) (-a) x = nlsWKBMassPrimitive a b x := by
  unfold nlsWKBMassPrimitive
  apply intervalIntegral.integral_congr
  intro t _
  simp only [Pi.neg_apply]
  ring

/-- The first WKB carrier has an exact mass-primitive correction,
including the total zero-frequency convention. -/
theorem nlsWKBCarrier_order_one (a b : ℝ → ℂ) (z : ℂ) (x : ℝ) :
    nlsWKBCarrier a b 1 z x = exp (-I*z*x)*exp (-(2*I*z)⁻¹*nlsWKBMassPrimitive a b x) := by
  have he (t : ℝ) : a t*nlsRiccatiApproximation a b 1 (2*I*z)⁻¹ t =
      (-(2*I*z)⁻¹)*(a t*b t) := by
    simp only [nlsRiccatiApproximation,Finset.sum_range_one,nlsRiccatiDensity_zero,
      Pi.neg_apply]
    ring
  rw [nlsWKBCarrier]
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul,exp_add]
  rfl

/-- A uniform pointwise potential bound controls the mass primitive on
all partial intervals of the physical period. -/
theorem norm_nlsWKBMassPrimitive_le (a b : ℝ → ℂ) (A : ℝ) (hA : 0 ≤ A)
    (ha : ∀ x : ℝ, ‖a x‖ ≤ A) (hb : ∀ x : ℝ, ‖b x‖ ≤ A)
    (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) : ‖nlsWKBMassPrimitive a b x‖ ≤ A^2 := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := x)
    (C := A^2) (f := fun t => a t*b t) (by
      intro t _
      rw [norm_mul,pow_two]
      exact mul_le_mul (ha t) (hb t) (norm_nonneg _) hA)
  simp only [sub_zero,abs_of_nonneg hx.1] at h
  exact h.trans (mul_le_of_le_one_right (sq_nonneg _) hx.2)

end NLS.ZakharovShabat
