import NLS.ZakharovShabat.ClassicalGradientFourierSummability

/-! # A common power bound before spectral-frequency selection

The interpolation constants depend only on the two time bounds and the
exponents. In particular they can be used simultaneously at every point
of an indexed spectral contour, as required in G.7.
-/

noncomputable section
open Set NLS.LinearVolterra NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- One summable power controls every gradient error with the stated time bounds. -/
theorem exists_classicalGradientFourier_power_bound
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) (hq : ENNReal.ofReal (1+1/p) < q)
    (A D : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D) :
    ∃ K α : ℝ, 0 ≤ K ∧ 1 < α*p ∧
      ∀ (φ : Curve (ℂ × ℂ)) (z w : ℂ) (v : ℂ × ℂ) (L : (ℂ × ℂ) →L[ℂ] ℂ)
      (P : (ℂ × ℂ) →L[ℝ] ℂ), ‖P‖ ≤ 1 → ∀ d : ℝ, 1 ≤ d →
      (∀ t : Icc (0 : ℝ) 1, ‖classicalEndpointGradientRemainder φ z w v L t‖ ≤ A/d) →
      (∀ t : Icc (0 : ℝ) 1, ‖deriv (classicalEndpointGradientRemainder φ z w v L) t‖ ≤ D) →
      ‖classicalEndpointGradientFourierCoefficients
        (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq)
        φ z w v L P‖ ≤ K*d^(-α) := by
  have hq1 : 1 < q := lt_of_le_of_lt
    (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq
  obtain ⟨r,ε,he0,he1,her,hr2,hrq,hep⟩ := exists_fundamentalFourier_summability_exponents p hp q hq
  have hr : 1 < r := by linarith
  let K := (2*A+D)*unitIntervalC1FourierConstant (q := ENNReal.ofReal (1+ε))
    (ENNReal.one_lt_ofReal.mpr (by linarith))+A
  let α := fundamentalFourierDecayExponent ε r
  refine ⟨K,α,?_,hep,?_⟩
  · let : Fact (1 ≤ ENNReal.ofReal (1+ε)) := ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
    have hconst := unitIntervalC1FourierConstant_nonneg
      (q := ENNReal.ofReal (1+ε)) (ENNReal.one_lt_ofReal.mpr (by linarith))
    positivity
  intro φ z w v L P hP d hd hv hder
  have hsmall := norm_classicalEndpointGradientFourierCoefficients_interpolate
    φ z w v L P hP (1+ε) r (by linarith) (by linarith) her hr2 A D d hA hD hd hv hder
  have he : (r-(1+ε))/(2-(1+ε)) = α := by unfold α fundamentalFourierDecayExponent; congr 1 <;> ring
  rw [he] at hsmall
  have hmono := norm_unitIntervalC1Coefficients_mono_exponent (ENNReal.one_lt_ofReal.mpr hr) hq1 hrq
    (fun t => P (classicalEndpointGradientRemainder φ z w v L t))
    (P.contDiff.comp (contDiff_classicalEndpointGradientRemainder _ _ _ _ _))
  calc
    _ ≤ K/d^α := hmono.trans hsmall
    _ = K*d^(-α) := by rw [Real.rpow_neg (by positivity),div_eq_mul_inv]

end NLS.ZakharovShabat
