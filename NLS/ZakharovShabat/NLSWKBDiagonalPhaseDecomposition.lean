import NLS.ZakharovShabat.SobolevWKBLeadingDiagonalApproximation

/-! # The exact diagonal phase and oscillatory decomposition

The leading diagonal approximation splits into its signed Riccati primitive and boundary and nested oscillatory terms.
-/

noncomputable section
open Set Complex MeasureTheory
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- The nonoscillatory diagonal primitive at the first omitted WKB order. -/
def nlsWKBDiagonalPhasePrimitive (a b : ℝ → ℂ) (N : ℕ) (z : ℂ) (t : ℝ) : ℂ :=
  -((2*I*z)⁻¹)^(N+1)*exp (-I*z*t)*
    (∫ x in (0:ℝ)..t, a x*nlsRiccatiDensity a b N x)

/-- The two oscillatory terms left after removing the diagonal primitive. -/
def nlsWKBDiagonalOscillatoryIntegral (a b : ℝ → ℂ) (N : ℕ) (z : ℂ) (t : ℝ) : ℂ :=
  a t*exp (I*z*t)*(∫ x in (0:ℝ)..t, nlsRiccatiDensity a b N x*exp (-2*I*z*x))-
  exp (-I*z*t)*(∫ x in (0:ℝ)..t, deriv a x*
    (exp (2*I*z*x)*(∫ y in (0:ℝ)..x, nlsRiccatiDensity a b N y*exp (-2*I*z*y))))

/-- The diagonal approximation splits exactly into its phase primitive
and its two sampled oscillatory terms, with no higher source derivative. -/
theorem nlsWKBLeadingDiagonalApproximation_eq_phase_add_oscillatory
    (a b : ℝ → ℂ) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (N : ℕ) (z : ℂ) (t : ℝ) :
    nlsWKBLeadingDiagonalApproximation a b N z t =
      nlsWKBDiagonalPhasePrimitive a b N z t+
      ((2*I*z)⁻¹)^(N+1)*nlsWKBDiagonalOscillatoryIntegral a b N z t := by
  let r := nlsRiccatiDensity a b N
  let w := (2*I*z)⁻¹
  let J (x : ℝ) := ∫ y in (0:ℝ)..x, r y*exp (-2*I*z*y)
  have hr : Continuous r := (contDiff_nlsRiccatiDensity a b ha hb N).continuous
  have hJ : Continuous J := (intervalIntegral.differentiable_integral_of_continuous
    (a := (0:ℝ)) (show Continuous (fun y : ℝ => r y*exp (-2*I*z*y)) by fun_prop)).continuous
  have hda : Continuous (deriv a) := ha.continuous_deriv (by simp)
  have hi (x : ℝ) : exp (I*z*x)*
      (I*deriv a x*nlsWKBLeadingTerm a b N z x+I*a x*nlsWKBLeadingScalar a b N z x) =
      w^N*(deriv a x*(exp (2*I*z*x)*J x)+a x*r x) := by
    have hexp : exp (I*z*x)*exp (-I*z*x) = 1 := by rw [← exp_add]; ring_nf; simp
    have hdouble : exp (2*I*z*x) = exp (I*z*x)*exp (I*z*x) := by rw [← exp_add]; congr 1; ring
    rw [hdouble]
    dsimp only [nlsWKBLeadingTerm,nlsWKBLeadingScalar,J,r,w]
    linear_combination (norm := (ring_nf; simp [I_sq]))
      ((2*I*z)⁻¹)^N*a x*nlsRiccatiDensity a b N x*hexp
  unfold nlsWKBLeadingDiagonalApproximation classicalDiagonalApproximation
  simp_rw [hi]
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  dsimp only [nlsWKBDiagonalPhasePrimitive,nlsWKBDiagonalOscillatoryIntegral,nlsWKBLeadingTerm,J,r,w]
  rw [pow_succ]
  ring_nf
  simp [I_sq]
  ring

end NLS.ZakharovShabat
