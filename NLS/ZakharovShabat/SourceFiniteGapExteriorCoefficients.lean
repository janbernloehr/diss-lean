import NLS.ZakharovShabat.SourceFiniteGapAtInfinity
import NLS.ZakharovShabat.SourceFiniteGapExteriorPeriod
import NLS.ComplexAnalysis.InversionCircleCoefficients

/-! # Exterior coefficients at actual finite-gap sources

The zero outer period kills the linear coefficient of the inversion germ.
The weighted outer contour equals `2πi` times its quadratic coefficient.
The identification of that coefficient with source mass is a separate step.
-/
noncomputable section
open Set Complex Metric NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- On a large circle the inversion germ is exactly the actual quotient. -/
theorem sourceFloquetLogDerivative_eq_inversion_on_circle
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (g : ℂ → ℂ) (r R : ℝ) (hR : 0 < R) (hRr : R⁻¹ < r)
    (he : ∀ z ∈ ball (0 : ℂ) r, z ≠ 0 → g z = sourceFloquetLogDerivative hp hp1 φ z⁻¹)
    (z : ℂ) (hz : z ∈ sphere (0 : ℂ) R) :
    sourceFloquetLogDerivative hp hp1 φ z = g z⁻¹ := by
  have hn : ‖z‖ = R := by simpa only [mem_sphere, dist_zero_right] using hz
  have hz0 : z ≠ 0 := norm_pos_iff.mp (hn.symm ▸ hR)
  have hzin : z⁻¹ ∈ ball (0 : ℂ) r := by
    simpa only [mem_ball, dist_zero_right, norm_inv, hn] using hRr
  simpa only [inv_inv] using (he z⁻¹ hzin (inv_ne_zero hz0)).symm

/-- There is no inverse-frequency term in the finite-gap quotient's expansion. -/
theorem sourceFiniteGap_inversionExtension_deriv_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) (r : ℝ) (hr : 0 < r)
    (g : ℂ → ℂ) (hg : AnalyticOnNhd ℂ g (ball 0 r))
    (he : ∀ z ∈ ball (0 : ℂ) r, z ≠ 0 → g z = sourceFloquetLogDerivative hp hp1 φ.val z⁻¹) :
    deriv g 0 = 0 := by
  obtain ⟨T, hT, hpzero⟩ := exists_sourceFiniteGap_exterior_period_zero hp hp1 φ hf
  let R := max T r⁻¹ + 1
  have hTR : T ≤ R := by dsimp [R]; linarith [le_max_left T r⁻¹]
  have hR : 0 < R := hT.trans_le hTR
  have hrR : r⁻¹ < R := by dsimp [R]; linarith [le_max_right T r⁻¹]
  have hRr : R⁻¹ < r := (inv_lt_comm₀ hR hr).mpr hrR
  have hc : (∮ z in C(0,R), sourceFloquetLogDerivative hp hp1 φ.val z) =
      (2*Real.pi*I : ℂ)*deriv g 0 := by
    rw [circleIntegral.integral_congr hR.le
      (sourceFloquetLogDerivative_eq_inversion_on_circle hp hp1 φ.val g r R hR hRr he)]
    exact circleIntegral_comp_inv_eq g r R hr hR hRr hg
  rw [hpzero R hTR] at hc
  have hne : (2*Real.pi*I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  exact (mul_eq_zero.mp hc.symm).resolve_left hne

/-- The weighted exterior contour extracts exactly the quadratic germ coefficient. -/
theorem sourceFloquetLogDerivative_weighted_circle_eq_coefficient
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (g : ℂ → ℂ) (r R : ℝ) (hr : 0 < r) (hR : 0 < R) (hRr : R⁻¹ < r)
    (hg : AnalyticOnNhd ℂ g (ball 0 r))
    (he : ∀ z ∈ ball (0 : ℂ) r, z ≠ 0 → g z = sourceFloquetLogDerivative hp hp1 φ z⁻¹) :
    (∮ z in C(0,R), z * sourceFloquetLogDerivative hp hp1 φ z) =
      (2*Real.pi*I : ℂ)*deriv (dslope g 0) 0 := by
  calc
    _ = ∮ z in C(0,R), z * g z⁻¹ := circleIntegral.integral_congr hR.le (fun z hz => by
      rw [sourceFloquetLogDerivative_eq_inversion_on_circle hp hp1 φ g r R hR hRr he z hz])
    _ = _ := circleIntegral_mul_comp_inv_eq g r R hr hR hRr hg

/-- The actual inversion germ has constant term `-i`, zero linear term,
and its quadratic coefficient computes every sufficiently large weighted contour. -/
theorem exists_sourceFiniteGap_exterior_coefficient_formula
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ r : ℝ, 0 < r ∧ ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (ball 0 r) ∧ g 0 = -I ∧ deriv g 0 = 0 ∧
      (∀ z ∈ ball (0 : ℂ) r, z ≠ 0 → g z = sourceFloquetLogDerivative hp hp1 φ.val z⁻¹) ∧
      ∀ R : ℝ, 0 < R → R⁻¹ < r →
        (∮ z in C(0,R), z * sourceFloquetLogDerivative hp hp1 φ.val z) =
          (2*Real.pi*I : ℂ)*deriv (dslope g 0) 0 := by
  obtain ⟨r, hr, g, hg, hg0, he⟩ := exists_sourceFiniteGap_logDerivative_normalized_at_infinity hp hp1 φ hf
  exact ⟨r, hr, g, hg, hg0, sourceFiniteGap_inversionExtension_deriv_zero hp hp1 φ hf r hr g hg he,
    he, fun R hR hRr => sourceFloquetLogDerivative_weighted_circle_eq_coefficient hp hp1 φ.val g r R hr hR hRr hg he⟩

/-- An exact exterior expansion with an analytic quadratic remainder;
its value at zero is precisely the weighted contour coefficient. -/
theorem exists_sourceFiniteGap_exterior_quadratic_remainder
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ r : ℝ, 0 < r ∧ ∃ h : ℂ → ℂ,
      AnalyticOnNhd ℂ h (ball 0 r) ∧
      (∀ z : ℂ, r⁻¹ < ‖z‖ →
        sourceFloquetLogDerivative hp hp1 φ.val z = -I + z⁻¹^2 * h z⁻¹) ∧
      ∀ R : ℝ, 0 < R → R⁻¹ < r →
        (∮ z in C(0,R), z * sourceFloquetLogDerivative hp hp1 φ.val z) =
          (2*Real.pi*I : ℂ)*h 0 := by
  obtain ⟨r, hr, g, hg, hg0, hgd, he, hcircle⟩ :=
    exists_sourceFiniteGap_exterior_coefficient_formula hp hp1 φ hf
  let h := dslope (dslope g 0) 0
  have hh := analyticOnNhd_dslope_zero (dslope g 0) r hr (analyticOnNhd_dslope_zero g r hr hg)
  refine ⟨r, hr, h, hh, ?_, ?_⟩
  · intro z hz
    have hzpos : 0 < ‖z‖ := (inv_pos.mpr hr).trans hz
    have hz0 : z ≠ 0 := norm_pos_iff.mp hzpos
    have hzin : z⁻¹ ∈ ball (0 : ℂ) r := by
      rw [mem_ball, dist_zero_right, norm_inv]
      exact (inv_lt_comm₀ hzpos hr).mpr hz
    have hgz : sourceFloquetLogDerivative hp hp1 φ.val z = g z⁻¹ := by
      simpa only [inv_inv] using (he z⁻¹ hzin (inv_ne_zero hz0)).symm
    rw [hgz, eq_second_dslope_expansion g z⁻¹, hg0, hgd, mul_zero, add_zero]
  · intro R hR hRr
    simpa only [h, dslope_same] using hcircle R hR hRr

end NLS.ZakharovShabat
