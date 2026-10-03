import NLS.ZakharovShabat.SourceFiniteGapExteriorCoefficients
import NLS.ZakharovShabat.SourceFiniteGapExteriorMassNormalization
import NLS.ComplexAnalysis.ExteriorPrimitiveCoefficient

/-! # Source mass as the exact finite-gap exterior contour coefficient -/
noncomputable section
open Set Complex Metric Filter Topology NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

/-- The analytic exterior remainder's value is forced by the actual
mass-normalized primitive, not supplied as an asymptotic hypothesis. -/
theorem sourceFiniteGap_quadratic_remainder_mass
    (φ : realTypeSourceSubmodule 2)
    (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (h : ℂ → ℂ) (r : ℝ) (hr : 0 < r) (hh : AnalyticOnNhd ℂ h (ball 0 r))
    (he : ∀ z : ℂ, r⁻¹ < ‖z‖ →
      sourceFloquetLogDerivative (by simp) (by norm_num) φ.val z = -I + z⁻¹^2*h z⁻¹) :
    sourceHilbertMass φ.val = 2*I*h 0 := by
  obtain ⟨R, hR, F, hF, hM⟩ := exists_sourceFiniteGap_exterior_primitive_norm_normalized φ hf
  obtain ⟨P, hP, hlim⟩ := exists_exterior_primitive_of_quadratic_remainder h r hr hh
  have hmass : Tendsto (fun y : ℝ => (2*y : ℂ)*(F ((y : ℂ)*I)-y)) atTop (𝓝 (sourceHilbertMass φ.val)) := by
    simpa only [sourceHilbertMass_eq_half_norm_sq_of_realType φ.val φ.property] using hM
  apply exterior_primitive_coefficient_unique F P
    (sourceFloquetLogDerivative (by simp) (by norm_num) φ.val) (max R r⁻¹)
    (hR.trans_le (le_max_left _ _)) _ _ _ _ hmass hlim
  · intro z hz
    exact hF z (lt_of_le_of_lt (le_max_left _ _) hz)
  · intro z hz
    have hz' : r⁻¹ < ‖z‖ := lt_of_le_of_lt (le_max_right _ _) hz
    rw [he z hz']
    exact hP z hz'

/-- The first nonconstant analytic exterior coefficient is exactly
`-i` times half the source mass. -/
theorem exists_sourceFiniteGap_mass_remainder
    (φ : realTypeSourceSubmodule 2)
    (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    ∃ r : ℝ, 0 < r ∧ ∃ h : ℂ → ℂ,
      AnalyticOnNhd ℂ h (ball 0 r) ∧ h 0 = -I*sourceHilbertMass φ.val/2 ∧
      (∀ z : ℂ, r⁻¹ < ‖z‖ →
        sourceFloquetLogDerivative (by simp) (by norm_num) φ.val z = -I + z⁻¹^2*h z⁻¹) ∧
      ∀ R : ℝ, 0 < R → R⁻¹ < r →
        (∮ z in C(0,R), z * sourceFloquetLogDerivative (by simp) (by norm_num) φ.val z) =
          (Real.pi : ℂ)*sourceHilbertMass φ.val := by
  obtain ⟨r, hr, h, hh, he, hc⟩ := exists_sourceFiniteGap_exterior_quadratic_remainder
    (by simp) (by norm_num) φ hf
  have hm := sourceFiniteGap_quadratic_remainder_mass φ hf h r hr hh he
  refine ⟨r, hr, h, hh, ?_, he, ?_⟩
  · rw [hm]
    ring_nf
    norm_num [I_sq]
  · intro R hR hRr
    rw [hc R hR hRr, hm]
    ring

/-- Every sufficiently large weighted contour of the actual finite-gap
quotient equals `π` times the original source mass. -/
theorem exists_sourceFiniteGap_weighted_contour_eq_mass
    (φ : realTypeSourceSubmodule 2)
    (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    ∃ T : ℝ, 0 < T ∧ ∀ R : ℝ, T ≤ R →
      (∮ z in C(0,R), z * sourceFloquetLogDerivative (by simp) (by norm_num) φ.val z) =
        (Real.pi : ℂ)*sourceHilbertMass φ.val := by
  obtain ⟨r, hr, _, _, _, _, hc⟩ := exists_sourceFiniteGap_mass_remainder φ hf
  refine ⟨r⁻¹+1, by positivity, ?_⟩
  intro R hR
  have hRpos : 0 < R := by linarith [inv_pos.mpr hr]
  apply hc R hRpos
  exact (inv_lt_comm₀ hRpos hr).mpr (by linarith)

/-- The large exterior contour recovers half the original Hilbert pair norm squared. -/
theorem exists_sourceFiniteGap_weighted_contour_eq_norm
    (φ : realTypeSourceSubmodule 2)
    (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    ∃ T : ℝ, 0 < T ∧ ∀ R : ℝ, T ≤ R →
      (∮ z in C(0,R), z * sourceFloquetLogDerivative (by simp) (by norm_num) φ.val z) =
        (Real.pi : ℂ)*((‖φ.val‖^2/2 : ℝ) : ℂ) := by
  simpa only [sourceHilbertMass_eq_half_norm_sq_of_realType φ.val φ.property] using
    exists_sourceFiniteGap_weighted_contour_eq_mass φ hf

end NLS.ZakharovShabat
