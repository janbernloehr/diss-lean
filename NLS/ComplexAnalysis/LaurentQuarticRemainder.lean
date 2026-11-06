import NLS.ComplexAnalysis.QuarticInversionRemainder
import NLS.ComplexAnalysis.LaurentSquareRemainder

/-! # Uniform quartic errors for normalized inverse-frequency phases -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis

theorem norm_fourth_sub_fourth_le (F P : ℂ) (Y : ℝ) (hY : 0 ≤ Y)
    (hF : ‖F‖ ≤ Y) (hP : ‖P‖ ≤ Y) :
    ‖F^4-P^4‖ ≤ 4*Y^3*‖F-P‖ := by
  have hsq : ‖F^2-P^2‖ ≤ ‖F-P‖*(2*Y) := by
    rw [show F^2-P^2 = (F-P)*(F+P) by ring,norm_mul]
    exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (by linarith)) (norm_nonneg _)
  have hplus : ‖F^2+P^2‖ ≤ 2*Y^2 := by
    have hh := norm_add_le (F^2) (P^2)
    simp only [norm_pow] at hh
    nlinarith [sq_le_sq₀ (norm_nonneg F) hY |>.mpr hF,
      sq_le_sq₀ (norm_nonneg P) hY |>.mpr hP]
  rw [show F^4-P^4 = (F^2-P^2)*(F^2+P^2) by ring,norm_mul]
  calc
    _ ≤ (‖F-P‖*(2*Y))*(2*Y^2) := mul_le_mul hsq hplus (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem norm_weighted_fourth_error_of_phase_error (F P z : ℂ) (D B : ℝ)
    (hz : 1 ≤ ‖z‖) (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hP : ‖P‖ ≤ B*‖z‖) (herror : ‖z‖^6*‖F-P‖ ≤ D) :
    ‖z‖^3*‖F^4-P^4‖ ≤ 4*(B+D)^3*D := by
  have hr : 0 ≤ ‖z‖ := norm_nonneg _
  have hr6 : 1 ≤ ‖z‖^6 := one_le_pow₀ hz
  have he : ‖F-P‖ ≤ D := by nlinarith [norm_nonneg (F-P)]
  have hF : ‖F‖ ≤ (B+D)*‖z‖ := by
    have hh := norm_add_le (F-P) P
    rw [sub_add_cancel] at hh
    nlinarith
  have hP' : ‖P‖ ≤ (B+D)*‖z‖ := by nlinarith
  have hh := mul_le_mul_of_nonneg_left
    (norm_fourth_sub_fourth_le F P ((B+D)*‖z‖) (by positivity) hF hP')
    (pow_nonneg hr 3)
  calc
    _ ≤ ‖z‖^3*(4*((B+D)*‖z‖)^3*‖F-P‖) := hh
    _ = (4*(B+D)^3)*(‖z‖^6*‖F-P‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left herror (by positivity)

theorem exists_phase_fourth_error_bound
    (A : ℂ → ℂ) (hA : AnalyticAt ℂ A 0) (hA0 : A 0 = 0) (H₀ H : ℂ)
    (h₁ : iteratedDeriv 1 A 0 = 0) (h₂ : iteratedDeriv 2 A 0 = 0)
    (h₃ : iteratedDeriv 3 A 0 = 3*I*H₀/2) (h₄ : iteratedDeriv 4 A 0 = 0)
    (h₅ : iteratedDeriv 5 A 0 = 15*I*H/2) :
    ∃ R : ℝ, 0 < R ∧ ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, R < ‖z‖ →
      ‖z‖^3*‖(-I*z+A z⁻¹)^4-z^4+H₀+H/(4*z^2)‖ ≤ C := by
  obtain ⟨B,hB,ε,hε,he⟩ := exists_phase_fourth_analytic_remainder A hA hA0 H₀ H h₁ h₂ h₃ h₄ h₅
  have hb : ∀ᶠ w in nhds (0 : ℂ), ‖B w‖ < ‖B 0‖+1 :=
    hB.continuousAt.norm.tendsto.eventually (gt_mem_nhds (lt_add_one _))
  obtain ⟨δ,hδ,hbound⟩ := Metric.mem_nhds_iff.mp hb
  refine ⟨max ε⁻¹ δ⁻¹,(inv_pos.mpr hε).trans_le (le_max_left _ _),‖B 0‖+1,by positivity,?_⟩
  intro z hz
  have hzpos : 0 < ‖z‖ := (inv_pos.mpr hε).trans ((le_max_left _ _).trans_lt hz)
  have hz0 : z ≠ 0 := norm_pos_iff.mp hzpos
  have hwε : ‖z⁻¹‖ < ε := by
    rw [norm_inv];exact (inv_lt_comm₀ hzpos hε).mpr ((le_max_left _ _).trans_lt hz)
  have hwδ : z⁻¹ ∈ ball (0 : ℂ) δ := by
    rw [mem_ball,dist_zero_right,norm_inv]
    exact (inv_lt_comm₀ hzpos hδ).mpr ((le_max_right _ _).trans_lt hz)
  have hrem : (-I*z+A z⁻¹)^4-z^4+H₀+H/(4*z^2) = z⁻¹^3*B z⁻¹ := by
    rw [he z hz0 hwε]
    field_simp
    ring
  rw [hrem,norm_mul,norm_pow,norm_inv]
  have hc : ‖z‖^3*((‖z‖⁻¹)^3*‖B z⁻¹‖) = ‖B z⁻¹‖ := by field_simp
  rw [hc]
  exact (hbound hwδ).le

end NLS.ComplexAnalysis
