import NLS.ComplexAnalysis.AnalyticTwoZeroRoot
import NLS.ComplexAnalysis.QuadraticRootPrimitive
import NLS.ComplexAnalysis.CircleIntegralIntegrationByParts
import NLS.ZakharovShabat.SourceStandardRootContourMidpoint

/-! # The oriented contour period of the normalized endpoint root

Differentiating (lambda-midpoint)*root expresses its derivative as
twice the root plus a constant times the inverse root. The known inverse
period then fixes the exact root period, with counterclockwise orientation.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis

theorem circleIntegral_quadratic_root_of_inverse_period
    (Q : ℂ → ℂ) (tau d c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hQ : AnalyticOnNhd ℂ Q (sphere c R))
    (hne : ∀ z ∈ sphere c R, Q z ≠ 0)
    (hsq : ∀ z ∈ sphere c R, Q z^2 = (z-tau)^2-d)
    (hd : ∀ z ∈ sphere c R, HasDerivAt Q ((z-tau)/Q z) z)
    (hinv : (∮ z in C(c,R), (Q z)⁻¹) = -(2*Real.pi*I)) :
    (∮ z in C(c,R), Q z) = (Real.pi*I)*d := by
  let H : ℂ → ℂ := fun z => (z-tau)*Q z
  have hder (z : ℂ) (hz : z ∈ sphere c R) : HasDerivAt H (2*Q z+d*(Q z)⁻¹) z := by
    have he : Q z+(z-tau)*((z-tau)/Q z) = 2*Q z+d*(Q z)⁻¹ := by
      have hh := hsq z hz
      field_simp [hne z hz]
      linear_combination -hh
    convert! (((hasDerivAt_id z).sub_const tau).mul (hd z hz)) using 1
    simpa only [id_eq,one_mul] using he.symm
  have hzero : (∮ z in C(c,R), deriv H z) = 0 :=
    circleIntegral.integral_eq_zero_of_hasDerivWithinAt hR
      (fun z hz => (hder z hz).differentiableAt.hasDerivAt.hasDerivWithinAt)
  have hi : CircleIntegrable Q c R := hQ.continuousOn.circleIntegrable hR
  have hri : CircleIntegrable (fun z => (Q z)⁻¹) c R :=
    (hQ.continuousOn.inv₀ hne).circleIntegrable hR
  have hi2 : CircleIntegrable (fun z => 2*Q z) c R := hi.const_mul 2
  have hdi : CircleIntegrable (fun z => d*(Q z)⁻¹) c R := hri.const_mul d
  have heq : (∮ z in C(c,R), 2*Q z+d*(Q z)⁻¹) = 0 := by
    rw [← hzero]
    apply circleIntegral.integral_congr hR
    intro z hz
    exact (hder z hz).deriv.symm
  rw [circleIntegral.integral_add hi2 hdi,
    circleIntegral.integral_const_mul,circleIntegral.integral_const_mul,hinv] at heq
  linear_combination (1/2 : ℂ)*heq

theorem endpointRoot_ne_zero (a b z : ℂ) (hz : z ∉ segment ℝ a b) :
    endpointRoot a b z ≠ 0 := by
  have hza : z ≠ a := fun he => hz (he ▸ left_mem_segment ℝ a b)
  have hzb : z ≠ b := fun he => hz (he ▸ right_mem_segment ℝ a b)
  intro he
  have hh := endpointRoot_sq a b z hz
  rw [he,zero_pow (by norm_num : 2 ≠ 0)] at hh
  exact mul_ne_zero (sub_ne_zero.mpr hza) (sub_ne_zero.mpr hzb) hh.symm

theorem endpointRoot_hasDerivAt (a b z : ℂ) (hz : z ∉ segment ℝ a b) :
    HasDerivAt (endpointRoot a b) ((z-(a+b)/2)/endpointRoot a b z) z := by
  apply hasDerivAt_root_of_sq_eq_quadratic (endpointRoot a b) ((a+b)/2) ((a-b)^2/4) z
    (analyticOnNhd_endpointRoot a b z hz) (endpointRoot_ne_zero a b z hz)
  have hclosed : IsClosed (segment ℝ a b) := by
    apply IsCompact.isClosed
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  filter_upwards [hclosed.isOpen_compl.mem_nhds hz] with w hw
  rw [endpointRoot_sq a b w hw]
  dsimp only [quadraticRootPolynomial]
  ring

/-- The whole gap-length circle has exact endpoint-root period
pi*i*(a-b)^2/4. No reality assumption on the endpoints is used. -/
theorem circleIntegral_endpointRoot (a b : ℂ) (hab : a ≠ b) :
    (∮ z in C((a+b)/2,‖a-b‖), endpointRoot a b z) =
      (Real.pi*I/4)*(a-b)^2 := by
  let gamma : ℝ := ‖a-b‖
  have hgamma : 0 < gamma := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
  have hseg : segment ℝ a b ⊆ ball ((a+b)/2) gamma := by
    apply (convex_ball _ _).segment_subset
    · rw [mem_ball,dist_eq_norm,show a-(a+b)/2 = (a-b)/2 by ring,norm_div]
      norm_num
      change gamma/2 < gamma
      linarith
    · rw [mem_ball,dist_eq_norm,show b-(a+b)/2 = (b-a)/2 by ring,norm_div,norm_sub_rev b a]
      norm_num
      change gamma/2 < gamma
      linarith
  have hcircle (z : ℂ) (hz : z ∈ sphere ((a+b)/2) gamma) : z ∉ segment ℝ a b := by
    intro hh
    exact sphere_disjoint_ball.le_bot ⟨hz,hseg hh⟩
  have hinv : (∮ z in C((a+b)/2,gamma), (endpointRoot a b z)⁻¹) = -(2*Real.pi*I) := by
    apply NLS.ZakharovShabat.circleIntegral_normalizedRoot_inv_of_radius _ _ gamma hgamma
    have he : ‖(b-a)^2‖*(gamma⁻¹)^2 = 1 := by
      rw [norm_pow,norm_sub_rev b a]
      change gamma^2*(gamma⁻¹)^2 = 1
      rw [← mul_pow,mul_inv_cancel₀ hgamma.ne',one_pow]
    rw [he]
    norm_num
  have heq := circleIntegral_quadratic_root_of_inverse_period (endpointRoot a b)
    ((a+b)/2) ((a-b)^2/4) ((a+b)/2) gamma hgamma.le
    (fun z hz => analyticOnNhd_endpointRoot a b z (hcircle z hz))
    (fun z hz => endpointRoot_ne_zero a b z (hcircle z hz))
    (fun z hz => by rw [endpointRoot_sq a b z (hcircle z hz)]; ring)
    (fun z hz => endpointRoot_hasDerivAt a b z (hcircle z hz)) hinv
  convert heq using 1
  ring

end NLS.ComplexAnalysis
