import NLS.ComplexAnalysis.InversionCircleCoefficients

/-! # Mass extracted by the squared phase divided by frequency

Only the first inverse-frequency coefficient is needed. The exact
algebraic identity leaves a polynomial and an analytic function of 1/z;
the existing inversion contour formula extracts its first derivative.
-/
noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis

/-- The mass contour of an actual analytic inverse-frequency phase.
No second Taylor coefficient or asymptotic error is assumed. -/
theorem exists_phase_square_over_frequency_contour (A : ℂ → ℂ)
    (hA : AnalyticAt ℂ A 0) (hA0 : A 0 = 0) (H : ℂ)
    (hd : deriv A 0 = I*H/2) :
    ∃ T : ℝ, 0 < T ∧ ∀ R : ℝ, T ≤ R →
      (∮ z in C(0,R), (-I*z+A z⁻¹)^2/z) = (2*Real.pi*I : ℂ)*H := by
  obtain ⟨r,hr,hAr⟩ := hA.exists_ball_analyticOnNhd
  let g : ℂ → ℂ := fun w => -2*I*A w+w*(A w)^2
  have hg : AnalyticOnNhd ℂ g (ball 0 r) := by
    intro w hw
    exact (analyticAt_const.mul (hAr w hw)).add (analyticAt_id.mul ((hAr w hw).pow 2))
  have hgd : deriv g 0 = H := by
    have h := (hA.differentiableAt.hasDerivAt.const_mul (-2*I)).add
      ((hasDerivAt_id (0 : ℂ)).mul (hA.differentiableAt.hasDerivAt.pow 2))
    have he := h.deriv
    change deriv g 0 = _ at he
    rw [he]
    simp only [Pi.pow_apply,id_eq,hA0,zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      mul_zero,zero_mul,add_zero]
    rw [hd]
    linear_combination -H*I_sq
  let T := r⁻¹+1
  have hT : 0 < T := by dsimp [T]; linarith [inv_pos.mpr hr]
  refine ⟨T,hT,?_⟩
  intro R hTR
  have hR := hT.trans_le hTR
  have hRr : R⁻¹ < r := (inv_lt_comm₀ hR hr).mpr (by dsimp [T] at hTR; linarith)
  have hgi : CircleIntegrable (fun z => g z⁻¹) 0 R := by
    apply ContinuousOn.circleIntegrable hR.le
    intro z hz
    have hn : ‖z‖ = R := by simpa only [mem_sphere,dist_zero_right] using hz
    have hz0 : z ≠ 0 := norm_pos_iff.mp (hn.symm ▸ hR)
    exact ((hg _ (by simpa only [mem_ball,dist_zero_right,norm_inv,hn] using hRr)).continuousAt.comp
      (continuousAt_inv₀ hz0)).continuousWithinAt
  have hP : Differentiable ℂ (fun z : ℂ => -z) := differentiable_id.neg
  have hzero : (∮ z in C(0,R), -z) = 0 :=
    (DiffContOnCl.mk_ball hP.differentiableOn hP.continuous.continuousOn).circleIntegral_eq_zero hR.le
  calc
    _ = ∮ z in C(0,R), -z+g z⁻¹ := by
      apply circleIntegral.integral_congr hR.le
      intro z hz
      have hn : ‖z‖ = R := by simpa only [mem_sphere,dist_zero_right] using hz
      have hz0 : z ≠ 0 := norm_pos_iff.mp (hn.symm ▸ hR)
      dsimp [g]
      field_simp
      ring_nf
      simp only [I_sq]
      ring
    _ = (∮ z in C(0,R), -z)+(∮ z in C(0,R), g z⁻¹) :=
      circleIntegral.integral_add (hP.continuous.continuousOn.circleIntegrable hR.le) hgi
    _ = _ := by rw [hzero,zero_add,circleIntegral_comp_inv_eq g r R hr hR hRr hg,hgd]

/-- A square vanishing at the origin has an analytic quotient by frequency,
with its literal value zero at the origin. The apparent pole is removable. -/
theorem analyticOnNhd_square_div_id_of_zero (F : ℂ → ℂ) (U : Set ℂ)
    (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U) (hF : AnalyticOnNhd ℂ F U) (hF0 : F 0 = 0) :
    AnalyticOnNhd ℂ (fun z => (F z)^2/z) U := by
  have hds : AnalyticOnNhd ℂ (dslope F 0) U :=
    ((differentiableOn_dslope (hU.mem_nhds h0)).mpr hF.differentiableOn).analyticOnNhd hU
  have he : (fun z => (F z)^2/z) = (fun z => F z*dslope F 0 z) := by
    funext z
    by_cases hz : z = 0
    · simp only [hz,hF0,zero_pow (by norm_num : (2 : ℕ) ≠ 0),zero_div,zero_mul]
    · rw [dslope_of_ne F hz,slope_def_field,sub_zero,hF0,sub_zero]
      ring
  rw [he]
  exact hF.mul hds

end NLS.ComplexAnalysis
