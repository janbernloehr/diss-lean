import NLS.ComplexAnalysis.InversionCircleCoefficients

/-! Dividing the squared exterior Floquet phase by the spectral variable
extracts its physical mass coefficient. Only the actual first Taylor
coefficient is used; no formal Laurent-residue assumption is introduced. -/
noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis

theorem exists_phase_inverse_square_mass_contour (A : ℂ → ℂ)
    (hA : AnalyticAt ℂ A 0) (hA0 : A 0=0) (M : ℂ) (hM : deriv A 0=I*M/2) :
    ∃ T : ℝ, 0 < T ∧ ∀ R : ℝ, T ≤ R →
      (∮ z in C(0,R), (-I*z+A z⁻¹)^2/z)=(2*Real.pi*I:ℂ)*M := by
  obtain ⟨r,hr,hAr⟩ := hA.exists_ball_analyticOnNhd
  let g : ℂ → ℂ := fun w => -2*I*A w+w*(A w)^2
  have hg : AnalyticOnNhd ℂ g (ball 0 r) := by
    intro w hw
    exact (analyticAt_const.mul (hAr w hw)).add (analyticAt_id.mul ((hAr w hw).pow 2))
  have hd : deriv g 0=M := by
    have h := (hA.differentiableAt.hasDerivAt.const_mul (-2*I)).add
      ((hasDerivAt_id (0:ℂ)).mul (hA.differentiableAt.hasDerivAt.pow 2))
    have he : deriv g 0=(-2*I)*deriv A 0+(1*(A 0)^2+0*(2*A 0*deriv A 0)) := by
      simpa only [g,Pi.add_apply,Pi.mul_apply,Pi.pow_apply,id_eq,Nat.reduceSub,pow_one] using! h.deriv
    rw [he,hA0,hM]
    ring_nf
    simp [I_sq]
  let T := r⁻¹+1
  have hT : 0 < T := by dsimp [T]; positivity
  refine ⟨T,hT,?_⟩
  intro R hTR
  have hR : 0 < R := hT.trans_le hTR
  have hRr : R⁻¹ < r := (inv_lt_comm₀ hR hr).mpr (by dsimp [T] at hTR; linarith)
  have hz0 (z : ℂ) (hz : z ∈ sphere (0:ℂ) R) : z ≠ 0 := by
    have hn : ‖z‖=R := by simpa only [mem_sphere,dist_zero_right] using hz
    exact norm_pos_iff.mp (hn.symm ▸ hR)
  have hgi : CircleIntegrable (fun z => g z⁻¹) 0 R := by
    apply ContinuousOn.circleIntegrable hR.le
    intro z hz
    have hn : ‖z‖=R := by simpa only [mem_sphere,dist_zero_right] using hz
    have hw : z⁻¹ ∈ ball (0:ℂ) r := by simpa only [mem_ball,dist_zero_right,norm_inv,hn] using hRr
    exact ((hg _ hw).continuousAt.comp (continuousAt_inv₀ (hz0 z hz))).continuousWithinAt
  have hzero : (∮ z in C(0,R), -z)=0 := by
    have hP : Differentiable ℂ (fun z : ℂ => -z) := differentiable_id.neg
    exact (DiffContOnCl.mk_ball hP.differentiableOn hP.continuous.continuousOn).circleIntegral_eq_zero hR.le
  calc
    _ = ∮ z in C(0,R), -z+g z⁻¹ := by
      apply circleIntegral.integral_congr hR.le
      intro z hz
      dsimp [g]
      field_simp [hz0 z hz]
      ring_nf
      simp only [I_sq]
      ring
    _ = (∮ z in C(0,R), -z)+(∮ z in C(0,R), g z⁻¹) :=
      circleIntegral.integral_add (continuous_neg.continuousOn.circleIntegrable hR.le) hgi
    _ = _ := by rw [hzero,zero_add,circleIntegral_comp_inv_eq g r R hr hR hRr hg,hd]

end NLS.ComplexAnalysis
