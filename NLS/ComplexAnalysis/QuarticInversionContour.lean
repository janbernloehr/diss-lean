import NLS.ComplexAnalysis.QuarticInversionRemainder
import NLS.ComplexAnalysis.InversionCircleCoefficients

/-! # The exact quartic Hamiltonian contour coefficient

The analytic inverse-frequency remainder contributes no period. The
simple-pole term therefore recovers the renormalized fourth Hamiltonian
exactly on every sufficiently large circle.
-/
noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis

theorem exists_phase_fourth_contour (A : ℂ → ℂ) (hA : AnalyticAt ℂ A 0)
    (hA0 : A 0 = 0) (H₁ H₂ H₃ H₄ : ℂ)
    (h₁ : iteratedDeriv 1 A 0 = I*H₁/2)
    (h₂ : iteratedDeriv 2 A 0 = I*H₂/2)
    (h₃ : iteratedDeriv 3 A 0 = 3*I*H₃/4)
    (h₄ : iteratedDeriv 4 A 0 = 3*I*H₄/2) :
    ∃ T : ℝ, 0 < T ∧ ∀ R : ℝ, T ≤ R →
      (∮ z in C(0,R), (-I*z+A z⁻¹)^4) = -(Real.pi*I/2 : ℂ)*(H₄-6*H₁*H₂) := by
  obtain ⟨B,hB,ε,hε,he⟩ := exists_phase_fourth_analytic_remainder A hA hA0 H₁ H₂ H₃ H₄ h₁ h₂ h₃ h₄
  obtain ⟨r,hr,hBr⟩ := hB.exists_ball_analyticOnNhd
  let a : ℂ := -(H₄-6*H₁*H₂)/4
  let g : ℂ → ℂ := fun w => a*w+w^2*B w
  let P : ℂ → ℂ := fun z => z^4-2*H₁*z^2-H₂*z-(H₃-3*H₁^2)/2
  have hg : AnalyticOnNhd ℂ g (ball 0 r) := by
    intro w hw
    exact (analyticAt_const.mul analyticAt_id).add ((analyticAt_id.pow 2).mul (hBr w hw))
  have hd : deriv g 0 = a := by
    have h := ((hasDerivAt_id (0:ℂ)).const_mul a).add
      (((hasDerivAt_id (0:ℂ)).pow 2).mul hB.differentiableAt.hasDerivAt)
    simpa [g,Pi.add_apply,Pi.mul_apply,Pi.pow_apply] using! h.deriv
  let T := max ε⁻¹ r⁻¹+1
  have hT : 0 < T := by dsimp [T]; linarith [inv_pos.mpr hε,le_max_left ε⁻¹ r⁻¹]
  refine ⟨T,hT,?_⟩
  intro R hTR
  have hR : 0 < R := hT.trans_le hTR
  have hRε : R⁻¹ < ε := (inv_lt_comm₀ hR hε).mpr (by dsimp [T] at hTR; linarith [le_max_left ε⁻¹ r⁻¹])
  have hRr : R⁻¹ < r := (inv_lt_comm₀ hR hr).mpr (by dsimp [T] at hTR; linarith [le_max_right ε⁻¹ r⁻¹])
  have hz0 (z : ℂ) (hz : z ∈ sphere (0:ℂ) R) : z ≠ 0 := by
    have hn : ‖z‖ = R := by simpa only [mem_sphere,dist_zero_right] using hz
    exact norm_pos_iff.mp (hn.symm ▸ hR)
  have hzball (z : ℂ) (hz : z ∈ sphere (0:ℂ) R) : z⁻¹ ∈ ball (0:ℂ) r := by
    have hn : ‖z‖ = R := by simpa only [mem_sphere,dist_zero_right] using hz
    simpa only [mem_ball,dist_zero_right,norm_inv,hn] using hRr
  have hgi : CircleIntegrable (fun z => g z⁻¹) 0 R := by
    apply ContinuousOn.circleIntegrable hR.le
    intro z hz
    exact ((hg _ (hzball z hz)).continuousAt.comp (continuousAt_inv₀ (hz0 z hz))).continuousWithinAt
  have hP : Differentiable ℂ P := by intro z; dsimp [P]; fun_prop
  have hzero : (∮ z in C(0,R), P z) = 0 :=
    (DiffContOnCl.mk_ball hP.differentiableOn hP.continuous.continuousOn).circleIntegral_eq_zero hR.le
  calc
    _ = ∮ z in C(0,R), P z+g z⁻¹ := by
      apply circleIntegral.integral_congr hR.le
      intro z hz
      have hn : ‖z‖ = R := by simpa only [mem_sphere,dist_zero_right] using hz
      dsimp only
      rw [he z (hz0 z hz) (by simpa only [norm_inv,hn] using hRε)]
      dsimp [phaseFourthLaurentPart,P,g,a]
      simp only [div_eq_mul_inv]
      ring
    _ = (∮ z in C(0,R), P z)+(∮ z in C(0,R), g z⁻¹) :=
      circleIntegral.integral_add (hP.continuous.continuousOn.circleIntegrable hR.le) hgi
    _ = _ := by
      rw [hzero,zero_add,circleIntegral_comp_inv_eq g r R hr hR hRr hg,hd]
      dsimp [a]
      ring

end NLS.ComplexAnalysis
