import NLS.ComplexAnalysis.CubicInversionRemainder
import NLS.ComplexAnalysis.InversionCircleCoefficients

/-! # The physical momentum coefficient of a squared inverse-frequency phase

The first two Taylor coefficients give an exact analytic inverse-square
remainder. Its contour integral vanishes, leaving precisely πi times H₂.
-/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ComplexAnalysis

/-- The square has its exact simple-pole coefficient and an analytic inverse-square remainder. -/
theorem exists_phase_square_analytic_remainder (A : ℂ → ℂ) (hA : AnalyticAt ℂ A 0)
    (hA0 : A 0 = 0) (H₁ H₂ : ℂ)
    (h₁ : iteratedDeriv 1 A 0 = I*H₁/2)
    (h₂ : iteratedDeriv 2 A 0 = I*H₂/2) :
    ∃ B : ℂ → ℂ, AnalyticAt ℂ B 0 ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ z : ℂ,
      z ≠ 0 → ‖z⁻¹‖ < ε →
      (-I*z+A z⁻¹)^2 = -z^2+H₁+H₂/(2*z)+z⁻¹^2*B z⁻¹ := by
  obtain ⟨D,hD,hTaylor⟩ := hA.exists_eventuallyEq_sum_add_pow_mul 3
  have ht : ∀ᶠ w in 𝓝 (0 : ℂ),
      A w = (I*H₁/2)*w+(I*H₂/4)*w^2+w^3*D w := by
    filter_upwards [hTaylor] with w hw
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,iteratedDeriv_zero,
      hA0,smul_eq_mul,mul_zero,h₁,h₂] at hw
    norm_num [Nat.factorial] at hw
    rw [hw]
    ring
  let Q : ℂ → ℂ := fun w => I*H₁/2+(I*H₂/4)*w+w^2*D w
  let B : ℂ → ℂ := fun w => -2*I*D w+(Q w)^2
  have hQ : AnalyticAt ℂ Q 0 := by dsimp [Q]; fun_prop
  have hB : AnalyticAt ℂ B 0 := by dsimp [B]; fun_prop
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp ht
  refine ⟨B,hB,ε,hε,?_⟩
  intro z hz hw
  have he := hball (show z⁻¹ ∈ ball (0 : ℂ) ε by simpa using hw)
  rw [he]
  dsimp [B,Q]
  field_simp
  ring_nf
  simp only [I_sq]
  ring

/-- The contour coefficient is πiH₂; the analytic inverse-square remainder contributes zero. -/
theorem exists_phase_square_contour (A : ℂ → ℂ) (hA : AnalyticAt ℂ A 0)
    (hA0 : A 0 = 0) (H₁ H₂ : ℂ)
    (h₁ : iteratedDeriv 1 A 0 = I*H₁/2)
    (h₂ : iteratedDeriv 2 A 0 = I*H₂/2) :
    ∃ T : ℝ, 0 < T ∧ ∀ R : ℝ, T ≤ R →
      (∮ z in C(0,R), (-I*z+A z⁻¹)^2) = (Real.pi : ℂ)*I*H₂ := by
  obtain ⟨B,hB,ε,hε,he⟩ := exists_phase_square_analytic_remainder A hA hA0 H₁ H₂ h₁ h₂
  obtain ⟨r,hr,hBr⟩ := hB.exists_ball_analyticOnNhd
  let g : ℂ → ℂ := fun w => (H₂/2)*w+w^2*B w
  let P : ℂ → ℂ := fun z => -z^2+H₁
  have hg : AnalyticOnNhd ℂ g (ball 0 r) := by
    intro w hw
    exact (analyticAt_const.mul analyticAt_id).add ((analyticAt_id.pow 2).mul (hBr w hw))
  have hd : deriv g 0 = H₂/2 := by
    have h := ((hasDerivAt_id (0:ℂ)).const_mul (H₂/2)).add
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
      dsimp [P,g]
      rw [div_eq_mul_inv]
      ring
    _ = (∮ z in C(0,R), P z)+(∮ z in C(0,R), g z⁻¹) :=
      circleIntegral.integral_add (hP.continuous.continuousOn.circleIntegrable hR.le) hgi
    _ = _ := by
      rw [hzero,zero_add,circleIntegral_comp_inv_eq g r R hr hR hRr hg,hd]
      ring
end NLS.ComplexAnalysis
