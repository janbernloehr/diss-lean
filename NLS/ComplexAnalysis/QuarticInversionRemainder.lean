import NLS.ComplexAnalysis.CubicInversionRemainder

/-! # The quartic Laurent coefficient of an analytic inversion phase

The first four physical Hamiltonian coefficients determine the quartic
phase through its simple pole. The remaining part is an analytic function
of inverse frequency times z^-2, uniformly in all complex directions.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Filter Topology Complex
namespace NLS.ComplexAnalysis

/-- The Laurent part that recovers H₄ − 6H₁H₂ from the actual phase. -/
def phaseFourthLaurentPart (H₁ H₂ H₃ H₄ z : ℂ) : ℂ :=
  z^4-2*H₁*z^2-H₂*z-(H₃-3*H₁^2)/2-(H₄-6*H₁*H₂)/(4*z)

private theorem fourth_phase_identity (z a b c d e : ℂ) (hz : z ≠ 0) :
    let Q := a+b*z⁻¹+c*z⁻¹^2+d*z⁻¹^3+z⁻¹^4*e
    let R := b+c*z⁻¹+d*z⁻¹^2+z⁻¹^3*e
    (-I*z+z⁻¹*Q)^4 = z^4+4*I*a*z^2+4*I*b*z+(4*I*c-6*a^2)+(4*I*d-12*a*b)*z⁻¹+
      z⁻¹^2*(4*I*e-12*a*(c+d*z⁻¹+z⁻¹^2*e)-6*R^2-4*I*Q^3+z⁻¹^2*Q^4) := by
  dsimp only
  field_simp
  ring_nf
  simp only [I_sq,I_pow_three,I_pow_four]
  ring

/-- The quartic Laurent error factors as z^-2 times an analytic germ. -/
theorem exists_phase_fourth_analytic_remainder (A : ℂ → ℂ) (hA : AnalyticAt ℂ A 0)
    (hA0 : A 0 = 0) (H₁ H₂ H₃ H₄ : ℂ)
    (h₁ : iteratedDeriv 1 A 0 = I*H₁/2)
    (h₂ : iteratedDeriv 2 A 0 = I*H₂/2)
    (h₃ : iteratedDeriv 3 A 0 = 3*I*H₃/4)
    (h₄ : iteratedDeriv 4 A 0 = 3*I*H₄/2) :
    ∃ B : ℂ → ℂ, AnalyticAt ℂ B 0 ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ z : ℂ,
      z ≠ 0 → ‖z⁻¹‖ < ε →
      (-I*z+A z⁻¹)^4 = phaseFourthLaurentPart H₁ H₂ H₃ H₄ z+z⁻¹^2*B z⁻¹ := by
  obtain ⟨D,hD,hTaylor⟩ := hA.exists_eventuallyEq_sum_add_pow_mul 5
  have ht : ∀ᶠ w in 𝓝 (0 : ℂ),
      A w = (I*H₁/2)*w+(I*H₂/4)*w^2+(I*H₃/8)*w^3+(I*H₄/16)*w^4+w^5*D w := by
    filter_upwards [hTaylor] with w hw
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,iteratedDeriv_zero,
      hA0,smul_eq_mul,mul_zero,h₁,h₂,h₃,h₄] at hw
    norm_num [Nat.factorial] at hw
    rw [hw]
    ring
  let a := I*H₁/2
  let b := I*H₂/4
  let c := I*H₃/8
  let d := I*H₄/16
  let Q : ℂ → ℂ := fun w => a+b*w+c*w^2+d*w^3+w^4*D w
  let R : ℂ → ℂ := fun w => b+c*w+d*w^2+w^3*D w
  let B : ℂ → ℂ := fun w => 4*I*D w-12*a*(c+d*w+w^2*D w)-6*(R w)^2-
    4*I*(Q w)^3+w^2*(Q w)^4
  have hQ : AnalyticAt ℂ Q 0 := by dsimp [Q]; fun_prop
  have hR : AnalyticAt ℂ R 0 := by dsimp [R]; fun_prop
  have hB : AnalyticAt ℂ B 0 := by dsimp [B]; fun_prop
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp ht
  refine ⟨B,hB,ε,hε,?_⟩
  intro z hz hw
  have he := hball (show z⁻¹ ∈ ball (0 : ℂ) ε by simpa using hw)
  have heA : A z⁻¹ = z⁻¹*Q z⁻¹ := by rw [he]; dsimp [Q,a,b,c,d]; ring
  rw [heA]
  have hc := fourth_phase_identity z a b c d (D z⁻¹) hz
  change (-I*z+z⁻¹*Q z⁻¹)^4 = z^4+4*I*a*z^2+4*I*b*z+(4*I*c-6*a^2)+
    (4*I*d-12*a*b)*z⁻¹+z⁻¹^2*B z⁻¹ at hc
  rw [hc]
  congr 1
  dsimp [phaseFourthLaurentPart,a,b,c,d]
  simp only [div_eq_mul_inv]
  ring_nf
  simp only [I_sq]
  ring

/-- The quartic Laurent remainder is uniformly O(z^-2) at infinity. -/
theorem exists_phase_fourth_error_bound (A : ℂ → ℂ) (hA : AnalyticAt ℂ A 0)
    (hA0 : A 0 = 0) (H₁ H₂ H₃ H₄ : ℂ)
    (h₁ : iteratedDeriv 1 A 0 = I*H₁/2)
    (h₂ : iteratedDeriv 2 A 0 = I*H₂/2)
    (h₃ : iteratedDeriv 3 A 0 = 3*I*H₃/4)
    (h₄ : iteratedDeriv 4 A 0 = 3*I*H₄/2) :
    ∃ R : ℝ, 0 < R ∧ ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, R < ‖z‖ →
      ‖(-I*z+A z⁻¹)^4-phaseFourthLaurentPart H₁ H₂ H₃ H₄ z‖ ≤ C/‖z‖^2 := by
  obtain ⟨B,hB,ε,hε,he⟩ := exists_phase_fourth_analytic_remainder A hA hA0 H₁ H₂ H₃ H₄ h₁ h₂ h₃ h₄
  have hb : ∀ᶠ w in 𝓝 (0 : ℂ), ‖B w‖ < ‖B 0‖+1 :=
    hB.continuousAt.norm.tendsto.eventually (gt_mem_nhds (lt_add_one _))
  obtain ⟨δ,hδ,hbound⟩ := Metric.mem_nhds_iff.mp hb
  let R := max ε⁻¹ δ⁻¹
  have hR : 0 < R := (inv_pos.mpr hε).trans_le (le_max_left _ _)
  refine ⟨R,hR,‖B 0‖+1,by positivity,?_⟩
  intro z hz
  have hzpos : 0 < ‖z‖ := hR.trans hz
  have hεz : ‖z⁻¹‖ < ε := by
    rw [norm_inv]
    exact (inv_lt_comm₀ hzpos hε).mpr ((le_max_left _ _).trans_lt hz)
  have hδz : z⁻¹ ∈ ball (0 : ℂ) δ := by
    rw [mem_ball,dist_zero_right,norm_inv]
    exact (inv_lt_comm₀ hzpos hδ).mpr ((le_max_right _ _).trans_lt hz)
  rw [he z (norm_pos_iff.mp hzpos) hεz,add_sub_cancel_left,norm_mul,norm_pow,norm_inv]
  exact (mul_le_mul_of_nonneg_left (hbound hδz).le (by positivity)).trans_eq (by
    rw [div_eq_mul_inv,inv_pow,mul_comm])

end NLS.ComplexAnalysis
