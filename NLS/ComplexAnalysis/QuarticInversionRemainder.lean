import NLS.ComplexAnalysis.CubicInversionRemainder

/-! # The fourth power of a normalized KdV inversion phase -/
noncomputable section
set_option autoImplicit false
open Set Metric Filter Topology Complex
namespace NLS.ComplexAnalysis

/-- The physical third and fifth coefficients determine the constant and
inverse-square terms of the quartic phase. The remaining term is an
analytic inverse-frequency remainder of order three. -/
theorem exists_phase_fourth_analytic_remainder
    (A : ℂ → ℂ) (hA : AnalyticAt ℂ A 0) (hA0 : A 0 = 0) (H₀ H : ℂ)
    (h₁ : iteratedDeriv 1 A 0 = 0) (h₂ : iteratedDeriv 2 A 0 = 0)
    (h₃ : iteratedDeriv 3 A 0 = 3*I*H₀/2) (h₄ : iteratedDeriv 4 A 0 = 0)
    (h₅ : iteratedDeriv 5 A 0 = 15*I*H/2) :
    ∃ B : ℂ → ℂ, AnalyticAt ℂ B 0 ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ z : ℂ,
      z ≠ 0 → ‖z⁻¹‖ < ε →
      (-I*z+A z⁻¹)^4 = z^4-H₀-(H/4)*z⁻¹^2+z⁻¹^3*B z⁻¹ := by
  obtain ⟨D,hD,hTaylor⟩ := hA.exists_eventuallyEq_sum_add_pow_mul 6
  have ht : ∀ᶠ w in nhds (0 : ℂ),
      A w = (I*H₀/4)*w^3+(I*H/16)*w^5+w^6*D w := by
    filter_upwards [hTaylor] with w hw
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,iteratedDeriv_zero,
      hA0,smul_eq_mul,mul_zero,h₁,h₂,h₃,h₄,h₅] at hw
    norm_num [Nat.factorial] at hw
    rw [hw]
    ring
  let Q : ℂ → ℂ := fun w => I*H₀/4+(I*H/16)*w^2+w^3*D w
  let B : ℂ → ℂ := fun w => 4*I*D w-6*w*(Q w)^2-4*I*w^5*(Q w)^3+w^9*(Q w)^4
  have hQ : AnalyticAt ℂ Q 0 := by dsimp [Q]; fun_prop
  have hB : AnalyticAt ℂ B 0 := by dsimp [B]; fun_prop
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp ht
  refine ⟨B,hB,ε,hε,?_⟩
  intro z hz hw
  have he := hball (show z⁻¹ ∈ ball (0 : ℂ) ε by simpa using hw)
  have heA : A z⁻¹ = z⁻¹^3*Q z⁻¹ := by rw [he]; dsimp [Q]; ring
  rw [heA]
  have hid (a b d : ℂ) :
      (-I*z+z⁻¹^3*(a+b*z⁻¹^2+z⁻¹^3*d))^4 = z^4+4*I*a+4*I*b*z⁻¹^2+
        z⁻¹^3*(4*I*d-6*z⁻¹*(a+b*z⁻¹^2+z⁻¹^3*d)^2-
          4*I*z⁻¹^5*(a+b*z⁻¹^2+z⁻¹^3*d)^3+z⁻¹^9*(a+b*z⁻¹^2+z⁻¹^3*d)^4) := by
    field_simp
    ring_nf
    simp only [I_sq,I_pow_three,I_pow_four]
    ring
  change (-I*z+z⁻¹^3*(I*H₀/4+(I*H/16)*z⁻¹^2+z⁻¹^3*D z⁻¹))^4 = _
  rw [hid]
  dsimp only [B,Q]
  ring_nf
  simp only [I_sq]
  ring

end NLS.ComplexAnalysis
