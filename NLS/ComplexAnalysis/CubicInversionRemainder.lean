import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! # Cubing an analytic inverse-frequency phase

The first three Taylor coefficients determine the cubic Laurent expansion.
The omitted terms are an analytic function of inverse frequency times
`z^-2`, giving a uniform quadratic bound in all complex directions.
-/
noncomputable section
open Set Metric Filter Topology Complex
namespace NLS.ComplexAnalysis

/-- The polynomial and simple-pole part of the cubic Hamiltonian expansion. -/
def phaseCubeLaurentPart (H₁ H₂ H₃ z : ℂ) : ℂ :=
  I*z^3-(3*I/2)*H₁*z-(3*I/4)*H₂-(3*I/8)*(H₃-2*H₁^2)/z

private theorem cube_phase_identity (z a b c d : ℂ) (hz : z ≠ 0) :
    let Q := a+b*z⁻¹+c*z⁻¹^2+z⁻¹^3*d
    (-I*z+z⁻¹*Q)^3 = I*z^3-3*a*z-3*b-(3*c+3*I*a^2)*z⁻¹+
      z⁻¹^2*(-3*d-3*I*(Q+a)*(b+c*z⁻¹+z⁻¹^2*d)+z⁻¹*Q^3) := by
  dsimp only
  field_simp
  ring_nf
  simp only [I_sq,I_pow_three]
  ring

/-- The cubic error is exactly a quadratic inverse-frequency factor times
an analytic remainder. -/
theorem exists_phase_cube_analytic_remainder (A : ℂ → ℂ) (hA : AnalyticAt ℂ A 0)
    (hA0 : A 0 = 0) (H₁ H₂ H₃ : ℂ)
    (h₁ : iteratedDeriv 1 A 0 = I*H₁/2)
    (h₂ : iteratedDeriv 2 A 0 = I*H₂/2)
    (h₃ : iteratedDeriv 3 A 0 = 3*I*H₃/4) :
    ∃ B : ℂ → ℂ, AnalyticAt ℂ B 0 ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ z : ℂ,
      z ≠ 0 → ‖z⁻¹‖ < ε →
      (-I*z+A z⁻¹)^3 = phaseCubeLaurentPart H₁ H₂ H₃ z+z⁻¹^2*B z⁻¹ := by
  obtain ⟨D,hD,hTaylor⟩ := hA.exists_eventuallyEq_sum_add_pow_mul 4
  have ht : ∀ᶠ w in 𝓝 (0 : ℂ),
      A w = (I*H₁/2)*w+(I*H₂/4)*w^2+(I*H₃/8)*w^3+w^4*D w := by
    filter_upwards [hTaylor] with w hw
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,iteratedDeriv_zero,
      hA0,smul_eq_mul,mul_zero,h₁,h₂,h₃] at hw
    norm_num [Nat.factorial] at hw
    rw [hw]
    ring
  let a := I*H₁/2
  let b := I*H₂/4
  let c := I*H₃/8
  let Q : ℂ → ℂ := fun w => a+b*w+c*w^2+w^3*D w
  let B : ℂ → ℂ := fun w => -3*D w-3*I*(Q w+a)*(b+c*w+w^2*D w)+w*(Q w)^3
  have hQ : AnalyticAt ℂ Q 0 := by dsimp [Q]; fun_prop
  have hB : AnalyticAt ℂ B 0 := by dsimp [B]; fun_prop
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp ht
  refine ⟨B,hB,ε,hε,?_⟩
  intro z hz hw
  have he := hball (show z⁻¹ ∈ ball (0 : ℂ) ε by simpa using hw)
  have heA : A z⁻¹ = z⁻¹*Q z⁻¹ := by rw [he]; dsimp [Q,a,b,c]; ring
  rw [heA]
  have hc := cube_phase_identity z a b c (D z⁻¹) hz
  change (-I*z+z⁻¹*Q z⁻¹)^3 =
    I*z^3-3*a*z-3*b-(3*c+3*I*a^2)*z⁻¹+z⁻¹^2*B z⁻¹ at hc
  rw [hc]
  congr 1
  dsimp [phaseCubeLaurentPart,a,b,c]
  simp only [div_eq_mul_inv]
  ring_nf
  simp only [I_pow_three]
  ring

/-- The cubic Laurent remainder is uniformly quadratic at infinity. -/
theorem exists_phase_cube_error_bound (A : ℂ → ℂ) (hA : AnalyticAt ℂ A 0)
    (hA0 : A 0 = 0) (H₁ H₂ H₃ : ℂ)
    (h₁ : iteratedDeriv 1 A 0 = I*H₁/2)
    (h₂ : iteratedDeriv 2 A 0 = I*H₂/2)
    (h₃ : iteratedDeriv 3 A 0 = 3*I*H₃/4) :
    ∃ R : ℝ, 0 < R ∧ ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, R < ‖z‖ →
      ‖(-I*z+A z⁻¹)^3-phaseCubeLaurentPart H₁ H₂ H₃ z‖ ≤ C/‖z‖^2 := by
  obtain ⟨B,hB,ε,hε,he⟩ := exists_phase_cube_analytic_remainder A hA hA0 H₁ H₂ H₃ h₁ h₂ h₃
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
