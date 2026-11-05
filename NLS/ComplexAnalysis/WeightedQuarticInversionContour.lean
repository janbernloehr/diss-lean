import NLS.ComplexAnalysis.QuarticInversionCoefficient
import NLS.ComplexAnalysis.PolynomialInversionCircleCoefficients

/-! The weighted quartic exterior contour extracts the exact physical
Hamiltonian combination from the analytic inverse-frequency phase. -/
noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis

theorem circleIntegral_pow_mul_comp_inv_eq_scalarTaylorCoefficient
    (g : ℂ → ℂ) (r R : ℝ) (hr : 0 < r) (hR : 0 < R) (hRr : R⁻¹ < r)
    (hg : AnalyticOnNhd ℂ g (ball 0 r)) (k : ℕ) :
    (∮ z in C(0,R), z^k*g z⁻¹)=(2*Real.pi*I:ℂ)*scalarTaylorCoefficient (k+1) g := by
  rw [circleIntegral_pow_mul_comp_inv_eq g r R hr hR hRr hg k]
  apply congrArg (fun v : ℂ => (2*Real.pi*I:ℂ)*v)
  exact div_eq_inv_mul _ _

theorem weighted_quartic_inversion_identity (z a : ℂ) (hz : z ≠ 0) :
    z*(-I*z+a)^4=z^5*(-I+z⁻¹*a)^4 := by
  have he : -I*z+a=z*(-I+z⁻¹*a) := by
    rw [mul_add,← mul_assoc z z⁻¹ a,mul_inv_cancel₀ hz,one_mul]
    ring
  rw [he,mul_pow]
  ring

theorem exists_phase_weighted_quartic_contour (A : ℂ → ℂ) (hA : AnalyticAt ℂ A 0)
    (hA0 : A 0=0) (H₁ H₃ H₅ : ℂ)
    (h₁ : iteratedDeriv 1 A 0=I*H₁/2) (h₂ : iteratedDeriv 2 A 0=0)
    (h₃ : iteratedDeriv 3 A 0=3*I*H₃/4) (h₅ : iteratedDeriv 5 A 0=15*I*H₅/4) :
    ∃ T : ℝ, 0 < T ∧ ∀ R : ℝ, T ≤ R →
      (∮ z in C(0,R), z*(-I*z+A z⁻¹)^4)=
        (-(Real.pi:ℂ)*I/2)*(H₅/2-3*H₁*H₃+2*H₁^3) := by
  let G : ℂ → ℂ := fun w => (-I+w*A w)^4
  have hG : AnalyticAt ℂ G 0 := (analyticAt_const.add (analyticAt_id.mul hA)).pow 4
  obtain ⟨r,hr,hGr⟩ := hG.exists_ball_analyticOnNhd
  let T := r⁻¹+1
  have hT : 0 < T := by dsimp [T]; positivity
  refine ⟨T,hT,?_⟩
  intro R hTR
  have hR := hT.trans_le hTR
  have hRr : R⁻¹ < r := (inv_lt_comm₀ hR hr).mpr (by dsimp [T] at hTR; linarith)
  have he : (∮ z in C(0,R), z*(-I*z+A z⁻¹)^4)=∮ z in C(0,R), z^5*G z⁻¹ := by
    apply circleIntegral.integral_congr hR.le
    intro z hz
    have hn : ‖z‖=R := by simpa only [mem_sphere,dist_zero_right] using hz
    have hz0 : z ≠ 0 := norm_pos_iff.mp (hn.symm ▸ hR)
    exact weighted_quartic_inversion_identity z (A z⁻¹) hz0
  have hc := scalarTaylorCoefficient_quartic_phase A hA hA0 H₁ H₃ H₅ h₁ h₂ h₃ h₅
  change scalarTaylorCoefficient 6 G= _ at hc
  calc
    _ = ∮ z in C(0,R), z^5*G z⁻¹ := he
    _ = (2*Real.pi*I:ℂ)*scalarTaylorCoefficient 6 G :=
      circleIntegral_pow_mul_comp_inv_eq_scalarTaylorCoefficient G r R hr hR hRr hGr 5
    _ = (2*Real.pi*I:ℂ)*(-(H₅/2-3*H₁*H₃+2*H₁^3)/4) := congrArg (fun v : ℂ => (2*Real.pi*I:ℂ)*v) hc
    _ = _ := by ring

end NLS.ComplexAnalysis
