import NLS.KdV.ClassicalHillMomentCutRoot
import NLS.ComplexAnalysis.CirclePolynomialIntegrationByParts

/-! # Actual high Hill Arnold action periods

The action period is the literal -1/pi primitive integral on the same
mapped frequency circle as the cubic moment. Analyticity, radius
independence and its exact Arnold integrand are proved for the actual
source-normalized primitive. Global Birkhoff identification is separate.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.KdV

def classicalHillHighContourAction (n : ℕ+) (q : Curve ℂ) : ℂ :=
  -(Real.pi : ℂ)⁻¹ * ∮ z in C((Real.pi : ℂ)*(n : ℕ),Real.pi/4),
    (classicalHillFrequencyPrimitive (z,q)+I*(n : ℂ)*Real.pi)*(2*z)

theorem exists_analytic_classicalHillHighContourActions (q : Curve ℂ) :
    ∃ N : ℕ, ∃ V : Set (Curve ℂ), 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) → AnalyticOnNhd ℂ (classicalHillHighContourAction n) V := by
  obtain ⟨N,V,_,hV,hq,hcover⟩ := exists_classicalHill_high_contour_neighborhood q
  refine ⟨N+1,V,by omega,hV,hq,?_⟩
  intro n hn
  have hG : AnalyticOnNhd ℂ
      (fun t : ℂ × Curve ℂ => (classicalHillFrequencyPrimitive t+I*(n : ℂ)*Real.pi)*(2*t.1))
      classicalHillFrequencyDomain :=
    (analyticOnNhd_classicalHillFrequencyPrimitive.add analyticOnNhd_const).mul
      (analyticOnNhd_const.mul analyticOnNhd_fst)
  have hi := analyticOnNhd_circleIntegral_of_jointAnalytic _ isOpen_classicalHillFrequencyDomain hG
    ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4) (by positivity) hV
    (fun a ha z hz => hcover a ha n (by omega) z hz)
  intro a ha
  exact (hi a ha).const_smul (c := -(Real.pi : ℂ)⁻¹)

theorem exists_classicalHill_high_action_radius_independence
    (q : Curve ℂ) (r : ℝ) (hr : 0 < r) (hrpi : r ≤ Real.pi/4) :
    ∃ N : ℕ, ∃ V : Set (Curve ℂ), 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      (∀ a ∈ V, ∀ n : ℕ+, N ≤ (n : ℕ) →
        ∀ z ∈ closedBall ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4),
          r ≤ ‖z-(Real.pi : ℂ)*(n : ℕ)‖ → (z^2,a) ∈ classicalHillContinuationDomain) ∧
      ∀ a ∈ V, ∀ n : ℕ+, N ≤ (n : ℕ) → ∀ rho ∈ Icc r (Real.pi/4),
        classicalHillHighContourAction n a =
          -(Real.pi : ℂ)⁻¹ * ∮ z in C((Real.pi : ℂ)*(n : ℕ),rho),
            (classicalHillFrequencyPrimitive (z,a)+I*(n : ℂ)*Real.pi)*(2*z) := by
  obtain ⟨N,V,hN,hV,hq,hcover,heq⟩ :=
    exists_classicalHill_high_power_period_radius_independence q r hr hrpi
  refine ⟨N,V,hN,hV,hq,hcover,?_⟩
  intro a ha n hn rho hrho
  simpa only [classicalHillHighContourAction,pow_one,neg_mul] using
    congrArg Neg.neg (heq a ha n hn rho hrho 1)

/-- The exact Arnold integrand, written in the frequency variable with
lambda=z^2 and d(lambda)=2*z*dz. No factor i is inserted. -/
theorem classicalHillHighContourAction_arnold
    (q : Curve ℂ) (n : ℕ+)
    (hcircle : ∀ z ∈ sphere ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4),
      (z^2,q) ∈ classicalHillContinuationDomain) :
    classicalHillHighContourAction n q = (Real.pi : ℂ)⁻¹ *
      ∮ z in C((Real.pi : ℂ)*(n : ℕ),Real.pi/4),
        z^2*(deriv (classicalHillDiscriminant q) (z^2)/classicalHillContinuedRoot (z^2,q))*(2*z) := by
  let F : ℂ → ℂ := fun z => classicalHillFrequencyPrimitive (z,q)+I*(n : ℂ)*Real.pi
  let D : Set ℂ := {z | (z^2,q) ∈ classicalHillContinuationDomain}
  have hF : AnalyticOnNhd ℂ F D := by
    intro z hz
    exact ((analyticOnNhd_classicalHillFrequencyPrimitive (z,q) hz).comp
      (f := fun z : ℂ => (z,q)) (analyticAt_id.prod analyticAt_const)).add analyticAt_const
  have hd (z : ℂ) (hz : z ∈ sphere ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4)) :
      deriv F z = (deriv (classicalHillDiscriminant q) (z^2)/classicalHillContinuedRoot (z^2,q))*(2*z) := by
    have hsq (z : ℂ) : HasDerivAt (fun w : ℂ => w^2) (2*z) z := by
      simpa using! (hasDerivAt_id z).pow 2
    have hh := ((hasDerivAt_classicalHillContinuedPrimitive (z^2,q) (hcircle z hz)).comp z (hsq z)).add_const
      (I*(n : ℂ)*Real.pi)
    exact hh.deriv
  have hip := circleIntegral_pow_mul_deriv_eq_neg F D hF ((Real.pi : ℂ)*(n : ℕ))
    (Real.pi/4) (by positivity) hcircle 1
  norm_num only [Nat.reduceAdd,pow_one,Nat.cast_one] at hip
  have hi : (∮ z in C((Real.pi : ℂ)*(n : ℕ),Real.pi/4), F z*(2*z)) =
      2*(∮ z in C((Real.pi : ℂ)*(n : ℕ),Real.pi/4), z*F z) := by
    have he : (fun z => F z*(2*z)) = fun z => (2 : ℂ)*(z*F z) := by funext z; ring
    rw [he,circleIntegral.integral_const_mul]
  calc
    _ = -(Real.pi : ℂ)⁻¹*(2*(∮ z in C((Real.pi : ℂ)*(n : ℕ),Real.pi/4), z*F z)) := by
      change -(Real.pi : ℂ)⁻¹*(∮ z in C((Real.pi : ℂ)*(n : ℕ),Real.pi/4), F z*(2*z)) = _
      rw [hi]
    _ = (Real.pi : ℂ)⁻¹*(∮ z in C((Real.pi : ℂ)*(n : ℕ),Real.pi/4), z^2*deriv F z) := by
      rw [hip]
      ring
    _ = _ := by
      congr 1
      apply circleIntegral.integral_congr (by positivity)
      intro z hz
      change z^2*deriv F z = _
      rw [hd z hz]
      ring

end NLS.KdV
