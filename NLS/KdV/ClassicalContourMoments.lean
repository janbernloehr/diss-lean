import NLS.KdV.ClassicalSourcePrimitive
import NLS.KdV.ActionHamiltonianMoments

/-! # Cubic moments of the constructed classical Hill primitive

These are literal contour integrals of the free-normalized continued
primitive, with the exact shift i*n*pi. Analyticity in the continuous
potential norm follows on a common neighborhood of every admissible fixed
circle. Spectral gap labeling, action identification and action descent
are still needed before these quantities can be used in Proposition 4.7.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
namespace NLS.KdV

/-- The actual logarithmic spectral derivative has zero period on every
circle in the continuation domain. The primitive is constructed here,
so zero period is a conclusion rather than an extra spectral input. -/
theorem classicalHillContinued_period_eq_zero
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (q : NLS.LinearVolterra.Curve ℂ)
    (hcircle : ∀ z ∈ sphere c r, (z,q) ∈ classicalHillContinuationDomain) :
    (∮ z in C(c,r), deriv (classicalHillDiscriminant q) z /
      classicalHillContinuedRoot (z,q)) = 0 := by
  exact circleIntegral.integral_eq_zero_of_hasDerivWithinAt hr
    (f := fun z => classicalHillContinuedPrimitive (z,q))
    (fun z hz => (hasDerivAt_classicalHillContinuedPrimitive (z,q) (hcircle z hz)).hasDerivWithinAt)

/-- The literal cubic contour moment of the constructed primitive. -/
def classicalHillContinuedMoment (n : ℕ+) (c : ℂ) (r : ℝ)
    (q : NLS.LinearVolterra.Curve ℂ) : ℂ :=
  cubicMoment (fun z => classicalHillContinuedPrimitive (z,q)+I*(n : ℂ)*Real.pi) c r

/-- Every circle in the actual continuation domain yields analytic
moments on one complex neighborhood of its base potential. -/
theorem exists_analyticOnNhd_classicalHillContinuedMoment
    (n : ℕ+) (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (q : NLS.LinearVolterra.Curve ℂ)
    (hcircle : ∀ z ∈ sphere c r, (z,q) ∈ classicalHillContinuationDomain) :
    ∃ V : Set (NLS.LinearVolterra.Curve ℂ), IsOpen V ∧ q ∈ V ∧
      AnalyticOnNhd ℂ (classicalHillContinuedMoment n c r) V := by
  obtain ⟨V,hV,hqV,hsub⟩ := exists_classicalHillContinuation_neighborhood
    (sphere c r) (isCompact_sphere c r) q hcircle
  refine ⟨V,hV,hqV,?_⟩
  exact analyticOnNhd_cubicMoment
    (fun t => classicalHillContinuedPrimitive t+I*(n : ℂ)*Real.pi)
    classicalHillContinuationDomain isOpen_classicalHillContinuationDomain
    (analyticOnNhd_classicalHillContinuedPrimitive.add analyticOnNhd_const)
    c r hr V hV (fun a ha z hz => hsub ⟨hz,ha⟩)

/-- At the free potential all such moments vanish whenever the circle
encloses a disc in the energy slit plane. The shifted primitive extends
through the free collapsed gap, despite the radicand vanishing there. -/
theorem classicalHillContinuedMoment_zero (n : ℕ+) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hdisc : closedBall c r ⊆ slitPlane) : classicalHillContinuedMoment n c r 0 = 0 := by
  unfold classicalHillContinuedMoment
  simp only [classicalHillContinuedPrimitive_base]
  exact cubicMoment_eq_zero_of_analyticOnNhd _ c r hr
    ((analyticOnNhd_classicalHillFreePrimitive.mono hdisc).add analyticOnNhd_const)

end NLS.KdV
