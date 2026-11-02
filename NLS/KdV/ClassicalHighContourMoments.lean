import NLS.KdV.ClassicalContourCoverage
import NLS.KdV.ClassicalContourMoments
import NLS.ComplexAnalysis.AffineLoopHomotopy
import NLS.ComplexAnalysis.HolomorphicPathPullback

/-! # An actual analytic high-contour moment family at every potential

Use lambda=z^2 on the counterclockwise circles C(n*pi,pi/4), with
the exact Jacobian 2*z. The constructed primitive is analytic near all
these contours on one common complex potential neighborhood, once n is
above a single cutoff. No contour-avoidance hypothesis is supplied.

The physical gap labels, action-space descent and uniform quadratic
action estimates remain to be identified before the global Hilbert
Hamiltonian extension follows.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

def classicalHillFrequencyDomain : Set (ℂ × NLS.LinearVolterra.Curve ℂ) :=
  (fun t => (t.1^2,t.2)) ⁻¹' classicalHillContinuationDomain

theorem isOpen_classicalHillFrequencyDomain : IsOpen classicalHillFrequencyDomain :=
  isOpen_classicalHillContinuationDomain.preimage (by fun_prop)

/-- The same actual primitive in the frequency coordinate. -/
def classicalHillFrequencyPrimitive (t : ℂ × NLS.LinearVolterra.Curve ℂ) : ℂ :=
  classicalHillContinuedPrimitive (t.1^2,t.2)

theorem analyticOnNhd_classicalHillFrequencyPrimitive :
    AnalyticOnNhd ℂ classicalHillFrequencyPrimitive classicalHillFrequencyDomain := by
  intro t ht
  exact (analyticOnNhd_classicalHillContinuedPrimitive (t.1^2,t.2) ht).comp
    (f := fun a : ℂ × NLS.LinearVolterra.Curve ℂ => (a.1^2,a.2))
    ((analyticAt_fst.pow 2).prod analyticAt_snd)

/-- Literal energy contour moment, written in the frequency coordinate
with the exact differential d(lambda)=2*z*dz. -/
def classicalHillHighContourMoment (n : ℕ+) (q : NLS.LinearVolterra.Curve ℂ) : ℂ :=
  (Real.pi : ℂ)⁻¹ * ∮ z in C((Real.pi : ℂ)*(n : ℕ),Real.pi/4),
    (classicalHillFrequencyPrimitive (z,q)+I*(n : ℂ)*Real.pi)^3*(2*z)

/-- The counterclockwise frequency circle mapped into the energy plane. -/
def classicalHillHighEnergyContour (n : ℕ+) :
    Path ((circleMap ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4) 0)^2)
      ((circleMap ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4) 0)^2) :=
  (circlePath ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4)).map (continuous_id.pow 2)

/-- The Jacobian formula is exactly the holomorphic one-form integral
over the actual mapped energy contour, with factor 1/pi unchanged. -/
theorem classicalHillHighContourMoment_eq_curveIntegral (n : ℕ+)
    (q : NLS.LinearVolterra.Curve ℂ) :
    classicalHillHighContourMoment n q = (Real.pi : ℂ)⁻¹ *
      ∫ᶜ z in classicalHillHighEnergyContour n,
        holomorphicOneForm (fun z => (classicalHillContinuedPrimitive (z,q)+I*(n : ℂ)*Real.pi)^3) z := by
  let f : ℂ → ℂ := fun z => (classicalHillContinuedPrimitive (z,q)+I*(n : ℂ)*Real.pi)^3
  have hsq (z : ℂ) : HasDerivAt (fun w : ℂ => w^2) (2*z) z := by
    simpa using! (hasDerivAt_id z).pow 2
  have hp := (holomorphicPathPullback_integral_and_integrability f
    (fun z => f (z^2)*(2*z)) (fun z : ℂ => z^2) (fun z : ℂ => 2*z) (continuous_id.pow 2)
    (circlePath ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4))
    ((circlePath_contDiffOn _ _).of_le (by norm_num))
    (fun _ _ => hsq _)
    (fun _ _ => rfl)).2
  rw [curveIntegral_circlePath] at hp
  change (Real.pi : ℂ)⁻¹ * (∮ z in C((Real.pi : ℂ)*(n : ℕ),Real.pi/4), f (z^2)*(2*z)) = _
  rw [← hp]
  rfl

/-- Each continuous potential has one complex neighborhood on which
every sufficiently high actual moment is analytic, with one cutoff
chosen before all potentials in that neighborhood and all tail indices. -/
theorem exists_analytic_classicalHillHighContourMoments (q : NLS.LinearVolterra.Curve ℂ) :
    ∃ N : ℕ, ∃ V : Set (NLS.LinearVolterra.Curve ℂ), 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N < (n : ℕ) → AnalyticOnNhd ℂ (classicalHillHighContourMoment n) V := by
  obtain ⟨N,V,hN,hV,hqV,hcover⟩ := exists_classicalHill_high_contour_neighborhood q
  refine ⟨N,V,hN,hV,hqV,?_⟩
  intro n hn
  have hG : AnalyticOnNhd ℂ
      (fun t : ℂ × NLS.LinearVolterra.Curve ℂ =>
        (classicalHillFrequencyPrimitive t+I*(n : ℂ)*Real.pi)^3*(2*t.1))
      classicalHillFrequencyDomain :=
    ((analyticOnNhd_classicalHillFrequencyPrimitive.add analyticOnNhd_const).pow 3).mul
      (analyticOnNhd_const.mul analyticOnNhd_fst)
  have hi := analyticOnNhd_circleIntegral_of_jointAnalytic _ isOpen_classicalHillFrequencyDomain hG
    ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4) (by positivity) hV
    (fun a ha z hz => hcover a ha n hn z hz)
  intro a ha
  exact (hi a ha).const_smul (c := (Real.pi : ℂ)⁻¹)

/-- The constructed high-contour moments vanish at the free potential,
including the free collapsed spectral point inside each contour. -/
theorem classicalHillHighContourMoment_zero (n : ℕ+) : classicalHillHighContourMoment n 0 = 0 := by
  let f : ℂ → ℂ := fun z => (classicalHillFreePrimitive (z^2)+I*(n : ℂ)*Real.pi)^3*(2*z)
  have hf : AnalyticOnNhd ℂ f (closedBall ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4)) := by
    intro z hz
    have hfree := (analyticOnNhd_classicalHillFreePrimitive (z^2)
      (sq_mem_slitPlane_of_high_closedBall n n.property z hz)).comp
        (f := fun z : ℂ => z^2) (analyticAt_id.pow 2)
    exact ((hfree.add analyticAt_const).pow 3).mul (analyticAt_const.mul analyticAt_id)
  have hi : (∮ z in C((Real.pi : ℂ)*(n : ℕ),Real.pi/4), f z) = 0 :=
    circleIntegral_eq_zero_of_differentiable_on_off_countable (by positivity) countable_empty
      hf.continuousOn (fun z hz => (hf z (ball_subset_closedBall hz.1)).differentiableAt)
  unfold classicalHillHighContourMoment classicalHillFrequencyPrimitive
  simp only [classicalHillContinuedPrimitive_base]
  change (Real.pi : ℂ)⁻¹ * (∮ z in C((Real.pi : ℂ)*(n : ℕ),Real.pi/4), f z) = 0
  rw [hi,mul_zero]

end NLS.KdV
