import NLS.ComplexAnalysis.TracePrimitiveContinuation
import NLS.ComplexAnalysis.CirclePolynomialIntegrationByParts
import NLS.ComplexAnalysis.ParametricCircleIntegralHigher

/-! # Contour moments of a free-normalized analytic trace primitive

The Arnold formulas at every nonnegative integer level follow from the
shared polynomial integration-by-parts theorem. Moment analyticity and
annular contour invariance use the constructed primitive near the contour;
no extension through the enclosed branch points is required.
-/

noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis.TracePrimitiveFamily
variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]
variable (f : NLS.ComplexAnalysis.TracePrimitiveFamily A)

def contourMoment (c : ℂ) (r : ℝ) (m : ℕ) (q : A) : ℂ :=
  -(Real.pi : ℂ)⁻¹ * ∮ z in C(c,r), z^m*f.primitive (z,q)

theorem period_eq_zero (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (q : A)
    (hc : ∀ z ∈ sphere c r, (z,q) ∈ f.continuationDomain) :
    (∮ z in C(c,r), deriv (fun z => f.trace (z,q)) z / f.root (z,q)) = 0 :=
  circleIntegral.integral_eq_zero_of_hasDerivWithinAt hr
    (f := fun z => f.primitive (z,q))
    (fun z hz => (f.hasDerivAt_primitive (z,q) (hc z hz)).hasDerivWithinAt)

theorem contourMoment_arnold (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (q : A)
    (hc : ∀ z ∈ sphere c r, (z,q) ∈ f.continuationDomain) (m : ℕ) :
    f.contourMoment c r m q = ((m+1 : ℂ)*(Real.pi : ℂ))⁻¹ *
      ∮ z in C(c,r), z^(m+1)*deriv (fun z => f.trace (z,q)) z / f.root (z,q) := by
  let P : ℂ → ℂ := fun z => f.primitive (z,q)
  let D : Set ℂ := {z | (z,q) ∈ f.continuationDomain}
  have hP : AnalyticOnNhd ℂ P D := by
    intro z hz
    exact (f.analytic_primitive (z,q) hz).comp
      (f := fun z : ℂ => (z,q)) (analyticAt_id.prod analyticAt_const)
  have hip := circleIntegral_pow_mul_deriv_eq_neg P D hP c r hr (fun z hz => hc z hz) m
  have hi : (∮ z in C(c,r), z^(m+1)*deriv (fun z => f.trace (z,q)) z / f.root (z,q)) =
      -(m+1 : ℂ)*(∮ z in C(c,r), z^m*P z) := by
    rw [← hip]
    apply circleIntegral.integral_congr hr
    intro z hz
    dsimp only [P]
    rw [(f.hasDerivAt_primitive (z,q) (hc z hz)).deriv]
    exact mul_div_assoc _ _ _
  rw [hi]
  dsimp only [contourMoment,P]
  have hm : (m+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

theorem exists_analytic_contourMoment (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (q : A)
    (hc : ∀ z ∈ sphere c r, (z,q) ∈ f.continuationDomain) (m : ℕ) :
    ∃ V : Set A, IsOpen V ∧ q ∈ V ∧ AnalyticOnNhd ℂ (f.contourMoment c r m) V := by
  obtain ⟨V,hV,hqV,hsub⟩ := f.exists_continuation_neighborhood (sphere c r)
    (isCompact_sphere _ _) q hc
  let F : ℂ × A → ℂ := fun t => t.1^m*f.primitive t
  have hF : AnalyticOnNhd ℂ F f.continuationDomain := by
    intro t ht
    exact (analyticAt_fst.pow m).mul (f.analytic_primitive t ht)
  have hraw := analyticOnNhd_circleIntegral_of_jointAnalytic F
    f.isOpen_continuationDomain hF c r hr hV (fun a ha z hz => hsub ⟨hz,ha⟩)
  exact ⟨V,hV,hqV,fun a ha => analyticAt_const.mul (hraw a ha)⟩

theorem contourMoment_base (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hdisc : closedBall c r ⊆ f.freeDomain) (m : ℕ) : f.contourMoment c r m 0 = 0 := by
  have ha : AnalyticOnNhd ℂ (fun z => z^m*f.freePrimitive z) (closedBall c r) := by
    intro z hz
    exact (analyticAt_id.pow m).mul (f.analytic_freePrimitive z (hdisc hz))
  have hi := (DiffContOnCl.mk_ball
    (ha.differentiableOn.mono ball_subset_closedBall) ha.continuousOn).circleIntegral_eq_zero hr
  simp only [contourMoment,f.primitive_base,hi,mul_zero]

theorem contourMoment_eq_of_annulus (c : ℂ) (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R)
    (q : A) (hA : ∀ z ∈ closedBall c R \ ball c r, (z,q) ∈ f.continuationDomain)
    (m : ℕ) : f.contourMoment c R m q = f.contourMoment c r m q := by
  have ha : AnalyticOnNhd ℂ (fun z => z^m*f.primitive (z,q))
      (closedBall c R \ ball c r) := by
    intro z hz
    exact (analyticAt_id.pow m).mul ((f.analytic_primitive (z,q) (hA z hz)).comp
      (f := fun z : ℂ => (z,q)) (analyticAt_id.prod analyticAt_const))
  have hi := Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
    hr hrR countable_empty ha.continuousOn
    (fun z hz => (ha z ⟨ball_subset_closedBall hz.1.1,
      fun h => hz.1.2 (ball_subset_closedBall h)⟩).differentiableAt)
  exact congrArg (fun a : ℂ => -(Real.pi : ℂ)⁻¹*a) hi

end NLS.ComplexAnalysis.TracePrimitiveFamily
