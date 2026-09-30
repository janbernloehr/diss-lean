import NLS.ComplexAnalysis.QuadraticCauchyEquation
import NLS.ZakharovShabat.SourceAngularCauchyCandidate
import NLS.ZakharovShabat.SourceStandardRootFirstMoment

/-!
# The actual angular Cauchy candidate satisfies the root equation

Divide the joint annular primitive by the selected standard root.
Its derivative and the selected root's exact derivative give the
quadratic equation on an enclosing circle. Cauchy projection carries
that equation to the whole disc. Only the analytic midpoint and
squared gap occur, so no endpoint splitting is needed at collapse.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceAngularSelectedPolynomial (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (m : ℤ) : ℂ → ℂ :=
  quadraticRootPolynomial (sourceStandardRootMidpoint hp hp1 ψ m)
    ((canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)^2/4)

theorem sourceAngularSelectedPolynomial_eq_endpoint_factor
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (m : ℤ) (z : ℂ) :
    sourceAngularSelectedPolynomial hp hp1 ψ m z =
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m-z)*
        (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m-z) := by
  unfold sourceAngularSelectedPolynomial quadraticRootPolynomial sourceStandardRootMidpoint
    canonicalPeriodicMidpoint canonicalPeriodicGap
  ring

namespace SourceAngularJointAnnulusChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {m : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
  {W V : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ} {r R : ℝ} {z₀ : ℂ}

/-- The actual analytic interior candidate satisfies the same equation as
the annular normalized quotient, at every complex source in the chart and
every spectral point of the interior disc. -/
theorem quotientCauchyCandidate_equation
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) (hmn : m ≠ n)
    (ρ : ℝ) (hrρ : r < ρ) (hρR : ρ < R) (z : ℂ) (hz : z ∈ ball (c m) ρ) :
    sourceAngularSelectedPolynomial hp hp1 ψ m z *
        deriv (fun w => sourceAngularQuotientCauchyCandidate hp hp1 n m s (c m) r R z₀ ρ (w,ψ)) z +
      (z-sourceStandardRootMidpoint hp hp1 ψ m)*
        sourceAngularQuotientCauchyCandidate hp hp1 n m s (c m) r R z₀ ρ (z,ψ) =
      sourceAngularGapNumerator hp hp1 n m s ψ z := by
  let Q := sourceStandardRoot hp hp1 ψ m
  let P : ℂ → ℂ := fun w => sourceAngularJointAnnularPrimitive hp hp1 n s (c m) r R z₀ (w,ψ)
  let f : ℂ → ℂ := fun w => P w/Q w
  let g := sourceAngularGapNumerator hp hp1 n m s ψ
  let τ := sourceStandardRootMidpoint hp hp1 ψ m
  let d := (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)^2/4
  have hcircle (w : ℂ) (hw : w ∈ sphere (c m) ρ) :
      w ∈ ball (c m) R \ closedBall (c m) r := by
    have hd := mem_sphere.mp hw
    exact ⟨mem_ball.mpr (hd.trans_lt hρR),fun h => (not_le_of_gt hrρ) (hd ▸ mem_closedBall.mp h)⟩
  have havoid (w : ℂ) (hw : w ∈ sphere (c m) ρ) : w ∉ sourcePeriodicSegment hp hp1 ψ m :=
    fun h => (hcircle w hw).2 (ball_subset_closedBall (D.gap_enclosed ψ hψ h))
  have hQne (w : ℂ) (hw : w ∈ sphere (c m) ρ) : Q w ≠ 0 :=
    sourceStandardRoot_ne_zero_off_segment hp hp1 ψ m w (havoid w hw)
  have hQa (w : ℂ) (hw : w ∈ sphere (c m) ρ) : AnalyticAt ℂ Q w :=
    sourceStandardRoot_analyticAt hp hp1 ψ m w (havoid w hw)
  have hPa (w : ℂ) (hw : w ∈ sphere (c m) ρ) : AnalyticAt ℂ P w :=
    (D.primitive_analytic n (w,ψ) ⟨hcircle w hw,hψ⟩).comp
      (f := fun w : ℂ => (w,ψ)) (analyticAt_id.prod analyticAt_const)
  have hf : AnalyticOnNhd ℂ f (sphere (c m) ρ) :=
    fun w hw => (hPa w hw).div (hQa w hw) (hQne w hw)
  have hg : AnalyticOnNhd ℂ g (closedBall (c m) ρ) := by
    intro w hw
    have hwT : w ∈ ball (c m) (T m) :=
      mem_ball.mpr ((mem_closedBall.mp hw).trans_lt (hρR.trans D.outer_lt_assigned))
    have hO := ((D.disc_family ψ hψ).contour_family.2 m).2.2.1 (ball_subset_closedBall hwT)
    exact (analyticOnNhd_sourcePsiCandidate hp hp1 n (w,(s n ψ : Coeff p)) (mem_univ _)
      |>.comp (f := fun w : ℂ => (w,(s n ψ : Coeff p))) (analyticAt_id.prod analyticAt_const)).div
      (analyticAt_const.mul ((D.omitted_analytic (w,ψ) ⟨hwT,hψ⟩).comp
        (f := fun w : ℂ => (w,ψ)) (analyticAt_id.prod analyticAt_const)))
      (mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero)
        (sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ w m hO))
  have heq (w : ℂ) (hw : w ∈ sphere (c m) ρ) :
      quadraticRootPolynomial τ d w*deriv f w+(w-τ)*f w = g w := by
    have hPd : HasDerivAt P (g w/Q w) w := by
      change HasDerivAt P (sourceAngularGapNumerator hp hp1 n m s ψ w /
        sourceStandardRoot hp hp1 ψ m w) w
      rw [← sourceAngularIntegrand_eq_gapNumerator_div_standardRoot hp hp1 n m s ψ w]
      exact D.spectral_derivative n hmn ψ hψ w (hcircle w hw)
    have hQd : HasDerivAt Q ((w-τ)/Q w) w := by
      have hd : HasDerivAt Q (deriv Q w) w := (hQa w hw).differentiableAt.hasDerivAt
      have hv : deriv Q w = (w-τ)/Q w :=
        deriv_sourceStandardRoot_off_segment hp hp1 ψ m w (havoid w hw)
      rw [hv] at hd
      exact hd
    have hfd := hPd.fun_div hQd (hQne w hw)
    have hsq : quadraticRootPolynomial τ d w = Q w^2 :=
      (sourceAngularSelectedPolynomial_eq_endpoint_factor hp hp1 ψ m w).trans
        (sourceStandardRoot_sq_of_not_mem_segment hp hp1 ψ m w (havoid w hw)).symm
    rw [hsq,hfd.deriv]
    dsimp only [f]
    field_simp [hQne w hw]
    ring
  exact circleCauchyTransform_quadratic_equation f g τ d (c m) ρ (D.inner_pos.trans hrρ) hf hg heq z hz

end SourceAngularJointAnnulusChartData
end NLS.ZakharovShabat
