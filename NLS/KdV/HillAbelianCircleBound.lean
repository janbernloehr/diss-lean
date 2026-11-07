import NLS.KdV.HillPhysicalOffIndexAbelianValue
import NLS.ZakharovShabat.SourceQuadraticSolutionCircleBound

/-! Quantitative enclosing-circle bounds for the ACTUAL filled Hill
quotient and physical divisor value, including COMPLEX collapsed gaps.
There is no division by the gap or the physical terminal sheet. -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem norm_offIndexAbelianFilledQuotient_le_of_circle_bound (P : HillProductEquationPatch)
    (n m : ℕ+) (hmn : m ≠ n) (q : PeriodOneHminusOne) (hq : q ∈ P.source)
    (c : ℂ) (a ρ M : ℝ) (hρ : 0 < ρ) (haρ : a < ρ)
    (hρD : closedBall c ρ ⊆ ball (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ))) (hM : 0 ≤ M)
    (hgap : sourcePeriodicSegment (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) ⊆
      ball c a)
    (hg : ∀ w ∈ sphere c ρ, ‖P.abelianGapNumerator n m (w,q)‖ ≤ M)
    (z : ℂ) (hz : z ∈ closedBall c a) :
    ‖P.offIndexAbelianFilledQuotient n m (z,q)‖ ≤ Real.pi*ρ^2*M/(ρ-a)^3 := by
  apply norm_quadratic_solution_le_of_source_circle_bound (by norm_num) (by norm_num)
    (P.sourcePsi q) ((m:ℕ):ℤ) (fun w => P.offIndexAbelianFilledQuotient n m (w,q))
    (fun w => P.abelianGapNumerator n m (w,q)) c a ρ M hρ haρ hM hgap _ _ hg z hz
  · intro w hw
    exact (P.analytic_offIndexAbelianFilledQuotient n m hmn (w,q)
      ⟨hρD hw,hq⟩).comp
      (f := fun w : ℂ => (w,q)) (analyticAt_id.prod analyticAt_const)
  · intro w hw
    exact P.offIndexAbelianFilledQuotient_equation n m hmn q hq w
      (hρD (sphere_subset_closedBall hw))

theorem norm_physicalOffIndexAbelianValue_le_of_circle_bound (P : HillProductEquationPatch)
    (n m : ℕ+) (hmn : m ≠ n) (q : PeriodOneHminusOne) (hq : q ∈ P.physicalDirichletSource)
    (c : ℂ) (a ρ M : ℝ) (hρ : 0 < ρ) (haρ : a < ρ)
    (hρD : closedBall c ρ ⊆ ball (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ))) (hM : 0 ≤ M)
    (hgap : sourcePeriodicSegment (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) ⊆
      ball c a)
    (hg : ∀ w ∈ sphere c ρ, ‖P.abelianGapNumerator n m (w,q)‖ ≤ M)
    (hμ : P.physicalDirichletFrequency ((m:ℕ):ℤ) q ∈ closedBall c a) :
    ‖P.physicalOffIndexAbelianValue n m q‖ ≤
      (‖P.physicalDirichletFrequency ((m:ℕ):ℤ) q-sourceStandardRootMidpoint (by norm_num) (by norm_num)
        (P.sourcePsi q) ((m:ℕ):ℤ)‖+‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ)‖/2)*
          (Real.pi*ρ^2*M/(ρ-a)^3) := by
  exact (P.norm_physicalOffIndexAbelianValue_le n m q hq).trans
    (mul_le_mul_of_nonneg_left (P.norm_offIndexAbelianFilledQuotient_le_of_circle_bound n m hmn q hq.1
      c a ρ M hρ haρ hρD hM hgap hg _ hμ) (by positivity))

end NLS.KdV.HillProductEquationPatch
