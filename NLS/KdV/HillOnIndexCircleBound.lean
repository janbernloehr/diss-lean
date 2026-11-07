import NLS.KdV.HillOnIndexPhysicalCorrection
import NLS.ZakharovShabat.SourceQuadraticSolutionCircleBound

/-! Quantitative enclosing-circle bounds for the ACTUAL filled Hill
diagonal remainder and physical AUXILIARY-divisor correction, including COMPLEX collapsed gaps.
There is no division by the gap or the physical terminal sheet. -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem norm_onIndexAbelianFilledRemainder_le_of_circle_bound (P : HillProductEquationPatch)
    (m : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ P.source)
    (c : ℂ) (a ρ M : ℝ) (hρ : 0 < ρ) (haρ : a < ρ)
    (hρD : closedBall c ρ ⊆ ball (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ))) (hM : 0 ≤ M)
    (hgap : sourcePeriodicSegment (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) ⊆
      ball c a)
    (hg : ∀ w ∈ sphere c ρ, ‖P.abelianGapNumerator m m (w,q)-I‖ ≤ M)
    (z : ℂ) (hz : z ∈ closedBall c a) :
    ‖P.onIndexAbelianFilledRemainder m (z,q)‖ ≤ Real.pi*ρ^2*M/(ρ-a)^3 := by
  apply norm_quadratic_solution_le_of_source_circle_bound (by norm_num) (by norm_num)
    (P.sourcePsi q) ((m:ℕ):ℤ) (fun w => P.onIndexAbelianFilledRemainder m (w,q))
    (fun w => P.abelianGapNumerator m m (w,q)-I) c a ρ M hρ haρ hM hgap _ _ hg z hz
  · intro w hw
    exact (P.analytic_onIndexAbelianFilledRemainder m (w,q)
      ⟨hρD hw,hq⟩).comp
      (f := fun w : ℂ => (w,q)) (analyticAt_id.prod analyticAt_const)
  · intro w hw
    exact P.onIndexAbelianFilledRemainder_equation m q hq w
      (hρD (sphere_subset_closedBall hw))

theorem norm_physicalOnIndexAbelianCorrection_le_of_circle_bound (P : HillProductEquationPatch)
    (m : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ P.physicalDirichletSource)
    (c : ℂ) (a ρ M : ℝ) (hρ : 0 < ρ) (haρ : a < ρ)
    (hρD : closedBall c ρ ⊆ ball (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ))) (hM : 0 ≤ M)
    (hgap : sourcePeriodicSegment (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) ⊆
      ball c a)
    (hg : ∀ w ∈ sphere c ρ, ‖P.abelianGapNumerator m m (w,q)-I‖ ≤ M)
    (hμ : P.physicalDirichletFrequency ((m:ℕ):ℤ) q ∈ closedBall c a) :
    ‖P.physicalOnIndexAbelianCorrection m q‖ ≤
      (‖P.physicalDirichletFrequency ((m:ℕ):ℤ) q-sourceStandardRootMidpoint (by norm_num) (by norm_num)
        (P.sourcePsi q) ((m:ℕ):ℤ)‖+‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ)‖/2)*
          (Real.pi*ρ^2*M/(ρ-a)^3) := by
  exact (show ‖P.physicalOnIndexAbelianCorrection m q‖ ≤
      (‖P.physicalDirichletFrequency ((m:ℕ):ℤ) q-sourceStandardRootMidpoint (by norm_num) (by norm_num)
        (P.sourcePsi q) ((m:ℕ):ℤ)‖+‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ)‖/2)*
          ‖P.onIndexAbelianFilledRemainder m (P.physicalDirichletFrequency ((m:ℕ):ℤ) q,q)‖ from by
      rw [physicalOnIndexAbelianCorrection,norm_mul]
      exact mul_le_mul_of_nonneg_right (P.norm_physicalDirichletRootCoefficient_le m q hq) (norm_nonneg _)).trans
    (mul_le_mul_of_nonneg_left (P.norm_onIndexAbelianFilledRemainder_le_of_circle_bound m q hq.1
      c a ρ M hρ haρ hρD hM hgap hg _ hμ) (by positivity))

end NLS.KdV.HillProductEquationPatch
