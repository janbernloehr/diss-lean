import NLS.KdV.HillAbelianNormalizedJointPrimitive

/-! The SAME filled quadratic quotient continues the actual normalized
Abelian integral onto ANY prescribed regular root sheet. Root ratios
retain the sign. Analytic terminal values can vanish; no division by a
terminal root or a gap length is used in their evaluation. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

def offIndexAbelianRegularSheetPrimitive (P : HillProductEquationPatch) (n m : ℕ+)
    (R : ℂ × PeriodOneHminusOne → ℂ) (t : ℂ × PeriodOneHminusOne) : ℂ :=
  R t*P.offIndexAbelianFilledQuotient n m t

theorem analytic_offIndexAbelianRegularSheetPrimitive (P : HillProductEquationPatch)
    (n m : ℕ+) (hmn : m ≠ n) (R : ℂ × PeriodOneHminusOne → ℂ)
    (D : Set (ℂ × PeriodOneHminusOne))
    (hD : D ⊆ ball (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ)) ×ˢ P.source)
    (hR : AnalyticOnNhd ℂ R D) : AnalyticOnNhd ℂ (P.offIndexAbelianRegularSheetPrimitive n m R) D :=
  hR.mul ((P.analytic_offIndexAbelianFilledQuotient n m hmn).mono hD)

theorem hasDerivAt_offIndexAbelianRegularSheetPrimitive (P : HillProductEquationPatch)
    (n m : ℕ+) (hmn : m ≠ n) (R : ℂ × PeriodOneHminusOne → ℂ)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (U : Set ℂ) (hU : IsOpen U)
    (hsub : U ⊆ ball (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ)))
    (hR : AnalyticOnNhd ℂ (fun w => R (w,q)) U) (hne : ∀ w ∈ U, R (w,q) ≠ 0)
    (hsq : ∀ w ∈ U, R (w,q)^2 = sourceAngularSelectedPolynomial (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) w)
    (z : ℂ) (hz : z ∈ U) :
    HasDerivAt (fun w => P.offIndexAbelianRegularSheetPrimitive n m R (w,q)) (P.abelianGapNumerator n m (z,q)/R (z,q)) z := by
  have hH := (P.analytic_offIndexAbelianFilledQuotient n m hmn (z,q) ⟨hsub hz,hq⟩).comp
    (f := fun w : ℂ => (w,q)) (analyticAt_id.prod analyticAt_const)
  have hnear : (fun w => R (w,q)^2) =ᶠ[𝓝 z] sourceAngularSelectedPolynomial (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact hsq w hw
  exact hasDerivAt_root_mul_of_quadratic_equation (fun w => R (w,q)) (fun w => P.offIndexAbelianFilledQuotient n m (w,q))
    _ _ _ z (hR z hz) (hne z hz) hnear hH (P.offIndexAbelianFilledQuotient_equation n m hmn q hq z (hsub hz))

theorem offIndexAbelianRegularSheetPrimitive_root_ratio (P : HillProductEquationPatch) (n m : ℕ+)
    (R : ℂ × PeriodOneHminusOne → ℂ) (t : ℂ × PeriodOneHminusOne) (hne : R t ≠ 0)
    (hsq : R t^2 = (sourceStandardRoot (by norm_num) (by norm_num) (P.sourcePsi t.2) ((m:ℕ):ℤ) t.1)^2) :
    P.offIndexAbelianRegularSheetPrimitive n m R t =
      (sourceStandardRoot (by norm_num) (by norm_num) (P.sourcePsi t.2) ((m:ℕ):ℤ) t.1/R t)*P.offIndexAbelianNormalizedPrimitive n m t := by
  unfold offIndexAbelianRegularSheetPrimitive offIndexAbelianNormalizedPrimitive
  field_simp [hne]
  linear_combination P.offIndexAbelianFilledQuotient n m t*hsq

theorem analyticAt_offIndexAbelian_filled_terminal_value (P : HillProductEquationPatch) (n m : ℕ+) (hmn : m ≠ n)
    (μ s : PeriodOneHminusOne → ℂ) (q : PeriodOneHminusOne) (hq : q ∈ P.source)
    (hμ : AnalyticAt ℂ μ q) (hs : AnalyticAt ℂ s q)
    (hinside : μ q ∈ ball (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ))) :
    AnalyticAt ℂ (fun y => s y*P.offIndexAbelianFilledQuotient n m (μ y,y)) q :=
  hs.mul ((P.analytic_offIndexAbelianFilledQuotient n m hmn (μ q,q) ⟨hinside,hq⟩).comp
    (f := fun y => (μ y,y)) (hμ.prod analyticAt_id))

end NLS.KdV.HillProductEquationPatch
