import NLS.KdV.HillAbelianRealNumerator
import NLS.KdV.HillOnIndexAbelianCosinePhase
import NLS.ZakharovShabat.SourceAngularCauchyReal

/-! The actual diagonal phase is real along every real cosine cover.
The period subtraction is exactly i, and the left endpoint fixes zero. -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem onIndexCosinePoint_mem_actual_gap (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (δ : ℂ)
    (hδ : δ^2 = (canonicalPeriodicGap (by norm_num) (by norm_num)
      (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((n:ℕ):ℤ)/2)^2) (t : ℝ) :
    cosineGapPoint (sourceStandardRootMidpoint (by norm_num) (by norm_num)
      (P.sourcePsi q) ((n:ℕ):ℤ)) δ (t:ℂ) ∈
      sourcePeriodicSegment (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ) := by
  rw [← sourcePeriodicSegment_eq_of_halfGap_sq (by norm_num) (by norm_num)
    (P.sourcePsi q) ((n:ℕ):ℤ) δ hδ]
  exact cosineGapPoint_real_mem_segment _ _ t

theorem onIndexAbelianCosinePhase_im_eq_zero_of_real (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) (δ : ℂ)
    (hδ : δ^2 = (canonicalPeriodicGap (by norm_num) (by norm_num)
      (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((n:ℕ):ℤ)/2)^2) (t : ℝ) :
    (P.onIndexAbelianCosinePhase n q δ (t:ℂ)).im = 0 := by
  let τ := sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)
  let H : ℂ → ℂ := fun z => P.onIndexAbelianFilledRemainder n (z,q)
  have hgap := P.onIndexCosinePoint_mem_actual_gap n q δ hδ
  have hball (x : ℝ) : cosineGapPoint τ δ (x:ℂ) ∈
      ball (P.centers ((n:ℕ):ℤ):ℂ) (P.radii ((n:ℕ):ℤ)) := by
    rw [← P.discs_eq]
    exact P.isolating.gap (P.sourcePsi q) (P.image q hq).2 _ (hgap x)
  let u : PeriodOneRealL2 := ⟨P.parent.parent.miuraBall.actionBall.lift q,
    P.parent.parent.miuraBall.actionBall.lift_real q (P.parent.subset (P.subset hq)).1 hr⟩
  have hreal : IsRealType (CoeffPair.toMax 2 (P.sourcePsi q)) := (hillMiuraRealSource u).property
  have hrem : (quadraticCosinePrimitive τ δ H (t:ℂ)).im = 0 := by
    apply quadraticCosinePrimitive_im_eq_zero τ δ H (fun z => P.abelianGapNumerator n n (z,q)-I)
    · intro x
      exact ((P.analytic_onIndexAbelianFilledRemainder n _ ⟨hball x,hq⟩).comp
        (f := fun z : ℂ => (z,q)) (analyticAt_id.prod analyticAt_const)).differentiableAt
    · intro x
      rw [← sourceAngularSelectedPolynomial_eq_halfGap (by norm_num) (by norm_num)
        (P.sourcePsi q) ((n:ℕ):ℤ) δ hδ]
      exact P.onIndexAbelianFilledRemainder_equation n q hq _ (hball x)
    · intro x
      have hg := P.abelianGapNumerator_rotated_im_eq_zero_of_real n n q hq hr _
        (sourcePeriodicSegment_im_eq_zero_of_realType (by norm_num) (by norm_num)
          (P.sourcePsi q) hreal ((n:ℕ):ℤ) _ (hgap x)) (ball_subset_closedBall (hball x))
      simpa only [mul_sub,Complex.sub_im,Complex.mul_im,Complex.neg_re,Complex.neg_im,
        I_re,I_im,neg_zero,mul_zero,zero_mul,zero_add,sub_zero] using hg
  simpa only [onIndexAbelianCosinePhase,Complex.add_im,Complex.sub_im,Complex.ofReal_im,
    sub_self,zero_add] using hrem

end NLS.KdV.HillProductEquationPatch
