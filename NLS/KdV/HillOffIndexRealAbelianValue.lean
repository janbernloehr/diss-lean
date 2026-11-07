import NLS.KdV.HillOnIndexRealPhysicalTerminal
import NLS.KdV.HillCanonicalPhysicalAbelianValue

/-! The ACTUAL physical off-index Abelian values are real on the
entire real native source form, including all open-gap endpoints and
closed gaps. These are finite individual terms, not an infinite sum. -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV
namespace HillProductEquationPatch

theorem offIndexAbelianCosinePrimitive_im_eq_zero_of_real (P : HillProductEquationPatch)
    (n m : ℕ+) (hmn : m ≠ n) (q : PeriodOneHminusOne) (hq : q ∈ P.source)
    (hr : IsRealPeriodOneHminusOne q) (δ : ℂ)
    (hδ : δ^2 = (canonicalPeriodicGap (by norm_num) (by norm_num)
      (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((m:ℕ):ℤ)/2)^2) (t : ℝ) :
    (quadraticCosinePrimitive (sourceStandardRootMidpoint (by norm_num) (by norm_num)
      (P.sourcePsi q) ((m:ℕ):ℤ)) δ (fun z => P.offIndexAbelianFilledQuotient n m (z,q)) (t:ℂ)).im = 0 := by
  let τ := sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ)
  have hgap := P.onIndexCosinePoint_mem_actual_gap m q δ hδ
  have hball (x : ℝ) : cosineGapPoint τ δ (x:ℂ) ∈
      ball (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ)) := by
    rw [← P.discs_eq]
    exact P.isolating.gap (P.sourcePsi q) (P.image q hq).2 _ (hgap x)
  let u : PeriodOneRealL2 := ⟨P.parent.parent.miuraBall.actionBall.lift q,
    P.parent.parent.miuraBall.actionBall.lift_real q (P.parent.subset (P.subset hq)).1 hr⟩
  have hreal : IsRealType (CoeffPair.toMax 2 (P.sourcePsi q)) := (hillMiuraRealSource u).property
  apply quadraticCosinePrimitive_im_eq_zero τ δ _ (fun z => P.abelianGapNumerator n m (z,q))
  · intro x
    exact ((P.analytic_offIndexAbelianFilledQuotient n m hmn _ ⟨hball x,hq⟩).comp
      (f := fun z : ℂ => (z,q)) (analyticAt_id.prod analyticAt_const)).differentiableAt
  · intro x
    rw [← sourceAngularSelectedPolynomial_eq_halfGap (by norm_num) (by norm_num)
      (P.sourcePsi q) ((m:ℕ):ℤ) δ hδ]
    exact P.offIndexAbelianFilledQuotient_equation n m hmn q hq _ (hball x)
  · intro x
    exact P.abelianGapNumerator_rotated_im_eq_zero_of_real n m q hq hr _
      (sourcePeriodicSegment_im_eq_zero_of_realType (by norm_num) (by norm_num)
        (P.sourcePsi q) hreal ((m:ℕ):ℤ) _ (hgap x)) (ball_subset_closedBall (hball x))

theorem physicalOffIndexAbelianValue_im_eq_zero_of_real (P : HillProductEquationPatch)
    (n m : ℕ+) (hmn : m ≠ n) (q : PeriodOneHminusOne) (hq : q ∈ P.source)
    (hr : IsRealPeriodOneHminusOne q) : (P.physicalOffIndexAbelianValue n m q).im = 0 := by
  by_cases hg : hillHminusCanonicalGapSquare m q = 0
  · simp only [physicalOffIndexAbelianValue,P.physical_root_coefficient_zero_of_real_closed_gap m q hq hr hg,
      zero_mul,zero_im]
  · obtain ⟨t,hpoint,hroot⟩ := P.exists_real_physical_cosine_terminal m q hq hr hg
    have h := P.offIndexAbelianCosinePrimitive_im_eq_zero_of_real n m hmn q hq hr
      (sourceStandardRootHalfGap (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ)) rfl t
    simpa only [quadraticCosinePrimitive,hpoint,hroot,physicalOffIndexAbelianValue] using h

end HillProductEquationPatch

theorem hillHminusPhysicalOffIndexAbelianValue_im_eq_zero_of_real (n m : ℕ+) (hmn : m ≠ n)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) :
    (hillHminusPhysicalOffIndexAbelianValue n m q).im = 0 := by
  obtain ⟨P,hq,_⟩ := exists_hillProductEquationPatch q hr
  rw [hillHminusPhysicalOffIndexAbelianValue_eq_patch_of_real P n m hmn q hq hr]
  exact P.physicalOffIndexAbelianValue_im_eq_zero_of_real n m hmn q hq hr

end NLS.KdV
