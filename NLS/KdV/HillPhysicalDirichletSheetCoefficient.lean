import NLS.KdV.HillPhysicalDirichletPlacement
import NLS.KdV.HminusOneDirichletSheet
import NLS.ZakharovShabat.SourceDeletedPairOmittedSquare
import NLS.ZakharovShabat.DiscriminantPairFactorization
import NLS.ComplexAnalysis.QuadraticRootBounds

/-! The selected quadratic root at the ACTUAL Hill Dirichlet divisor.
Its sign is the physical norming multiplier's sign. One nonvanishing
omitted-product denominator works before ALL indices; no division by
a gap or by a possibly zero physical sheet is used. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

def abelianGapRootMultiplier (P : HillProductEquationPatch) (m : ℕ+) (t : ℂ × PeriodOneHminusOne) : ℂ :=
  2*I*sourceStandardRootOmittedProduct (by norm_num) (by norm_num) ((m:ℕ):ℤ) (P.sourcePsi t.2) t.1

theorem abelianGapRootMultiplier_ne_zero (P : HillProductEquationPatch) (m : ℕ+)
    (t : ℂ × PeriodOneHminusOne)
    (ht : t ∈ ball (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ)) ×ˢ P.source) :
    P.abelianGapRootMultiplier m t ≠ 0 := by
  let D := P.isolating.periodCircle (P.sourcePsi t.2) (P.image t.2 ht.2).2 ((m:ℕ):ℤ)
    (P.centers ((m:ℕ):ℤ)) (P.radii ((m:ℕ):ℤ)) (P.radii_pos _) (P.discs_eq _)
  exact mul_ne_zero (by simp) (sourceStandardRootOmittedProduct_ne_zero (by norm_num) (by norm_num)
    (P.sourcePsi t.2) t.1 ((m:ℕ):ℤ) (D.closedBall_subset_omittedDomain (ball_subset_closedBall ht.1)))

theorem analytic_abelianGapRootMultiplier (P : HillProductEquationPatch) (m : ℕ+) :
    AnalyticOnNhd ℂ (P.abelianGapRootMultiplier m)
      (ball (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ)) ×ˢ P.source) := by
  intro t ht
  let D := P.isolating.periodCircle (P.sourcePsi t.2) (P.image t.2 ht.2).2 ((m:ℕ):ℤ)
    (P.centers ((m:ℕ):ℤ)) (P.radii ((m:ℕ):ℤ)) (P.radii_pos _) (P.discs_eq _)
  have hz := D.closedBall_subset_omittedDomain (ball_subset_closedBall ht.1)
  have hO := ((P.quotients.roots.joint ((m:ℕ):ℤ)).2 (t.1,P.sourcePsi t.2) ⟨(P.image _ ht.2).1,hz⟩).comp
    (f := fun x : ℂ × PeriodOneHminusOne => (x.1,P.sourcePsi x.2))
    (analyticAt_fst.prod ((P.analytic_sourcePsi t.2 ht.2).comp (f := Prod.snd) analyticAt_snd))
  exact analyticAt_const.mul hO

theorem abelianGapRootMultiplier_sq_mul_polynomial (P : HillProductEquationPatch) (m : ℕ+)
    (t : ℂ × PeriodOneHminusOne)
    (ht : t ∈ ball (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ)) ×ˢ P.source) :
    P.abelianGapRootMultiplier m t^2*sourceAngularSelectedPolynomial (by norm_num) (by norm_num)
      (P.sourcePsi t.2) ((m:ℕ):ℤ) t.1 = hillHminusRadicand t.2 (t.1^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ)) := by
  let D := P.isolating.periodCircle (P.sourcePsi t.2) (P.image t.2 ht.2).2 ((m:ℕ):ℤ)
    (P.centers ((m:ℕ):ℤ)) (P.radii ((m:ℕ):ℤ)) (P.radii_pos _) (P.discs_eq _)
  have hother := D.closedBall_subset_omittedDomain (ball_subset_closedBall ht.1)
  rw [hillHminusRadicand,hillHminusDiscriminant_shifted_miura_square t.2 _ _ t.1
    (P.parent.parent.miuraBall.actionBall.image t.2 (P.parent.subset (P.subset ht.2)).1)]
  change P.abelianGapRootMultiplier m t^2*sourceAngularSelectedPolynomial (by norm_num) (by norm_num)
    (P.sourcePsi t.2) ((m:ℕ):ℤ) t.1 = (canonicalDiscriminant (by norm_num) (periodOnePotential (P.sourcePsi t.2)) t.1)^2-4
  rw [sourceAngularSelectedPolynomial_eq_endpoint_factor,
    canonicalDiscriminant_sq_sub_four_eq_pair_mul (by norm_num) (by norm_num) _ (periodOnePotential_mem _) ((m:ℕ):ℤ),
    ← sourceStandardRootOmittedProduct_sq_eq_canonicalDeletedPeriodicProduct (by norm_num) (by norm_num) (P.sourcePsi t.2) ((m:ℕ):ℤ) t.1 hother]
  unfold abelianGapRootMultiplier
  rw [mul_pow,mul_pow,I_sq]
  ring

def physicalDirichletRootCoefficient (P : HillProductEquationPatch) (m : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  hillHminusDirichletSheet m q/P.abelianGapRootMultiplier m (P.physicalDirichletFrequency ((m:ℕ):ℤ) q,q)

theorem source_subset_canonicalDirichlet (P : HillProductEquationPatch) : P.source ⊆ hillHminusCanonicalDirichletDomain := by
  intro q hq
  exact mem_iUnion.mpr ⟨P.parent.parent,(P.parent.subset (P.subset hq)).1⟩

theorem analytic_physicalDirichletRootCoefficient (P : HillProductEquationPatch) (m : ℕ+) :
    AnalyticOnNhd ℂ (P.physicalDirichletRootCoefficient m) P.physicalDirichletSource := by
  intro q hq
  have hμ := P.analytic_physicalDirichletFrequency ((m:ℕ):ℤ) q hq.1
  have ht : (P.physicalDirichletFrequency ((m:ℕ):ℤ) q,q) ∈
      ball (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ)) ×ˢ P.source :=
    ⟨P.physicalDirichletFrequency_mem_disc q hq _,hq.1⟩
  have hM := (P.analytic_abelianGapRootMultiplier m _ ht).comp
    (f := fun y => (P.physicalDirichletFrequency ((m:ℕ):ℤ) y,y)) (hμ.prod analyticAt_id)
  exact (analyticOnNhd_hillHminusDirichletSheet m q (P.source_subset_canonicalDirichlet hq.1)).div hM
    (P.abelianGapRootMultiplier_ne_zero m _ ht)

theorem physicalDirichletSheet_sq_frequency (P : HillProductEquationPatch) (m : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) :
    (hillHminusDirichletSheet m q)^2 =
      (canonicalDiscriminant (by norm_num) (periodOnePotential (P.sourcePsi q)) (P.physicalDirichletFrequency ((m:ℕ):ℤ) q))^2-4 := by
  rw [hillHminusDirichletSheet_sq m q (P.source_subset_canonicalDirichlet hq),← P.physicalDirichletFrequency_energy m q hq]
  rw [hillHminusDiscriminant_shifted_miura_square q _ _ _ (P.parent.parent.miuraBall.actionBall.image q (P.parent.subset (P.subset hq)).1)]
  rfl

theorem physicalDirichletRootCoefficient_sq (P : HillProductEquationPatch) (m : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.physicalDirichletSource) :
    (P.physicalDirichletRootCoefficient m q)^2 = sourceAngularSelectedPolynomial (by norm_num) (by norm_num)
      (P.sourcePsi q) ((m:ℕ):ℤ) (P.physicalDirichletFrequency ((m:ℕ):ℤ) q) := by
  let μ := P.physicalDirichletFrequency ((m:ℕ):ℤ) q
  let D := P.isolating.periodCircle (P.sourcePsi q) (P.image q hq.1).2 ((m:ℕ):ℤ)
    (P.centers ((m:ℕ):ℤ)) (P.radii ((m:ℕ):ℤ)) (P.radii_pos _) (P.discs_eq _)
  have hμ : μ ∈ sourceStandardRootOmittedDomain (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) :=
    D.closedBall_subset_omittedDomain (ball_subset_closedBall (P.physicalDirichletFrequency_mem_disc q hq _))
  rw [physicalDirichletRootCoefficient,div_pow,P.physicalDirichletSheet_sq_frequency m q hq.1,
    sourceAngularSelectedPolynomial_eq_endpoint_factor,
    canonicalDiscriminant_sq_sub_four_eq_pair_mul (by norm_num) (by norm_num) _ (periodOnePotential_mem _) ((m:ℕ):ℤ),
    ← sourceStandardRootOmittedProduct_sq_eq_canonicalDeletedPeriodicProduct (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) μ hμ]
  unfold abelianGapRootMultiplier
  rw [mul_pow,mul_pow,I_sq]
  have hO := sourceStandardRootOmittedProduct_ne_zero (by norm_num) (by norm_num) (P.sourcePsi q) μ ((m:ℕ):ℤ) hμ
  dsimp only [μ] at hO
  field_simp [hO]
  ring

theorem norm_physicalDirichletRootCoefficient_le (P : HillProductEquationPatch) (m : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.physicalDirichletSource) :
    ‖P.physicalDirichletRootCoefficient m q‖ ≤
      ‖P.physicalDirichletFrequency ((m:ℕ):ℤ) q-sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ)‖+
        ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ)‖/2 := by
  apply norm_le_of_sq_eq_gap_polynomial
  simpa only [sourceAngularSelectedPolynomial,quadraticRootPolynomial,sourcePeriodicGapDisplacement_apply] using
    P.physicalDirichletRootCoefficient_sq m q hq

end NLS.KdV.HillProductEquationPatch
