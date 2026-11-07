import NLS.Articles.KdVPseudomeasures.OriginalHillOffIndexAbelianEndpoints
import NLS.KdV.HillAbelianRegularRootSheets

/-! Actual off-index Abelian source analyticity on the UNCHANGED
original native patch. The filled quotient crosses ALL complex cuts
and collapsed gaps. The genuine improper integral and prescribed
regular root-sheet continuation use that SAME quotient. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.KdV NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures

theorem original_Hill_filled_Abelian_quotient_joint_analytic (P : HillProductEquationPatch) :
    ∀ n m : ℕ+, m ≠ n →
      AnalyticOnNhd ℂ (P.offIndexAbelianFilledQuotient n m)
        (ball (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ)) ×ˢ P.source) ∧
      ∀ q ∈ P.source, ∀ z ∈ ball (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ)),
        sourceAngularSelectedPolynomial (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) z*
          deriv (fun w => P.offIndexAbelianFilledQuotient n m (w,q)) z+
          (z-sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ))*P.offIndexAbelianFilledQuotient n m (z,q) =
            P.abelianGapNumerator n m (z,q) := by
  intro n m hmn
  exact ⟨P.analytic_offIndexAbelianFilledQuotient n m hmn,P.offIndexAbelianFilledQuotient_equation n m hmn⟩

theorem original_Hill_improper_Abelian_integral_joint_analytic (P : HillProductEquationPatch) :
    ∀ n m : ℕ+, m ≠ n → IsOpen (P.offIndexAbelianJointDomain m) ∧
      AnalyticOnNhd ℂ (fun t : ℂ × PeriodOneHminusOne => P.offIndexAbelianEndpointIntegral n m t.2 t.1)
        (P.offIndexAbelianJointDomain m) ∧
      ∀ q ∈ P.source,
        (∀ z ∈ P.abelianGapDisc m q, P.offIndexAbelianEndpointIntegral n m q z =
          P.offIndexAbelianNormalizedPrimitive n m (z,q)) ∧
        (∀ z ∈ P.abelianGapDisc m q, HasDerivAt (fun w => P.offIndexAbelianNormalizedPrimitive n m (w,q))
          (P.abelianFrequencyDifferential n (z,q)) z) ∧
        ∀ a ∈ ({canonicalPeriodicLeft (by norm_num) (by norm_num) (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((m:ℕ):ℤ),
          canonicalPeriodicRight (by norm_num) (by norm_num) (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((m:ℕ):ℤ)} : Set ℂ),
          Tendsto (fun z => P.offIndexAbelianNormalizedPrimitive n m (z,q)) (𝓝[P.abelianGapDisc m q] a) (𝓝 0) := by
  intro n m hmn
  exact ⟨P.offIndexAbelianJointDomain_open m,P.analytic_offIndexAbelianEndpointIntegral_joint n m hmn,
    fun q hq => ⟨P.offIndexAbelianEndpointIntegral_eq_filled_root_product n m hmn q hq,
      P.hasDerivAt_offIndexAbelianNormalizedPrimitive n m hmn q hq,
      P.offIndexAbelianNormalizedPrimitive_endpoint_limit n m hmn q hq⟩⟩

theorem original_Hill_Abelian_prescribed_root_sheet_analytic (P : HillProductEquationPatch)
    (n m : ℕ+) (hmn : m ≠ n) (R : ℂ × PeriodOneHminusOne → ℂ)
    (D : Set (ℂ × PeriodOneHminusOne))
    (hD : D ⊆ ball (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ)) ×ˢ P.source)
    (hR : AnalyticOnNhd ℂ R D) : AnalyticOnNhd ℂ (P.offIndexAbelianRegularSheetPrimitive n m R) D :=
  P.analytic_offIndexAbelianRegularSheetPrimitive n m hmn R D hD hR

end NLS.Articles.KdVPseudomeasures
