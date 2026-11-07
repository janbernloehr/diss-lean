import NLS.Articles.KdVPseudomeasures.OriginalHillAnalyticAbelianFamily
import NLS.KdV.HillPhysicalAbelianRegularGerm

/-! ACTUAL Hill physical divisor evaluation of the off-index Abelian
family. The auxiliary-boundary phase, exact original energy, and
physical norming-sheet sign are retained on ONE open complex native
domain before ALL indices, including zero-sheet/branch-point values. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.KdV NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures

theorem original_Hill_common_physical_divisor_source (P : HillProductEquationPatch) :
    IsOpen P.physicalDirichletSource ∧ P.physicalDirichletSource ⊆ P.source ∧
      (∀ q : OriginalHminusOnePotential, originalPeriodOneCoefficients q ∈ P.source →
        originalPeriodOneCoefficients q ∈ P.physicalDirichletSource) ∧
      ∀ q ∈ P.physicalDirichletSource,
        (∀ k : ℤ, P.physicalDirichletFrequency k q ∈ ball (P.centers k:ℂ) (P.radii k)) ∧
        ∀ m : ℕ+, P.physicalDirichletFrequency ((m:ℕ):ℤ) q^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ) =
          hillHminusCanonicalDirichlet m q :=
  ⟨P.physicalDirichletSource_open,inter_subset_left,
    (fun q hq => P.real_mem_physicalDirichletSource _ hq (originalPeriodOneCoefficients_real q)),
    fun q hq => ⟨P.physicalDirichletFrequency_mem_disc q hq,fun m => P.physicalDirichletFrequency_energy m q hq.1⟩⟩

theorem original_Hill_actual_Dirichlet_root_sheet (P : HillProductEquationPatch) :
    ∀ m : ℕ+, AnalyticOnNhd ℂ (P.physicalDirichletRootCoefficient m) P.physicalDirichletSource ∧
      ∀ q ∈ P.physicalDirichletSource,
        (P.physicalDirichletRootCoefficient m q)^2 = sourceAngularSelectedPolynomial (by norm_num) (by norm_num)
          (P.sourcePsi q) ((m:ℕ):ℤ) (P.physicalDirichletFrequency ((m:ℕ):ℤ) q) ∧
        P.abelianGapRootMultiplier m (P.physicalDirichletFrequency ((m:ℕ):ℤ) q,q)*P.physicalDirichletRootCoefficient m q =
          hillHminusDirichletSheet m q := by
  intro m
  exact ⟨P.analytic_physicalDirichletRootCoefficient m,fun q hq =>
    ⟨P.physicalDirichletRootCoefficient_sq m q hq,P.physicalDirichletRootCoefficient_preserves_sheet m q hq⟩⟩

theorem original_Hill_physical_offIndex_Abelian_value_analytic (P : HillProductEquationPatch) :
    ∀ n m : ℕ+, m ≠ n → AnalyticOnNhd ℂ (P.physicalOffIndexAbelianValue n m) P.physicalDirichletSource ∧
      (∀ q ∈ P.physicalDirichletSource, hillHminusDirichletSheet m q = 0 → P.physicalOffIndexAbelianValue n m q = 0) ∧
      ∀ q ∈ P.physicalDirichletSource,
        P.physicalDirichletFrequency ((m:ℕ):ℤ) q ∈ P.abelianGapDisc m q →
        P.physicalDirichletRootCoefficient m q ≠ 0 →
        P.physicalOffIndexAbelianValue n m q =
          (sourceStandardRoot (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) (P.physicalDirichletFrequency ((m:ℕ):ℤ) q)/
            P.physicalDirichletRootCoefficient m q)*P.offIndexAbelianEndpointIntegral n m q (P.physicalDirichletFrequency ((m:ℕ):ℤ) q) := by
  intro n m hmn
  exact ⟨P.analytic_physicalOffIndexAbelianValue n m hmn,
    (fun q _ hs => P.physicalOffIndexAbelianValue_zero_of_sheet_zero n m q hs),
    P.physicalOffIndexAbelianValue_eq_improper_integral_on_cut_complement n m hmn⟩

end NLS.Articles.KdVPseudomeasures
