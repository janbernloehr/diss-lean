import NLS.KdV.HillOffIndexUniformSeries
import NLS.ComplexAnalysis.LocalAnalyticApproximationOn
import NLS.ComplexAnalysis.BanachSmoothAnalyticOn

/-! Full Banach-source analyticity of the ACTUAL physical infinite
correction on the unchanged physical source of a retained family. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem localUniformAnalyticApproximation_physicalOffIndexAbelianCorrection
    (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots) (n : ℕ+) :
    HasLocalUniformAnalyticApproximationOn (P.physicalOffIndexAbelianPartialSum n)
      (P.physicalOffIndexAbelianCorrection n) P.physicalDirichletSource := by
  apply HasLocalUniformAnalyticApproximationOn.of_open_local_uniform P.physicalDirichletSource_open
    (P.analytic_physicalOffIndexAbelianPartialSum n)
  intro q hq
  obtain ⟨U,hU,hqU,_,hconv⟩ := P.exists_local_uniform_physicalOffIndexAbelianCorrection H q hq
  exact ⟨U,hU,hqU,hconv n⟩

theorem analytic_physicalOffIndexAbelianCorrection (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots) (n : ℕ+) :
    AnalyticOnNhd ℂ (P.physicalOffIndexAbelianCorrection n) P.physicalDirichletSource :=
  analyticOnNhd_of_complexSmoothOn _ P.physicalDirichletSource_open
    (P.localUniformAnalyticApproximation_physicalOffIndexAbelianCorrection H n).contDiffOn

theorem exists_uniform_fderiv_physicalOffIndexAbelianCorrection (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.physicalDirichletSource) :
    ∃ r : ℝ, 0 < r ∧ ball q r ⊆ P.physicalDirichletSource ∧
      TendstoUniformlyOn (fun N => fderiv ℂ (P.physicalOffIndexAbelianPartialSum n N))
        (fderiv ℂ (P.physicalOffIndexAbelianCorrection n)) atTop (ball q r) :=
  (P.localUniformAnalyticApproximation_physicalOffIndexAbelianCorrection H n).uniform_fderiv q hq

end NLS.KdV.HillProductEquationPatch
