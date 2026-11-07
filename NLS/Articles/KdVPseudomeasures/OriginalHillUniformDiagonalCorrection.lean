import NLS.Articles.KdVPseudomeasures.OriginalHillActionAngleAmplitude
import NLS.KdV.HillOnIndexUniformCartesianBound

/-! Uniform diagonal correction and frequency-weight estimates for
ACTUAL Hill action-angle formulas. All complex collapsed gaps are
included. Original energy-weight conversion remains a separate step. -/
noncomputable section
open Set Metric Complex NLS.KdV NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures

theorem original_Hill_diagonal_correction_UNIFORM_ALL_n_bound (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots) :
    ∀ q ∈ P.physicalDirichletSource, ∃ U : Set PeriodOneHminusOne,
      IsOpen U ∧ q ∈ U ∧ U ⊆ P.physicalDirichletSource ∧
      ∃ C : ℝ, 0 < C ∧ ∀ a ∈ U, ∀ n : ℕ+,
        ‖P.physicalOnIndexAbelianCorrection n a‖ ≤ C :=
  P.exists_local_uniform_physicalOnIndexAbelianCorrection_bound H

theorem original_Hill_diagonal_phase_UNIFORM_ALL_n_bound (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots) :
    ∀ q ∈ P.physicalDirichletSource, ∃ U : Set PeriodOneHminusOne,
      IsOpen U ∧ q ∈ U ∧ U ⊆ P.physicalDirichletSource ∧
      ∃ C : ℝ, 0 < C ∧ ∀ a ∈ U, ∀ n : ℕ+,
        ‖Complex.exp (I*P.physicalOnIndexAbelianCorrection n a)‖ ≤ C ∧
          ‖Complex.exp (-I*P.physicalOnIndexAbelianCorrection n a)‖ ≤ C :=
  P.exists_local_uniform_physicalOnIndex_phase_exponential_bound H

theorem exists_original_Hill_uniform_diagonal_correction_patch (q : OriginalHminusOnePotential) :
    ∃ P : HillProductEquationPatch, originalPeriodOneCoefficients q ∈ P.physicalDirichletSource ∧
      ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ originalPeriodOneCoefficients q ∈ U ∧
        U ⊆ P.physicalDirichletSource ∧ ∃ C : ℝ, 0 < C ∧
          ∀ a ∈ U, ∀ n : ℕ+, ‖P.physicalOnIndexAbelianCorrection n a‖ ≤ C := by
  obtain ⟨A,H⟩ := exists_miuraHillPsiFamily_with_original_estimates
  have hr := originalPeriodOneCoefficients_real q
  obtain ⟨P,hq,_,hA⟩ := exists_hillProductEquationPatch_with_family A (originalPeriodOneCoefficients q) hr
  have HP : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots := by rw [hA]; exact H
  have hphysical := P.real_mem_physicalDirichletSource _ hq hr
  exact ⟨P,hphysical,P.exists_local_uniform_physicalOnIndexAbelianCorrection_bound HP _ hphysical⟩

end NLS.Articles.KdVPseudomeasures
