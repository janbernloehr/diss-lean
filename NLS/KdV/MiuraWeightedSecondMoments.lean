import NLS.KdV.MiuraHillPsiOriginalEstimates
import NLS.ZakharovShabat.SourceWeightedSecondMomentSums

/-! # The same actual Miura numerator branch supports weighted moment sums -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

/-- No change of root family or normalized numerator is made: the
weighted moment atlas uses precisely the supplied actual Miura family. -/
theorem MiuraHillPsiFamily.exists_weighted_secondMoment_atlas
    (B : MiuraHillPsiFamily)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) B.originalDomain B.domain B.roots) :
    ∃ W : Set (CoeffPair 2), ∃ A : SourceAbelianMomentAtlas (by norm_num) (by norm_num) W B.roots,
      ∃ U : Set (CoeffPair 2), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus 2 ⊆ U ∧
        U ⊆ A.domain ∩ B.domain ∧
        (∀ ψ ∈ U, ∀ n : ℤ, Summable (fun k : ℤ => ‖(k : ℂ)*A.moment n k 2 ψ‖)) ∧
        (∀ n : ℤ, AnalyticOnNhd ℂ (A.weightedSecondMomentSum n) U) ∧
        ∀ φ ∈ U, ∃ T : Set (CoeffPair 2), IsOpen T ∧ φ ∈ T ∧ T ⊆ U ∧
          ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ T, ∀ n : ℤ,
            ‖A.weightedSecondMomentSum n ψ‖ ≤ (1+‖(n : ℂ)‖)*C := by
  classical
  obtain ⟨W,_hW,_hrealW,hcharts⟩ := H.angular_extension.toSourcePsiNormalizedComplexExtension.exists_moment_localCharts
    B.domain_open B.real_subset
  choose L hL using hcharts
  let A : SourceAbelianMomentAtlas (by norm_num) (by norm_num) W B.roots := ⟨L⟩
  obtain ⟨U,hU,hUc,hreal,hsub,hsum,ha,_hconv,hbound⟩ :=
    A.exists_analytic_weightedSecondMomentSum H.angular_extension B.domain_open B.real_subset
  exact ⟨W,A,U,hU,hUc,hreal,hsub,hsum,ha,hbound⟩

end NLS.KdV
