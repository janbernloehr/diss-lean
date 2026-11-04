import NLS.Articles.KdVPseudomeasures.OriginalHillCommonAnalyticZeroSequences
import NLS.KdV.HillUniformlyBoundedZeroSequenceDomain
import NLS.KdV.HillPeriodJacobianUniformComplexInverse
import NLS.KdV.HillCanonicalZeroSequencePeriods

/-! Locally uniform FULL-l2 bounds and full operator inverse bounds
for ALL original Hill zero sequences on common complex neighborhoods.
The regular quotient bounds include every signed row and collapsed gap;
the finer squared-energy-gap estimate remains a separate obligation. -/
noncomputable section
open Set Metric Complex NLS.KdV NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures

theorem original_Hill_locally_uniform_complex_zero_sequence_bounds :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ IsConnected U ∧
      (∀ q : OriginalHminusOnePotential, originalPeriodOneCoefficients q ∈ U) ∧
      U ⊆ hillHminusCanonicalZeroSequenceDomain ∧
      (∀ n : ℕ+, AnalyticOnNhd ℂ (hillHminusCanonicalZeroSequence n) U) ∧
      ∀ q ∈ U, ∃ r M C : ℝ, 0 < r ∧ 0 ≤ M ∧ 0 ≤ C ∧ ball q r ⊆ U ∧
        ∀ y ∈ ball q r, ∀ n : ℕ+, ‖hillHminusCanonicalZeroSequence n y‖ ≤ M ∧
          ‖fderiv ℂ (hillHminusCanonicalZeroSequence n) y‖ ≤ C := by
  refine ⟨hillHminusUniformZeroSequenceDomain,isOpen_hillHminusUniformZeroSequenceDomain,
    isConnected_hillHminusUniformZeroSequenceDomain,
    (fun q => real_mem_hillHminusUniformZeroSequenceDomain _ (originalPeriodOneCoefficients_real q)),
    hillHminusUniformZeroSequenceDomain_subset,
    (fun n => (analyticOnNhd_hillHminusCanonicalZeroSequence n).mono hillHminusUniformZeroSequenceDomain_subset),?_⟩
  intro q hq
  obtain ⟨r,M,hr,hM,hU,hbound⟩ := exists_locally_uniform_hillHminusZeroSequence_norm_bound q hq
  obtain ⟨s,C,hs,hC,_,hder⟩ := exists_locally_uniform_hillHminusZeroSequence_fderiv_bound q hq
  refine ⟨min r s,M,C,lt_min hr hs,hM,hC,(ball_subset_ball (min_le_left _ _)).trans hU,?_⟩
  exact fun y hy n => ⟨hbound y (ball_subset_ball (min_le_left _ _) hy) n,
    hder y (ball_subset_ball (min_le_right _ _) hy) n⟩

theorem original_Hill_common_complex_zero_sequence_inverse_bound (q : OriginalHminusOnePotential) :
    ∃ P : HillProductEquationPatch, originalPeriodOneCoefficients q ∈ P.source ∧
      ∃ r M : ℝ, 0 < r ∧ 0 ≤ M ∧
        ∀ y ∈ ball (originalPeriodOneCoefficients q) r, ∀ n : ℕ+,
          ∃ R : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2,
            (P.sequenceJacobian n (hillHminusCanonicalZeroSequence n y,y)).comp R = ContinuousLinearMap.id ℂ _ ∧
            R.comp (P.sequenceJacobian n (hillHminusCanonicalZeroSequence n y,y)) = ContinuousLinearMap.id ℂ _ ∧ ‖R‖ ≤ M := by
  obtain ⟨P,hq,_⟩ := exists_hillProductEquationPatch _ (originalPeriodOneCoefficients_real q)
  obtain ⟨r,M,hr,hM,_,hbound⟩ := P.exists_common_complex_source_sequenceJacobian_inverse _ hq (originalPeriodOneCoefficients_real q)
  exact ⟨P,hq,r,M,hr,hM,fun y hy n => (hbound y hy n).2⟩

theorem original_Hill_common_complex_zero_sequence_quotient_bounds (q : OriginalHminusOnePotential) :
    ∃ P : HillProductEquationPatch, originalPeriodOneCoefficients q ∈ P.source ∧
      ∃ r c Q : ℝ, 0 < r ∧ 0 < c ∧ 0 ≤ Q ∧
        ∀ y ∈ ball (originalPeriodOneCoefficients q) r, ∀ n : ℕ+,
          P.equation n (hillHminusCanonicalZeroSequence n y,y) = 0 ∧
          ∀ k : ℤ,
            c ≤ ‖sourceSingleRootQuotientJointProduct (by norm_num) (by norm_num) k
              (sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi y) k,
                P.frequencySource (hillHminusCanonicalZeroSequence n y,y))‖ ∧
            ∀ z ∈ P.discs k,
              ‖sourceSingleRootQuotientJointProduct (by norm_num) (by norm_num) k
                (z,P.frequencySource (hillHminusCanonicalZeroSequence n y,y))‖ ≤ Q := by
  obtain ⟨P,hq,_⟩ := exists_hillProductEquationPatch _ (originalPeriodOneCoefficients_real q)
  obtain ⟨r,c,hr,hc,_,hlower⟩ := P.exists_common_zero_sequence_midpoint_quotient_lower_bound _ hq (originalPeriodOneCoefficients_real q)
  obtain ⟨s,Q,hs,hQ,_,hupper⟩ := P.exists_common_zero_sequence_allDisc_quotient_upper_bound _ hq (originalPeriodOneCoefficients_real q)
  obtain ⟨t,ht,_,hperiod⟩ := P.exists_common_canonical_zero_sequence_period_ball _ hq (originalPeriodOneCoefficients_real q)
  let ρ := min r (min s t)
  have hρ : 0 < ρ := lt_min hr (lt_min hs ht)
  refine ⟨P,hq,ρ,c,Q,hρ,hc,hQ,?_⟩
  intro y hy n
  have hyr := ball_subset_ball (min_le_left r (min s t)) hy
  have hys := ball_subset_ball ((min_le_right r (min s t)).trans (min_le_left s t)) hy
  have hyt := ball_subset_ball ((min_le_right r (min s t)).trans (min_le_right s t)) hy
  exact ⟨(hperiod y hyt n).2,fun k => ⟨hlower y hyr n k,hupper y hys n k⟩⟩

end NLS.Articles.KdVPseudomeasures
