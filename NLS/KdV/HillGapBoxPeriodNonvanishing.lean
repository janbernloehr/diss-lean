import NLS.ComplexAnalysis.CompactNonzeroNormLowerBound
import NLS.KdV.HillGlobalGapPeriodCriterion

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate unitInterval

namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem hillAbelianCandidatePeriod_own_ne_zero
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr) (n : ℕ) (hn : 1 ≤ n) :
    hillAbelianCandidatePeriod q hq hr roots n n ≠ 0 := by
  intro hperiod
  obtain ⟨E,hE,hzero⟩ := exists_hillAbelianPsiCandidate_zero_of_intrinsic_period_zero
    q hq hr roots hroots n n hn hperiod
  exact hillAbelianPsiCandidate_ne_zero_on_own_gap q hq hr roots hroots n hn E hE hzero

theorem exists_hillAbelianCandidatePeriod_own_norm_lower_bound (n : ℕ) (hn : 1 ≤ n) :
    ∃ c : ℝ, 0 < c ∧ ∀ roots ∈ hillGapRootBox q hq hr,
      c ≤ ‖hillAbelianCandidatePeriod q hq hr roots n n‖ := by
  let : CompactSpace (hillGapRootBox q hq hr) :=
    isCompact_iff_compactSpace.mp (isCompact_hillGapRootBox q hq hr)
  obtain ⟨roots,hroots⟩ := hillGapRootBox_nonempty q hq hr
  let : Nonempty (hillGapRootBox q hq hr) := ⟨⟨roots,hroots⟩⟩
  obtain ⟨c,hc,hbound⟩ := exists_pos_norm_lower_bound_of_compactSpace
    (fun roots : hillGapRootBox q hq hr => hillAbelianCandidatePeriod q hq hr roots.val n n)
    (continuous_hillAbelianCandidatePeriod q hq hr n n hn)
    (fun roots => hillAbelianCandidatePeriod_own_ne_zero q hq hr roots.val roots.property n hn)
  exact ⟨c,hc,fun roots hroots => hbound ⟨roots,hroots⟩⟩

end NLS.KdV
