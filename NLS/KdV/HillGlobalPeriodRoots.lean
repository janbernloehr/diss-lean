import NLS.FunctionalAnalysis.CountableIntervalBoxFixedPoint
import NLS.KdV.HillContinuousGapRootMap

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.FunctionalAnalysis
open scoped ENNReal ComplexConjugate

namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem exists_hillAbelian_global_period_roots (n : ℕ) (hn : 1 ≤ n) :
    ∃ roots : hillGapRootBox q hq hr, ∀ k : ℕ, 1 ≤ k → k ≠ n →
      hillAbelianCandidatePeriod q hq hr roots.val n k = 0 := by
  obtain ⟨roots,hfix⟩ := exists_fixed_point_countableIntervalBox
    (fun j => hillRealLabels q hq hr (2*(j+1)-1))
    (fun j => hillRealLabels q hq hr (2*(j+1)))
    (fun j => monotone_hillRealLabels q hq hr (by omega : 2*(j+1)-1 ≤ 2*(j+1)))
    (hillAbelianGapRootMap q hq hr n hn) (continuous_hillAbelianGapRootMap q hq hr n hn)
  exact ⟨roots,fun k hk hkn => hillAbelianGapRootMap_fixed_point_periods q hq hr n hn roots hfix k hk hkn⟩

theorem exists_hillAbelian_global_normalized_period_roots (n : ℕ) (hn : 1 ≤ n) :
    ∃ roots : hillGapRootBox q hq hr,
      hillAbelianCandidatePeriod q hq hr roots.val n n ≠ 0 ∧
      ∀ k : ℕ, 1 ≤ k → hillAbelianCandidatePeriod q hq hr roots.val n k/
        hillAbelianCandidatePeriod q hq hr roots.val n n = if k = n then 1 else 0 := by
  obtain ⟨roots,hperiods⟩ := exists_hillAbelian_global_period_roots q hq hr n hn
  have hown := hillAbelianCandidatePeriod_own_ne_zero q hq hr roots.val roots.property n hn
  refine ⟨roots,hown,?_⟩
  intro k hk
  by_cases hkn : k = n
  · subst k
    rw [if_pos rfl,div_self hown]
  · rw [if_neg hkn,hperiods k hk hkn,zero_div]

def hillAbelianSelectedGlobalRoots (n : ℕ) (hn : 1 ≤ n) : hillGapRootBox q hq hr :=
  Classical.choose (exists_hillAbelian_global_normalized_period_roots q hq hr n hn)

theorem hillAbelianSelectedGlobalRoots_periods (n : ℕ) (hn : 1 ≤ n) :
    hillAbelianCandidatePeriod q hq hr (hillAbelianSelectedGlobalRoots q hq hr n hn).val n n ≠ 0 ∧
      ∀ k : ℕ, 1 ≤ k → hillAbelianCandidatePeriod q hq hr (hillAbelianSelectedGlobalRoots q hq hr n hn).val n k/
        hillAbelianCandidatePeriod q hq hr (hillAbelianSelectedGlobalRoots q hq hr n hn).val n n =
          if k = n then 1 else 0 :=
  Classical.choose_spec (exists_hillAbelian_global_normalized_period_roots q hq hr n hn)

end NLS.KdV
