import NLS.ZakharovShabat.PeriodicEndpointRegions
import NLS.ZakharovShabat.BoundaryCharacteristicOrders

/-! # Global multiplicities of periodic endpoint labels

Every repeated occurrence in a complete paired sequence contributes its
exact original operator multiplicity, with no restriction to a central block.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat

/-- The full endpoint enumeration counts each periodic eigenvalue with its algebraic multiplicity. -/
theorem PeriodicEndpointLabeling.global_multiplicity
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {φ : PairSpace p}
    {N : ℕ} {ξ η : ℤ → ℂ} (h : PeriodicEndpointLabeling hp φ N ξ η) (z : ℂ) :
    (∑ᶠ n : ℤ, ({ξ n,η n} : Multiset ℂ).count z) = periodicAlgebraicMultiplicity hp φ z := by
  obtain ⟨K,hzK,hNK⟩ := ((eventually_mem_centralSpectralBox z).and (Filter.eventually_ge_atTop N)).exists
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.Icc (-(K:ℤ)) K) (by
    intro n hn
    have hmem : z ∈ ({ξ n,η n} : Multiset ℂ) := Multiset.count_pos.mp (Nat.pos_of_ne_zero hn)
    have he : ξ n = z ∨ η n = z := by
      simpa only [Multiset.insert_eq_cons,Multiset.mem_cons,Multiset.mem_singleton,eq_comm] using hmem
    have hi : n.natAbs ≤ K := by
      by_contra hnK
      have hd := abs_lt.mp (h.abs_re_distant_sub_lt n (by omega) z he)
      have hb := abs_le.mp hzK.1.le
      by_cases hsign : 0 ≤ n
      · have hc : (K:ℝ)+1 ≤ (n:ℝ) := by exact_mod_cast (show (K:ℤ)+1 ≤ n by omega)
        nlinarith [Real.pi_pos]
      · have hc : (n:ℝ) ≤ -(K:ℝ)-1 := by exact_mod_cast (show n ≤ -(K:ℤ)-1 by omega)
        nlinarith [Real.pi_pos]
    simp only [Finset.mem_coe,Finset.mem_Icc]
    omega)]
  rw [(h.central_at_larger_cutoff K hNK).count_eq]
  by_cases hz : z ∈ periodicSpectrum hp φ
  · rw [if_pos ((mem_centralPeriodicSpectrum hp φ K z).mpr ⟨hz,hzK⟩)]
  · rw [if_neg (fun hmem => hz ((mem_centralPeriodicSpectrum hp φ K z).mp hmem).1)]
    exact ((periodicAlgebraicMultiplicity_eq_zero_iff hp φ z).mpr
      (by simpa only [periodicSpectrum,Set.mem_compl_iff,not_not] using hz)).symm

end NLS.ZakharovShabat
