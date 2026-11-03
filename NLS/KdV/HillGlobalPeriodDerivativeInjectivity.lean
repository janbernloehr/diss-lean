import NLS.KdV.HillPeriodKernelNumeratorProportionality
import NLS.KdV.HillNumeratorVariationRootValues
import NLS.SequenceSpaces.PositiveDeletedSpace

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

theorem hillAbelian_off_period_kernel_coordinate_eq_zero
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr) (n : ℕ) (hn : 1 ≤ n) (h : Coeff 2)
    (hperiods : ∀ k : ℕ, 1 ≤ k → k ≠ n → hillAbelianCandidatePeriod q hq hr roots n k = 0)
    (hkernel : ∀ k : ℕ, 1 ≤ k → k ≠ n →
      fderiv ℂ (hillAbelianHilbertPeriod q hq hr n k) (hillGapRootHilbertCoordinates q hq hr roots hroots) h = 0)
    (j : ℕ) (hjn : j+1 ≠ n) : h ((j+1 : ℕ) : ℤ) = 0 := by
  let a := hillGapRootHilbertCoordinates q hq hr roots hroots
  have hprop := hillAbelianNumeratorRootVariation_proportional_of_off_period_kernel q hq hr h0q h0r
    roots hroots n hn h hperiods hkernel
  have hψ : hillAbelianHilbertPsi n ((roots j : ℂ),a) = 0 := by
    rw [hillAbelianHilbertPsi_eq_genuine_candidate q hq hr roots hroots n]
    exact (hillAbelianPsiCandidate_zero_iff q hq hr roots hroots n hn _).mpr ⟨j,hjn,rfl⟩
  have hV : hillAbelianNumeratorRootVariation n a h (roots j : ℂ) = 0 := by
    have he := congrFun hprop (roots j : ℂ)
    change hillAbelianNumeratorRootVariation n a h (roots j : ℂ) = _ at he
    rw [hψ,mul_zero] at he
    exact he
  have hroot : hillAbelianHilbertRootEnergy a (j+1) = (roots j : ℂ) :=
    (hillGapRootHilbertCoordinates_reconstruct q hq hr roots hroots j).symm
  rw [hillAbelianNumeratorRootVariation_at_root n (j+1) (by omega) hjn a h _ hroot] at hV
  have hs := hillAbelianRootSlope_ne_zero_on_gap q hq hr roots hroots n (j+1) hn (by omega) (roots j : ℂ)
    (ofReal_mem_ordered_segment _ _ _ (monotone_hillRealLabels q hq hr (by omega)) (hroots j))
  have hc : ((j+1 : ℕ) : ℂ)*h ((j+1 : ℕ) : ℤ) = 0 := (mul_eq_zero.mp hV).resolve_right hs
  exact (mul_eq_zero.mp hc).resolve_left (by exact_mod_cast (show j+1 ≠ 0 by omega))

theorem hillAbelian_off_period_kernel_eq_zero_of_supported
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr) (n : ℕ) (hn : 1 ≤ n) (h : Coeff 2)
    (hsupport : ∀ m : ℤ, m ≤ 0 ∨ m = (n : ℤ) → h m = 0)
    (hperiods : ∀ k : ℕ, 1 ≤ k → k ≠ n → hillAbelianCandidatePeriod q hq hr roots n k = 0)
    (hkernel : ∀ k : ℕ, 1 ≤ k → k ≠ n →
      fderiv ℂ (hillAbelianHilbertPeriod q hq hr n k) (hillGapRootHilbertCoordinates q hq hr roots hroots) h = 0) : h = 0 := by
  ext m
  change h m = 0
  by_cases hm : m ≤ 0 ∨ m = (n : ℤ)
  · exact hsupport m hm
  · have hj : (((m.toNat-1+1 : ℕ)) : ℤ) = m := by omega
    have ht := hillAbelian_off_period_kernel_coordinate_eq_zero q hq hr h0q h0r roots hroots n hn h
      hperiods hkernel (m.toNat-1) (by omega)
    simpa only [hj] using ht

theorem hillAbelian_positiveDeleted_off_period_kernel_eq_zero
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr) (n : ℕ) (hn : 1 ≤ n)
    (h : PositiveDeletedCoeff 2 (n : ℤ))
    (hperiods : ∀ k : ℕ, 1 ≤ k → k ≠ n → hillAbelianCandidatePeriod q hq hr roots n k = 0)
    (hkernel : ∀ k : ℕ, 1 ≤ k → k ≠ n →
      fderiv ℂ (hillAbelianHilbertPeriod q hq hr n k) (hillGapRootHilbertCoordinates q hq hr roots hroots) (h : Coeff 2) = 0) :
    h = 0 := by
  have hs := (Coeff.positiveDeletedProjection_eq_self_iff 2 (n : ℤ) (h : Coeff 2)).mp
    (Coeff.positiveDeleted_fixed 2 (n : ℤ) h)
  apply Subtype.ext
  exact hillAbelian_off_period_kernel_eq_zero_of_supported q hq hr h0q h0r roots hroots n hn h hs hperiods hkernel

theorem hillAbelianSelectedGlobalRoots_period_derivative_kernel_eq_zero
    (n : ℕ) (hn : 1 ≤ n) (h : PositiveDeletedCoeff 2 (n : ℤ))
    (hkernel : ∀ k : ℕ, 1 ≤ k → k ≠ n →
      fderiv ℂ (hillAbelianHilbertPeriod q hq hr n k)
        (hillGapRootHilbertCoordinates q hq hr (hillAbelianSelectedGlobalRoots q hq hr n hn).val
          (hillAbelianSelectedGlobalRoots q hq hr n hn).property) (h : Coeff 2) = 0) : h = 0 := by
  apply hillAbelian_positiveDeleted_off_period_kernel_eq_zero q hq hr h0q h0r
    (hillAbelianSelectedGlobalRoots q hq hr n hn).val
    (hillAbelianSelectedGlobalRoots q hq hr n hn).property n hn h ?_ hkernel
  intro k hk hkn
  have hp := (hillAbelianSelectedGlobalRoots_periods q hq hr n hn).2 k hk
  rw [if_neg hkn,div_eq_zero_iff] at hp
  exact hp.resolve_right (hillAbelianSelectedGlobalRoots_periods q hq hr n hn).1

end NLS.KdV
