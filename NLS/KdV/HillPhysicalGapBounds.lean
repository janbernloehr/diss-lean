import NLS.KdV.HillWeightIndependence
import NLS.KdV.HillGapTail

/-! # Weighted high-gap bounds for the actual physical Hill discriminant

The weighted reduction has now been identified with the actual rough
energy discriminant. Thus the coefficient and tail estimates apply to
its actual characteristic roots in the high strips. The intrinsic real
labels and their direct gap bounds are supplied downstream by
`HillCanonicalGapBounds`; these general results also support other
characteristic-root families.
-/

noncomputable section
open scoped ENNReal
namespace NLS.KdV

theorem hillPeriodOne_physical_gap_le (w : SpectralWeight)
    (q : WeightedCoeff w.doubleIndex.toWeight 2) (n : ℕ) (hn : 1 ≤ n)
    (hcut : 8*‖q‖ ≤ (n : ℝ)) (z y : ℂ)
    (hz : z ∈ reducedHillStrip n) (hy : y ∈ reducedHillStrip n)
    (hdz : hillL2Discriminant (w.toCoeff (hillPeriodOnePotential w q)) z ^ 2 = 4)
    (hdy : hillL2Discriminant (w.toCoeff (hillPeriodOnePotential w q)) y ^ 2 = 4) :
    w (2*(n : ℤ))*‖z-y‖ ≤ 6*‖q‖ := by
  have hq : w.toCoeff (hillPeriodOnePotential w q) ∈ Coeff.paritySubspace 0 := by
    rw [toCoeff_hillPeriodOnePotential]
    exact Coeff.periodDouble_mem _
  have hc : 8*‖hillPeriodOnePotential w q‖ ≤ (n : ℝ) := by
    simpa only [norm_hillPeriodOnePotential] using hcut
  exact hillPeriodOne_gap_le w q n hn hcut z y hz hy
    ((hillReduced_weighted_zero_iff_l2Discriminant w _ hq n hn z hz hc).mpr hdz)
    ((hillReduced_weighted_zero_iff_l2Discriminant w _ hq n hn y hy hc).mpr hdy)

/-- Corrected-constant Appendix A.7 tail estimate for actual characteristic
root families, in the exact source period-one weight and Fourier norm. -/
theorem hillPeriodOne_physical_gap_tail_bound (w : SpectralWeight)
    (q : WeightedCoeff w.doubleIndex.toWeight 2) (N : ℕ) (hN : 1 ≤ N)
    (hcut : 8*‖q‖ ≤ (N : ℝ)) (ξp ξm : ℕ → ℂ)
    (hp : ∀ n, N ≤ n → ξp n ∈ reducedHillStrip n)
    (hm : ∀ n, N ≤ n → ξm n ∈ reducedHillStrip n)
    (hdp : ∀ n, N ≤ n → hillL2Discriminant (w.toCoeff (hillPeriodOnePotential w q)) (ξp n) ^ 2 = 4)
    (hdm : ∀ n, N ≤ n → hillL2Discriminant (w.toCoeff (hillPeriodOnePotential w q)) (ξm n) ^ 2 = 4) :
    Summable (fun k : ℕ => (w (2*((k+N : ℕ) : ℤ)))^2*‖ξp (k+N)-ξm (k+N)‖^2) ∧
      (∑' k : ℕ, (w (2*((k+N : ℕ) : ℤ)))^2*‖ξp (k+N)-ξm (k+N)‖^2) ≤
        9*‖Coeff.fourierTail N (WeightedCoeff.weightEquiv w.doubleIndex.toWeight 2 q)‖^2+
          2304*‖q‖^4/(N : ℝ) := by
  have hq : w.toCoeff (hillPeriodOnePotential w q) ∈ Coeff.paritySubspace 0 := by
    rw [toCoeff_hillPeriodOnePotential]
    exact Coeff.periodDouble_mem _
  have hc (n : ℕ) (hn : N ≤ n) : 8*‖hillPeriodOnePotential w q‖ ≤ (n : ℝ) := by
    rw [norm_hillPeriodOnePotential]
    exact hcut.trans (by exact_mod_cast hn)
  apply hillPeriodOne_gap_tail_bound w q N hN hcut ξp ξm hp hm
  · intro n hn
    exact (hillReduced_weighted_zero_iff_l2Discriminant w _ hq n (hN.trans hn)
      (ξp n) (hp n hn) (hc n hn)).mpr (hdp n hn)
  · intro n hn
    exact (hillReduced_weighted_zero_iff_l2Discriminant w _ hq n (hN.trans hn)
      (ξm n) (hm n hn) (hc n hn)).mpr (hdm n hn)

end NLS.KdV
