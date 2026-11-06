import NLS.KdV.HillCommonMixedRootCoordinates
import NLS.KdV.HillHighIntrinsicPeriodComparison

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- The own normalization period with exactly the same original low and
free high contour convention as the actual mixed period equations. -/
def hillMixedOwnComplexPeriod (N n : ℕ) (t : Coeff 2 × Coeff 2) : ℂ :=
  if n<N then hillAbelianComplexPeriod q hq hr n n t else hillAbelianComplexPeriod 0 h0q h0r n n t

theorem analyticOnNhd_hillMixedOwnComplexPeriod
    (N n : ℕ) (hn : 1≤n) (B D : ℝ) (hc : HillComplexTailPeriodControl h0q h0r N B D)
    (U : Set (Coeff 2)) (hU : IsOpen U) (hsub : U⊆ball 0 B)
    (hLow : ∀ k : ℕ, 1≤k → k<N → AnalyticOnNhd ℂ (hillAbelianComplexPeriod q hq hr k k) (univ ×ˢ U)) :
    AnalyticOnNhd ℂ (hillMixedOwnComplexPeriod q hq hr h0q h0r N n) (univ ×ˢ U) := by
  unfold hillMixedOwnComplexPeriod
  by_cases hnN : n<N
  · simpa only [if_pos hnN] using hLow n hn hnN
  · have hhigh := analyticOnNhd_hillAbelianComplexPeriod_of_domain 0 h0q h0r n n hn U hU (by
      intro p hp E hE
      have hpB : ‖p‖≤B := (show ‖p‖<B by simpa only [mem_ball,dist_zero_right] using hsub hp).le
      exact (hc p hpB).1 n (by omega) E hE)
    simpa only [if_neg hnN] using hhigh

theorem hillMixedOwnComplexPeriod_at_base
    (N n : ℕ) (hN : 1≤N) (hn : 1≤n) (B D : ℝ)
    (hc : HillComplexTailPeriodControl h0q h0r N B D) (hp : ‖SpectralWeight.one.toCoeff q‖≤B) (a : Coeff 2) :
    hillMixedOwnComplexPeriod q hq hr h0q h0r N n (a,SpectralWeight.one.toCoeff q)=hillAbelianHilbertPeriod q hq hr n n a := by
  unfold hillMixedOwnComplexPeriod
  by_cases hnN : n<N
  · rw [if_pos hnN,hillAbelianComplexPeriod_at_base q hq hr n n hn a]
  · rw [if_neg hnN,hillHighAbelianComplexPeriod_eq_intrinsic_physical h0q h0r N hN B D hc q hq hr hp n n (by omega) a]
    rfl

theorem hillMixedOwnComplexPeriod_selected_ne_zero
    (N n : ℕ) (hN : 1≤N) (hn : 1≤n) (B D : ℝ)
    (hc : HillComplexTailPeriodControl h0q h0r N B D) (hp : ‖SpectralWeight.one.toCoeff q‖≤B) :
    hillMixedOwnComplexPeriod q hq hr h0q h0r N n
      (hillAbelianSelectedGlobalRootCoordinates q hq hr n hn,SpectralWeight.one.toCoeff q)≠0 := by
  rw [hillMixedOwnComplexPeriod_at_base q hq hr h0q h0r N n hN hn B D hc hp]
  rw [hillAbelianSelectedGlobalRootCoordinates,hillAbelianHilbertPeriod_eq_genuine_period q hq hr
    (hillAbelianSelectedGlobalRoots q hq hr n hn).val (hillAbelianSelectedGlobalRoots q hq hr n hn).property n n]
  exact (hillAbelianSelectedGlobalRoots_periods q hq hr n hn).1

end NLS.KdV
