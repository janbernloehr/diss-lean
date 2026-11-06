import NLS.KdV.HillUniformComplexPeriodRoot
import NLS.ComplexAnalysis.BanachAnalyticZeroBound

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical

namespace NLS.KdV



variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- The actual common complex period-root charts have a uniform linear
source bound. Both the constants and the radii precede the coordinate index. -/
theorem exists_hillComplexFreeSupportedPeriods_common_linear_root_bound :
    ∃ ρ δ C : ℝ, 0<ρ ∧ 0<δ ∧ 0<C ∧ ∀ n : ℕ, 1≤n →
      ∃ s : Coeff 2 → PositiveDeletedCoeff 2 (n : ℤ),
        AnalyticOnNhd ℂ s (ball 0 δ) ∧ s 0=0 ∧ ∀ p∈ball 0 δ,
          ‖s p‖≤C*‖p‖ ∧ (s p,p)∈ball 0 ρ ∧
          hillComplexFreeSupportedPeriodMap hq hr n (s p,p)=0 ∧
          (∀ k : ℕ, 1≤k → k≠n → hillAbelianComplexPeriod 0 hq hr n k ((s p : Coeff 2),p)=0) ∧
          ∀ a∈ball 0 ρ, hillComplexFreeSupportedPeriodMap hq hr n (a,p)=0 → a=s p := by
  obtain ⟨ρ,δ,hρ,hδ,hcharts⟩ := exists_hillComplexFreeSupportedPeriods_common_analytic_root hq hr
  refine ⟨ρ,δ/4,8*ρ/δ,hρ,by positivity,by positivity,?_⟩
  intro n hn
  obtain ⟨s,ha,hzero,hinfo⟩ := hcharts n hn
  have hsub : ball (0 : Coeff 2) (δ/4) ⊆ ball 0 δ := ball_subset_ball (by linarith)
  have hbound (p : Coeff 2) (hp : p∈ball 0 δ) : ‖s p‖≤ρ := by
    have hmem := (hinfo p hp).1
    have hh : ‖(s p,p)‖<ρ := by simpa only [mem_ball,dist_zero_right] using hmem
    exact (le_max_left ‖s p‖ ‖p‖).trans hh.le
  refine ⟨s,ha.mono hsub,hzero,?_⟩
  intro p hp
  exact ⟨norm_le_mul_norm_of_analytic_zero_ball_bound s δ ρ hδ ha hzero hbound p hp,
    hinfo p (hsub hp)⟩

end NLS.KdV
