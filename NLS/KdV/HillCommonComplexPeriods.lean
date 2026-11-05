import NLS.KdV.HillCommonComplexContourDomain
import NLS.KdV.HillComplexPeriodDomainAnalytic

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal

namespace NLS.KdV

variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillAbelianComplexPeriods_common_free_neighborhood :
    ∃ U : Set (Coeff 2), IsOpen U ∧ (0 : Coeff 2) ∈ U ∧
      ∀ n k : ℕ, 1 ≤ k →
        AnalyticOnNhd ℂ (hillAbelianComplexPeriod 0 hq hr n k) (univ ×ˢ U) := by
  obtain ⟨ε,C,hε,_,hbound⟩ := exists_hillFreeGapContour_common_complex_neighborhood hq hr
  refine ⟨ball 0 ε,isOpen_ball,mem_ball_self hε,?_⟩
  intro n k hk
  apply analyticOnNhd_hillAbelianComplexPeriod_of_domain 0 hq hr n k hk (ball 0 ε) isOpen_ball
  intro p hp E hE
  have hp' : ‖p‖ ≤ ε := by
    exact (show ‖p‖ < ε by simpa only [mem_ball,dist_zero_right] using hp).le
  exact (hbound p hp' k hk E hE).1

end NLS.KdV
