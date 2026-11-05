import NLS.KdV.HillGlobalPeriodRoots

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.FunctionalAnalysis
open scoped ENNReal ComplexConjugate

namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

def hillAbelianSelectedGlobalPsi (n : ℕ) (hn : 1 ≤ n) (E : ℂ) : ℂ :=
  hillAbelianPsiCandidate (hillAbelianSelectedGlobalRoots q hq hr n hn).val n E/
    hillAbelianCandidatePeriod q hq hr (hillAbelianSelectedGlobalRoots q hq hr n hn).val n n

theorem analyticOnNhd_hillAbelianSelectedGlobalPsi_energy (n : ℕ) (hn : 1 ≤ n) :
    AnalyticOnNhd ℂ (hillAbelianSelectedGlobalPsi q hq hr n hn) univ := by
  intro E _
  exact ((analyticOnNhd_hillAbelianPsiCandidate q hq hr
    (hillAbelianSelectedGlobalRoots q hq hr n hn).val
    (hillAbelianSelectedGlobalRoots q hq hr n hn).property n) E (mem_univ _)).div_const

theorem hillAbelianSelectedGlobalPsi_intrinsic_periods (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : 1 ≤ k) :
    (2*(Real.pi:ℂ))⁻¹ * ∮ E in C((hillRealGapCenter q hq hr k : ℂ),
      hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k),
      hillAbelianSelectedGlobalPsi q hq hr n hn E/hillEnergyCanonicalRootProduct q hq hr E =
        if k = n then 1 else 0 := by
  let roots := (hillAbelianSelectedGlobalRoots q hq hr n hn).val
  let C := hillAbelianCandidatePeriod q hq hr roots n n
  have he : (fun E => hillAbelianSelectedGlobalPsi q hq hr n hn E/hillEnergyCanonicalRootProduct q hq hr E) =
      (fun E => C⁻¹*(hillAbelianPsiCandidate roots n E/hillEnergyCanonicalRootProduct q hq hr E)) := by
    funext E
    unfold hillAbelianSelectedGlobalPsi
    dsimp only [roots,C]
    ring
  rw [he,circleIntegral.integral_const_mul]
  have hratio := (hillAbelianSelectedGlobalRoots_periods q hq hr n hn).2 k hk
  change hillAbelianCandidatePeriod q hq hr roots n k/C = _ at hratio
  rw [← hratio]
  unfold hillAbelianCandidatePeriod
  ring

end NLS.KdV
