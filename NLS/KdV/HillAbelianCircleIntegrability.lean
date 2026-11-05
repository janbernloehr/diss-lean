import NLS.KdV.HillAbelianCandidatePeriods

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal

namespace NLS.KdV



theorem hillAbelianCandidate_circleIntegrable
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (σ : ℕ → ℝ) (hσ : σ ∈ hillGapRootBox q hq hr) (n k : ℕ) (hk : 1 ≤ k) :
    CircleIntegrable (fun z => hillAbelianPsiCandidate σ n z /
      hillEnergyCanonicalRootProduct q hq hr z) (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k + hillRealGapCollar q hq hr k) := by
  have hsub := hillRealGapContour_sphere_subset q hq hr k hk
  have hnum := (analyticOnNhd_hillAbelianPsiCandidate q hq hr σ hσ n).continuousOn.mono
    (subset_univ (sphere (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k + hillRealGapCollar q hq hr k)))
  have hden := (analyticOnNhd_hillEnergyCanonicalRootProduct q hq hr).continuousOn.mono hsub
  exact (hnum.div hden
    (fun z hz => hillEnergyCanonicalRootProduct_ne_zero_on_realCutDomain q hq hr z
      (hsub hz))).circleIntegrable
        (add_nonneg (hillRealGapContour_geometry q hq hr k hk).1
          (hillRealGapContour_geometry q hq hr k hk).2.1.le)

end NLS.KdV
