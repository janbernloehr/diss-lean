import NLS.KdV.HillAbelianProductContinuity
import NLS.ComplexAnalysis.ContinuousCircleIntegral
import NLS.KdV.HillRealGapContours

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal

namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

def hillAbelianCandidatePeriod (σ : ℕ → ℝ) (n k : ℕ) : ℂ :=
  (2*(Real.pi : ℂ))⁻¹ * ∮ z in C((hillRealGapCenter q hq hr k : ℂ),
      hillRealGapHalfLength q hq hr k + hillRealGapCollar q hq hr k),
    hillAbelianPsiCandidate σ n z / hillEnergyCanonicalRootProduct q hq hr z

theorem continuous_hillAbelianCandidatePeriod (n k : ℕ) (hk : 1 ≤ k) :
    Continuous (fun σ : hillGapRootBox q hq hr =>
      hillAbelianCandidatePeriod q hq hr σ.val n k) := by
  let : CompactSpace (hillGapRootBox q hq hr) :=
    isCompact_iff_compactSpace.mp (isCompact_hillGapRootBox q hq hr)
  let c := (hillRealGapCenter q hq hr k : ℂ)
  let R := hillRealGapHalfLength q hq hr k + hillRealGapCollar q hq hr k
  obtain ⟨hd,hη,_⟩ := hillRealGapContour_geometry q hq hr k hk
  have hR : 0 ≤ R := add_nonneg hd hη.le
  have hsub := hillRealGapContour_sphere_subset q hq hr k hk
  have hden : ContinuousOn (fun p : (hillGapRootBox q hq hr) × ℂ =>
      hillEnergyCanonicalRootProduct q hq hr p.2) (univ ×ˢ sphere c R) := by
    exact (analyticOnNhd_hillEnergyCanonicalRootProduct q hq hr).continuousOn.comp
      continuous_snd.continuousOn (fun p hp => hsub hp.2)
  have hF : ContinuousOn (fun p : (hillGapRootBox q hq hr) × ℂ =>
      hillAbelianPsiCandidate p.1.val n p.2 / hillEnergyCanonicalRootProduct q hq hr p.2)
      (univ ×ˢ sphere c R) :=
    (continuous_hillAbelianPsiCandidate_joint q hq hr n).continuousOn.div hden
      (fun p hp => hillEnergyCanonicalRootProduct_ne_zero_on_realCutDomain q hq hr p.2
        (hsub hp.2))
  exact continuous_const.mul
    (continuous_circleIntegral_of_continuous_joint_on_sphere _ c R hR hF)

end NLS.KdV
