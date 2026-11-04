import NLS.KdV.HillHomogeneousSpectralSequence
import NLS.Articles.KdVEstimates.IntegerEstimates
import NLS.Articles.KdVEstimates.EstimateAdapter

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.KdV
open scoped ENNReal Classical

namespace NLS.Articles.KdVEstimates



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

theorem integer_hillSpectralSequence_estimates (m : ℕ) (hm : 1≤m) :
    ∃ c d : ℝ, 0<c ∧ 0<d ∧
      ∀ p : RealHillWeightedPotential (hillIntegerWeight m), p.val.val 0=0 →
      let b := hillRealNativeIntegerLower m (m-1) (by omega) p
      let S := ‖hillHomogeneousSpectralSequence h0q h0r m m le_rfl p‖
      let T := ‖hillHomogeneousSpectralSequence h0q h0r m (m-1) (by omega) p‖
      (S ≤ c*(‖p.val‖+(1+‖b.val‖)^m*‖b.val‖)) ∧
      (‖p.val‖ ≤ d*(S+(1+T)^m*T)) := by
  obtain ⟨c,d,hc,hd,hbound⟩ := theorem2_native m hm
  refine ⟨2*c,2*d,by positivity,by positivity,?_⟩
  intro p hmean
  obtain ⟨hforward,hinverse⟩ := hbound p hmean
  dsimp only at hforward hinverse ⊢
  constructor
  · exact directSobolevBound_of_actionBound m (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hc.le
      (norm_hillHomogeneousSpectralSequence_sq h0q h0r m m le_rfl p) hforward
  · exact inverseSobolevBound_of_actionBound m (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hd.le
      (norm_hillHomogeneousSpectralSequence_sq h0q h0r m m le_rfl p)
      (norm_hillHomogeneousSpectralSequence_sq h0q h0r m (m-1) (by omega) p) hinverse

end NLS.Articles.KdVEstimates
