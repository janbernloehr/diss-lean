import NLS.Fourier.PeriodicEndpointLowerInclusion
import NLS.SequenceSpaces.EndpointCompactInclusion

/-! Compactness of the original endpoint norm ball in every admissible
lower original distribution space, with the entire distribution unchanged. -/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.Fourier.PeriodicFourierLebesgue
variable {L : ℝ} [Fact (0 < L)] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Compact image of the full original endpoint norm ball; no physical
symmetry or finite-mode approximation is imposed on the source ball. -/
theorem isCompact_endpointLowerInclusion_closedBall (r t R : ℝ) (hp : p ≠ ⊤)
    (h : 1 < (-r-t)*p.toReal) :
    IsCompact (endpointLowerInclusion (L := L) (-r) t hp h '' closedBall 0 R) := by
  have hc := (WeightedCoeff.isCompact_endpointLowerInclusion_closedBall r t R hp h).image
    (sobolevCoefficients (L := L) t p).symm.continuous
  convert hc using 1
  ext v
  constructor
  · rintro ⟨q,hq,rfl⟩
    refine ⟨WeightedCoeff.endpointLowerInclusion (-r) t hp h
      (sobolevCoefficients (-r) ⊤ q),⟨sobolevCoefficients (-r) ⊤ q,?_,rfl⟩,rfl⟩
    simpa only [Metric.mem_closedBall,dist_zero_right,LinearIsometryEquiv.norm_map] using hq
  · rintro ⟨_,⟨a,ha,rfl⟩,rfl⟩
    refine ⟨(sobolevCoefficients (-r) ⊤).symm a,?_,?_⟩
    · simpa only [Metric.mem_closedBall,dist_zero_right,LinearIsometryEquiv.norm_map] using ha
    · change (sobolevCoefficients t p).symm (WeightedCoeff.endpointLowerInclusion (-r) t hp h
        ((sobolevCoefficients (-r) ⊤) ((sobolevCoefficients (-r) ⊤).symm a))) = _
      rw [LinearIsometryEquiv.apply_symm_apply]

end NLS.Fourier.PeriodicFourierLebesgue
