import NLS.Fourier.PeriodicIntervalFourierLebesgue
import NLS.Fourier.IntrinsicFourierEmbedding

/-!
# Lemma A.9: continuous embeddings into the original distribution spaces

The intrinsic interval Sobolev quotient embeds complex linearly and continuously
into original FLᑫ for 0<s<1/2 and q>1/(s+1/2), and separately for s=1/2 and q>1.
Both maps are injective, preserve the actual interval function, and retain the
explicit physical dilation constants. The L² inclusion supplies all targets
q≥2, including infinity. Zero regularity uses the ordinary L² API from
`PeriodicIntervalFourierLebesgue`, not the intrinsic graph norm at s=0.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace NLS.Fourier
open SmoothPeriodicTest
variable {L : ℝ} [Fact (0 < L)]

namespace IntrinsicIntervalSobolev
open PeriodicFourierLebesgue
variable {s : ℝ}

/-- The continuous original-space A.9 injection for 0<s<1/2. -/
def originalFourierEmbedding {q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hs : 0 < s) (hs₁ : s < 1/2) (hq : 1/(s+1/2) < q) :
    IntrinsicIntervalSobolev s L →L[ℂ] PeriodicFourierLebesgue L Weight.one (ENNReal.ofReal q) :=
  (unweightedCoefficients _).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (fourierEmbedding hs hs₁ hq)

/-- Every coefficient is the actual normalized integral of the physical representative. -/
theorem originalFourierEmbedding_coefficient {q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hs : 0 < s) (hs₁ : s < 1/2) (hq : 1/(s+1/2) < q)
    (f : IntrinsicIntervalSobolev s L) (n : ℤ) :
    (originalFourierEmbedding hs hs₁ hq f).val (mode (-n)) =
      intervalFourierCoefficient L (intervalPullback L f.val) n := by
  rw [← unweightedCoefficients_apply]
  change unweightedCoefficients _ ((unweightedCoefficients _).symm (fourierEmbedding hs hs₁ hq f)) n = _
  rw [LinearIsometryEquiv.apply_symm_apply,fourierEmbedding_apply]

/-- The subcritical embedding preserves the entire original distribution. -/
theorem originalFourierEmbedding_val {q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hs : 0 < s) (hs₁ : s < 1/2) (hq : 1/(s+1/2) < q) (f : IntrinsicIntervalSobolev s L) :
    (originalFourierEmbedding hs hs₁ hq f).val = Distribution.ofL1 (intervalPullback L f.val)
      (intervalIntegrable_of_memLp_two (memLp_intervalPullback (Fact.out : 0 < L) f.val)) := by
  apply Distribution.ext_coefficients
  intro n
  rw [originalFourierEmbedding_coefficient,Distribution.ofL1_coefficient]

/-- The subcritical original-space embedding is injective. -/
theorem originalFourierEmbedding_injective {q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hs : 0 < s) (hs₁ : s < 1/2) (hq : 1/(s+1/2) < q) :
    Function.Injective (originalFourierEmbedding (L := L) hs hs₁ hq) :=
  (unweightedCoefficients _).symm.injective.comp (fourierEmbedding_injective hs hs₁ hq)

/-- The original-space bound retains the explicit physical dilation constant. -/
theorem norm_originalFourierEmbedding_le {q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hs : 0 < s) (hs₁ : s < 1/2) (hq : 1/(s+1/2) < q) (f : IntrinsicIntervalSobolev s L) :
    ‖originalFourierEmbedding hs hs₁ hq f‖ ≤ arbitraryPeriodFourierBoundConstant L hs hs₁ hq * ‖f‖ := by
  change ‖(unweightedCoefficients _).symm (fourierEmbedding hs hs₁ hq f)‖ ≤ _
  simpa only [LinearIsometryEquiv.norm_map] using norm_fourierEmbedding_le hs hs₁ hq f

/-- Arbitrary interval input is recovered as its original normalized functional. -/
theorem originalFourierEmbedding_ofFunction_val {q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hs : 0 < s) (hs₁ : s < 1/2) (hq : 1/(s+1/2) < q)
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 L)))
    (hE : fractionalIntervalEnergy s L f < ⊤) :
    (originalFourierEmbedding hs hs₁ hq (ofFunction f hf hE)).val =
      Distribution.ofL1 f (intervalIntegrable_of_memLp_two hf) := by
  apply Distribution.ext_coefficients
  intro n
  rw [originalFourierEmbedding_coefficient,Distribution.ofL1_coefficient,
    intervalFourierCoefficient_intervalPullback (Fact.out : 0 < L)]
  exact fourierCoeff_intervalL2Class (Fact.out : 0 < L) f hf n

/-- The intrinsic-class embedding has the exact original smooth-test action. -/
theorem originalFourierEmbedding_apply {q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hs : 0 < s) (hs₁ : s < 1/2) (hq : 1/(s+1/2) < q)
    (f : IntrinsicIntervalSobolev s L) (g : SmoothPeriodicTest L) :
    (originalFourierEmbedding hs hs₁ hq f).val g =
      (L:ℂ)⁻¹ * ∫ x in (0:ℝ)..L, intervalPullback L f.val x * g x := by
  rw [originalFourierEmbedding_val,Distribution.ofL1_apply]

/-- The arbitrary-input embedding has exactly the original 1/L interval action. -/
theorem originalFourierEmbedding_ofFunction_apply {q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hs : 0 < s) (hs₁ : s < 1/2) (hq : 1/(s+1/2) < q)
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 L)))
    (hE : fractionalIntervalEnergy s L f < ⊤) (g : SmoothPeriodicTest L) :
    (originalFourierEmbedding hs hs₁ hq (ofFunction f hf hE)).val g =
      (L:ℂ)⁻¹ * ∫ x in (0:ℝ)..L, f x * g x := by
  rw [originalFourierEmbedding_ofFunction_val,Distribution.ofL1_apply]

/-- The continuous original-space injection at half regularity for every finite q>1. -/
def originalHalfFourierEmbedding {q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)] (hq : 1 < q) :
    IntrinsicIntervalSobolev (1/2) L →L[ℂ] PeriodicFourierLebesgue L Weight.one (ENNReal.ofReal q) :=
  (unweightedCoefficients _).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (halfFourierEmbedding hq)

/-- The half-regularity map retains all actual physical Fourier coefficients. -/
theorem originalHalfFourierEmbedding_coefficient {q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)] (hq : 1 < q)
    (f : IntrinsicIntervalSobolev (1/2) L) (n : ℤ) :
    (originalHalfFourierEmbedding hq f).val (mode (-n)) =
      intervalFourierCoefficient L (intervalPullback L f.val) n := by
  rw [← unweightedCoefficients_apply]
  change unweightedCoefficients _ ((unweightedCoefficients _).symm (halfFourierEmbedding hq f)) n = _
  rw [LinearIsometryEquiv.apply_symm_apply,halfFourierEmbedding_apply]

/-- The half-regularity map preserves the entire original distribution. -/
theorem originalHalfFourierEmbedding_val {q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)] (hq : 1 < q)
    (f : IntrinsicIntervalSobolev (1/2) L) :
    (originalHalfFourierEmbedding hq f).val = Distribution.ofL1 (intervalPullback L f.val)
      (intervalIntegrable_of_memLp_two (memLp_intervalPullback (Fact.out : 0 < L) f.val)) := by
  apply Distribution.ext_coefficients
  intro n
  rw [originalHalfFourierEmbedding_coefficient,Distribution.ofL1_coefficient]

/-- The original half-regularity map is injective. -/
theorem originalHalfFourierEmbedding_injective {q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)] (hq : 1 < q) :
    Function.Injective (originalHalfFourierEmbedding (L := L) hq) :=
  (unweightedCoefficients _).symm.injective.comp (halfFourierEmbedding_injective hq)

/-- The half-regularity bound retains its explicit physical dilation factors. -/
theorem norm_originalHalfFourierEmbedding_le {q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)] (hq : 1 < q)
    (f : IntrinsicIntervalSobolev (1/2) L) :
    ‖originalHalfFourierEmbedding hq f‖ ≤
      (halfIntervalFourierLebesgueBoundConstant hq * Real.sqrt (intrinsicDilationConstant (1/2) (L/2)).toReal) * ‖f‖ := by
  change ‖(unweightedCoefficients _).symm (halfFourierEmbedding hq f)‖ ≤ _
  simpa only [LinearIsometryEquiv.norm_map] using norm_halfFourierEmbedding_le hq f

/-- The half-regularity map recovers arbitrary original interval input. -/
theorem originalHalfFourierEmbedding_ofFunction_val {q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)] (hq : 1 < q)
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 L)))
    (hE : fractionalIntervalEnergy (1/2) L f < ⊤) :
    (originalHalfFourierEmbedding hq (ofFunction f hf hE)).val =
      Distribution.ofL1 f (intervalIntegrable_of_memLp_two hf) := by
  apply Distribution.ext_coefficients
  intro n
  rw [originalHalfFourierEmbedding_coefficient,Distribution.ofL1_coefficient,
    intervalFourierCoefficient_intervalPullback (Fact.out : 0 < L)]
  exact fourierCoeff_intervalL2Class (Fact.out : 0 < L) f hf n

/-- The ordinary L² inclusion supplies all targets q≥2, including infinity. -/
def originalL2TargetEmbedding {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 2 ≤ q) :
    IntrinsicIntervalSobolev s L →L[ℂ] PeriodicFourierLebesgue L Weight.one q :=
  (l2OriginalEmbedding hq).comp toL2Continuous

/-- The L²-target map represents the same physical interval function. -/
theorem originalL2TargetEmbedding_val {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 2 ≤ q)
    (f : IntrinsicIntervalSobolev s L) :
    (originalL2TargetEmbedding hq f).val = Distribution.ofL1 (intervalPullback L f.val)
      (intervalIntegrable_of_memLp_two (memLp_intervalPullback (Fact.out : 0 < L) f.val)) :=
  l2OriginalEmbedding_val hq f.val

/-- The L²-target bound has the exact inverse square-root length factor. -/
theorem norm_originalL2TargetEmbedding_le {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 2 ≤ q)
    (f : IntrinsicIntervalSobolev s L) :
    ‖originalL2TargetEmbedding hq f‖ ≤ (Real.sqrt L)⁻¹ * ‖f‖ :=
  (norm_l2OriginalEmbedding_le hq f.val).trans (norm_toL2_le f)

/-- The L²-target map on intrinsic classes is injective. -/
theorem originalL2TargetEmbedding_injective {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 2 ≤ q) :
    Function.Injective (originalL2TargetEmbedding (s := s) (L := L) hq) :=
  (l2OriginalEmbedding_injective hq).comp Subtype.val_injective

end IntrinsicIntervalSobolev
end NLS.Fourier
