import NLS.Fourier.IntrinsicSobolevComplete

/-!
# Weighted Fourier synthesis into the intrinsic interval space

Weighted Hilbert coefficients synthesize actual interval Sobolev classes for
`0<s<1` on every positive interval. The physical norm bound combines restriction
on a period with the exact interval-coordinate dilation factors.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NLS.Fourier

/-- Physical interval coordinates preserve fractional energy finiteness in both directions. -/
theorem fractionalIntervalEnergy_intervalPullback_lt_top_iff {L : ℝ} (hL : 0 < L)
    (s : ℝ) (f : CircleL2) :
    fractionalIntervalEnergy s L (intervalPullback L f) < ⊤ ↔
      fractionalIntervalEnergy s 2 (circlePullback f) < ⊤ := by
  simpa only [intervalPullback, div_mul_cancel₀ 2 hL.ne'] using
    fractionalIntervalEnergy_dilation_lt_top_iff (by positivity : 0 < 2 / L) s L (circlePullback f)

/-- The full physical interval norm is controlled by the period-two norm with its dilation factor. -/
theorem intrinsicIntervalSize_intervalPullback_le {L : ℝ} (hL : 0 < L) (s : ℝ) (f : CircleL2)
    (hE : fractionalIntervalEnergy s 2 (circlePullback f) < ⊤) :
    intrinsicIntervalSize s L (intervalPullback L f) ≤
      Real.sqrt (intrinsicDilationConstant s (2 / L)).toReal * intrinsicIntervalSize s 2 (circlePullback f) := by
  have hf : MemLp (circlePullback f) 2 (volume.restrict (Ioo 0 ((2 / L) * L))) := by
    simpa only [div_mul_cancel₀ 2 hL.ne', Measure.restrict_congr_set Ioo_ae_eq_Ioc] using memLp_circlePullback f
  have he : fractionalIntervalEnergy s ((2 / L) * L) (circlePullback f) < ⊤ := by
    simpa only [div_mul_cancel₀ 2 hL.ne'] using hE
  simpa only [div_mul_cancel₀ 2 hL.ne', intervalPullback] using
    intrinsicIntervalSize_dilation_le (by positivity : 0 < 2 / L) s L (circlePullback f) hf he

namespace IntrinsicIntervalSobolev
variable {s L : ℝ} [Fact (0 < L)]

/-- Weighted Fourier synthesis as an actual intrinsic interval class, valid throughout `0<s<1`. -/
def weightedSynthesis (hs : 0 < s) (hs₁ : s < 1) :
    WeightedCoeff (Weight.sobolev s) 2 →ₗ[ℂ] IntrinsicIntervalSobolev s L where
  toFun a := ⟨sobolevL2Synthesis hs.le a, by
    apply (memLp_fractionalDifferenceQuotient_iff s L _ (measurable_intervalPullback L _)).mpr
    apply (fractionalIntervalEnergy_intervalPullback_lt_top_iff (Fact.out : 0 < L) s _).mpr
    exact fractionalIntervalEnergy_lt_top_of_periodic hs _
      (hasFractionalPeriodicRegularity_sobolevL2Synthesis hs hs₁ a)⟩
  map_add' a b := by
    apply Subtype.ext
    exact map_add _ a b
  map_smul' c a := by
    apply Subtype.ext
    exact map_smul _ c a

@[simp] theorem weightedSynthesis_val (hs : 0 < s) (hs₁ : s < 1)
    (a : WeightedCoeff (Weight.sobolev s) 2) : (weightedSynthesis (L := L) hs hs₁ a).val = sobolevL2Synthesis hs.le a := rfl

@[simp] theorem weightedSynthesis_coefficient (hs : 0 < s) (hs₁ : s < 1)
    (a : WeightedCoeff (Weight.sobolev s) 2) (n : ℤ) :
    intervalFourierCoefficient L (intervalPullback L (weightedSynthesis (L := L) hs hs₁ a).val) n = a.val n := by
  rw [intervalFourierCoefficient_intervalPullback (Fact.out : 0 < L), weightedSynthesis_val,
    fourierCoeff_sobolevL2Synthesis]

/-- Explicit synthesis norm constant on an arbitrary physical interval. -/
def weightedSynthesisBoundConstant (s L : ℝ) : ℝ :=
  Real.sqrt (intrinsicDilationConstant s (2 / L)).toReal * Real.sqrt (intervalRestrictionConstant s).toReal

theorem weightedSynthesisBoundConstant_nonneg (s L : ℝ) : 0 ≤ weightedSynthesisBoundConstant s L := by
  unfold weightedSynthesisBoundConstant
  positivity

/-- Weighted synthesis is uniformly bounded in the exact physical intrinsic norm. -/
theorem norm_weightedSynthesis_le (hs : 0 < s) (hs₁ : s < 1) (a : WeightedCoeff (Weight.sobolev s) 2) :
    ‖weightedSynthesis (L := L) hs hs₁ a‖ ≤ weightedSynthesisBoundConstant s L * ‖a‖ := by
  rw [norm_eq_size, weightedSynthesis_val]
  have hE := fractionalIntervalEnergy_lt_top_of_periodic hs _
    (hasFractionalPeriodicRegularity_sobolevL2Synthesis hs hs₁ a)
  exact (intrinsicIntervalSize_intervalPullback_le (Fact.out : 0 < L) s _ hE).trans
    ((mul_le_mul_of_nonneg_left (intrinsicIntervalSize_sobolevL2Synthesis_le hs hs₁ a)
      (Real.sqrt_nonneg _)).trans_eq (mul_assoc _ _ _).symm)

/-- Continuous weighted synthesis on every positive physical interval. -/
def weightedSynthesisContinuous (hs : 0 < s) (hs₁ : s < 1) :
    WeightedCoeff (Weight.sobolev s) 2 →L[ℂ] IntrinsicIntervalSobolev s L :=
  (weightedSynthesis hs hs₁).mkContinuous (weightedSynthesisBoundConstant s L) (norm_weightedSynthesis_le hs hs₁)

theorem weightedSynthesis_injective (hs : 0 < s) (hs₁ : s < 1) :
    Function.Injective (weightedSynthesis (L := L) hs hs₁) := by
  intro a b h
  exact sobolevL2Synthesis_injective hs.le (congrArg (fun f : IntrinsicIntervalSobolev s L => f.val) h)

end IntrinsicIntervalSobolev
end NLS.Fourier
