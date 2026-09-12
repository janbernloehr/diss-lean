import NLS.Fourier.IntrinsicSobolevEquivalence

/-!
# Finite Fourier approximation in the intrinsic interval norm

Below half regularity, finite Fourier truncations converge in the full
intrinsic interval norm, even for original data with unequal endpoints.
The truncations preserve exactly the selected physical Fourier coefficients.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace NLS.Fourier.IntrinsicIntervalSobolev
variable {s L : ℝ} [Fact (0 < L)]

/-- Finite Fourier projection transported through the actual intrinsic/weighted equivalence. -/
def fourierTruncate (hs : 0 < s) (hs₁ : s < 1 / 2) (t : Finset ℤ)
    (f : IntrinsicIntervalSobolev s L) : IntrinsicIntervalSobolev s L :=
  (weightedEquiv hs hs₁).symm (WeightedCoeff.truncate (Weight.sobolev s) 2 t (weightedEquiv hs hs₁ f))

/-- The physical coefficients of a truncation are exactly the selected original coefficients. -/
theorem fourierTruncate_coefficient (hs : 0 < s) (hs₁ : s < 1 / 2) (t : Finset ℤ)
    (f : IntrinsicIntervalSobolev s L) (n : ℤ) :
    intervalFourierCoefficient L (intervalPullback L (fourierTruncate hs hs₁ t f).val) n =
      if n ∈ t then intervalFourierCoefficient L (intervalPullback L f.val) n else 0 := by
  rw [fourierTruncate, intervalFourierCoefficient_intervalPullback (Fact.out : 0 < L),
    weightedEquiv_symm_val, fourierCoeff_sobolevL2Synthesis, WeightedCoeff.truncate_apply, weightedEquiv_apply]

/-- The full intrinsic Fourier projections have a common norm bound independent of the selected frequencies. -/
theorem norm_fourierTruncate_le (hs : 0 < s) (hs₁ : s < 1 / 2) (t : Finset ℤ)
    (f : IntrinsicIntervalSobolev s L) :
    ‖fourierTruncate hs hs₁ t f‖ ≤
      (weightedSynthesisBoundConstant s L * weightedAnalysisBoundConstant s L) * ‖f‖ := by
  exact (norm_weightedEquiv_symm_le hs hs₁ _).trans
    ((mul_le_mul_of_nonneg_left ((WeightedCoeff.norm_truncate_le _ _ t _).trans
      (norm_weightedEquiv_le hs hs₁ f)) (weightedSynthesisBoundConstant_nonneg s L)).trans_eq
        (mul_assoc _ _ _).symm)

/-- Fourier truncation converges in the exact physical intrinsic norm below half regularity. -/
theorem tendsto_fourierTruncate (hs : 0 < s) (hs₁ : s < 1 / 2) (f : IntrinsicIntervalSobolev s L) :
    Tendsto (fun t : Finset ℤ => fourierTruncate hs hs₁ t f) atTop (𝓝 f) := by
  have h := (weightedEquiv (L := L) hs hs₁).symm.continuous.tendsto (weightedEquiv hs hs₁ f) |>.comp
    (WeightedCoeff.tendsto_truncate _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (weightedEquiv hs hs₁ f))
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using! h

/-- Classes supported on finitely many Fourier frequencies are dense in the full intrinsic norm. -/
theorem dense_finite_fourierSupport (hs : 0 < s) (hs₁ : s < 1 / 2) :
    Dense {f : IntrinsicIntervalSobolev s L | ∃ t : Finset ℤ, ∀ n ∉ t,
      intervalFourierCoefficient L (intervalPullback L f.val) n = 0} := by
  intro f
  apply mem_closure_of_tendsto (tendsto_fourierTruncate hs hs₁ f)
  exact Eventually.of_forall (fun t => ⟨t, fun n hn => by rw [fourierTruncate_coefficient, if_neg hn]⟩)

end NLS.Fourier.IntrinsicIntervalSobolev
