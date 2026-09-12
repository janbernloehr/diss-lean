import NLS.Fourier.IntrinsicSobolevSynthesis
import NLS.Fourier.IntrinsicFourierEmbedding

/-!
# Intrinsic and weighted Fourier Sobolev spaces are continuously equivalent

For `0<s<1/2`, the actual normalized Fourier integrals identify the intrinsic
interval Hilbert space with the weighted Fourier Hilbert space. Both directions
have explicit uniform norm bounds on every positive interval length.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NLS.Fourier.IntrinsicIntervalSobolev
variable {s L : ℝ} [Fact (0 < L)]

/-- Weighted analysis uses the actual Fourier coefficients of the underlying physical class. -/
def weightedAnalysis (hs : 0 < s) (hs₁ : s < 1 / 2) :
    IntrinsicIntervalSobolev s L →ₗ[ℂ] WeightedCoeff (Weight.sobolev s) 2 where
  toFun f := ⟨fourierCoeff f.val, by
    simpa only [intervalFourierCoefficient_intervalPullback (Fact.out : 0 < L)] using!
      memlp_sobolev_intervalFourierCoefficient (Fact.out : 0 < L) hs hs₁ _
        (memLp_intervalPullback (Fact.out : 0 < L) f.val) f.energy_lt_top⟩
  map_add' f g := by
    apply Subtype.ext
    funext n
    change fourierCoeff (f.val + g.val) n = fourierCoeff f.val n + fourierCoeff g.val n
    simp only [← fourierBasis_repr, map_add, lp.coeFn_add, Pi.add_apply]
  map_smul' c f := by
    apply Subtype.ext
    funext n
    change fourierCoeff (c • f.val) n = c * fourierCoeff f.val n
    simp only [← fourierBasis_repr, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]

@[simp] theorem weightedAnalysis_apply (hs : 0 < s) (hs₁ : s < 1 / 2)
    (f : IntrinsicIntervalSobolev s L) (n : ℤ) : (weightedAnalysis hs hs₁ f).val n = fourierCoeff f.val n := rfl

@[simp] theorem weightedSynthesis_weightedAnalysis (hs : 0 < s) (hs₁ : s < 1 / 2)
    (f : IntrinsicIntervalSobolev s L) : weightedSynthesis hs (by linarith) (weightedAnalysis hs hs₁ f) = f := by
  apply Subtype.ext
  apply fourierBasis.repr.injective
  ext n
  simp only [fourierBasis_repr, weightedSynthesis_val, fourierCoeff_sobolevL2Synthesis, weightedAnalysis_apply]

@[simp] theorem weightedAnalysis_weightedSynthesis (hs : 0 < s) (hs₁ : s < 1 / 2)
    (a : WeightedCoeff (Weight.sobolev s) 2) :
    weightedAnalysis hs hs₁ (weightedSynthesis (L := L) hs (by linarith) a) = a := by
  apply Subtype.ext
  funext n
  simp only [weightedAnalysis_apply, weightedSynthesis_val, fourierCoeff_sobolevL2Synthesis]

/-- Explicit analysis norm constant, including dilation from the physical interval to period two. -/
def weightedAnalysisBoundConstant (s L : ℝ) : ℝ :=
  Real.sqrt (intervalSobolevBoundConstant s).toReal * Real.sqrt (intrinsicDilationConstant s (L / 2)).toReal

theorem weightedAnalysisBoundConstant_nonneg (s L : ℝ) : 0 ≤ weightedAnalysisBoundConstant s L := by
  unfold weightedAnalysisBoundConstant
  positivity

/-- Uniform weighted coefficient control in the actual intrinsic norm on arbitrary interval lengths. -/
theorem norm_weightedAnalysis_le (hs : 0 < s) (hs₁ : s < 1 / 2) (f : IntrinsicIntervalSobolev s L) :
    ‖weightedAnalysis hs hs₁ f‖ ≤ weightedAnalysisBoundConstant s L * ‖f‖ := by
  have hL : 0 < L := Fact.out
  have hE := (fractionalIntervalEnergy_intervalPullback_lt_top_iff hL s f.val).mp f.energy_lt_top
  have he : weightedAnalysis hs hs₁ f = intervalSobolevCoefficients hs hs₁
      (circlePullback f.val) (memLp_circlePullback f.val) hE := by
    apply Subtype.ext
    funext n
    simp only [weightedAnalysis_apply, intervalSobolevCoefficients_apply, periodTwoCoefficient_circlePullback]
  have hscale := intrinsicIntervalSize_periodTwoDilation_le hL s (intervalPullback L f.val)
    (memLp_intervalPullback hL f.val) f.energy_lt_top
  rw [intervalDilation_intervalPullback hL, ← norm_eq_size] at hscale
  rw [he]
  exact (norm_intervalSobolevCoefficients_le hs hs₁ _ _ hE).trans
    ((mul_le_mul_of_nonneg_left hscale (Real.sqrt_nonneg _)).trans_eq (mul_assoc _ _ _).symm)

/-- The algebraic identification between intrinsic interval and weighted Fourier classes. -/
def weightedLinearEquiv (hs : 0 < s) (hs₁ : s < 1 / 2) :
    IntrinsicIntervalSobolev s L ≃ₗ[ℂ] WeightedCoeff (Weight.sobolev s) 2 where
  toLinearMap := weightedAnalysis hs hs₁
  invFun := weightedSynthesis hs (by linarith)
  left_inv := weightedSynthesis_weightedAnalysis hs hs₁
  right_inv := weightedAnalysis_weightedSynthesis hs hs₁

/-- The genuine continuous linear equivalence invoked in the subcritical interval Sobolev identification. -/
def weightedEquiv (hs : 0 < s) (hs₁ : s < 1 / 2) :
    IntrinsicIntervalSobolev s L ≃L[ℂ] WeightedCoeff (Weight.sobolev s) 2 :=
  (weightedLinearEquiv hs hs₁).toContinuousLinearEquivOfBounds
    (weightedAnalysisBoundConstant s L) (weightedSynthesisBoundConstant s L)
    (norm_weightedAnalysis_le hs hs₁) (norm_weightedSynthesis_le hs (by linarith))

/-- The equivalence preserves the actual normalized physical Fourier integrals. -/
@[simp] theorem weightedEquiv_apply (hs : 0 < s) (hs₁ : s < 1 / 2)
    (f : IntrinsicIntervalSobolev s L) (n : ℤ) :
    (weightedEquiv hs hs₁ f).val n = intervalFourierCoefficient L (intervalPullback L f.val) n := by
  exact (intervalFourierCoefficient_intervalPullback (Fact.out : 0 < L) f.val n).symm

/-- Its inverse is the existing actual `L²` Fourier synthesis, restricted to the physical interval. -/
@[simp] theorem weightedEquiv_symm_val (hs : 0 < s) (hs₁ : s < 1 / 2)
    (a : WeightedCoeff (Weight.sobolev s) 2) :
    ((weightedEquiv (L := L) hs hs₁).symm a).val = sobolevL2Synthesis hs.le a := rfl

/-- Uniform forward bound for the continuous equivalence. -/
theorem norm_weightedEquiv_le (hs : 0 < s) (hs₁ : s < 1 / 2) (f : IntrinsicIntervalSobolev s L) :
    ‖weightedEquiv hs hs₁ f‖ ≤ weightedAnalysisBoundConstant s L * ‖f‖ := norm_weightedAnalysis_le hs hs₁ f

/-- Uniform inverse bound retains the original physical interval normalization. -/
theorem norm_weightedEquiv_symm_le (hs : 0 < s) (hs₁ : s < 1 / 2)
    (a : WeightedCoeff (Weight.sobolev s) 2) :
    ‖(weightedEquiv (L := L) hs hs₁).symm a‖ ≤ weightedSynthesisBoundConstant s L * ‖a‖ :=
  norm_weightedSynthesis_le hs (by linarith) a

/-- Passing arbitrary interval input to the intrinsic quotient does not alter any Fourier coefficient. -/
@[simp] theorem weightedEquiv_ofFunction (hs : 0 < s) (hs₁ : s < 1 / 2)
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 L)))
    (hE : fractionalIntervalEnergy s L f < ⊤) (n : ℤ) :
    (weightedEquiv hs hs₁ (ofFunction f hf hE)).val n = intervalFourierCoefficient L f n := by
  rw [weightedEquiv_apply, intervalFourierCoefficient_intervalPullback (Fact.out : 0 < L)]
  exact fourierCoeff_intervalL2Class (Fact.out : 0 < L) f hf n

/-- A.9's intrinsic Fourier map factors through the identified weighted Hilbert space. -/
theorem fourierEmbedding_eq_weightedEquiv {q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hs : 0 < s) (hs₁ : s < 1 / 2) (hq : 1 / (s + 1 / 2) < q) :
    fourierEmbedding (L := L) hs hs₁ hq =
      (WeightedCoeff.hilbertSobolevInclusion s q hs.le
        (intervalFourierLebesgue_threshold hs.le hs₁ hq).1.le
        (intervalFourierLebesgue_threshold hs.le hs₁ hq).2).comp (weightedEquiv hs hs₁).toContinuousLinearMap := by
  ext f n
  simp only [fourierEmbedding_apply, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    WeightedCoeff.hilbertSobolevInclusion_apply, weightedEquiv_apply]

end NLS.Fourier.IntrinsicIntervalSobolev
