import NLS.ZakharovShabat.WeightedSquareEstimate

/-!
# Forgetting the spectral weight in the complementary equation

The inclusion preserves physical Fourier coefficients and the actual operator
`T_n`. Unit spectral weights give the source's unweighted finite-exponent pair
norm; its signed shifts are isometries.
-/

noncomputable section
open scoped ENNReal
namespace NLS.SpectralWeight
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Forget a spectral weight without changing scalar Fourier coefficients. -/
def forgetWeight (w : SpectralWeight) :
    WeightedCoeff w.toWeight p →L[ℂ] WeightedCoeff one.toWeight p :=
  WeightedCoeff.inclusionCLM w.toWeight one.toWeight w.one_le

@[simp] theorem forgetWeight_apply (w : SpectralWeight) (f : WeightedCoeff w.toWeight p) (k : ℤ) :
    (w.forgetWeight f).val k = f.val k := WeightedCoeff.inclusionCLM_apply _ _ _ _ _

theorem norm_forgetWeight_le (w : SpectralWeight) (f : WeightedCoeff w.toWeight p) :
    ‖w.forgetWeight f‖ ≤ ‖f‖ := WeightedCoeff.norm_inclusionCLM_le _ _ _ _

/-- Forget a spectral weight on the exact source pair space. -/
def forgetPairWeight (w : SpectralWeight) :
    WeightedCoeffPair w.toWeight p →L[ℂ] WeightedCoeffPair one.toWeight p :=
  WeightedCoeffPair.mapComponents _ _ w.forgetWeight w.forgetWeight

@[simp] theorem forgetPairWeight_fst (w : SpectralWeight) (f : WeightedCoeffPair w.toWeight p) :
    (w.forgetPairWeight f).fst = w.forgetWeight f.fst := rfl
@[simp] theorem forgetPairWeight_snd (w : SpectralWeight) (f : WeightedCoeffPair w.toWeight p) :
    (w.forgetPairWeight f).snd = w.forgetWeight f.snd := rfl

theorem norm_forgetPairWeight_le (hp : p ≠ ⊤) (w : SpectralWeight) (f : WeightedCoeffPair w.toWeight p) :
    ‖w.forgetPairWeight f‖ ≤ ‖f‖ := by
  simpa only [one_mul] using! WeightedCoeffPair.norm_mapComponents_le hp _ _
    w.forgetWeight w.forgetWeight zero_le_one
    (fun a => by simpa using w.norm_forgetWeight_le a)
    (fun a => by simpa using w.norm_forgetWeight_le a) f

/-- Unit-weight signed shifts preserve the exact finite-exponent pair norm. -/
@[simp] theorem shiftedPairNorm_one (hp : p ≠ ⊤) (i : ℤ) (f : WeightedCoeffPair one.toWeight p) :
    one.shiftedPairNorm i f = ‖f‖ := by
  apply le_antisymm
  · simpa only [one_apply, one_mul] using one.shiftedPairNorm_le hp i f
  · simpa only [one_apply, one_mul] using one.norm_le_shiftedPairNorm hp i f

end NLS.SpectralWeight
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Taking the weighted remainder commutes with forgetting the weight. -/
theorem forgetPairWeight_fourierTail (w : SpectralWeight) (N : ℕ) (f : WeightedCoeffPair w.toWeight p) :
    w.forgetPairWeight (weightedPairFourierTail w.toWeight N f) =
      weightedPairFourierTail SpectralWeight.one.toWeight N (w.forgetPairWeight f) := by
  apply weightedPair_ext <;> intro k <;>
    simp only [SpectralWeight.forgetPairWeight_fst, SpectralWeight.forgetPairWeight_snd,
      weightedPairFourierTail_fst, weightedPairFourierTail_snd, SpectralWeight.forgetWeight_apply,
      WeightedCoeff.fourierTail_apply]

/-- The weighted and unweighted `T_n` are the same Fourier operator on their common inputs. -/
theorem forgetPairWeight_potentialInverse (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ f : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    w.forgetPairWeight (weightedPotentialInverse hp w φ n z hz f) =
      weightedPotentialInverse hp SpectralWeight.one (w.forgetPairWeight φ) n z hz (w.forgetPairWeight f) := by
  apply weightedPair_ext <;> intro k <;>
    simp only [SpectralWeight.forgetPairWeight_fst, SpectralWeight.forgetPairWeight_snd,
      SpectralWeight.forgetWeight_apply, weightedPotentialInverse_fst, weightedPotentialInverse_snd,
      SpectralWeight.convolution_apply, complementaryScalarL1_apply]

/-- The unit-weight specialization of Lemma 6.5 bounds the ordinary unshifted operator square. -/
theorem norm_unweightedPotentialInverse_sq_le (hp : p ≠ ⊤)
    (φ : WeightedCoeffPair SpectralWeight.one.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    ‖(weightedPotentialInverse hp SpectralWeight.one φ n z hz).comp
      (weightedPotentialInverse hp SpectralWeight.one φ n z hz)‖ ≤
      weightedSquareBound hp SpectralWeight.one φ n := by
  apply ContinuousLinearMap.opNorm_le_bound _ (weightedSquareBound_nonneg hp _ _ _)
  intro f
  simpa only [SpectralWeight.shiftedPairNorm_one hp, ContinuousLinearMap.comp_apply] using
    shiftedPairNorm_weightedPotentialInverse_sq_refined hp SpectralWeight.one φ n z hz f

end NLS.ZakharovShabat
