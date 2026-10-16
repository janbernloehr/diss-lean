import NLS.ZakharovShabat.SourceBirkhoffWeightedMap

/-! # The original Birkhoff map between weighted real spaces

Both input and output retain the original unweighted coefficient values.
Positive coordinate weighting proves membership and injectivity without changing
the map. The target norm is exactly the weighted component-sum lp norm.
-/
noncomputable section
namespace NLS.ZakharovShabat
open scoped ENNReal
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- The original real Birkhoff map on the original weighted source and target spaces. -/
def originalWeightedRealMap (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (w : SpectralWeight) (a : weightedRealSourceSubmodule (p := p) w) :
    WithLp p (WeightedRealCoeff (sourceFrequencyWeight w) p × WeightedRealCoeff (sourceFrequencyWeight w) p) :=
  WithLp.toLp p
    ((WeightedRealCoeff.weightEquiv (sourceFrequencyWeight w) p).symm
      (D.weightedRealMap w (weightedRealSourceEquiv w a)).fst,
     (WeightedRealCoeff.weightEquiv (sourceFrequencyWeight w) p).symm
      (D.weightedRealMap w (weightedRealSourceEquiv w a)).snd)

@[simp] theorem originalWeightedRealMap_fst (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (w : SpectralWeight) (a : weightedRealSourceSubmodule (p := p) w) (n : ℤ) :
    (D.originalWeightedRealMap w a).fst.val.val n =
      ((sourceRealBirkhoffMap hp hp1 s (originalWeightedRealSource w a)).1 n : ℂ) := by
  change ((D.weightedRealMap w (weightedRealSourceEquiv w a)).fst n : ℂ) / (w (2*n) : ℂ) = _
  rw [weightedRealMap_fst, Complex.ofReal_mul, mul_div_cancel_left₀ _ (w.toWeight.complex_ne_zero _)]
  rfl

@[simp] theorem originalWeightedRealMap_snd (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (w : SpectralWeight) (a : weightedRealSourceSubmodule (p := p) w) (n : ℤ) :
    (D.originalWeightedRealMap w a).snd.val.val n =
      ((sourceRealBirkhoffMap hp hp1 s (originalWeightedRealSource w a)).2 n : ℂ) := by
  change ((D.weightedRealMap w (weightedRealSourceEquiv w a)).snd n : ℂ) / (w (2*n) : ℂ) = _
  rw [weightedRealMap_snd, Complex.ofReal_mul, mul_div_cancel_left₀ _ (w.toWeight.complex_ne_zero _)]
  rfl

/-- The map is injective on the full original weighted real source space. -/
theorem originalWeightedRealMap_injective (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (w : SpectralWeight) : Function.Injective (D.originalWeightedRealMap w) := by
  intro a b hab
  apply (weightedRealSourceEquiv w).injective
  apply D.weightedRealMap_injective w
  apply (WithLp.equiv p _).injective
  apply Prod.ext
  · apply (WeightedRealCoeff.weightEquiv (sourceFrequencyWeight w) p).symm.injective
    exact congrArg (fun z => z.fst) hab
  · apply (WeightedRealCoeff.weightEquiv (sourceFrequencyWeight w) p).symm.injective
    exact congrArg (fun z => z.snd) hab

/-- Exact p-th norm power in the original weighted target pair norm. -/
theorem originalWeightedRealMap_norm_rpow (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (w : SpectralWeight) (a : weightedRealSourceSubmodule (p := p) w) :
    ‖D.originalWeightedRealMap w a‖ ^ p.toReal = ∑' n : ℤ,
      (|w (2*n) * (sourceRealBirkhoffMap hp hp1 s (originalWeightedRealSource w a)).1 n| ^ p.toReal +
       |w (2*n) * (sourceRealBirkhoffMap hp hp1 s (originalWeightedRealSource w a)).2 n| ^ p.toReal) := by
  calc
    _ = ‖D.weightedRealMap w (weightedRealSourceEquiv w a)‖ ^ p.toReal := by
      rw [norm_withLp_prod_rpow hp, norm_withLp_prod_rpow hp]
      change ‖(WeightedRealCoeff.weightEquiv (sourceFrequencyWeight w) p).symm
          (D.weightedRealMap w (weightedRealSourceEquiv w a)).fst‖ ^ p.toReal +
        ‖(WeightedRealCoeff.weightEquiv (sourceFrequencyWeight w) p).symm
          (D.weightedRealMap w (weightedRealSourceEquiv w a)).snd‖ ^ p.toReal = _
      rw [weightedRealCoeff_inverse_norm, weightedRealCoeff_inverse_norm]
    _ = _ := D.weightedRealMap_norm_rpow w (weightedRealSourceEquiv w a)


end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
