import NLS.SequenceSpaces.PositiveWeightedCoefficients

/-! # Normalized weight equivalences on positive-frequency Banach spaces

Weighting and unweighting give bounded linear equivalences between the
closed positive-index spaces. Raw coefficients record the literal ratio
of the two weights, while the transported sequence norms are preserved.
-/
noncomputable section
open scoped ENNReal
namespace NLS.WeightedCoeff
variable (w v : Weight) (p : ℝ≥0∞) [Fact (1 ≤ p)]

def positiveWeightMap : positiveSubmodule w p →L[ℂ] positiveSubmodule v p :=
  (((weightIsometry v p).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (weightIsometry w p).toContinuousLinearEquiv.toContinuousLinearMap).comp
      (positiveSubmodule w p).subtypeL).codRestrict (positiveSubmodule v p) (by
    intro a n hn
    change ((w n : ℂ)*a.val.val n)/(v n : ℂ) = 0
    rw [a.property n hn,mul_zero,zero_div])

@[simp] theorem positiveWeightMap_apply (a : positiveSubmodule w p) (n : ℤ) :
    (positiveWeightMap w v p a).val.val n = ((w n : ℂ)*a.val.val n)/(v n : ℂ) := rfl

theorem positiveWeightMap_inverse (a : positiveSubmodule w p) :
    positiveWeightMap v w p (positiveWeightMap w v p a) = a := by
  apply Subtype.ext
  apply Subtype.ext
  funext n
  rw [positiveWeightMap_apply,positiveWeightMap_apply]
  field_simp [w.complex_ne_zero n,v.complex_ne_zero n]

def positiveWeightEquiv : positiveSubmodule w p ≃L[ℂ] positiveSubmodule v p where
  toLinearEquiv :=
    { toLinearMap := (positiveWeightMap w v p).toLinearMap
      invFun := positiveWeightMap v w p
      left_inv := positiveWeightMap_inverse w v p
      right_inv := positiveWeightMap_inverse v w p }
  continuous_toFun := (positiveWeightMap w v p).continuous
  continuous_invFun := (positiveWeightMap v w p).continuous

@[simp] theorem positiveWeightEquiv_apply (a : positiveSubmodule w p) (n : ℤ) :
    (positiveWeightEquiv w v p a).val.val n = ((w n : ℂ)*a.val.val n)/(v n : ℂ) := rfl

@[simp] theorem positiveWeightEquiv_symm_apply (a : positiveSubmodule v p) (n : ℤ) :
    ((positiveWeightEquiv w v p).symm a).val.val n = ((v n : ℂ)*a.val.val n)/(w n : ℂ) := rfl

end NLS.WeightedCoeff
