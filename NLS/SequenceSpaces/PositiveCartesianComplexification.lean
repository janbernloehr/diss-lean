import NLS.SequenceSpaces.SignedSobolevWeight
import NLS.SequenceSpaces.SymmetricWeightedReflection
import NLS.SequenceSpaces.PairNorm

/-! A bounded complex linear map takes positive Cartesian sequences to
signed complex coordinates: z_n=(x_n-i*y_n)/sqrt2, z_-n=(x_n+i*y_n)/sqrt2.
The zero mode is removed, and the literal signed weight is retained. -/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS.WeightedCoeffPair
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def signedCartesianCLM (s : ℝ) :
    WeightedCoeffPair (Weight.positiveSobolev s) p →L[ℂ] WeightedCoeff (Weight.signedSobolev s) p :=
  let U := WeightedCoeff.positiveToSignedCLM (p := p) s
  let X := U.comp ((ContinuousLinearMap.fst ℂ _ _).comp (toMax (Weight.positiveSobolev s) p).toContinuousLinearMap)
  let Y := U.comp ((ContinuousLinearMap.snd ℂ _ _).comp (toMax (Weight.positiveSobolev s) p).toContinuousLinearMap)
  let R := (WeightedCoeff.symmetricReflection (Weight.signedSobolev s) (Weight.signedSobolev_neg s)).toContinuousLinearEquiv.toContinuousLinearMap
  (1/(Real.sqrt 2:ℂ)) • ((X-I • Y)+R.comp (X+I • Y))

theorem signedCartesianCLM_apply (s : ℝ) (a : WeightedCoeffPair (Weight.positiveSobolev s) p) (k : ℤ) :
    (signedCartesianCLM s a).val k =
      ((if 0 < k then a.fst.val k-I*a.snd.val k else 0)+
        (if 0 < -k then a.fst.val (-k)+I*a.snd.val (-k) else 0))/(Real.sqrt 2:ℂ) := by
  change ((1/(Real.sqrt 2:ℂ)) •
    ((WeightedCoeff.positiveToSignedCLM s a.fst-I • WeightedCoeff.positiveToSignedCLM s a.snd)+
      WeightedCoeff.symmetricReflection (Weight.signedSobolev s) (Weight.signedSobolev_neg s)
        (WeightedCoeff.positiveToSignedCLM s a.fst+I • WeightedCoeff.positiveToSignedCLM s a.snd))).val k = _
  simp only [WeightedCoeff.smul_val,WeightedCoeff.add_val,WeightedCoeff.sub_val,
    WeightedCoeff.symmetricReflection_apply,WeightedCoeff.positiveToSignedCLM_apply]
  split_ifs <;> ring

theorem signedCartesianCLM_positive (s : ℝ) (a : WeightedCoeffPair (Weight.positiveSobolev s) p)
    (k : ℤ) (hk : 0 < k) :
    (signedCartesianCLM s a).val k=(a.fst.val k-I*a.snd.val k)/(Real.sqrt 2:ℂ) := by
  rw [signedCartesianCLM_apply,if_pos hk,if_neg (by omega : ¬0 < -k),add_zero]

theorem signedCartesianCLM_negative (s : ℝ) (a : WeightedCoeffPair (Weight.positiveSobolev s) p)
    (k : ℤ) (hk : 0 < k) :
    (signedCartesianCLM s a).val (-k)=(a.fst.val k+I*a.snd.val k)/(Real.sqrt 2:ℂ) := by
  rw [signedCartesianCLM_apply,neg_neg,if_neg (by omega : ¬0 < -k),if_pos hk,zero_add]

theorem signedCartesianCLM_zero (s : ℝ) (a : WeightedCoeffPair (Weight.positiveSobolev s) p) :
    (signedCartesianCLM s a).val 0=0 := by
  simp only [signedCartesianCLM_apply,neg_zero,lt_self_iff_false,ite_false,add_zero,zero_div]

end NLS.WeightedCoeffPair
