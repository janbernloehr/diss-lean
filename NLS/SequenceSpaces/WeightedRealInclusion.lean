import NLS.SequenceSpaces.WeightedRealCoeff
import NLS.SequenceSpaces.WeightedMultiplier
import NLS.SequenceSpaces.PairNorm

/-! # Forgetting a bounded-below weight on real coefficients

The continuous real inclusion preserves every raw coefficient and is
injective. Pair inclusions use the actual lp source topology and the
maximum-norm unweighted target used by the original Birkhoff map.
-/
noncomputable section
open scoped ENNReal
namespace NLS.WeightedRealCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A weight bounded below by one can be forgotten continuously. -/
def forgetWeightCLM (w : Weight) (hw : ∀ n, 1 ≤ w n) :
    WeightedRealCoeff w p →L[ℝ] RealCoeff p :=
  (Coeff.reCLM p).comp
    ((((WeightedCoeff.weightIsometry Weight.one p).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (WeightedCoeff.inclusionCLM w Weight.one hw)).restrictScalars ℝ).comp (complexCLM w p))

@[simp] theorem forgetWeightCLM_apply (w : Weight) (hw : ∀ n, 1 ≤ w n)
    (a : WeightedRealCoeff w p) (n : ℤ) : forgetWeightCLM w hw a n = (a.val.val n).re := by
  change ((Weight.one n:ℂ)*(WeightedCoeff.inclusionCLM w Weight.one hw a.val).val n).re = _
  rw [Weight.one_apply,Complex.ofReal_one,one_mul]
  exact congrArg Complex.re (WeightedCoeff.inclusionCLM_apply w Weight.one hw a.val n)

/-- Forgetting the weight preserves the actual complex coefficient, which is real. -/
@[simp] theorem coe_forgetWeightCLM_apply (w : Weight) (hw : ∀ n, 1 ≤ w n)
    (a : WeightedRealCoeff w p) (n : ℤ) : (forgetWeightCLM w hw a n:ℂ) = a.val.val n := by
  rw [forgetWeightCLM_apply]
  apply Complex.ext
  · rfl
  · simpa using (im_eq_zero w p a n).symm

theorem forgetWeightCLM_injective (w : Weight) (hw : ∀ n, 1 ≤ w n) :
    Function.Injective (forgetWeightCLM (p := p) w hw) := by
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  funext n
  have he := congrArg (fun c : RealCoeff p => (c n:ℂ)) h
  simpa only [coe_forgetWeightCLM_apply] using he

/-- The raw unweighted image retains the original weighted membership. -/
theorem mem_weighted_forgetWeightCLM (w : Weight) (hw : ∀ n, 1 ≤ w n)
    (a : WeightedRealCoeff w p) : Memℓp (fun n : ℤ => w n*forgetWeightCLM w hw a n) p := by
  have h := (weightEquiv w p a).property
  change Memℓp (fun n : ℤ => ((w n:ℂ)*a.val.val n).re) p at h
  simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    forgetWeightCLM_apply] using h

/-- Pair inclusion into the unweighted real target, preserving raw coefficients. -/
def forgetPairWeightCLM (w : Weight) (hw : ∀ n, 1 ≤ w n) :
    WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p) →L[ℝ] (RealCoeff p × RealCoeff p) :=
  ((forgetWeightCLM w hw).prodMap (forgetWeightCLM w hw)).comp
    (WithLp.prodContinuousLinearEquiv p ℝ _ _).toContinuousLinearMap

@[simp] theorem forgetPairWeightCLM_fst (w : Weight) (hw : ∀ n, 1 ≤ w n)
    (a : WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p)) :
    (forgetPairWeightCLM w hw a).1 = forgetWeightCLM w hw a.fst := rfl

@[simp] theorem forgetPairWeightCLM_snd (w : Weight) (hw : ∀ n, 1 ≤ w n)
    (a : WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p)) :
    (forgetPairWeightCLM w hw a).2 = forgetWeightCLM w hw a.snd := rfl

theorem forgetPairWeightCLM_injective (w : Weight) (hw : ∀ n, 1 ≤ w n) :
    Function.Injective (forgetPairWeightCLM (p := p) w hw) := by
  intro a b h
  apply (WithLp.equiv p _).injective
  exact Prod.ext (forgetWeightCLM_injective w hw (congrArg Prod.fst h))
    (forgetWeightCLM_injective w hw (congrArg Prod.snd h))

end NLS.WeightedRealCoeff
