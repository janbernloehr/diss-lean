import NLS.SequenceSpaces.WeightedRealTruncation

/-! # Physical unit-speed action reduction in native weighted real coordinates

The selected mode is the actual raw coefficient projection. Its radial
rescaling lowers the unweighted physical action at unit speed and commutes
with forgetting the weight. The derivative retains the native weighted norm.
-/
noncomputable section
set_option autoImplicit false
open Set
open scoped ENNReal
namespace NLS.WeightedRealCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The native real cutoff as a bounded real linear operator. -/
def truncateCLM (w : Weight) (S : Finset ℤ) : WeightedRealCoeff w p →L[ℝ] WeightedRealCoeff w p :=
  (WeightedCoeff.reCLM w p).comp
    ((((WeightedCoeff.weightIsometry w p).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((Coeff.truncateCLM S).comp
        (WeightedCoeff.weightIsometry w p).toContinuousLinearEquiv.toContinuousLinearMap)).restrictScalars ℝ).comp
      (WeightedRealCoeff.complexCLM w p))

@[simp] theorem truncateCLM_apply (w : Weight) (S : Finset ℤ) (a : WeightedRealCoeff w p) :
    truncateCLM w S a = truncate w S a := rfl

/-- The pair cutoff is bounded linear in the actual native pair norm. -/
def truncatePairCLM (w : Weight) (S : Finset ℤ) :
    WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p) →L[ℝ]
      WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p) :=
  (WithLp.prodContinuousLinearEquiv p ℝ _ _).symm.toContinuousLinearMap.comp
    (((truncateCLM w S).prodMap (truncateCLM w S)).comp
      (WithLp.prodContinuousLinearEquiv p ℝ _ _).toContinuousLinearMap)

@[simp] theorem truncatePairCLM_apply (w : Weight) (S : Finset ℤ)
    (z : WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p)) :
    truncatePairCLM w S z = truncatePair w S z := rfl

/-- The selected native raw mode as a bounded real linear projection. -/
def pairModeCLM (w : Weight) (n : ℤ) :
    WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p) →L[ℝ]
      WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p) :=
  truncatePairCLM w {n}

/-- Forgetting the weight gives exactly the original selected mode. -/
theorem forget_pairModeCLM (w : Weight) (hw : ∀ n, 1 ≤ w n)
    (z : WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p)) (n : ℤ) :
    forgetPairWeightCLM w hw (pairModeCLM w n z) = RealCoeff.pairMode (forgetPairWeightCLM w hw z) n := by
  rw [pairModeCLM,truncatePairCLM_apply,forget_truncatePair]
  simp [RealCoeff.truncatePair,RealCoeff.truncate,RealCoeff.pairMode]

/-- Reduce the actual unweighted selected action using its native raw mode. -/
def actionReduction (w : Weight) (hw : ∀ n, 1 ≤ w n)
    (z : WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p)) (n : ℤ) (t : ℝ) :
    WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p) :=
  z+(RealCoeff.actionReductionScale (RealCoeff.pairAction (forgetPairWeightCLM w hw z) n) t-1) • pairModeCLM w n z

@[simp] theorem actionReduction_zero (w : Weight) (hw : ∀ n, 1 ≤ w n)
    (z : WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p)) (n : ℤ) :
    actionReduction w hw z n 0 = z := by
  simp [actionReduction,RealCoeff.actionReductionScale]

/-- The full weighted curve preserves every raw unweighted coordinate. -/
theorem forget_actionReduction (w : Weight) (hw : ∀ n, 1 ≤ w n)
    (z : WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p)) (n : ℤ) (t : ℝ) :
    forgetPairWeightCLM w hw (actionReduction w hw z n t) =
      RealCoeff.actionReduction (forgetPairWeightCLM w hw z) n t := by
  simp only [actionReduction,map_add,map_smul,forget_pairModeCLM,RealCoeff.actionReduction]

/-- Its derivative is computed in the full native norm, including the
standard total-division convention when the initial action vanishes. -/
theorem hasDerivAt_actionReduction_zero (w : Weight) (hw : ∀ n, 1 ≤ w n)
    (z : WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p)) (n : ℤ) :
    HasDerivAt (actionReduction w hw z n)
      ((-1/(2*RealCoeff.pairAction (forgetPairWeightCLM w hw z) n)) • pairModeCLM w n z) 0 := by
  let a := RealCoeff.pairAction (forgetPairWeightCLM w hw z) n
  have hs := (((hasDerivAt_id (0:ℝ)).div_const a).const_sub 1).sqrt (by norm_num)
  have hd := ((hs.sub_const 1).smul_const (pairModeCLM w n z)).const_add z
  convert! hd using 1
  norm_num only [id_eq,zero_div,sub_zero,Real.sqrt_one,mul_one]
  dsimp only [a]
  congr 1
  simp only [div_eq_mul_inv,mul_inv_rev,neg_mul,one_mul]

/-- The selected raw action decreases at exactly unit speed before collapse. -/
theorem pairAction_actionReduction_same (w : Weight) (hw : ∀ n, 1 ≤ w n)
    (z : WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p)) (n : ℤ)
    (ha : 0 < RealCoeff.pairAction (forgetPairWeightCLM w hw z) n) (t : ℝ)
    (ht : t ≤ RealCoeff.pairAction (forgetPairWeightCLM w hw z) n) :
    RealCoeff.pairAction (forgetPairWeightCLM w hw (actionReduction w hw z n t)) n =
      RealCoeff.pairAction (forgetPairWeightCLM w hw z) n-t := by
  rw [forget_actionReduction,RealCoeff.pairAction_actionReduction_same _ n ha t ht]

/-- Every other raw action is unchanged. -/
theorem pairAction_actionReduction_ne (w : Weight) (hw : ∀ n, 1 ≤ w n)
    (z : WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p)) (n k : ℤ) (hkn : k ≠ n) (t : ℝ) :
    RealCoeff.pairAction (forgetPairWeightCLM w hw (actionReduction w hw z n t)) k =
      RealCoeff.pairAction (forgetPairWeightCLM w hw z) k := by
  rw [forget_actionReduction,RealCoeff.pairAction_actionReduction_ne _ n k hkn t]

end NLS.WeightedRealCoeff
