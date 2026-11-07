import NLS.SequenceSpaces.WeightedHilbertProduct
import NLS.SequenceSpaces.WeightedMultiplier
import NLS.SequenceSpaces.SignedSobolevWeight

/-! A weighted infinity symbol multiplies a weighted Hilbert sequence
analytically. A comparison with the product weight specifies the exact
stronger target, without changing any raw coefficient. -/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.WeightedCoeff

private theorem product_weight_comparison (u v w : Weight) (hw : ∀ k, w k ≤ u k * v k) :
    ∀ k, w k ≤ (u.product v) k := hw

def weightedInfinityPointwiseProduct (u v w : Weight) (hw : ∀ k, w k ≤ u k * v k)
    (b : WeightedCoeff u ⊤) (a : WeightedCoeff v 2) : WeightedCoeff w 2 :=
  inclusionCLM (u.product v) w (product_weight_comparison u v w hw)
    ((weightIsometry (u.product v) 2).symm
      (Coeff.holderProduct (p := ⊤) (r := 2) (q := 2)
        (weightIsometry u ⊤ b) (weightIsometry v 2 a)))

theorem weightedInfinityPointwiseProduct_apply (u v w : Weight) (hw : ∀ k, w k ≤ u k * v k)
    (b : WeightedCoeff u ⊤) (a : WeightedCoeff v 2) (k : ℤ) :
    (weightedInfinityPointwiseProduct u v w hw b a).val k = b.val k * a.val k := by
  rw [weightedInfinityPointwiseProduct,inclusionCLM_apply]
  change ((u k : ℂ) * b.val k * ((v k : ℂ) * a.val k)) / ((u k * v k : ℝ) : ℂ) = _
  push_cast
  field_simp [u.complex_ne_zero k,v.complex_ne_zero k]

theorem analyticAt_weightedInfinityPointwiseProduct (u v w : Weight) (hw : ∀ k, w k ≤ u k * v k)
    (z : WeightedCoeff u ⊤ × WeightedCoeff v 2) :
    AnalyticAt ℂ (fun y => weightedInfinityPointwiseProduct u v w hw y.1 y.2) z := by
  have hb : AnalyticAt ℂ (fun y : WeightedCoeff u ⊤ × WeightedCoeff v 2 => weightIsometry u ⊤ y.1) z :=
    ((weightIsometry u ⊤).toContinuousLinearEquiv.toContinuousLinearMap.analyticAt _).comp
    (f := Prod.fst) analyticAt_fst
  have ha : AnalyticAt ℂ (fun y : WeightedCoeff u ⊤ × WeightedCoeff v 2 => weightIsometry v 2 y.2) z :=
    ((weightIsometry v 2).toContinuousLinearEquiv.toContinuousLinearMap.analyticAt _).comp
    (f := Prod.snd) analyticAt_snd
  exact ((inclusionCLM (u.product v) w (product_weight_comparison u v w hw) (p := 2)).analyticAt _).comp
    (((weightIsometry (u.product v) 2).symm.toContinuousLinearEquiv.toContinuousLinearMap.analyticAt _).comp
      (((Coeff.holderProduct (p := ⊤) (r := 2) (q := 2)).analyticAt_bilinear _).comp₂ hb ha))

private theorem signed_order_product_bound (s t : ℝ) (ht : t = s + 1) (k : ℤ) :
    Weight.signedSobolev t k ≤ Weight.sobolev 1 k * Weight.signedSobolev s k := by
  have hb : 0 < max 1 |(k : ℝ)| := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  rw [ht]
  change (max 1 |(k : ℝ)|)^(s+1) ≤ _
  rw [Real.rpow_add hb,Real.rpow_one]
  change (max 1 |(k : ℝ)|)^s * max 1 |(k : ℝ)| ≤ (1+|(k : ℝ)|)^1 * (max 1 |(k : ℝ)|)^s
  rw [Real.rpow_one,mul_comm]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_pos_of_pos hb s).le
  exact max_le (by linarith [abs_nonneg (k : ℝ)]) (by linarith)

def signedSobolevInfinityProduct (s t : ℝ) (ht : t = s + 1)
    (b : WeightedCoeff (Weight.sobolev 1) ⊤) (a : WeightedCoeff (Weight.signedSobolev s) 2) :
    WeightedCoeff (Weight.signedSobolev t) 2 :=
  weightedInfinityPointwiseProduct _ _ _ (signed_order_product_bound s t ht) b a

theorem signedSobolevInfinityProduct_apply (s t : ℝ) (ht : t = s + 1)
    (b : WeightedCoeff (Weight.sobolev 1) ⊤) (a : WeightedCoeff (Weight.signedSobolev s) 2) (k : ℤ) :
    (signedSobolevInfinityProduct s t ht b a).val k = b.val k * a.val k :=
  weightedInfinityPointwiseProduct_apply _ _ _ _ b a k

theorem analyticAt_signedSobolevInfinityProduct (s t : ℝ) (ht : t = s + 1)
    (z : WeightedCoeff (Weight.sobolev 1) ⊤ × WeightedCoeff (Weight.signedSobolev s) 2) :
    AnalyticAt ℂ (fun y => signedSobolevInfinityProduct s t ht y.1 y.2) z :=
  analyticAt_weightedInfinityPointwiseProduct _ _ _ _ z

end NLS.WeightedCoeff
