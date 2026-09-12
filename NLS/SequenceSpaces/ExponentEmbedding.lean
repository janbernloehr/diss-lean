import NLS.SequenceSpaces.SobolevDerivative

/-!
# Contractive embeddings into larger sequence exponents

Increasing the Banach exponent decreases the counting-measure sequence norm.
The weighted embedding preserves raw coefficients and composes with decreasing
Sobolev regularity, including the infinity target.
-/

noncomputable section
open scoped ENNReal
namespace NLS
namespace Coeff
variable {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

private theorem norm_exponentMap_le_one (h : p ≤ q) (a : Coeff p) (ha : ‖a‖ ≤ 1) :
    ‖lp.linearMapOfLE ℂ (fun _ : ℤ => ℂ) h a‖ ≤ 1 := by
  by_cases hq : q = ⊤
  · subst q
    apply lp.norm_le_of_forall_le zero_le_one
    intro n
    exact (lp.norm_apply_le_norm (ne_of_gt (zero_lt_one.trans_le Fact.out)) a n).trans ha
  · have hp : p ≠ ⊤ := ne_top_of_le_ne_top hq h
    have hpr : 0 < p.toReal := ENNReal.toReal_pos
      (ne_of_gt (zero_lt_one.trans_le Fact.out)) hp
    have hqr : 0 < q.toReal := ENNReal.toReal_pos
      (ne_of_gt (zero_lt_one.trans_le Fact.out)) hq
    apply lp.norm_le_of_forall_sum_le hqr zero_le_one
    intro S
    calc
      ∑ n ∈ S, ‖lp.linearMapOfLE ℂ (fun _ : ℤ => ℂ) h a n‖ ^ q.toReal
          ≤ ∑ n ∈ S, ‖a n‖ ^ p.toReal := by
        apply Finset.sum_le_sum
        intro n _
        exact Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg _)
          ((lp.norm_apply_le_norm (ne_of_gt (zero_lt_one.trans_le Fact.out)) a n).trans ha)
          hpr.le ((ENNReal.toReal_le_toReal hp hq).mpr h)
      _ ≤ ‖a‖ ^ p.toReal := lp.sum_rpow_le_norm_rpow hpr a S
      _ ≤ 1 ^ q.toReal := by
        rw [Real.one_rpow]
        exact Real.rpow_le_one (norm_nonneg _) ha hpr.le

/-- Increasing the sequence exponent is contractive, including the infinity endpoint. -/
theorem norm_exponentMap_le (h : p ≤ q) (a : Coeff p) :
    ‖lp.linearMapOfLE ℂ (fun _ : ℤ => ℂ) h a‖ ≤ ‖a‖ := by
  by_cases ha : a = 0
  · subst a
    simp
  · have hpos : 0 < ‖a‖ := norm_pos_iff.mpr ha
    have hb : ‖(‖a‖⁻¹ : ℂ) • a‖ ≤ 1 := by
      simp [norm_smul, Complex.norm_real, hpos.ne']
    have h := norm_exponentMap_le_one h ((‖a‖⁻¹ : ℂ) • a) hb
    rw [map_smul, norm_smul] at h
    simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos] at h
    have hh := mul_le_mul_of_nonneg_left h hpos.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul, mul_one] using hh

/-- The continuous identity map from a smaller to a larger Banach sequence exponent. -/
def exponentInclusion (h : p ≤ q) : Coeff p →L[ℂ] Coeff q :=
  (lp.linearMapOfLE ℂ (fun _ : ℤ => ℂ) h).mkContinuous 1
    (by intro a; simpa only [one_mul] using norm_exponentMap_le h a)

@[simp] theorem exponentInclusion_apply (h : p ≤ q) (a : Coeff p) (n : ℤ) :
    exponentInclusion h a n = a n := rfl

theorem norm_exponentInclusion_le (h : p ≤ q) (a : Coeff p) :
    ‖exponentInclusion h a‖ ≤ ‖a‖ := norm_exponentMap_le h a

theorem exponentInclusion_injective (h : p ≤ q) :
    Function.Injective (exponentInclusion h) := by
  intro a b hab
  ext n
  exact congrArg (fun c : Coeff q => c n) hab

@[simp] theorem exponentInclusion_trans [Fact (1 ≤ r)] (hpq : p ≤ q) (hqr : q ≤ r)
    (a : Coeff p) : exponentInclusion hqr (exponentInclusion hpq a) =
      exponentInclusion (hpq.trans hqr) a := by ext n; rfl

end Coeff
namespace WeightedCoeff
variable {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- Keep the weight and increase the Banach exponent without changing the raw sequence. -/
def exponentInclusion (w : Weight) (h : p ≤ q) : WeightedCoeff w p →L[ℂ] WeightedCoeff w q :=
  (weightIsometry w q).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((Coeff.exponentInclusion h).comp (weightIsometry w p).toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem exponentInclusion_apply (w : Weight) (h : p ≤ q)
    (a : WeightedCoeff w p) (n : ℤ) : (exponentInclusion w h a).val n = a.val n := by
  change ((w n : ℂ) * a.val n) / (w n : ℂ) = _
  exact mul_div_cancel_left₀ _ (w.complex_ne_zero n)

theorem norm_exponentInclusion_le (w : Weight) (h : p ≤ q) (a : WeightedCoeff w p) :
    ‖exponentInclusion w h a‖ ≤ ‖a‖ := by
  change ‖(weightIsometry w q).symm (Coeff.exponentInclusion h (weightIsometry w p a))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact Coeff.norm_exponentInclusion_le h (weightIsometry w p a)

theorem exponentInclusion_injective (w : Weight) (h : p ≤ q) :
    Function.Injective (exponentInclusion w h) := by
  intro a b hab
  apply Subtype.ext
  funext n
  simpa only [exponentInclusion_apply] using congrArg (fun c => c.val n) hab

@[simp] theorem exponentInclusion_trans [Fact (1 ≤ r)] (w : Weight)
    (hpq : p ≤ q) (hqr : q ≤ r) (a : WeightedCoeff w p) :
    exponentInclusion w hqr (exponentInclusion w hpq a) =
      exponentInclusion w (hpq.trans hqr) a := by
  apply Subtype.ext
  funext n
  simp only [exponentInclusion_apply]

/-- Decreasing Sobolev regularity and increasing exponent gives a contractive embedding. -/
def sobolevExponentInclusion {s t : ℝ} (hst : t ≤ s) (hpq : p ≤ q) :
    WeightedCoeff (Weight.sobolev s) p →L[ℂ] WeightedCoeff (Weight.sobolev t) q :=
  (exponentInclusion _ hpq).comp (sobolevInclusion hst)

@[simp] theorem sobolevExponentInclusion_apply {s t : ℝ} (hst : t ≤ s) (hpq : p ≤ q)
    (a : WeightedCoeff (Weight.sobolev s) p) (n : ℤ) :
    (sobolevExponentInclusion hst hpq a).val n = a.val n := by
  simp only [sobolevExponentInclusion, ContinuousLinearMap.coe_comp, Function.comp_apply,
    exponentInclusion_apply, sobolevInclusion_apply]

theorem norm_sobolevExponentInclusion_le {s t : ℝ} (hst : t ≤ s) (hpq : p ≤ q)
    (a : WeightedCoeff (Weight.sobolev s) p) : ‖sobolevExponentInclusion hst hpq a‖ ≤ ‖a‖ :=
  (norm_exponentInclusion_le _ hpq _).trans (norm_sobolevInclusion_le hst a)

end WeightedCoeff
end NLS
