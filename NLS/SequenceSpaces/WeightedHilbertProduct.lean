import NLS.SequenceSpaces.HolderEmbedding
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! # Products of two weighted Hilbert coefficient sequences

Pointwise multiplication adds the two weights and produces an actual
weighted summable sequence, with its exact coefficients and unit bound.
-/
noncomputable section
set_option autoImplicit false
open Set
open scoped ENNReal
namespace NLS

/-- The pointwise product of two positive weights. -/
def Weight.product (w v : Weight) : Weight :=
  ⟨fun n => w n * v n,fun n => mul_pos (w.positive n) (v.positive n)⟩

@[simp] theorem Weight.product_apply (w v : Weight) (n : ℤ) :
    w.product v n = w n * v n := rfl

namespace WeightedCoeff

/-- The actual pointwise product with the product weight and summable target. -/
def hilbertProduct (w v : Weight) (a : WeightedCoeff w 2) (b : WeightedCoeff v 2) :
    WeightedCoeff (w.product v) 1 :=
  (weightIsometry (w.product v) 1).symm
    (Coeff.holderProduct (q := 1) (weightIsometry w 2 a) (weightIsometry v 2 b))

@[simp] theorem hilbertProduct_apply (w v : Weight)
    (a : WeightedCoeff w 2) (b : WeightedCoeff v 2) (n : ℤ) :
    (hilbertProduct w v a b).val n = a.val n * b.val n := by
  change ((w n : ℂ) * a.val n * ((v n : ℂ) * b.val n)) / ((w n * v n : ℝ) : ℂ) = _
  push_cast
  field_simp [w.complex_ne_zero n,v.complex_ne_zero n]

/-- The weighted Hilbert product has Hölder constant one. -/
theorem norm_hilbertProduct_le (w v : Weight) (a : WeightedCoeff w 2) (b : WeightedCoeff v 2) :
    ‖hilbertProduct w v a b‖ ≤ ‖a‖ * ‖b‖ := by
  unfold hilbertProduct
  rw [LinearIsometryEquiv.norm_map]
  simpa only [LinearIsometryEquiv.norm_map] using
    Coeff.norm_holderProduct_le (q := 1) (weightIsometry w 2 a) (weightIsometry v 2 b)

/-- Multiplication is analytic into the stronger weighted summable target. -/
theorem analyticOnNhd_hilbertProduct (w v : Weight) :
    AnalyticOnNhd ℂ (fun z : WeightedCoeff w 2 × WeightedCoeff v 2 =>
      hilbertProduct w v z.1 z.2) univ := by
  intro z _
  have ha := ((weightIsometry w 2).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (ContinuousLinearMap.fst ℂ (WeightedCoeff w 2) (WeightedCoeff v 2))).analyticAt z
  have hb := ((weightIsometry v 2).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (ContinuousLinearMap.snd ℂ (WeightedCoeff w 2) (WeightedCoeff v 2))).analyticAt z
  exact ((weightIsometry (w.product v) 1).symm.toContinuousLinearEquiv.toContinuousLinearMap.analyticAt _).comp
    (((Coeff.holderProduct (p := 2) (r := 2) (q := 1)).analyticAt_bilinear _).comp₂ ha hb)

/-- The raw product is absolutely summable after multiplying by both weights. -/
theorem summable_norm_hilbertProduct (w v : Weight)
    (a : WeightedCoeff w 2) (b : WeightedCoeff v 2) :
    Summable (fun n : ℤ => w n * v n * ‖a.val n * b.val n‖) := by
  have h := (weightIsometry (w.product v) 1 (hilbertProduct w v a b)).property.norm.summable_of_one
  simpa only [weightIsometry,LinearIsometryEquiv.coe_mk,LinearEquiv.coe_coe,
    weightEquiv_apply,hilbertProduct_apply,norm_mul,Complex.norm_real,
    Real.norm_of_nonneg (le_of_lt ((w.product v).positive _)),Weight.product_apply,
    Real.norm_of_nonneg (w.positive _).le,Real.norm_of_nonneg (v.positive _).le] using h

end WeightedCoeff
end NLS
