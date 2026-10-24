import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Interval estimates imply domination of real measures -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal NNReal
namespace NLS.FunctionalAnalysis

/-- Domination on half-open intervals extends to the actual Stieltjes measure. -/
theorem measure_le_stieltjes_of_Ioc (μ : Measure ℝ) (f : StieltjesFunction ℝ)
    (h : ∀ a b : ℝ, μ (Ioc a b) ≤ ENNReal.ofReal (f b-f a)) : μ ≤ f.measure := by
  rw [← Measure.toOuterMeasure_le,StieltjesFunction.measure]
  change μ.toOuterMeasure ≤ OuterMeasure.ofFunction f.length f.length_empty
  apply OuterMeasure.le_ofFunction.mpr
  intro s
  rw [StieltjesFunction.length_eq]
  refine le_iInf (fun a => le_iInf (fun b => le_iInf (fun hs => ?_)))
  have hsub : s ⊆ Ioc a b := by
    intro x hx
    exact hs ⟨hx,not_isBot x⟩
  exact (measure_mono hsub).trans (h a b)

/-- Length bounds on half-open intervals imply domination by Lebesgue measure. -/
theorem measure_le_smul_volume_of_Ioc (μ : Measure ℝ) (C : ℝ≥0)
    (h : ∀ a b : ℝ, μ (Ioc a b) ≤ (C : ℝ≥0∞)*ENNReal.ofReal (b-a)) :
    μ ≤ C • (volume : Measure ℝ) := by
  have hle : μ ≤ (C • StieltjesFunction.id).measure := by
    apply measure_le_stieltjes_of_Ioc
    intro a b
    change μ (Ioc a b) ≤ ENNReal.ofReal ((C : ℝ)*b-(C : ℝ)*a)
    rw [← mul_sub,ENNReal.ofReal_mul C.coe_nonneg,ENNReal.ofReal_coe_nnreal]
    exact h a b
  rwa [StieltjesFunction.measure_smul,← Real.volume_eq_stieltjes_id] at hle

/-- For finite measures it suffices to bound the real mass of nontrivial closed intervals. -/
theorem measure_le_smul_volume_of_real_Icc (μ : Measure ℝ) [IsFiniteMeasure μ] (C : ℝ≥0)
    (h : ∀ a b : ℝ, a < b → μ.real (Icc a b) ≤ (C : ℝ)*(b-a)) :
    μ ≤ C • (volume : Measure ℝ) := by
  apply measure_le_smul_volume_of_Ioc
  intro a b
  by_cases hab : a < b
  · calc
      μ (Ioc a b) ≤ μ (Icc a b) := measure_mono Ioc_subset_Icc_self
      _ = ENNReal.ofReal (μ.real (Icc a b)) := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal ((C : ℝ)*(b-a)) := ENNReal.ofReal_le_ofReal (h a b hab)
      _ = (C : ℝ≥0∞)*ENNReal.ofReal (b-a) := by
        rw [ENNReal.ofReal_mul C.coe_nonneg,ENNReal.ofReal_coe_nnreal]
  · simp [Ioc_eq_empty_of_le (le_of_not_gt hab)]

end NLS.FunctionalAnalysis
