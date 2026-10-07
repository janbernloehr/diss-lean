import NLS.SequenceSpaces.ShiftedWeight
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # From coordinate derivatives to the weighted Banach-space derivative

Norm continuity of a curve and its candidate velocity allows the scalar
fundamental theorem to be lifted coefficient by coefficient. The resulting
Bochner integral identity supplies the strong derivative, including endpoints.
-/
noncomputable section
open Set MeasureTheory intervalIntegral
namespace NLS.SpectralWeight

/-- Evaluation of one original weighted coefficient is bounded and linear. -/
def coefficientCLM (w : SpectralWeight) (n : ℤ) : WeightedCoeff w.toWeight 1 →L[ℂ] ℂ :=
  (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 1 n).comp w.toCoeff

@[simp] theorem coefficientCLM_apply (w : SpectralWeight) (n : ℤ) (a : WeightedCoeff w.toWeight 1) :
    w.coefficientCLM n a = a.val n := w.toCoeff_apply a n

/-- The scalar coordinate equations imply the full weighted integral identity. -/
theorem eq_add_integral_of_coordinate_derivatives (w : SpectralWeight)
    (a b : ℝ) (f g : ℝ → WeightedCoeff w.toWeight 1)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hd : ∀ time ∈ Ioo a b, ∀ n : ℤ, HasDerivAt (fun r => (f r).val n) ((g time).val n) time)
    (time : ℝ) (ht : time ∈ Icc a b) : f time = f a + ∫ r in a..time, g r := by
  have hsub : Icc a time ⊆ Icc a b := Icc_subset_Icc_right ht.2
  have hint : IntervalIntegrable g volume a time := (hg.mono hsub).intervalIntegrable_of_Icc ht.1
  apply Subtype.ext
  funext n
  rw [← coefficientCLM_apply,← coefficientCLM_apply,map_add,
    ← (w.coefficientCLM n).intervalIntegral_comp_comm hint]
  have hcont : ContinuousOn (fun r => w.coefficientCLM n (f r)) (Icc a time) :=
    (w.coefficientCLM n).continuous.comp_continuousOn (hf.mono hsub)
  have hgcont : ContinuousOn (fun r => w.coefficientCLM n (g r)) (Icc a time) :=
    (w.coefficientCLM n).continuous.comp_continuousOn (hg.mono hsub)
  have hd' (r : ℝ) (hr : r ∈ Ioo a time) :
      HasDerivAt (fun x => w.coefficientCLM n (f x)) (w.coefficientCLM n (g r)) r := by
    simpa only [coefficientCLM_apply] using hd r ⟨hr.1,hr.2.trans_le ht.2⟩ n
  have he := integral_eq_sub_of_hasDerivAt_of_le ht.1 hcont hd'
    (hgcont.intervalIntegrable_of_Icc ht.1)
  rw [he]
  abel

/-- Continuous coefficient velocities are actual derivatives in the weighted norm. -/
theorem hasDerivWithinAt_of_coordinate_derivatives (w : SpectralWeight)
    (a b : ℝ) (f g : ℝ → WeightedCoeff w.toWeight 1)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hd : ∀ time ∈ Ioo a b, ∀ n : ℤ, HasDerivAt (fun r => (f r).val n) ((g time).val n) time)
    (time : ℝ) (ht : time ∈ Icc a b) : HasDerivWithinAt f (g time) (Icc a b) time := by
  have hint : IntervalIntegrable g volume a time :=
    (hg.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
  let : Fact (time ∈ Icc a b) := ⟨ht⟩
  have hdint := integral_hasDerivWithinAt_right (s := Icc a b) hint
    (hg.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc time) (hg time ht)
  have h := hdint.const_add (f a)
  apply h.congr_of_mem _ ht
  intro r hr
  exact w.eq_add_integral_of_coordinate_derivatives a b f g hf hg hd r hr

end NLS.SpectralWeight
