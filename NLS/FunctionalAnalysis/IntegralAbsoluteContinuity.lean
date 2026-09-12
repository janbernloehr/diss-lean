import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-!
# Absolute continuity of vector-valued primitives

The scalar norm primitive controls the variation of a Banach-valued primitive.
This extends mathlib's real-valued integral result to the complex-valued
functions needed for periodic Sobolev domains.
-/

noncomputable section
open MeasureTheory Set
namespace NLS.FunctionalAnalysis

variable {E : Type*} [NormedAddCommGroup E]

/-- An integrable Banach-valued function has an absolutely continuous primitive. -/
theorem absolutelyContinuousOnInterval_integral [NormedSpace ℝ E] {f : ℝ → E} {a b c : ℝ}
    (hf : IntervalIntegrable f volume a b) (hc : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (fun x => ∫ t in c..x, f t) a b := by
  have hn := hf.norm.absolutelyContinuousOnInterval_intervalIntegral hc
  rw [absolutelyContinuousOnInterval_iff] at hn ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδprop⟩ := hn ε hε
  refine ⟨δ, hδ, fun intervals hi hl => lt_of_le_of_lt ?_ (hδprop intervals hi hl)⟩
  apply Finset.sum_le_sum
  intro i hii
  have hleft := hf.mono_set (uIcc_subset_uIcc hc (hi.1 i hii).1)
  have hright := hf.mono_set (uIcc_subset_uIcc hc (hi.1 i hii).2)
  rw [dist_eq_norm, Real.dist_eq,
    intervalIntegral.integral_interval_sub_left hleft hright,
    intervalIntegral.integral_interval_sub_left hleft.norm hright.norm]
  exact intervalIntegral.norm_integral_le_abs_integral_norm

/-- Absolute continuity depends only on values in the closed interval. -/
theorem absolutelyContinuousOnInterval_congr {f g : ℝ → E} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hfg : EqOn f g (uIcc a b)) :
    AbsolutelyContinuousOnInterval g a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδprop⟩ := hf ε hε
  refine ⟨δ, hδ, fun intervals hi hl => ?_⟩
  have he : (∑ i ∈ Finset.range intervals.1,
      dist (g (intervals.2 i).1) (g (intervals.2 i).2)) =
      ∑ i ∈ Finset.range intervals.1, dist (f (intervals.2 i).1) (f (intervals.2 i).2) := by
    apply Finset.sum_congr rfl
    intro i hii
    rw [hfg (hi.1 i hii).1, hfg (hi.1 i hii).2]
  rw [he]
  exact hδprop intervals hi hl

/-- Adding the integration constant preserves absolute continuity. -/
theorem absolutelyContinuousOnInterval_const_add {f : ℝ → E} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (c : E) :
    AbsolutelyContinuousOnInterval (fun x => c + f x) a b := by
  simpa only [AbsolutelyContinuousOnInterval, dist_add_left] using hf

end NLS.FunctionalAnalysis
