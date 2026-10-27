import NLS.Fourier.FoldedSobolev
import NLS.Fourier.FractionalHardy
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! # Reflection preserves the full classical interval H¹ class -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set NLS.FunctionalAnalysis
namespace NLS.Fourier

/-- Reflection preserves interval square integrability, with no regularity outside the interval. -/
theorem memLp_unit_reflection {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) :
    MemLp (fun x => f (1-x)) 2 (volume.restrict (Ioc 0 1)) := by
  have hm : MeasurePreserving (fun x : ℝ => 1-x)
      (volume.restrict (Ioc 0 1)) (volume.restrict (Ioc 0 1)) := by
    simpa only [restrict_Ioo_eq_restrict_Ioc] using measurePreserving_interval_reflection 1
  exact hf.comp_measurePreserving hm

/-- The reflected H¹ function is the primitive of the reflected negative derivative. -/
theorem intervalH1_reflection_eq_integral {f : ℝ → ℂ} (hf : HasIntervalH1Regularity f)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    f (1-x) = f 1 + ∫ t in (0 : ℝ)..x, -deriv f (1-t) := by
  have hi : IntervalIntegrable (deriv f) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr (hf.2.integrable (by norm_num))
  have hs : uIcc (1-x) 1 ⊆ uIcc (0 : ℝ) 1 :=
    uIcc_subset_uIcc (by simpa using (show 1-x ∈ Icc (0 : ℝ) 1 from ⟨by linarith [hx.2],by linarith [hx.1]⟩)) (by simp)
  rw [intervalIntegral.integral_neg,intervalIntegral.integral_comp_sub_left,sub_zero,
    integral_deriv_eq_sub_complex (hf.1.mono hs) (hi.mono_set hs)]
  abel

/-- Reflection preserves full interval H¹ regularity, without a global smooth extension. -/
theorem HasIntervalH1Regularity.reflect {f : ℝ → ℂ} (hf : HasIntervalH1Regularity f) :
    HasIntervalH1Regularity (fun x => f (1-x)) := by
  have hm := (memLp_unit_reflection hf.2).neg
  have hi : IntervalIntegrable (fun x => -deriv f (1-x)) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr (hm.integrable (by norm_num))
  refine ⟨?_,?_⟩
  · apply absolutelyContinuousOnInterval_congr
      (absolutelyContinuousOnInterval_const_add
        (absolutelyContinuousOnInterval_integral hi (c := 0) (by simp)) (f 1))
    intro x hx
    exact (intervalH1_reflection_eq_integral hf (by simpa using hx)).symm
  · change MemLp (fun x => deriv (fun t => f (1-t)) x) 2 (volume.restrict (Ioc 0 1))
    simp only [deriv_comp_const_sub]
    exact hm

end NLS.Fourier
