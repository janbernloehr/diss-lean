import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Analytic.ChangeOrigin

/-! # Analytic filling from nonreal energies

A function specified independently off the real axis has a unique value
at every point where those values agree with a continuous germ. Analytic
germs give analytic filled functions, without selecting values by a
comparison function in the definition.
-/
noncomputable section
open Set Complex Filter Topology
namespace NLS.ComplexAnalysis

def nonrealBoundaryExtension (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  limUnder (𝓝[{w : ℂ | w.im ≠ 0}] z) f

theorem nhdsWithin_nonreal_neBot (z : ℂ) : NeBot (𝓝[{w : ℂ | w.im ≠ 0}] z) := by
  by_cases hi : z.im = 0
  · apply mem_closure_iff_nhdsWithin_neBot.mp
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    refine ⟨z+((ε/2 : ℝ) : ℂ)*I,?_,?_⟩
    · change (z+((ε/2 : ℝ) : ℂ)*I).im ≠ 0
      simpa only [add_im,mul_im,ofReal_im,ofReal_re,I_re,I_im,mul_zero,mul_one,
        zero_mul,zero_add,add_zero,hi] using (half_pos hε).ne'
    · have he : z-(z+((ε/2 : ℝ) : ℂ)*I) = -(((ε/2 : ℝ) : ℂ)*I) := by ring
      rw [dist_eq_norm,he,norm_neg,norm_mul,norm_I,mul_one]
      norm_cast
      rw [Real.norm_eq_abs,abs_of_pos (half_pos hε)]
      linarith
  · exact nhdsWithin_neBot_of_mem hi

theorem nonrealBoundaryExtension_eq_of_continuousAt {f g : ℂ → ℂ} {z : ℂ}
    (hg : ContinuousAt g z) (he : ∀ w : ℂ, w.im ≠ 0 → f w = g w) :
    nonrealBoundaryExtension f z = g z := by
  let := nhdsWithin_nonreal_neBot z
  have ht : Tendsto f (𝓝[{w : ℂ | w.im ≠ 0}] z) (𝓝 (g z)) := by
    apply (hg.tendsto.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact (he w hw).symm
  exact ht.limUnder_eq

theorem nonrealBoundaryExtension_eq_self {f : ℂ → ℂ} {z : ℂ} (hf : ContinuousAt f z) :
    nonrealBoundaryExtension f z = f z :=
  nonrealBoundaryExtension_eq_of_continuousAt hf (fun _ _ => rfl)

theorem analyticAt_nonrealBoundaryExtension {f g : ℂ → ℂ} {z : ℂ}
    (hg : AnalyticAt ℂ g z) (he : ∀ w : ℂ, w.im ≠ 0 → f w = g w) :
    AnalyticAt ℂ (nonrealBoundaryExtension f) z := by
  apply hg.congr
  filter_upwards [hg.eventually_continuousAt] with w hw
  exact (nonrealBoundaryExtension_eq_of_continuousAt hw he).symm

end NLS.ComplexAnalysis
