import NLS.ComplexAnalysis.QuadraticPuncturedLimit
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # Filling a quadratic divided-difference identity

The square coordinate may be ramified at zero. Punctured continuity and the
actual derivative still determine the diagonal value, including that point.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.ComplexAnalysis

theorem value_of_quadratic_divided_difference (f G : ℂ → ℂ) (a z κ d : ℂ)
    (hz : z^2=a) (hf : HasDerivAt f d a) (hfa : f a=0) (hG : ContinuousAt G z)
    (h : ∀ w : ℂ, (a-w^2)*G w=κ*f (w^2)) : G z= -κ*d := by
  have hquad : Tendsto (fun w : ℂ => w^2) (𝓝[≠] z) (𝓝[≠] a) := by
    simpa only [hz] using tendsto_sq_punctured z
  have hs := hf.tendsto_slope.comp hquad
  have he : ∀ᶠ w in 𝓝[≠] z, G w= -κ*slope f a (w^2) := by
    have hne := (tendsto_nhdsWithin_iff.mp hquad).2
    filter_upwards [hne] with w hw
    simp only [mem_compl_iff,mem_singleton_iff] at hw
    rw [slope_def_field,hfa,sub_zero,← mul_div_assoc]
    apply (eq_div_iff (sub_ne_zero.mpr hw)).mpr
    linear_combination -h w
  have heq : G =ᶠ[𝓝[≠] z] (fun w => -κ*slope f a (w^2)) := he
  have ht := (tendsto_const_nhds (x := -κ)).mul hs
  exact tendsto_nhds_unique (hG.tendsto.mono_left nhdsWithin_le_nhds) (ht.congr' heq.symm)

end NLS.ComplexAnalysis
