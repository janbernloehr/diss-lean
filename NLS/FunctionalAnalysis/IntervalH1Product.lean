import NLS.FunctionalAnalysis.ComplexAbsoluteContinuity
import NLS.ZakharovShabat.PhysicalL2IntegralPairing

/-! # Products of actual H1 interval curves

Absolute continuity and L2 first derivatives are preserved by pointwise
multiplication of continuous interval curves. Derivatives are actual
classical derivatives almost everywhere on the original unit interval.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.FunctionalAnalysis

theorem absolutelyContinuous_curve_mul (f g : Curve ℂ)
    (hf : AbsolutelyContinuousOnInterval (extend f) 0 1)
    (hg : AbsolutelyContinuousOnInterval (extend g) 0 1) :
    AbsolutelyContinuousOnInterval (extend (f*g)) 0 1 := by
  simpa only [NLS.LinearVolterra.extend,ContinuousMap.mul_apply,Pi.smul_def,smul_eq_mul,Pi.mul_def] using! hf.smul hg

theorem ae_deriv_curve_mul (f g : Curve ℂ)
    (hf : AbsolutelyContinuousOnInterval (extend f) 0 1)
    (hg : AbsolutelyContinuousOnInterval (extend g) 0 1) :
    deriv (extend (f*g)) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      (fun s => deriv (extend f) s*extend g s+extend f s*deriv (extend g) s) := by
  filter_upwards [ae_restrict_of_ae (ae_differentiableAt_complex hf),
    ae_restrict_of_ae (ae_differentiableAt_complex hg),ae_restrict_mem measurableSet_Ioc] with s hs ht hx
  have hx' : s ∈ uIcc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using Ioc_subset_Icc_self hx
  have h := ((hs hx').hasDerivAt.mul (ht hx').hasDerivAt).deriv
  exact h

theorem memLp_deriv_curve_mul (f g : Curve ℂ)
    (hf : AbsolutelyContinuousOnInterval (extend f) 0 1)
    (hg : AbsolutelyContinuousOnInterval (extend g) 0 1)
    (hf₂ : MemLp (deriv (extend f)) 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hg₂ : MemLp (deriv (extend g)) 2 (volume.restrict (Ioc (0 : ℝ) 1))) :
    MemLp (deriv (extend (f*g))) 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have h₁ : MemLp (fun s => deriv (extend f) s*extend g s) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (curveBoundedExtension ℂ g).memLp_top.mul hf₂
  have h₂ : MemLp (fun s => extend f s*deriv (extend g) s) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    hg₂.mul (curveBoundedExtension ℂ f).memLp_top
  exact (memLp_congr_ae (ae_deriv_curve_mul f g hf hg)).mpr (h₁.add h₂)

end NLS.FunctionalAnalysis
