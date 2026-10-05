import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp

/-! # Recovering a derivative from a nonzero scalar sequence -/
noncomputable section
open Filter Topology
namespace NLS.ComplexAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A ray quotient limit identifies the derivative in that direction.
The scalar sequence need not contain a neighborhood of zero. -/
theorem derivative_apply_eq_of_ray_limit
    (f : E → ℂ) (L : E →L[ℂ] ℂ) (hf : HasFDerivAt f L 0) (hzero : f 0 = 0)
    (v : E) {ι : Type*} {l : Filter ι} [l.NeBot] (a : ι → ℂ)
    (ha : Tendsto a l (𝓝 0)) (hne : ∀ᶠ i in l, a i ≠ 0) (c : ℂ)
    (hc : Tendsto (fun i => f (a i • v)/a i) l (𝓝 c)) : L v = c := by
  have hd : HasDerivAt (fun z : ℂ => f (z • v)) (L v) 0 := by
    have hline : HasDerivAt (fun z : ℂ => z • v) v 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).smul_const v
    simpa only [zero_smul] using! hf.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hane : Tendsto a l (𝓝[≠] (0 : ℂ)) := tendsto_nhdsWithin_iff.mpr ⟨ha,hne⟩
  have hs := hd.tendsto_slope.comp hane
  apply tendsto_nhds_unique _ hc
  simpa only [Function.comp_def,slope,zero_smul,hzero,sub_zero,vsub_eq_sub,smul_eq_mul,
    div_eq_mul_inv,mul_comm] using hs

end NLS.ComplexAnalysis
