import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Normed.Operator.LinearIsometry

noncomputable section
set_option autoImplicit false
open Filter Topology
namespace NLS.FunctionalAnalysis

/-- A differentiable map fixing the origin and preserving its distance
from the origin has a norm-preserving derivative there. No inverse or
surjectivity of the derivative is assumed. -/
theorem norm_derivative_zero_of_norm_map
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (A : E →L[ℝ] F) (hf : HasFDerivAt f A 0)
    (hn : ∀ x : E, ‖f x‖ = ‖x‖) (h : E) : ‖A h‖ = ‖h‖ := by
  have hzero : f 0 = 0 := norm_eq_zero.mp (by simpa only [norm_zero] using hn 0)
  have hi : HasDerivAt (fun t : ℝ => t • h) h 0 := by
    simpa only [id_eq,one_smul] using (hasDerivAt_id (0 : ℝ)).smul_const h
  have hf' : HasFDerivAt f A ((fun t : ℝ => t • h) 0) := by
    simpa only [zero_smul] using hf
  have hd : HasDerivAt (fun t : ℝ => f (t • h)) (A h) 0 :=
    hf'.comp_hasDerivAt (0 : ℝ) hi
  have hc := hd.tendsto_slope.norm
  have he : (fun t : ℝ => ‖slope (fun s : ℝ => f (s • h)) 0 t‖) =ᶠ[𝓝[≠] (0 : ℝ)]
      (fun _ => ‖h‖) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := ht
    simp only [slope,vsub_eq_sub,sub_zero,zero_smul,hzero,norm_smul,hn,Real.norm_eq_abs,abs_inv]
    rw [←mul_assoc,inv_mul_cancel₀ (abs_ne_zero.mpr ht0),one_mul]
  exact tendsto_nhds_unique hc (tendsto_const_nhds.congr' he.symm)

/-- The derivative in the preceding criterion, packaged as its actual
linear isometry. This asserts no inverse. -/
def derivativeZeroLinearIsometry
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (A : E →L[ℝ] F) (hf : HasFDerivAt f A 0)
    (hn : ∀ x : E, ‖f x‖ = ‖x‖) : E →ₗᵢ[ℝ] F where
  toLinearMap := A.toLinearMap
  norm_map' := norm_derivative_zero_of_norm_map f A hf hn

end NLS.FunctionalAnalysis
