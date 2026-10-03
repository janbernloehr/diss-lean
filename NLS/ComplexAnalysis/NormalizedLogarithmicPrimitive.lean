import NLS.ComplexAnalysis.PrimitiveRemovableBoundary
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Exponentiating an endpoint-normalized logarithmic primitive

A primitive of `M'/M` determines the multiplier itself. A boundary
normalization fixes the multiplicative constant without choosing a
principal logarithm or imposing a slit-plane restriction.
-/
noncomputable section
open Set Filter Topology Complex
namespace NLS.ComplexAnalysis

/-- The integrating factor is constant, and its boundary value fixes
that constant on the entire connected domain. -/
theorem multiplier_eq_exp_of_normalized_primitive
    (q F M : ℂ → ℂ) (U : Set ℂ) (c A : ℂ)
    (hU : IsOpen U) (hconn : IsPreconnected U) [NeBot (𝓝[U] c)]
    (hF : ∀ z ∈ U, HasDerivAt F (q z) z)
    (hM : ∀ z ∈ U, HasDerivAt M (M z*q z) z)
    (hFlim : Tendsto F (𝓝[U] c) (𝓝 0))
    (hMlim : Tendsto M (𝓝[U] c) (𝓝 A)) :
    ∀ z ∈ U, M z = A*exp (F z) := by
  let H : ℂ → ℂ := fun z => exp (-F z)*M z
  have hH (z : ℂ) (hz : z ∈ U) : HasDerivAt H 0 z := by
    convert ((hF z hz).neg.cexp).mul (hM z hz) using 1 <;> first | rfl | ring
  have hlim : Tendsto H (𝓝[U] c) (𝓝 A) := by
    have he := (Complex.continuous_exp.tendsto (- (0 : ℂ))).comp hFlim.neg
    simpa only [H,Function.comp_def,neg_zero,exp_zero,one_mul] using he.mul hMlim
  have hconst := primitives_eq_of_common_boundary_limit (fun _ => 0) H (fun _ => A) U c A
    hU hconn hH (fun z _ => hasDerivAt_const z A) hlim tendsto_const_nhds
  intro z hz
  have he : exp (F z)*exp (-F z) = 1 := by rw [← exp_add,add_neg_cancel,exp_zero]
  have h := congrArg (fun w : ℂ => exp (F z)*w) (hconst hz)
  change exp (F z)*(exp (-F z)*M z) = exp (F z)*A at h
  rw [← mul_assoc,he,one_mul,mul_comm] at h
  exact h

end NLS.ComplexAnalysis
