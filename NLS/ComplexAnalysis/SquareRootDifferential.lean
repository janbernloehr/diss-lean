import NLS.ComplexAnalysis.SquareRootSourceStationarity

noncomputable section
set_option autoImplicit false
open Filter Topology
namespace NLS.ComplexAnalysis

/-- The entire differential of a nonzero analytic square root of twice
a scalar function, in the physical action-amplitude normalization. -/
theorem fderiv_squareRoot_twice_of_sq_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A J : E → ℂ) (q : E) (hA : AnalyticAt ℂ A q) (hJ : AnalyticAt ℂ J q)
    (hsq : ∀ᶠ a in 𝓝 q, A a ^ 2 = 2 * J a) (hne : A q ≠ 0) :
    fderiv ℂ A q = (A q)⁻¹ • fderiv ℂ J q := by
  have hd := hA.differentiableAt.hasFDerivAt.mul hA.differentiableAt.hasFDerivAt
  have he : (fun a => A a * A a) =ᶠ[𝓝 q] (fun a => 2 * J a) := by
    filter_upwards [hsq] with a ha
    simpa only [pow_two] using ha
  have hu := (hd.congr_of_eventuallyEq he.symm).unique
    (hJ.differentiableAt.hasFDerivAt.const_mul 2)
  ext v
  have hv := congrArg (fun L : E →L[ℂ] ℂ => L v) hu
  simp only [add_apply,smul_apply,smul_eq_mul] at hv ⊢
  have heq : A q * (fderiv ℂ A q) v = (fderiv ℂ J q) v := by
    linear_combination (1/2:ℂ) * hv
  rw [←heq,←mul_assoc,inv_mul_cancel₀ hne,one_mul]

end NLS.ComplexAnalysis
