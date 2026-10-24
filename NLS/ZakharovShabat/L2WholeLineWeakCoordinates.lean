import NLS.ZakharovShabat.L2WholeLineAdjointEquation
import NLS.ZakharovShabat.L2WholeLineWeakDerivative
import NLS.ZakharovShabat.L2WholeLineReality

/-! # Scalar weak derivatives of the actual whole-line adjoint equation -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Complex
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- A conjugated scalar test in the first component of the physical domain. -/
def wholeLineFirstTest (ψ : ℝ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    WholeLineTestFunction :=
  ⟨fun t => WithLp.toLp 2 (star (ψ t),0),
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℂ ℂ).symm.contDiff.comp
      ((Complex.conjCLE.contDiff.comp hψ).prodMk contDiff_const),
    hc.comp_left (g := fun z : ℂ => WithLp.toLp 2 (star z,0)) (by simp)⟩

/-- A conjugated scalar test in the second component of the physical domain. -/
def wholeLineSecondTest (ψ : ℝ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    WholeLineTestFunction :=
  ⟨fun t => WithLp.toLp 2 (0,star (ψ t)),
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℂ ℂ).symm.contDiff.comp
      (contDiff_const.prodMk (Complex.conjCLE.contDiff.comp hψ)),
    hc.comp_left (g := fun z : ℂ => WithLp.toLp 2 (0,star z)) (by simp)⟩

/-- The first coordinate of the actual weak physical equation is the
distributional derivative identity, with the original signed coefficient. -/
theorem WholeLineWeakEquation.first_weak_derivative
    {u : IntervalPairL2} {f g : WholeLineL2}
    (hu : IsClassicalRealType (intervalL2Representative u))
    (hfg : WholeLineWeakEquation u f g)
    (ψ : ℝ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    (∫ t : ℝ, deriv ψ t * (wholeLineL2Pair f t).1 + ψ t * (wholeLineWeakDerivative u f g t).1) = 0 := by
  have he := hfg.integral_residual_eq_zero (wholeLineFirstTest ψ hψ hc)
  have hr : (fun t => inner ℂ (wholeLineTestPhysicalExpression u (wholeLineFirstTest ψ hψ hc) t) (f t) -
      inner ℂ (wholeLineFirstTest ψ hψ hc t) (g t)) =ᵐ[volume]
      (fun t => -I * (deriv ψ t * (wholeLineL2Pair f t).1 + ψ t * (wholeLineWeakDerivative u f g t).1)) := by
    filter_upwards [ae_l2WholeLinePotential_real u hu] with t ht
    simp only [wholeLineFirstTest,wholeLineTestPhysicalExpression,physicalOperator,
      WithLp.prod_inner_apply,RCLike.inner_apply',wholeLineL2Pair,wholeLineWeakDerivative]
    simp only [deriv.star,deriv_const]
    rw [ht]
    simp
    ring_nf
    simp [I_sq,sub_eq_add_neg]
  rw [integral_congr_ae hr,integral_const_mul] at he
  exact (mul_eq_zero.mp he).resolve_left (neg_ne_zero.mpr I_ne_zero)

/-- The second coordinate has the opposite signed derivative, exactly
as prescribed by the original Zakharov-Shabat differential expression. -/
theorem WholeLineWeakEquation.second_weak_derivative
    {u : IntervalPairL2} {f g : WholeLineL2}
    (hu : IsClassicalRealType (intervalL2Representative u))
    (hfg : WholeLineWeakEquation u f g)
    (ψ : ℝ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    (∫ t : ℝ, deriv ψ t * (wholeLineL2Pair f t).2 + ψ t * (wholeLineWeakDerivative u f g t).2) = 0 := by
  have he := hfg.integral_residual_eq_zero (wholeLineSecondTest ψ hψ hc)
  have hr : (fun t => inner ℂ (wholeLineTestPhysicalExpression u (wholeLineSecondTest ψ hψ hc) t) (f t) -
      inner ℂ (wholeLineSecondTest ψ hψ hc t) (g t)) =ᵐ[volume]
      (fun t => I * (deriv ψ t * (wholeLineL2Pair f t).2 + ψ t * (wholeLineWeakDerivative u f g t).2)) := by
    filter_upwards [ae_l2WholeLinePotential_real u hu] with t ht
    simp only [wholeLineSecondTest,wholeLineTestPhysicalExpression,physicalOperator,
      WithLp.prod_inner_apply,RCLike.inner_apply',wholeLineL2Pair,wholeLineWeakDerivative]
    simp only [deriv.star,deriv_const]
    rw [ht]
    simp
    ring_nf
    simp [I_sq,sub_eq_add_neg]
  rw [integral_congr_ae hr,integral_const_mul] at he
  exact (mul_eq_zero.mp he).resolve_left I_ne_zero

end NLS.ZakharovShabat
