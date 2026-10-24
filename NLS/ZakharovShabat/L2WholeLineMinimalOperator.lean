import NLS.ZakharovShabat.L2WholeLineTestDomain
import Mathlib.LinearAlgebra.LinearPMap

/-! # The densely defined minimal physical operator on the real line

The original signed expression is complex linear on differentiable pairs.
Its L2 realization on smooth compact tests gives an actual partial linear
map on the Hermitian whole-line Hilbert space, with a dense domain.
Self-adjointness, closure identification and spectral claims are not asserted.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace NLS.ZakharovShabat

/-- The signed physical expression respects addition on differentiable pairs. -/
theorem physicalOperator_add (φ f g : ℝ → ℂ × ℂ)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    physicalOperator φ (f+g) = physicalOperator φ f + physicalOperator φ g := by
  funext x
  apply Prod.ext
  · simp only [physicalOperator,Pi.add_apply,Prod.fst_add,Prod.snd_add]
    rw [deriv_fun_add (hf.fst x) (hg.fst x)]
    ring
  · simp only [physicalOperator,Pi.add_apply,Prod.fst_add,Prod.snd_add]
    rw [deriv_fun_add (hf.snd x) (hg.snd x)]
    ring

/-- The signed physical expression respects complex scalar multiplication. -/
theorem physicalOperator_smul (φ f : ℝ → ℂ × ℂ) (hf : Differentiable ℝ f) (c : ℂ) :
    physicalOperator φ (c • f) = c • physicalOperator φ f := by
  funext x
  apply Prod.ext
  · simp only [physicalOperator,Pi.smul_apply,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
    rw [deriv_const_mul c (hf.fst x)]
    ring
  · simp only [physicalOperator,Pi.smul_apply,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
    rw [deriv_const_mul c (hf.snd x)]
    ring



private theorem differentiable_wholeLineTestPair (f : WholeLineTestFunction) :
    Differentiable ℝ (fun t => (f t).ofLp) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ℂ ℂ).differentiable.comp
    (f.property.1.differentiable (by norm_num))

theorem wholeLineTestPhysicalExpression_add (u : IntervalPairL2) (f g : WholeLineTestFunction) :
    wholeLineTestPhysicalExpression u (f+g) =
      wholeLineTestPhysicalExpression u f + wholeLineTestPhysicalExpression u g := by
  funext t
  exact congrArg (WithLp.toLp 2) (congrFun (physicalOperator_add (l2WholeLinePotential u)
    (fun t => (f t).ofLp) (fun t => (g t).ofLp)
    (differentiable_wholeLineTestPair f) (differentiable_wholeLineTestPair g)) t)

theorem wholeLineTestPhysicalExpression_smul (u : IntervalPairL2) (f : WholeLineTestFunction) (c : ℂ) :
    wholeLineTestPhysicalExpression u (c • f) = c • wholeLineTestPhysicalExpression u f := by
  funext t
  exact congrArg (WithLp.toLp 2) (congrFun (physicalOperator_smul (l2WholeLinePotential u)
    (fun t => (f t).ofLp) (differentiable_wholeLineTestPair f) c) t)

/-- The actual physical operator on smooth compact tests takes values in L2. -/
def wholeLineTestOperator (u : IntervalPairL2) : WholeLineTestFunction →ₗ[ℂ] WholeLineL2 where
  toFun f := (memLp_wholeLineTestPhysicalExpression u f).toLp (wholeLineTestPhysicalExpression u f)
  map_add' f g := by
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall (congrFun (wholeLineTestPhysicalExpression_add u f g))
  map_smul' c f := by
    rw [← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall (congrFun (wholeLineTestPhysicalExpression_smul u f c))

theorem wholeLineTestOperator_ae (u : IntervalPairL2) (f : WholeLineTestFunction) :
    wholeLineTestOperator u f =ᵐ[volume] wholeLineTestPhysicalExpression u f :=
  (memLp_wholeLineTestPhysicalExpression u f).coeFn_toLp

/-- Test functions and their actual L2 classes identify the dense operator domain. -/
def wholeLineTestDomainEquiv : WholeLineTestFunction ≃ₗ[ℂ] LinearMap.range wholeLineTestInclusion :=
  LinearEquiv.ofInjective wholeLineTestInclusion wholeLineTestInclusion_injective

/-- The minimal whole-line realization of the original signed differential expression.
Its domain is exactly the L2 image of smooth compactly supported pairs. -/
def wholeLineMinimalOperator (u : IntervalPairL2) : WholeLineL2 →ₗ.[ℂ] WholeLineL2 where
  domain := LinearMap.range wholeLineTestInclusion
  toFun := (wholeLineTestOperator u).comp wholeLineTestDomainEquiv.symm.toLinearMap

theorem wholeLineMinimalOperator_dense_domain (u : IntervalPairL2) :
    Dense (↑(wholeLineMinimalOperator u).domain : Set WholeLineL2) := denseRange_wholeLineTestInclusion

/-- On every element of its domain the minimal realization uses the actual physical expression. -/
theorem wholeLineMinimalOperator_test (u : IntervalPairL2) (f : WholeLineTestFunction) :
    wholeLineMinimalOperator u (wholeLineTestDomainEquiv f) = wholeLineTestOperator u f := by
  change wholeLineTestOperator u (wholeLineTestDomainEquiv.symm (wholeLineTestDomainEquiv f)) = _
  rw [LinearEquiv.symm_apply_apply]

theorem wholeLineMinimalOperator_test_ae (u : IntervalPairL2) (f : WholeLineTestFunction) :
    wholeLineMinimalOperator u (wholeLineTestDomainEquiv f) =ᵐ[volume]
      wholeLineTestPhysicalExpression u f := by
  rw [wholeLineMinimalOperator_test]
  exact wholeLineTestOperator_ae u f

end NLS.ZakharovShabat
