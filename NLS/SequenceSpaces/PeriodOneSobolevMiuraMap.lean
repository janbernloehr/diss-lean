import NLS.SequenceSpaces.PeriodOneMiuraTameProduct
import NLS.SequenceSpaces.PeriodOneMiuraShift
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-! # The actual Miura map in the stronger native Sobolev norms

The literal product is bounded bilinear H^t times H^t into H^(t-1).
Together with the exact unit-period derivative, this defines an entire
complex analytic shifted Miura map and its actual bounded Jacobian.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS

private theorem native_product_comm (t : ℝ) (ht : 0≤t)
    (a b : WeightedCoeff (Weight.sobolev t) 2) :
    periodOneSobolevMiuraProduct t ht a b=periodOneSobolevMiuraProduct t ht b a := by
  apply Subtype.ext
  exact congrArg (fun p : PeriodOneHminusOne => p.val) (periodOneMiuraProduct_comm
    (WeightedCoeff.sobolevToL2 ht a) (WeightedCoeff.sobolevToL2 ht b))

/-- Actual Sobolev multiplication as a bounded complex bilinear map. -/
def periodOneSobolevMiuraProductCLM (t : ℝ) (ht : 0 ≤ t) :
    WeightedCoeff (Weight.sobolev t) 2 →L[ℂ]
      WeightedCoeff (Weight.sobolev t) 2 →L[ℂ] WeightedCoeff (Weight.sobolev (t-1)) 2 :=
  (LinearMap.mk₂ ℂ (periodOneSobolevMiuraProduct t ht)
    (by
      intro a a' b
      apply Subtype.ext
      funext n
      change (periodOneMiuraProduct (WeightedCoeff.sobolevToL2 ht (a+a'))
        (WeightedCoeff.sobolevToL2 ht b)).val n=_
      simp only [map_add,_root_.add_apply,periodOneSobolevMiuraProduct,WeightedCoeff.add_val]; rfl)
    (by
      intro c a b
      apply Subtype.ext
      funext n
      change (periodOneMiuraProduct (WeightedCoeff.sobolevToL2 ht (c • a))
        (WeightedCoeff.sobolevToL2 ht b)).val n=_
      simp only [map_smul,_root_.smul_apply,periodOneSobolevMiuraProduct,
        WeightedCoeff.smul_val]; rfl)
    (by
      intro a b b'
      apply Subtype.ext
      funext n
      change (periodOneMiuraProduct (WeightedCoeff.sobolevToL2 ht a)
        (WeightedCoeff.sobolevToL2 ht (b+b'))).val n=_
      simp only [map_add,periodOneSobolevMiuraProduct,WeightedCoeff.add_val]; rfl)
    (by
      intro c a b
      apply Subtype.ext
      funext n
      change (periodOneMiuraProduct (WeightedCoeff.sobolevToL2 ht a)
        (WeightedCoeff.sobolevToL2 ht (c • b))).val n=_
      simp only [map_smul,periodOneSobolevMiuraProduct,WeightedCoeff.smul_val]; rfl)).mkContinuous₂
    (2*(2 : ℝ)^t*‖inverseBracketCoefficients‖)
    (fun a b => norm_periodOneSobolevMiuraProduct_le t ht a b)

@[simp] theorem periodOneSobolevMiuraProductCLM_apply (t : ℝ) (ht : 0 ≤ t)
    (a b : WeightedCoeff (Weight.sobolev t) 2) :
    periodOneSobolevMiuraProductCLM t ht a b=periodOneSobolevMiuraProduct t ht a b := rfl

/-- The exact first-order shifted linear part in the stronger norms. -/
def periodOneSobolevMassOperator (m : ℕ) (t : ℝ) :
    WeightedCoeff (Weight.sobolev t) 2 →L[ℂ] WeightedCoeff (Weight.sobolev (t-1)) 2 :=
  (2 : ℂ) • (WeightedCoeff.sobolevDerivative (t-1)).comp
    (WeightedCoeff.sobolevInclusion (by linarith : (t-1)+1 ≤ t))+
      (((m : ℝ)+1 : ℝ) : ℂ) • WeightedCoeff.sobolevInclusion (by linarith : t-1 ≤ t)

@[simp] theorem periodOneSobolevMassOperator_apply (m : ℕ) (t : ℝ)
    (a : WeightedCoeff (Weight.sobolev t) 2) (n : ℤ) :
    (periodOneSobolevMassOperator m t a).val n=periodOneMassSymbol m n*a.val n := by
  simp only [periodOneSobolevMassOperator,_root_.add_apply,
    _root_.smul_apply,ContinuousLinearMap.comp_apply,WeightedCoeff.add_val,
    WeightedCoeff.smul_val,WeightedCoeff.sobolevDerivative_apply,WeightedCoeff.sobolevInclusion_apply,
    periodOneMassSymbol,ofReal_add,ofReal_one]
  ring

/-- The literal shifted Miura equation as a map H^t to H^(t-1). -/
def periodOneSobolevShiftedMiura (m : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (a : WeightedCoeff (Weight.sobolev t) 2) : WeightedCoeff (Weight.sobolev (t-1)) 2 :=
  periodOneSobolevMassOperator m t a+periodOneSobolevMiuraProductCLM t ht a a

@[simp] theorem periodOneSobolevShiftedMiura_apply (m : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (a : WeightedCoeff (Weight.sobolev t) 2) (n : ℤ) :
    (periodOneSobolevShiftedMiura m t ht a).val n=
      periodOneMassSymbol m n*a.val n+∑' j : ℤ, a.val (n-j)*a.val j := by
  rw [periodOneSobolevShiftedMiura,WeightedCoeff.add_val,periodOneSobolevMassOperator_apply,
    periodOneSobolevMiuraProductCLM_apply,periodOneSobolevMiuraProduct_apply]

/-- The bounded native Sobolev Jacobian of the ACTUAL shifted Miura map. -/
def periodOneSobolevMiuraJacobian (m : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (a : WeightedCoeff (Weight.sobolev t) 2) :
    WeightedCoeff (Weight.sobolev t) 2 →L[ℂ] WeightedCoeff (Weight.sobolev (t-1)) 2 :=
  periodOneSobolevMassOperator m t+
    (periodOneSobolevMiuraProductCLM t ht a+(periodOneSobolevMiuraProductCLM t ht).flip a)

/-- Analyticity is in the actual stronger domain AND codomain norms. -/
theorem analyticAt_periodOneSobolevShiftedMiura (m : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (a : WeightedCoeff (Weight.sobolev t) 2) :
    AnalyticAt ℂ (periodOneSobolevShiftedMiura m t ht) a :=
  ((periodOneSobolevMassOperator m t).analyticAt a).add
    (((periodOneSobolevMiuraProductCLM t ht).analyticAt_bilinear _).comp₂ analyticAt_id analyticAt_id)

theorem hasFDerivAt_periodOneSobolevShiftedMiura (m : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (a : WeightedCoeff (Weight.sobolev t) 2) :
    HasFDerivAt (periodOneSobolevShiftedMiura m t ht) (periodOneSobolevMiuraJacobian m t ht a) a := by
  have h := (periodOneSobolevMiuraProductCLM t ht).hasFDerivAt_of_bilinear
    (hasFDerivAt_id a) (hasFDerivAt_id a)
  have he : (periodOneSobolevMiuraProductCLM t ht).precompR _ a (ContinuousLinearMap.id ℂ _)+
      (periodOneSobolevMiuraProductCLM t ht).precompL _ (ContinuousLinearMap.id ℂ _) a=
      periodOneSobolevMiuraProductCLM t ht a+(periodOneSobolevMiuraProductCLM t ht).flip a := by
    ext v
    rfl
  rw [show id a=a from rfl,he] at h
  exact (periodOneSobolevMassOperator m t).hasFDerivAt.add h

@[simp] theorem periodOneSobolevMiuraJacobian_apply (m : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (a v : WeightedCoeff (Weight.sobolev t) 2) (n : ℤ) :
    (periodOneSobolevMiuraJacobian m t ht a v).val n=
      periodOneMassSymbol m n*v.val n+2*(∑' j : ℤ, a.val (n-j)*v.val j) := by
  have hcomm : periodOneSobolevMiuraProductCLM t ht v a=periodOneSobolevMiuraProductCLM t ht a v :=
    native_product_comm t ht v a
  simp only [periodOneSobolevMiuraJacobian,_root_.add_apply,ContinuousLinearMap.flip_apply,
    WeightedCoeff.add_val,hcomm,periodOneSobolevMassOperator_apply,
    periodOneSobolevMiuraProductCLM_apply,periodOneSobolevMiuraProduct_apply]
  ring

end NLS
