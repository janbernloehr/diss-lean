import NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianWeakJacobian

/-! # Injectivity of the ACTUAL rough signed differential on mean-zero directions

The existing weak mean-zero Jacobian unit is transferred back through
its exact original weighted lift and projection. No reality restriction
is imposed on the two complex directions being compared.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

theorem signed_fderiv_injective_on_meanZero (D : GlobalRoughAbelianForwardData)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (hm : q.val 0=0)
    (v w : PeriodOneHminusOne) (hv : v.val 0=0) (hw : w.val 0=0)
    (he : fderiv ℂ D.signed q v=fderiv ℂ D.signed q w) : v=w := by
  let P := WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1))
  let L := WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1))
  let a := P q
  have hq : L a=q := WeightedCoeff.meanZeroWeightedLift_projection _ q hm
  have hreal : IsRealPeriodOneHminusOne (L a) := by rw [hq];exact hr
  have hi := (ContinuousLinearMap.isUnit_iff_bijective.mp (D.isUnit_fderiv_meanZeroForward a hreal)).injective
  have ha : a∈D.meanZeroDomain := D.real_mem_domain _ hreal
  have hd := D.fderiv_meanZeroForward a ha
  have hPv : L (P v)=v := WeightedCoeff.meanZeroWeightedLift_projection _ v hv
  have hPw : L (P w)=w := WeightedCoeff.meanZeroWeightedLift_projection _ w hw
  have hP : P v=P w := by
    apply hi
    rw [hd]
    change WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1/2))
        (fderiv ℂ D.signed (L a) (L (P v)))=
      WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1/2))
        (fderiv ℂ D.signed (L a) (L (P w)))
    rw [hq,hPv,hPw,he]
  exact hPv.symm.trans ((congrArg L hP).trans hPw)

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
