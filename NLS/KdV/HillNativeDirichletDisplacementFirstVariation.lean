import NLS.KdV.HillNativeDirichletFirstVariation
import NLS.KdV.HillNativeMidpointFirstVariation

/-! Exact centered ORIGINAL-energy Dirichlet first variation. The mean
cancels in every complex native direction, before imposing mean zero. -/
noncomputable section
open Set Complex
namespace NLS.KdV

theorem fderiv_hillHminusDirichlet_sub_midpoint_zero (n : ℕ+) :
    fderiv ℂ (fun q => hillHminusCanonicalDirichlet n q-hillHminusCanonicalEnergyMidpoint n q) 0 =
      hillFreeDirichletGradient n-WeightedCoeff.evalCLM (Weight.sobolev (-1)) 2 0 := by
  have hr : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have hd := (analyticOnNhd_hillHminusCanonicalDirichlet n 0
    (real_mem_hillHminusCanonicalDirichletDomain 0 hr)).differentiableAt.hasFDerivAt
  have hm := (analyticOnNhd_hillHminusCanonicalEnergyMidpoint n 0
    (real_mem_hillHminusCanonicalZeroSequenceDomain 0 hr)).differentiableAt.hasFDerivAt
  have he := (hd.sub hm).fderiv
  change fderiv ℂ (fun q => hillHminusCanonicalDirichlet n q-hillHminusCanonicalEnergyMidpoint n q) 0 = _ at he
  rw [he,fderiv_hillHminusCanonicalDirichlet_zero,fderiv_hillHminusCanonicalEnergyMidpoint_zero]

theorem fderiv_hillHminusDirichlet_sub_midpoint_zero_apply (n : ℕ+) (h : PeriodOneHminusOne) :
    (fderiv ℂ (fun q => hillHminusCanonicalDirichlet n q-hillHminusCanonicalEnergyMidpoint n q) 0) h =
      -(h.val (n:ℤ)+h.val (-(n:ℤ)))/2 := by
  rw [fderiv_hillHminusDirichlet_sub_midpoint_zero,sub_apply,hillFreeDirichletGradient_apply,
    WeightedCoeff.evalCLM_apply]
  ring

end NLS.KdV
