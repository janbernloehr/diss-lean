import NLS.KdV.HillNativeNormingFirstVariation

/-! The ACTUAL prescribed sheet differential retains the free norming
parity sign and every positive index. -/
noncomputable section
open Set Complex
namespace NLS.KdV

theorem hillHminusDirichletNorming_zero_sq (n : ℕ+) :
    hillHminusDirichletNorming n 0 ^ 2 = 1 := by
  rw [hillHminusDirichletNorming_zero,← pow_mul,Nat.mul_comm (n:ℕ) 2,pow_mul]
  norm_num

theorem fderiv_hillHminusDirichletSheet_zero (n : ℕ+) :
    fderiv ℂ (hillHminusDirichletSheet n) 0 = (-2:ℂ) • hillFreeNormingGradient n := by
  have hr : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have h0 := real_mem_hillHminusCanonicalDirichletDomain 0 hr
  have hN := (analyticOnNhd_hillHminusDirichletNorming n 0 h0).differentiableAt.hasFDerivAt
  have hI := (hasFDerivAt_inv (hillHminusDirichletNorming_ne_zero n 0 h0)).comp 0 hN
  have hd := (hI.sub hN).fderiv
  change fderiv ℂ (hillHminusDirichletSheet n) 0 = _ at hd
  rw [hillHminusDirichletNorming_zero_sq,inv_one,fderiv_hillHminusDirichletNorming_zero] at hd
  rw [hd]
  ext h
  simp only [sub_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply,smul_apply,smul_eq_mul]
  ring

theorem fderiv_hillHminusDirichletSheet_zero_apply (n : ℕ+) (h : PeriodOneHminusOne) :
    (fderiv ℂ (hillHminusDirichletSheet n) 0) h =
      ((-1:ℂ)^(n:ℕ)/(2*I*((Real.pi:ℂ)*n)))*(h.val (n:ℤ)-h.val (-(n:ℤ))) := by
  rw [fderiv_hillHminusDirichletSheet_zero,smul_apply,hillFreeNormingGradient_apply,smul_eq_mul]
  ring

end NLS.KdV
