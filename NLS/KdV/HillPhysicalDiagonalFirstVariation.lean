import NLS.KdV.HillPhysicalFreeRootCoefficientDerivative

/-! The actual physical diagonal factors differentiate to the two signed
Fourier coefficients on the complex mean-zero tangent, at every index. -/
noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV.HillProductEquationPatch

theorem fderiv_physicalOnIndexCartesianPlus_zero_mean_zero (P : HillProductEquationPatch)
    (h0 : (0 : PeriodOneHminusOne) ∈ P.source) (n : ℕ+) (h : PeriodOneHminusOne) (hh : h.val 0=0) :
    (fderiv ℂ (P.physicalOnIndexCartesianPlus n) 0) h=2*h.val (-(n:ℤ)) := by
  have hr : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have hp := P.real_mem_physicalDirichletSource 0 h0 hr
  let τ := fun q => sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)
  have ht := (P.analytic_abelianGapMidpoint n 0 h0).differentiableAt
  have hμ := (P.analytic_physicalDirichletFrequency ((n:ℕ):ℤ) 0 h0).differentiableAt
  have hs := (P.analytic_physicalDirichletRootCoefficient n 0 hp).differentiableAt
  have hc : DifferentiableAt ℂ (fun q => Complex.exp (I*P.physicalOnIndexAbelianCorrection n q)) 0 :=
    (analyticAt_const.mul (P.analytic_physicalOnIndexAbelianCorrection n 0 hp)).cexp.differentiableAt
  have hz : P.physicalDirichletFrequency ((n:ℕ):ℤ) 0-τ 0-P.physicalDirichletRootCoefficient n 0=0 := by
    rw [P.physicalDirichletFrequency_zero_eq_midpoint h0 n,P.physicalDirichletRootCoefficient_zero]
    change τ 0-τ 0-0=0
    ring
  have hd := fderiv_three_factors_apply_of_middle_zero (fun q => (-4:ℂ)*τ q)
    (fun q => P.physicalDirichletFrequency ((n:ℕ):ℤ) q-τ q-P.physicalDirichletRootCoefficient n q)
    (fun q => Complex.exp (I*P.physicalOnIndexAbelianCorrection n q)) 0 h
    ((hasFDerivAt_const (-4:ℂ) (0:PeriodOneHminusOne)).differentiableAt.mul ht) ((hμ.sub ht).sub hs) hc hz
  change (fderiv ℂ (P.physicalOnIndexCartesianPlus n) 0) h = _ at hd
  have hb := ((hμ.hasFDerivAt.sub ht.hasFDerivAt).sub hs.hasFDerivAt).fderiv
  change fderiv ℂ (fun q => P.physicalDirichletFrequency ((n:ℕ):ℤ) q-τ q-P.physicalDirichletRootCoefficient n q) 0 = _ at hb
  rw [hd,hb]
  simp only [sub_apply]
  rw [P.fderiv_physicalDirichletFrequency_zero_mean_zero h0 n h hh,
    P.fderiv_physicalFrequencyMidpoint_zero_mean_zero h0 n h hh,
    P.fderiv_physicalDirichletRootCoefficient_zero_apply h0 n h,
    P.physicalOnIndexAbelianCorrection_zero,mul_zero,Complex.exp_zero,mul_one]
  change -4*P.parent.parent.miuraBall.freeFrequencyMidpoint n*(_-0-_) = _
  have hτ : P.parent.parent.miuraBall.freeFrequencyMidpoint n ≠ 0 := fun hz =>
    (ne_of_gt (P.parent.parent.miuraBall.freeFrequencyMidpoint_pos
      (P.parent.subset (P.subset h0)).1 n)) (by rw [hz]; rfl)
  field_simp [hτ]
  ring

theorem fderiv_physicalOnIndexCartesianMinus_zero_mean_zero (P : HillProductEquationPatch)
    (h0 : (0 : PeriodOneHminusOne) ∈ P.source) (n : ℕ+) (h : PeriodOneHminusOne) (hh : h.val 0=0) :
    (fderiv ℂ (P.physicalOnIndexCartesianMinus n) 0) h=2*h.val (n:ℤ) := by
  have hr : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have hp := P.real_mem_physicalDirichletSource 0 h0 hr
  let τ := fun q => sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)
  have ht := (P.analytic_abelianGapMidpoint n 0 h0).differentiableAt
  have hμ := (P.analytic_physicalDirichletFrequency ((n:ℕ):ℤ) 0 h0).differentiableAt
  have hs := (P.analytic_physicalDirichletRootCoefficient n 0 hp).differentiableAt
  have hc : DifferentiableAt ℂ (fun q => Complex.exp (-I*P.physicalOnIndexAbelianCorrection n q)) 0 :=
    (analyticAt_const.mul (P.analytic_physicalOnIndexAbelianCorrection n 0 hp)).cexp.differentiableAt
  have hz : P.physicalDirichletFrequency ((n:ℕ):ℤ) 0-τ 0+P.physicalDirichletRootCoefficient n 0=0 := by
    rw [P.physicalDirichletFrequency_zero_eq_midpoint h0 n,P.physicalDirichletRootCoefficient_zero]
    change τ 0-τ 0+0=0
    ring
  have hd := fderiv_three_factors_apply_of_middle_zero (fun q => (-4:ℂ)*τ q)
    (fun q => P.physicalDirichletFrequency ((n:ℕ):ℤ) q-τ q+P.physicalDirichletRootCoefficient n q)
    (fun q => Complex.exp (-I*P.physicalOnIndexAbelianCorrection n q)) 0 h
    ((hasFDerivAt_const (-4:ℂ) (0:PeriodOneHminusOne)).differentiableAt.mul ht) ((hμ.sub ht).add hs) hc hz
  change (fderiv ℂ (P.physicalOnIndexCartesianMinus n) 0) h = _ at hd
  have hb := ((hμ.hasFDerivAt.sub ht.hasFDerivAt).add hs.hasFDerivAt).fderiv
  change fderiv ℂ (fun q => P.physicalDirichletFrequency ((n:ℕ):ℤ) q-τ q+P.physicalDirichletRootCoefficient n q) 0 = _ at hb
  rw [hd,hb]
  simp only [add_apply,sub_apply]
  rw [P.fderiv_physicalDirichletFrequency_zero_mean_zero h0 n h hh,
    P.fderiv_physicalFrequencyMidpoint_zero_mean_zero h0 n h hh,
    P.fderiv_physicalDirichletRootCoefficient_zero_apply h0 n h,
    P.physicalOnIndexAbelianCorrection_zero,mul_zero,Complex.exp_zero,mul_one]
  change -4*P.parent.parent.miuraBall.freeFrequencyMidpoint n*(_-0+_) = _
  have hτ : P.parent.parent.miuraBall.freeFrequencyMidpoint n ≠ 0 := fun hz =>
    (ne_of_gt (P.parent.parent.miuraBall.freeFrequencyMidpoint_pos
      (P.parent.subset (P.subset h0)).1 n)) (by rw [hz]; rfl)
  field_simp [hτ]
  ring

end NLS.KdV.HillProductEquationPatch
