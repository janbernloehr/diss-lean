import NLS.KdV.HillPhysicalFreeRootMultiplier
import NLS.KdV.HillNativeNormingFirstVariation

/-! Exact ACTUAL auxiliary frequency derivative at zero. The positive
quadratic energy branch is the already constructed physical divisor,
not a substituted square-root coordinate. -/
noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV.HillProductEquationPatch

theorem fderiv_physicalDirichletFrequency_zero_apply (P : HillProductEquationPatch)
    (h0 : (0 : PeriodOneHminusOne) ∈ P.source) (n : ℕ+) (h : PeriodOneHminusOne) :
    (fderiv ℂ (P.physicalDirichletFrequency ((n:ℕ):ℤ)) 0) h =
      (h.val 0-(h.val (n:ℤ)+h.val (-(n:ℤ)))/2)/
        (2*P.parent.parent.miuraBall.freeFrequencyMidpoint n) := by
  have hf := (P.analytic_physicalDirichletFrequency ((n:ℕ):ℤ) 0 h0).differentiableAt
  have he : hillHminusCanonicalDirichlet n =ᶠ[𝓝 0] fun q =>
      P.physicalDirichletFrequency ((n:ℕ):ℤ) q^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ) := by
    filter_upwards [P.source_open.mem_nhds h0] with q hq
    exact (P.physicalDirichletFrequency_energy n q hq).symm
  have hb := fderiv_square_energy_apply _ _ 0 h _ hf he
  rw [fderiv_hillHminusCanonicalDirichlet_zero,hillFreeDirichletGradient_apply,
    P.physicalDirichletFrequency_zero_eq_midpoint h0 n] at hb
  have ht : P.parent.parent.miuraBall.freeFrequencyMidpoint n ≠ 0 := fun hz =>
    (ne_of_gt (P.parent.parent.miuraBall.freeFrequencyMidpoint_pos
      (P.parent.subset (P.subset h0)).1 n)) (by rw [hz]; rfl)
  apply (eq_div_iff (mul_ne_zero (by norm_num) ht)).2
  calc
    _ = 2*P.parent.parent.miuraBall.freeFrequencyMidpoint n*
        ((fderiv ℂ (P.physicalDirichletFrequency ((n:ℕ):ℤ)) 0) h) := by ring
    _ = _ := hb.symm

theorem fderiv_physicalDirichletFrequency_zero_mean_zero (P : HillProductEquationPatch)
    (h0 : (0 : PeriodOneHminusOne) ∈ P.source) (n : ℕ+) (h : PeriodOneHminusOne) (hh : h.val 0=0) :
    (fderiv ℂ (P.physicalDirichletFrequency ((n:ℕ):ℤ)) 0) h =
      -(h.val (n:ℤ)+h.val (-(n:ℤ)))/(4*P.parent.parent.miuraBall.freeFrequencyMidpoint n) := by
  rw [P.fderiv_physicalDirichletFrequency_zero_apply h0 n h,hh]
  ring

theorem fderiv_physicalFrequencyMidpoint_zero_mean_zero (P : HillProductEquationPatch)
    (h0 : (0 : PeriodOneHminusOne) ∈ P.source) (n : ℕ+) (h : PeriodOneHminusOne) (hh : h.val 0=0) :
    (fderiv ℂ (fun q => sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) (n:ℕ)) 0) h=0 := by
  exact (P.parent.parent.miuraBall.actionBall.fderiv_diracSource_free_symmetric_mean_zero
    (P.parent.subset (P.subset h0)).1 h hh (n:ℕ)).1

end NLS.KdV.HillProductEquationPatch
