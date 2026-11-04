import NLS.KdV.HillHminusOneMiuraSheets

/-! Exact root normalization of ANY real shifted Miura realization of
zero Hill potential. The lift is not assumed to be zero or constant. -/
noncomputable section
open Set Complex NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

theorem classicalHillFreeRoot_eq_sine (μ : ℂ) :
    classicalHillFreeRoot μ = -2*I*sin (sqrt μ) := by
  change 2*sinh (-I*sqrt μ) = _
  rw [show -I*sqrt μ = -(sqrt μ*I) by ring,sinh_neg,sinh_mul_I]
  ring

theorem hillHminusContinuedRoot_zero_eq_freeRoot (μ : ℂ) :
    hillHminusContinuedRoot (μ,0)=classicalHillFreeRoot μ := by
  change hillHminusSourceFamily.root (μ,0)=_
  rw [TracePrimitiveFamily.root_base]
  rfl

theorem sourceCanonicalRoot_shifted_free_miura (u : PeriodOneRealL2) (c : ℝ)
    (hi : periodOneMiura u.val = periodOneL2Inclusion (lp.single 2 0 (c:ℂ)))
    (z : ℂ) (hzr : 0 < z.re) (hzi : z.im ≠ 0) :
    sourceCanonicalRoot (by norm_num) (by norm_num) (hillMiuraDiagonal u.val) z =
      -2*I*sin (sqrt (z^2-(c:ℂ))) := by
  have h := (hillHminus_shifted_miura_sheets u 0 c (by simpa only [zero_add] using hi) z hzr hzi).1
  rw [hillHminusContinuedRoot_zero_eq_freeRoot,classicalHillFreeRoot_eq_sine] at h
  exact h.symm

end NLS.KdV
