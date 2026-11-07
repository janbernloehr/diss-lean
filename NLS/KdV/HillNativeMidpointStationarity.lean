import NLS.KdV.HillMiuraFreeIsospectral
import NLS.KdV.HillCanonicalEnergyMidpoints
import NLS.ComplexAnalysis.QuadraticCoordinateVariation

/-! The ACTUAL native periodic energy midpoint is stationary at zero
in EVERY mean-zero complex H-minus-one direction. Actual local Miura
symmetric data agree with the canonical midpoint by real-form uniqueness. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV

theorem HillHminusMiuraGapBall.fderiv_energyMidpoint_free_mean_zero
    (B : HillHminusMiuraGapBall) (h0 : (0 : PeriodOneHminusOne) ∈ B.source)
    (h : PeriodOneHminusOne) (hh : h.val 0=0) (n : ℕ+) :
    (fderiv ℂ (B.energyMidpoint n) 0) h=0 := by
  let M : PeriodOneHminusOne → ℂ := fun q => sourceStandardRootMidpoint (by norm_num) (by norm_num)
    (B.actionBall.diracSource q) (n:ℕ)
  let G : PeriodOneHminusOne → ℂ := fun q => (canonicalPeriodicGap (by norm_num) (by norm_num)
    (periodOnePotential (B.actionBall.diracSource q)) (periodOnePotential_mem _) (n:ℕ))^2
  have hM : DifferentiableAt ℂ M 0 := (B.midpoint_analytic (n:ℕ) 0 h0).differentiableAt
  have hG : DifferentiableAt ℂ G 0 := (B.dirac_gap_square_analytic (n:ℕ) 0 h0).differentiableAt
  have hv := B.actionBall.fderiv_diracSource_free_symmetric_mean_zero h0 h hh (n:ℕ)
  have he : B.energyMidpoint n = fun q => M q^2+(1/4:ℂ)*G q-(B.actionBall.shift:ℂ) := by
    funext q
    change M q^2+G q/4-(B.actionBall.shift:ℂ) = _
    ring
  rw [he]
  have hd := fderiv_quadratic_coordinate_apply M G 0 h (1/4) (-(B.actionBall.shift:ℂ)) hM hG
  change (fderiv ℂ (fun q => M q^2+(1/4:ℂ)*G q-(B.actionBall.shift:ℂ)) 0) h = _ at hd
  rw [hd]
  change (fderiv ℂ M 0) h=0 ∧ (fderiv ℂ G 0) h=0 at hv
  rw [hv.1,hv.2,mul_zero,mul_zero,add_zero]

theorem HillHminusMiuraGapBall.canonical_energyMidpoint_eq_locally_zero
    (B : HillHminusMiuraGapBall) (h0 : (0 : PeriodOneHminusOne) ∈ B.source) (n : ℕ+) :
    hillHminusCanonicalEnergyMidpoint n =ᶠ[𝓝 0] B.energyMidpoint n := by
  have hr : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have hd := real_mem_hillHminusCanonicalZeroSequenceDomain 0 hr
  obtain ⟨r,hrpos,hsub⟩ := Metric.mem_nhds_iff.mp
    ((B.source_open.inter isOpen_hillHminusCanonicalZeroSequenceDomain).mem_nhds ⟨h0,hd⟩)
  have he : EqOn (hillHminusCanonicalEnergyMidpoint n) (B.energyMidpoint n) (ball 0 r) := by
    apply analytic_eqOn_of_real_periodOneHminus (ball 0 r) isOpen_ball
      (convex_ball 0 r).isPreconnected ⟨0,mem_ball_self hrpos,hr⟩
      (hillHminusCanonicalEnergyMidpoint n) (B.energyMidpoint n)
      ((analyticOnNhd_hillHminusCanonicalEnergyMidpoint n).mono (fun q hq => (hsub hq).2))
      ((B.analytic_energyMidpoint n).mono (fun q hq => (hsub hq).1))
    intro q hq hqr
    rw [hillHminusCanonicalEnergyMidpoint_real n q hqr,B.energyMidpoint_eq_real n q (hsub hq).1 hqr]
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hrpos)] with q hq
  exact he hq

theorem fderiv_hillHminusCanonicalEnergyMidpoint_zero_mean_zero (n : ℕ+)
    (h : PeriodOneHminusOne) (hh : h.val 0=0) :
    (fderiv ℂ (hillHminusCanonicalEnergyMidpoint n) 0) h=0 := by
  have hr : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  obtain ⟨B,hB⟩ := exists_hillHminusMiuraGapBall 0 hr
  rw [(B.canonical_energyMidpoint_eq_locally_zero hB n).fderiv_eq]
  exact B.fderiv_energyMidpoint_free_mean_zero hB h hh n

end NLS.KdV
