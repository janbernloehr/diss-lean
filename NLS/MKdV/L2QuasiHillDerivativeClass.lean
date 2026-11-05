import NLS.MKdV.L2QuasiHillRegularity
import NLS.Fourier.IntervalCurveL2

/-! # Analytic physical L2 classes of rough Hill position derivatives

The derivative is u*y+w in the actual physical quotient. Joint bounded
multiplication upgrades the position's uniform analyticity to the full
H1 graph, without differentiating representatives pointwise in parameters.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open NLS.LinearVolterra NLS.ZakharovShabat NLS.Fourier
namespace NLS.MKdV

def l2QuasiHillPositionDerivativeClass (u : IntervalL2) (mu : ℂ) (v : ℂ × ℂ) : IntervalL2 :=
  intervalCurveMultiplication (l2QuasiHillPosition u mu v) u+
    intervalCurveL2 (l2QuasiHillMomentum u mu v)

theorem l2QuasiHillPositionDerivativeClass_representative (u : IntervalL2) (mu : ℂ) (v : ℂ × ℂ) :
    l2QuasiHillPositionDerivativeClass u mu v =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      deriv (extend (l2QuasiHillPosition u mu v)) := by
  filter_upwards [Lp.coeFn_add (intervalCurveMultiplication (l2QuasiHillPosition u mu v) u)
      (intervalCurveL2 (l2QuasiHillMomentum u mu v)),
    intervalCurveMul_representative (l2QuasiHillPosition u mu v) u,
    intervalCurveL2_representative (l2QuasiHillMomentum u mu v),ae_deriv_l2QuasiHillPosition u mu v]
    with s ha hm hw hd
  dsimp only [l2QuasiHillPositionDerivativeClass]
  rw [ha]
  simp only [Pi.add_apply,intervalCurveMultiplication_apply] at *
  rw [hm,hw,hd]

theorem analyticOnNhd_l2QuasiHillPositionDerivativeClass_joint (v : ℂ × ℂ) :
    AnalyticOnNhd ℂ (fun p : ℂ × IntervalL2 => l2QuasiHillPositionDerivativeClass p.2 p.1 v) univ := by
  intro p _
  have hsol := analyticOnNhd_l2QuasiHillSolution_joint v p (mem_univ _)
  have hy := ((ContinuousLinearMap.compLeftContinuous ℂ (Icc (0 : ℝ) 1)
    (ContinuousLinearMap.fst ℂ ℂ ℂ)).analyticAt _).comp hsol
  have hw := ((ContinuousLinearMap.compLeftContinuous ℂ (Icc (0 : ℝ) 1)
    (ContinuousLinearMap.snd ℂ ℂ ℂ)).analyticAt _).comp hsol
  exact ((intervalCurveMultiplication.analyticAt_bilinear _).comp₂ hy analyticAt_snd).add
    ((intervalCurveL2.analyticAt _).comp hw)

end NLS.MKdV
