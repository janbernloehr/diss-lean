import NLS.MKdV.L2QuasiHillWeakEquation
import NLS.Fourier.IntervalL2Products

/-! # Analytic dependence of the weak Miura form on the rough L2 lift

For fixed H1 test curves, the factored form is a quadratic polynomial in
the original physical L2 profile and affine in the constant energy shift.
This is genuine norm analyticity, using the actual bilinear L2 integral.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open NLS.LinearVolterra NLS.ZakharovShabat NLS.Fourier
namespace NLS.MKdV

theorem shiftedMiuraWeakForm_eq_intervalL2Bilinear (u : IntervalL2) (c : ℂ) (y φ : Curve ℂ)
    (hy₂ : MemLp (deriv (extend y)) 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hφ₂ : MemLp (deriv (extend φ)) 2 (volume.restrict (Ioc (0 : ℝ) 1))) :
    shiftedMiuraWeakForm u c y φ =
      intervalL2Bilinear (hy₂.toLp (deriv (extend y))-intervalCurveMulCLM y u)
        (hφ₂.toLp (deriv (extend φ))-intervalCurveMulCLM φ u)-
          c*(∫ s in (0 : ℝ)..1, extend y s*extend φ s) := by
  rw [shiftedMiuraWeakForm,intervalL2Bilinear_eq_integral]
  congr 1
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  filter_upwards [hy₂.coeFn_toLp,hφ₂.coeFn_toLp,
    intervalCurveMul_representative y u,intervalCurveMul_representative φ u,
    Lp.coeFn_sub (hy₂.toLp _) (intervalCurveMulCLM y u),
    Lp.coeFn_sub (hφ₂.toLp _) (intervalCurveMulCLM φ u)] with s hy hφ huy huφ hs₁ hs₂
  rw [hs₁,hs₂]
  simp only [Pi.sub_apply,intervalCurveMulCLM_apply]
  rw [hy,hφ,huy,huφ]

theorem analyticOnNhd_shiftedMiuraWeakForm (y φ : Curve ℂ)
    (hy₂ : MemLp (deriv (extend y)) 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hφ₂ : MemLp (deriv (extend φ)) 2 (volume.restrict (Ioc (0 : ℝ) 1))) :
    AnalyticOnNhd ℂ (fun p : ℂ × IntervalL2 => shiftedMiuraWeakForm p.2 p.1 y φ) univ := by
  intro p _
  have hy : AnalyticAt ℂ (fun p : ℂ × IntervalL2 => hy₂.toLp (deriv (extend y))-intervalCurveMulCLM y p.2) p :=
    analyticAt_const.sub ((intervalCurveMulCLM y).analyticAt p.2 |>.comp analyticAt_snd)
  have hφ : AnalyticAt ℂ (fun p : ℂ × IntervalL2 => hφ₂.toLp (deriv (extend φ))-intervalCurveMulCLM φ p.2) p :=
    analyticAt_const.sub ((intervalCurveMulCLM φ).analyticAt p.2 |>.comp analyticAt_snd)
  have hb := (intervalL2Bilinear.analyticAt_bilinear _).comp₂ hy hφ
  have hs : AnalyticAt ℂ (fun p : ℂ × IntervalL2 => p.1*(∫ s in (0 : ℝ)..1, extend y s*extend φ s)) p :=
    analyticAt_fst.mul analyticAt_const
  have h := hb.sub hs
  exact h.congr (Filter.Eventually.of_forall (fun q =>
    (shiftedMiuraWeakForm_eq_intervalL2Bilinear q.2 q.1 y φ hy₂ hφ₂).symm))

end NLS.MKdV
