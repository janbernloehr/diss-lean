import NLS.Fourier.UnitIntervalL2Equiv
import NLS.Fourier.IntervalBilinearParseval
import NLS.SequenceSpaces.ConjugateDuality
import NLS.SequenceSpaces.Reflection
import NLS.ZakharovShabat.L2ScalarVolterra

/-! # Bounded physical bilinear products on the unit interval

The unconjugated L2 pairing is the actual Lebesgue integral. A fixed
continuous interval curve acts by bounded complex-linear multiplication
on physical L2 classes. All representative identities are a.e. identities.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.Fourier

def intervalL2Bilinear : IntervalL2 →L[ℂ] IntervalL2 →L[ℂ] ℂ :=
  let K := unitL2SynthesisEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap
  ((ContinuousLinearMap.compL ℂ IntervalL2 (Coeff 2) ℂ).flip K).comp
    (Coeff.dualPairing.comp (Coeff.reflection.toContinuousLinearEquiv.toContinuousLinearMap.comp K))

theorem intervalL2Bilinear_eq_integral (u v : IntervalL2) :
    intervalL2Bilinear u v = ∫ s in (0 : ℝ)..1, u s*v s := by
  change Coeff.dualPairing (Coeff.reflection (unitL2SynthesisEquiv.symm u))
    (unitL2SynthesisEquiv.symm v) = _
  rw [Coeff.dualPairing_apply]
  simp only [Coeff.reflection_apply,unitL2SynthesisEquiv_symm_coefficient,
    intervalFourierCoefficient_eq_fourierCoeffOn (by norm_num : (0 : ℝ) < 1)]
  simpa only [unitFourierCoefficient_eq_fourierCoeffOn] using
    tsum_bilinear_unitFourierCoefficient_of_memLp (Lp.memLp u) (Lp.memLp v)

theorem analyticOnNhd_intervalL2Bilinear :
    AnalyticOnNhd ℂ (fun p : IntervalL2 × IntervalL2 => intervalL2Bilinear p.1 p.2) univ :=
  fun p _ => intervalL2Bilinear.analyticAt_bilinear p

def intervalCurveMul (f : Curve ℂ) (u : IntervalL2) : IntervalL2 :=
  ((curveBoundedExtension ℂ f).memLp_top.mul (Lp.memLp u)).toLp
    (fun s => u s*NLS.LinearVolterra.extend f s)

theorem intervalCurveMul_representative (f : Curve ℂ) (u : IntervalL2) :
    intervalCurveMul f u =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] (fun s => u s*NLS.LinearVolterra.extend f s) :=
  ((curveBoundedExtension ℂ f).memLp_top.mul (Lp.memLp u)).coeFn_toLp

theorem norm_intervalCurveMul_le (f : Curve ℂ) (u : IntervalL2) :
    ‖intervalCurveMul f u‖ ≤ ‖f‖*‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [intervalCurveMul_representative f u] with s hs
  rw [hs,norm_mul]
  exact (mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (norm_nonneg _)).trans_eq (mul_comm _ _)

def intervalCurveMulCLM (f : Curve ℂ) : IntervalL2 →L[ℂ] IntervalL2 :=
  LinearMap.mkContinuous
    { toFun := intervalCurveMul f
      map_add' := by
        intro u v
        apply Lp.ext
        filter_upwards [intervalCurveMul_representative f (u+v),intervalCurveMul_representative f u,
          intervalCurveMul_representative f v,Lp.coeFn_add u v,Lp.coeFn_add (intervalCurveMul f u) (intervalCurveMul f v)]
          with s ha hu hv huv hsum
        simp only [ha,hsum,huv,Pi.add_apply,hu,hv,add_mul]
      map_smul' := by
        intro c u
        apply Lp.ext
        filter_upwards [intervalCurveMul_representative f (c • u),intervalCurveMul_representative f u,
          Lp.coeFn_smul c u,Lp.coeFn_smul c (intervalCurveMul f u)] with s hc hu hcu hres
        simp only [hc,hres,hcu,Pi.smul_apply,smul_eq_mul,hu,RingHom.id_apply,mul_assoc] }
    ‖f‖ (norm_intervalCurveMul_le f)

@[simp] theorem intervalCurveMulCLM_apply (f : Curve ℂ) (u : IntervalL2) :
    intervalCurveMulCLM f u = intervalCurveMul f u := rfl

end NLS.Fourier
