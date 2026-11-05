import NLS.KdV.HillHminusOneWeakPotentialFunctional
import NLS.Fourier.PeriodOneMassPhysical
import NLS.Fourier.IntervalCurveL2

/-! # An intrinsic resolvent formula for the original H^-1 potential pairing

Writing q=(d/dx+m+1)U gives <q,g>=<U,(m+1)g-g'> on
periodic H1 test products. The formula is proved for the actual physical
classes by integration by parts and then in H^-1 by density. Its graph
variables are jointly analytic and do not contain a Riccati lift.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open NLS.LinearVolterra NLS.ZakharovShabat NLS.Fourier NLS.MKdV NLS.FunctionalAnalysis
namespace NLS.KdV

def hillHminusMassProfile (m : ℕ) : PeriodOneHminusOne →L[ℂ] IntervalL2 :=
  unitL2SynthesisEquiv.toContinuousLinearEquiv.toContinuousLinearMap.comp (periodOneMassInverse m)

def hillHminusMassPotential (m : ℕ) (q : PeriodOneHminusOne) (g : Curve ℂ) (dg : IntervalL2) : ℂ :=
  intervalL2Bilinear (hillHminusMassProfile m q)
    (((((m : ℝ)+1 : ℝ) : ℂ)) • intervalCurveL2 g-dg)

theorem analyticOnNhd_hillHminusMassPotential_joint (m : ℕ) :
    AnalyticOnNhd ℂ (fun p : PeriodOneHminusOne × (Curve ℂ × IntervalL2) =>
      hillHminusMassPotential m p.1 p.2.1 p.2.2) univ := by
  intro p _
  have hU : AnalyticAt ℂ (fun a : PeriodOneHminusOne × (Curve ℂ × IntervalL2) =>
      hillHminusMassProfile m a.1) p :=
    ((hillHminusMassProfile m).analyticAt _).comp analyticAt_fst
  have hg0 : AnalyticAt ℂ (fun p : PeriodOneHminusOne × (Curve ℂ × IntervalL2) => p.2.1) p :=
    analyticAt_fst.comp (f := Prod.snd) analyticAt_snd
  have hg := (intervalCurveL2.analyticAt _).comp hg0
  have hd : AnalyticAt ℂ (fun p : PeriodOneHminusOne × (Curve ℂ × IntervalL2) => p.2.2) p :=
    analyticAt_snd.comp (f := Prod.snd) analyticAt_snd
  exact (intervalL2Bilinear.analyticAt_bilinear _).comp₂ hU
    ((hg.const_smul (c := ((((m : ℝ)+1 : ℝ) : ℂ)))).sub hd)

theorem mass_potential_integral_by_parts (m : ℕ) (a : ScalarDomain 2) (g : Curve ℂ)
    (hg : AbsolutelyContinuousOnInterval (extend g) 0 1)
    (hg₂ : MemLp (deriv (extend g)) 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hend : extend g 1 = extend g 0) :
    (∫ s in (0 : ℝ)..1,
      unitL2SynthesisEquiv (periodOneDerivative a+(((m : ℝ)+1 : ℝ) : ℂ) • scalarInclusion a) s*extend g s) =
      intervalL2Bilinear (unitL2SynthesisEquiv (scalarInclusion a))
        (((((m : ℝ)+1 : ℝ) : ℂ)) • intervalCurveL2 g-hg₂.toLp (deriv (extend g))) := by
  let U : ℝ → ℂ := fun s => periodOneSobolevSynthesis a (s : AddCircle (2 : ℝ))
  let c : ℂ := (((m : ℝ)+1 : ℝ) : ℂ)
  have hU := absolutelyContinuous_periodOneSobolevSynthesis a
  have hUc := continuous_periodOneSobolevSynthesis a
  have hdU := intervalIntegrable_deriv_periodOneSobolevSynthesis a
  change AbsolutelyContinuousOnInterval U 0 1 at hU
  change Continuous U at hUc
  change IntervalIntegrable (deriv U) volume 0 1 at hdU
  have hdg := intervalIntegrable_of_memLp_two hg₂
  have hdug := hdU.mul_continuousOn (continuous_extend g).continuousOn
  have hUdg := hdg.continuousOn_mul hU.continuousOn
  have hUg : IntervalIntegrable (fun s => U s*extend g s) volume 0 1 :=
    (hUc.mul (continuous_extend g)).intervalIntegrable (μ := volume) 0 1
  have hip := integral_mul_deriv_eq_complex hU hg hdU hdg
  have hbound : U 1*extend g 1-U 0*extend g 0 = 0 := by
    rw [show U 1 = U 0 from by simpa only [zero_add] using periodOneSobolevSynthesis_periodic a 0,hend,sub_self]
  change (∫ s in (0 : ℝ)..1, U s*deriv (extend g) s) =
    U 1*extend g 1-U 0*extend g 0-(∫ s in (0 : ℝ)..1, deriv U s*extend g s) at hip
  rw [hbound,zero_sub] at hip
  have hleft : (∫ s in (0 : ℝ)..1,
      unitL2SynthesisEquiv (periodOneDerivative a+c • scalarInclusion a) s*extend g s) =
      (∫ s in (0 : ℝ)..1, deriv U s*extend g s)+c*(∫ s in (0 : ℝ)..1, U s*extend g s) := by
    calc
      _ = ∫ s in (0 : ℝ)..1, deriv U s*extend g s+c*(U s*extend g s) := by
        apply intervalIntegral.integral_congr_ae_restrict
        rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        filter_upwards [unitL2Synthesis_mass_representative m a] with s hs
        rw [hs]
        ring
      _ = _ := by rw [intervalIntegral.integral_add hdug (hUg.const_mul c),intervalIntegral.integral_const_mul]
  have hright : intervalL2Bilinear (unitL2SynthesisEquiv (scalarInclusion a))
      (c • intervalCurveL2 g-hg₂.toLp (deriv (extend g))) =
      c*(∫ s in (0 : ℝ)..1, U s*extend g s)-(∫ s in (0 : ℝ)..1, U s*deriv (extend g) s) := by
    rw [intervalL2Bilinear_eq_integral]
    calc
      _ = ∫ s in (0 : ℝ)..1, c*(U s*extend g s)-U s*deriv (extend g) s := by
        apply intervalIntegral.integral_congr_ae_restrict
        rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        filter_upwards [unitL2Synthesis_scalarInclusion_representative a,
          intervalCurveL2_representative g,hg₂.coeFn_toLp,
          Lp.coeFn_sub (c • intervalCurveL2 g) (hg₂.toLp _),Lp.coeFn_smul c (intervalCurveL2 g)]
          with s hu hg hd hs hsm
        rw [hu,hs]
        simp only [Pi.sub_apply,hsm,Pi.smul_apply,smul_eq_mul,hg,hd]
        ring
      _ = _ := by rw [intervalIntegral.integral_sub (hUg.const_mul c) hUdg,intervalIntegral.integral_const_mul]
  change _ = intervalL2Bilinear _ (c • intervalCurveL2 g-hg₂.toLp _)
  rw [hleft,hright,hip]
  ring

theorem hillHminusWeakPotential_eq_mass (m : ℕ) (q : PeriodOneHminusOne) (y φ : Curve ℂ)
    (hy : AbsolutelyContinuousOnInterval (extend y) 0 1)
    (hφ : AbsolutelyContinuousOnInterval (extend φ) 0 1)
    (hy₂ : MemLp (deriv (extend y)) 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hφ₂ : MemLp (deriv (extend φ)) 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hend : extend y 1*extend φ 1 = extend y 0*extend φ 0) :
    hillHminusWeakPotential q y φ = hillHminusMassPotential m q (y*φ)
      ((memLp_deriv_curve_mul y φ hy hφ hy₂ hφ₂).toLp (deriv (extend (y*φ)))) := by
  let hg₂ := memLp_deriv_curve_mul y φ hy hφ hy₂ hφ₂
  let T : IntervalL2 := ((((m : ℝ)+1 : ℝ) : ℂ)) • intervalCurveL2 (y*φ)-hg₂.toLp (deriv (extend (y*φ)))
  have hL : Continuous (fun a : Coeff 2 => hillHminusWeakPotential (periodOneMassOperator m a) y φ) :=
    (continuous_hillHminusWeakPotential y φ hy hφ hy₂ hφ₂ hend).comp (periodOneMassOperator m).continuous
  have hR : Continuous (fun a : Coeff 2 => intervalL2Bilinear (unitL2SynthesisEquiv a) T) :=
    ((intervalL2Bilinear.flip T).continuous.comp unitL2SynthesisEquiv.continuous)
  have he : (fun a : Coeff 2 => hillHminusWeakPotential (periodOneMassOperator m a) y φ) =
      (fun a : Coeff 2 => intervalL2Bilinear (unitL2SynthesisEquiv a) T) := by
    apply (scalarInclusion_denseRange (p := 2) (by simp)).equalizer hL hR
    funext a
    dsimp only [Function.comp_def]
    rw [periodOneMassOperator_scalarInclusion,
      hillHminusWeakPotential_eq_physicalL2 y φ hy hφ hy₂ hφ₂ hend,physicalL2HillPotentialPairing_apply]
    exact mass_potential_integral_by_parts m a (y*φ) (absolutelyContinuous_curve_mul y φ hy hφ) hg₂ hend
  have h := congrFun he (periodOneMassInverse m q)
  rw [periodOneMassOperator_inverse] at h
  exact h

end NLS.KdV
