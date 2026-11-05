import NLS.KdV.HillMeanZeroTraceProductDecay
import NLS.KdV.HillActionVariationPeriods
import NLS.KdV.HillComplexEntirePeriodInterpolation
import Mathlib.Analysis.Calculus.FDeriv.Analytic

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

theorem analyticOnNhd_hillL2Discriminant_source_variation (p h : Coeff 2) :
    AnalyticOnNhd ℂ (fun E => (fderiv ℂ (fun a : Coeff 2 => hillL2Discriminant a E) p) h) univ := by
  have he (E : ℂ) : (fderiv ℂ (fun t : ℂ × Coeff 2 => hillL2Discriminant t.2 t.1) (E,p)) (0,h) =
      (fderiv ℂ (fun a : Coeff 2 => hillL2Discriminant a E) p) h := by
    have hd := (analyticOnNhd_hillL2Discriminant_joint (E,p) (mem_univ _)).differentiableAt.hasFDerivAt.comp p
      (hasFDerivAt_prodMk_right E p)
    exact (congrArg (fun T : Coeff 2 →L[ℂ] ℂ => T h) hd.fderiv).symm
  intro E _
  simp_rw [←he]
  have hd := (analyticOnNhd_hillL2Discriminant_joint (E,p) (mem_univ _)).fderiv
  have hc := hd.comp (f := fun E : ℂ => (E,p)) (analyticAt_id.prod analyticAt_const)
  let ev : ((ℂ × Coeff 2) →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ (0,h)
  exact (ev.analyticAt _).comp hc

theorem hillL2Discriminant_source_variation_periodDouble (p h : Coeff 2) (E : ℂ) :
    (fderiv ℂ (fun a : Coeff 2 => hillL2Discriminant a E) (Coeff.periodDouble p)) (Coeff.periodDouble h) =
      (fderiv ℂ (fun a : Coeff 2 => hillL2Discriminant (Coeff.periodDouble a) E) p) h := by
  have hD := (analyticOnNhd_hillL2Discriminant_joint (E,Coeff.periodDouble p) (mem_univ _)).comp
    (f := fun a : Coeff 2 => (E,a)) (analyticAt_const.prod analyticAt_id)
  have hd := hD.differentiableAt.hasFDerivAt.comp p
    (Coeff.periodDouble.toContinuousLinearMap.hasFDerivAt (x := p))
  exact (congrArg (fun T : Coeff 2 →L[ℂ] ℂ => T h) hd.fderiv).symm

/-- At the ORIGINAL real source, every even complex mean-zero L2
vector annihilating ALL original actions annihilates the discriminant at
EVERY complex energy. Closed and low gaps are included. -/
theorem hillOriginalTrace_variation_zero_of_mean_zero_action_kernel
    (q : RealPeriodOneHillPotential) (h : Coeff 2)
    (heven : h ∈ Coeff.paritySubspace 0) (hzero : h 0 = 0)
    (hkernel : ∀ n : ℕ+, (fderiv ℂ (hillRealSourceMoment q.val q.property.1 q.property.2 n 0)
      (SpectralWeight.one.toCoeff q.val)) h = 0) (E : ℂ) :
    (fderiv ℂ (fun a : Coeff 2 => hillL2Discriminant a E)
      (SpectralWeight.one.toCoeff q.val)) h = 0 := by
  let p := Coeff.periodHalve (SpectralWeight.one.toCoeff q.val)
  let v := Coeff.periodHalve h
  have hp : Coeff.periodDouble p = SpectralWeight.one.toCoeff q.val :=
    (Coeff.periodDouble_periodHalve _).trans
      ((Coeff.parityProjection_eq_self_iff 0 _).mpr q.property.1)
  have hv : Coeff.periodDouble v = h :=
    (Coeff.periodDouble_periodHalve _).trans
      ((Coeff.parityProjection_eq_self_iff 0 _).mpr heven)
  have hv0 : v 0 = 0 := by simpa only [v,Coeff.periodHalve_apply,mul_zero] using hzero
  have hi (w : ℂ) : (fderiv ℂ (fun a : Coeff 2 => hillL2Discriminant a w)
      (SpectralWeight.one.toCoeff q.val)) h =
      (fderiv ℂ (fun a : Coeff 2 => hillL2Discriminant (Coeff.periodDouble a) w) p) v := by
    rw [←hp,←hv]
    exact hillL2Discriminant_source_variation_periodDouble p v w
  have hall := complex_entire_eq_zero_of_hill_periods_and_product_decay
    q.val q.property.1 q.property.2
    (fun w => (fderiv ℂ (fun a : Coeff 2 => hillL2Discriminant a w)
      (SpectralWeight.one.toCoeff q.val)) h)
    (analyticOnNhd_hillL2Discriminant_source_variation _ h)
    (hillTraceVariation_periods_zero_of_action_kernel q h hkernel) (by
      intro roots hroots ε hε
      have hb := eventually_hillMeanZeroTraceVariation_div_full_product_le q p v hv0 roots hroots ε hε
      simpa only [←hi] using hb)
  exact congrFun hall E

end NLS.KdV
