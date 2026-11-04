import NLS.ComplexAnalysis.MixedSpectralSourceDerivative
import NLS.ComplexAnalysis.QuotientDerivative

/-! # Variations of a trace and its nonvanishing square root

The actual relation R squared = Delta squared minus four determines the
root derivative and makes the varied trace differential an exact energy
derivative. No choice of a primitive or logarithm is assumed.
-/
noncomputable section
open Set Complex Filter Topology
namespace NLS.ComplexAnalysis
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]

/-- The root identity determines every derivative of a nonzero trace root. -/
theorem fderiv_trace_root_apply (D R : A → ℂ) (a v : A)
    (hD : DifferentiableAt ℂ D a) (hR : DifferentiableAt ℂ R a) (hne : R a≠0)
    (hsq : ∀ᶠ p in 𝓝 a, R p^2=D p^2-4) :
    (fderiv ℂ R a) v=D a*((fderiv ℂ D a) v)/R a := by
  have he : (fun p => R p*R p) =ᶠ[𝓝 a] (fun p => D p*D p-4) := by
    filter_upwards [hsq] with p hp
    simpa only [pow_two] using hp
  have hd := congrArg (fun L : A →L[ℂ] ℂ => L v) he.fderiv_eq
  rw [(hR.hasFDerivAt.fun_mul hR.hasFDerivAt).fderiv,
    ((hD.hasFDerivAt.fun_mul hD.hasFDerivAt).sub_const 4).fderiv] at hd
  simp only [add_apply,smul_apply,smul_eq_mul] at hd
  apply (eq_div_iff hne).mpr
  linear_combination hd/2

/-- Source evaluation of a joint analytic derivative is analytic in energy. -/
theorem analyticOnNhd_source_fderiv_apply (F : ℂ × A → ℂ) (U : Set (ℂ × A))
    (hU : IsOpen U) (hF : AnalyticOnNhd ℂ F U) (a h : A) :
    AnalyticOnNhd ℂ (fun z => (fderiv ℂ (fun p : A => F (z,p)) a) h)
      {z | (z,a)∈U} := by
  let ev : ((ℂ × A) →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ (0,h)
  have hJ := ev.comp_analyticOnNhd hF.fderiv
  intro z hz
  have he : (fun w => (fderiv ℂ (fun p : A => F (w,p)) a) h) =ᶠ[𝓝 z]
      (fun w => (fderiv ℂ F (w,a)) (0,h)) := by
    filter_upwards [(hU.preimage (continuous_id.prodMk continuous_const)).mem_nhds hz] with w hw
    rw [fderiv_source_section_eq_joint F w a (hF _ hw).differentiableAt]
    simp
  exact ((hJ (z,a) hz).comp (f := fun w : ℂ => (w,a))
    (analyticAt_id.prod analyticAt_const)).congr he.symm

/-- The variation of the trace differential is an exact energy derivative. -/
theorem fderiv_trace_differential_eq_deriv_source_quotient
    (D R : ℂ × A → ℂ) (U : Set (ℂ × A)) (hU : IsOpen U)
    (hD : AnalyticOnNhd ℂ D U) (hR : AnalyticOnNhd ℂ R U)
    (hne : ∀ t∈U, R t≠0) (hsq : ∀ t∈U, R t^2=D t^2-4)
    (z : ℂ) (a h : A) (hza : (z,a)∈U) :
    (fderiv ℂ (fun p : A => deriv (fun w : ℂ => D (w,p)) z/R (z,p)) a) h =
      deriv (fun w : ℂ => (fderiv ℂ (fun p : A => D (w,p)) a) h/R (w,a)) z := by
  have hDs := (hD (z,a) hza).comp (f := fun p : A => (z,p)) (analyticAt_const.prod analyticAt_id)
  have hRs := (hR (z,a) hza).comp (f := fun p : A => (z,p)) (analyticAt_const.prod analyticAt_id)
  have hDz := (hD (z,a) hza).comp (f := fun w : ℂ => (w,a)) (analyticAt_id.prod analyticAt_const)
  have hRz := (hR (z,a) hza).comp (f := fun w : ℂ => (w,a)) (analyticAt_id.prod analyticAt_const)
  have hN := ((analyticOnNhd_spectral_deriv_of_analyticOnNhd D U hU hD) (z,a) hza).comp
    (f := fun p : A => (z,p)) (analyticAt_const.prod analyticAt_id)
  have hJ := (analyticOnNhd_source_fderiv_apply D U hU hD a h z hza).differentiableAt
  have hs : ∀ᶠ p in 𝓝 a, R (z,p)^2=D (z,p)^2-4 := by
    filter_upwards [(hU.preimage (continuous_const.prodMk continuous_id)).mem_nhds hza] with p hp
    exact hsq _ hp
  have hz : ∀ᶠ w in 𝓝 z, R (w,a)^2=D (w,a)^2-4 := by
    filter_upwards [(hU.preimage (continuous_id.prodMk continuous_const)).mem_nhds hza] with w hw
    exact hsq _ hw
  have hRs' := fderiv_trace_root_apply (fun p : A => D (z,p)) (fun p : A => R (z,p)) a h
    hDs.differentiableAt hRs.differentiableAt (hne _ hza) hs
  have hRz' : deriv (fun w : ℂ => R (w,a)) z=
      D (z,a)*deriv (fun w : ℂ => D (w,a)) z/R (z,a) := by
    simpa only [fderiv_apply_one_eq_deriv] using
      fderiv_trace_root_apply (fun w : ℂ => D (w,a)) (fun w : ℂ => R (w,a)) z 1
        hDz.differentiableAt hRz.differentiableAt (hne _ hza) hz
  rw [fderiv_div_apply (fun p : A => deriv (fun w : ℂ => D (w,p)) z) (fun p : A => R (z,p)) a hN.differentiableAt hRs.differentiableAt (hne _ hza) h,
    fderiv_source_deriv_spectral_eq_deriv_spectral_fderiv_source D U hU hD z a hza h,
    deriv_fun_div (c := fun w : ℂ => (fderiv ℂ (fun p : A => D (w,p)) a) h) (d := fun w : ℂ => R (w,a)) hJ hRz.differentiableAt (hne _ hza),hRs',hRz']
  ring
end NLS.ComplexAnalysis
