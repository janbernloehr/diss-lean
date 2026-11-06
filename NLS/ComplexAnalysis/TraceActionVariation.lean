import NLS.ComplexAnalysis.JointSpectralDerivativeAnalytic
import NLS.ComplexAnalysis.TraceRootVariation
import NLS.ComplexAnalysis.ParametricCircleStationarity
import NLS.ComplexAnalysis.CirclePolynomialIntegrationByParts

/-! # Differentiating the actual Arnold contour action

An analytic trace and a nonvanishing root of its radicand determine the
source derivative of the literal energy-weighted trace period. The
variation of the differential is exact in energy; closed-contour
integration by parts gives the negative unweighted trace variation.
-/
noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]

theorem fderiv_circleIntegral_apply_on_compact_contour
    (F : ℂ × A → ℂ) (U : Set (ℂ × A)) (hU : IsOpen U)
    (hF : AnalyticOnNhd ℂ F U) (c : ℂ) (r : ℝ) (hr : 0≤r) (a h : A)
    (hc : ∀ z∈sphere c r, (z,a)∈U) :
    (fderiv ℂ (fun p : A => ∮ z in C(c,r), F (z,p)) a) h=
      ∮ z in C(c,r), (fderiv ℂ (fun p : A => F (z,p)) a) h := by
  obtain ⟨W,hW,haW,M,_,hb⟩ := exists_uniform_joint_fderiv_bound_on_circle F U hU hF c r a hc
  exact fderiv_circleIntegral_apply_of_jointAnalytic F U hU hF c r hr W hW a haW M
    (fun p hp θ => (hb _ (circleMap_mem_sphere c hr θ) p hp).1)
    (fun p hp θ => (hb _ (circleMap_mem_sphere c hr θ) p hp).2) h

/-- The exact action derivative, before multiplication by the source's
factor `1/pi`. The root choice is retained without sign ambiguity. -/
theorem fderiv_arnold_trace_period_apply
    (D R : ℂ × A → ℂ) (U : Set (ℂ × A)) (hU : IsOpen U)
    (hD : AnalyticOnNhd ℂ D U) (hR : AnalyticOnNhd ℂ R U)
    (hne : ∀ t∈U, R t≠0) (hsq : ∀ t∈U, R t^2=D t^2-4)
    (c : ℂ) (r : ℝ) (hr : 0≤r) (a h : A)
    (hc : ∀ z∈sphere c r, (z,a)∈U) :
    (fderiv ℂ (fun p : A => ∮ z in C(c,r),
      z*deriv (fun w : ℂ => D (w,p)) z/R (z,p)) a) h=
      -(∮ z in C(c,r), (fderiv ℂ (fun p : A => D (z,p)) a) h/R (z,a)) := by
  let F : ℂ × A → ℂ := fun t => t.1*(deriv (fun w : ℂ => D (w,t.2)) t.1/R t)
  have hF : AnalyticOnNhd ℂ F U := fun t ht => analyticAt_fst.mul
    (((analyticOnNhd_spectral_deriv_of_analyticOnNhd D U hU hD) t ht).div (hR t ht) (hne t ht))
  have he : (fun p : A => ∮ z in C(c,r), z*deriv (fun w : ℂ => D (w,p)) z/R (z,p))=
      (fun p : A => ∮ z in C(c,r), F (z,p)) := by
    funext p
    congr 1
    funext z
    exact mul_div_assoc _ _ _
  rw [he,fderiv_circleIntegral_apply_on_compact_contour F U hU hF c r hr a h hc]
  let J : ℂ → ℂ := fun z => (fderiv ℂ (fun p : A => D (z,p)) a) h/R (z,a)
  have hJ : AnalyticOnNhd ℂ J {z | (z,a)∈U} := by
    intro z hz
    exact (analyticOnNhd_source_fderiv_apply D U hU hD a h z hz).div
      ((hR (z,a) hz).comp (f := fun w : ℂ => (w,a)) (analyticAt_id.prod analyticAt_const)) (hne _ hz)
  have hparts := circleIntegral_pow_mul_deriv_eq_neg J {z | (z,a)∈U} hJ c r hr hc 0
  simp only [zero_add,pow_one,pow_zero,one_mul,neg_mul] at hparts
  calc
    _ = ∮ z in C(c,r), z*deriv J z := by
      apply circleIntegral.integral_congr hr
      intro z hz
      change (fderiv ℂ (z • fun p : A => deriv (fun w : ℂ => D (w,p)) z/R (z,p)) a) h=_
      rw [fderiv_const_smul_field]
      change z*((fderiv ℂ (fun p : A => deriv (fun w : ℂ => D (w,p)) z/R (z,p)) a) h)=_
      rw [fderiv_trace_differential_eq_deriv_source_quotient D R U hU hD hR hne hsq z a h (hc z hz)]
    _ = _ := by simpa only [Nat.cast_zero,zero_add,one_mul,J] using hparts

end NLS.ComplexAnalysis
