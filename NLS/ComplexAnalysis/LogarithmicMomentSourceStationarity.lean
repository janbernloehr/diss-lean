import NLS.ComplexAnalysis.JointSpectralDerivativeAnalytic
import NLS.ComplexAnalysis.CircleSourceStationarity
import NLS.ComplexAnalysis.MixedSpectralSourceDerivative
import NLS.ComplexAnalysis.AnalyticLogarithmicMoments
import NLS.ComplexAnalysis.QuotientDerivative

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate Classical

namespace NLS.ComplexAnalysis

variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

theorem logarithmicCircleMoment_source_fderiv_eq_zero
    (F : ℂ × A → ℂ) (hF : AnalyticOnNhd ℂ F univ)
    (c : ℂ) (r : ℝ) (hr : 0≤r) (j : ℕ) (p h : A)
    (hb : ∀ z∈sphere c r, F (z,p)≠0)
    (hzero : ∀ z : ℂ, (fderiv ℂ (fun b : A => F (z,b)) p) h=0) :
    DifferentiableAt ℂ (logarithmicCircleMoment F c r j) p ∧
      (fderiv ℂ (logarithmicCircleMoment F c r j) p) h=0 := by
  let D : Set (ℂ × A) := {t | F t≠0}
  have hD : IsOpen D := isOpen_ne_fun (continuous_iff_continuousAt.mpr (fun t => (hF t (mem_univ _)).continuousAt)) continuous_const
  have hd := analyticOnNhd_spectral_deriv_of_analyticOnNhd F univ isOpen_univ hF
  let G : ℂ × A → ℂ := fun t => t.1^j*logDeriv (fun w => F (w,t.2)) t.1
  have hG : AnalyticOnNhd ℂ G D := by
    intro t ht
    exact (analyticAt_fst.pow j).mul ((hd t (mem_univ _)).div (hF t (mem_univ _)) ht)
  have hker (z : ℂ) (hz : z∈sphere c r) : (fderiv ℂ (fun b : A => G (z,b)) p) h=0 := by
    have hFs : AnalyticAt ℂ (fun b : A => F (z,b)) p :=
      (hF (z,p) (mem_univ _)).comp (f := fun b : A => (z,b)) (analyticAt_const.prod analyticAt_id)
    have hds : AnalyticAt ℂ (fun b : A => deriv (fun w => F (w,b)) z) p :=
      (hd (z,p) (mem_univ _)).comp (f := fun b : A => (z,b)) (analyticAt_const.prod analyticAt_id)
    have hdz : (fderiv ℂ (fun b : A => deriv (fun w => F (w,b)) z) p) h=0 := by
      rw [fderiv_source_deriv_spectral_eq_deriv_spectral_fderiv_source F univ isOpen_univ hF z p (mem_univ _) h]
      have he : (fun w : ℂ => (fderiv ℂ (fun b : A => F (w,b)) p) h)=(fun _ => (0 : ℂ)) := funext hzero
      rw [he,deriv_const]
    change (fderiv ℂ (fun b : A => z^j*(deriv (fun w => F (w,b)) z/F (z,b))) p) h=0
    have hquot : AnalyticAt ℂ (fun b : A => deriv (fun w => F (w,b)) z/F (z,b)) p := hds.div hFs (hb z hz)
    rw [fderiv_const_mul hquot.differentiableAt]
    simp only [smul_apply,smul_eq_mul]
    rw [fderiv_div_apply _ _ p hds.differentiableAt hFs.differentiableAt (hb z hz) h,hdz,hzero z]
    simp only [zero_mul,mul_zero,sub_zero,zero_div]
  have hcont := circleIntegral_source_fderiv_eq_zero G D hD hG c r hr p h hb hker
  refine ⟨hcont.1.const_mul (2*Real.pi*I)⁻¹,?_⟩
  change (fderiv ℂ (fun b : A => (2*Real.pi*I)⁻¹*(∮ z in C(c,r),G (z,b))) p) h=0
  rw [fderiv_const_mul hcont.1]
  simp only [smul_apply,smul_eq_mul,hcont.2,mul_zero]

end NLS.ComplexAnalysis
