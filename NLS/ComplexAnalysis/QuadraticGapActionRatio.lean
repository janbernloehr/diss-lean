import NLS.ComplexAnalysis.ParametricSineSquareCosineMeanLocal
import NLS.ComplexAnalysis.SineSquareCosineMoments
import NLS.ComplexAnalysis.JointSpectralDerivativeAnalytic
import NLS.ComplexAnalysis.EntireEvenSquareDescent

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open MeasureTheory
open scoped ENNReal ComplexConjugate

namespace NLS.ComplexAnalysis



variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

def quadraticGapActionRatio (H : ℂ × A → ℂ) (t s : A → ℂ) (a : A) : ℂ :=
  (-2*I/(Real.pi : ℂ))*parametricSineSquareCosineMean
    (fun x : ℂ × A => deriv (fun w => H (w,x.2)) x.1) t (sqrt (s a),a)

theorem analyticAt_quadraticGapActionRatio_of_collapse
    (H : ℂ × A → ℂ) (t s : A → ℂ) (a : A)
    (hH : AnalyticAt ℂ H (t a,a)) (ht : AnalyticAt ℂ t a) (hs : AnalyticAt ℂ s a) (hs0 : s a = 0) :
    AnalyticAt ℂ (quadraticGapActionRatio H t s) a := by
  let D : Set (ℂ × A) := {x | AnalyticAt ℂ H x}
  have hD : IsOpen D := isOpen_analyticAt ℂ H
  have hH' : AnalyticOnNhd ℂ (fun x : ℂ × A => deriv (fun w => H (w,x.2)) x.1) D :=
    analyticOnNhd_spectral_deriv_of_analyticOnNhd H D hD (fun _ hx => hx)
  have hopen : IsOpen ((fun z : ℂ => (z,a)) ⁻¹' D) := hD.preimage (continuous_id.prodMk continuous_const)
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hH)
  have hsq : AnalyticAt ℂ (fun p : A => (sqrt (s p))^2) a := by
    simpa only [complex_sqrt_sq] using hs
  have hm := analyticAt_parametricSineSquareCosineMean_of_analytic_square
    (fun x : ℂ × A => deriv (fun w => H (w,x.2)) x.1) t (fun p => sqrt (s p)) D hD hH' a ht hsq (ε/2)
      (by rw [hs0,Complex.sqrt_zero,norm_zero];positivity)
      (fun z hz => hball (closedBall_subset_ball (half_lt_self hε) hz))
  exact analyticAt_const.mul hm

omit [NormedAddCommGroup A] [NormedSpace ℂ A] in
theorem quadraticGapActionRatio_at_collapse
    (H : ℂ × A → ℂ) (t s : A → ℂ) (a : A) (hs0 : s a = 0) :
    quadraticGapActionRatio H t s a = -I*deriv (fun w => H (w,a)) (t a) := by
  rw [quadraticGapActionRatio,hs0,Complex.sqrt_zero,parametricSineSquareCosineMean_zero]
  field_simp

end NLS.ComplexAnalysis
