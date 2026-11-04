import NLS.ComplexAnalysis.QuadraticGapActionRatio

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal Classical

namespace NLS.ComplexAnalysis



variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

theorem analyticAt_quadraticGapActionRatio_of_disc
    (H : ℂ × A → ℂ) (t s : A → ℂ) (a : A)
    (ht : AnalyticAt ℂ t a) (hs : AnalyticAt ℂ s a)
    (R : ℝ) (hR : ‖sqrt (s a)‖ < R)
    (hH : ∀ z ∈ closedBall (t a) R, AnalyticAt ℂ H (z,a)) :
    AnalyticAt ℂ (quadraticGapActionRatio H t s) a := by
  let D : Set (ℂ × A) := {x | AnalyticAt ℂ H x}
  have hD : IsOpen D := isOpen_analyticAt ℂ H
  have hd : AnalyticOnNhd ℂ (fun x : ℂ × A => deriv (fun w => H (w,x.2)) x.1) D :=
    analyticOnNhd_spectral_deriv_of_analyticOnNhd H D hD (fun _ hx => hx)
  have hsq : AnalyticAt ℂ (fun p : A => (sqrt (s p))^2) a := by
    simpa only [complex_sqrt_sq] using hs
  exact analyticAt_const.mul (analyticAt_parametricSineSquareCosineMean_of_analytic_square
    _ t (fun p => sqrt (s p)) D hD hd a ht hsq R hR hH)

end NLS.ComplexAnalysis
