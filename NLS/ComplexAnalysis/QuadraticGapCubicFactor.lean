import NLS.ComplexAnalysis.QuadraticGapCubicMoment
import NLS.ComplexAnalysis.ParametricSineFourthCosineMeanLocal
import NLS.ComplexAnalysis.EntireEvenSquareDescent

/-! # The analytic coefficient after removing a fourth half-gap factor -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS.ComplexAnalysis
variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

def cubicRootAmplitudeFactor (Q : ℂ × A → ℂ) (s : A → ℂ) (a : A) : ℂ :=
  (-2*I/(Real.pi : ℂ))*parametricSineFourthCosineMean (fun t => Q t^3)
    (fun _ => 0) (sqrt (s a),a)

theorem analyticAt_cubicRootAmplitudeFactor
    (Q : ℂ × A → ℂ) (s : A → ℂ) (a : A) (ρ : ℝ) (hρ : 0 < ρ)
    (V : Set A) (hV : IsOpen V) (ha : a ∈ V)
    (hQ : AnalyticOnNhd ℂ Q (ball (0 : ℂ) ρ ×ˢ V))
    (hs : AnalyticAt ℂ s a) (hs0 : s a=0) :
    AnalyticAt ℂ (cubicRootAmplitudeFactor Q s) a := by
  unfold cubicRootAmplitudeFactor
  apply analyticAt_const.mul
  apply analyticAt_parametricSineFourthCosineMean_of_analytic_square
    (fun t => Q t^3) (fun _ => 0) (fun p => sqrt (s p))
    (ball (0 : ℂ) ρ ×ˢ V) (isOpen_ball.prod hV) (hQ.pow 3)
    a analyticAt_const (by simpa only [complex_sqrt_sq] using hs) (ρ/2)
  · rw [hs0,sqrt_zero,norm_zero]
    exact half_pos hρ
  · intro z hz
    exact ⟨closedBall_subset_ball (half_lt_self hρ) hz,ha⟩

omit [NormedAddCommGroup A] [NormedSpace ℂ A] in
theorem cubicRootAmplitudeFactor_at_collapse
    (Q : ℂ × A → ℂ) (s : A → ℂ) (a : A) (hs0 : s a=0) :
    cubicRootAmplitudeFactor Q s a=(-3*I/4)*Q (0,a)^3 := by
  rw [cubicRootAmplitudeFactor,hs0,sqrt_zero]
  simp only [parametricSineFourthCosineMean,zero_mul,zero_add]
  rw [intervalIntegral.integral_mul_const,integral_complex_sin_fourth]
  field_simp
  ring

omit [NormedAddCommGroup A] [NormedSpace ℂ A] in
theorem cubicRootAmplitudeFactor_eq_root_period
    (Q : ℂ × A → ℂ) (s : A → ℂ) (a : A) (δ : ℂ) (hδ : δ^2=s a)
    (r R : ℝ) (hr : ‖δ‖ < r) (hrR : r < R)
    (hQ : AnalyticOnNhd ℂ (fun z => Q (z,a)) (closedBall (0 : ℂ) R)) :
    (Real.pi : ℂ)⁻¹*(∮ z in C((0 : ℂ),r), (Q (z,a)*endpointRoot (-δ) δ z)^3) =
      δ^4*cubicRootAmplitudeFactor Q s a := by
  have hs : sqrt (s a)^2=δ^2 := (complex_sqrt_sq _).trans hδ.symm
  have hm : parametricSineFourthCosineMean (fun t => Q t^3) (fun _ => 0) (sqrt (s a),a)=
      parametricSineFourthCosineMean (fun t => Q t^3) (fun _ => 0) (δ,a) := by
    rcases eq_or_eq_neg_of_sq_eq_sq _ _ hs with hh | hh
    · rw [hh]
    · rw [hh,parametricSineFourthCosineMean_neg]
  have hi := circleIntegral_cubic_endpointRoot_eq_fourth_gap (fun z => Q (z,a)) 0 δ r R hr hrR hQ
  simp only [zero_sub,zero_add] at hi
  rw [hi,cubicRootAmplitudeFactor,hm]
  simp only [parametricSineFourthCosineMean,cosineGapPoint,zero_add,←ofReal_cos]
  ring

omit [NormedAddCommGroup A] [NormedSpace ℂ A] in
theorem cubicRootAmplitudeFactor_eq_shifted_root_period
    (Q : ℂ × A → ℂ) (s : A → ℂ) (a : A) (τ δ : ℂ) (hδ : δ^2=s a)
    (r R : ℝ) (hr : ‖δ‖ < r) (hrR : r < R)
    (hQ : AnalyticOnNhd ℂ (fun z => Q (z-τ,a)) (closedBall τ R)) :
    (Real.pi : ℂ)⁻¹*(∮ z in C(τ,r), (Q (z-τ,a)*endpointRoot (τ-δ) (τ+δ) z)^3) =
      δ^4*cubicRootAmplitudeFactor Q s a := by
  have hs : sqrt (s a)^2=δ^2 := (complex_sqrt_sq _).trans hδ.symm
  have hm : parametricSineFourthCosineMean (fun t => Q t^3) (fun _ => 0) (sqrt (s a),a)=
      parametricSineFourthCosineMean (fun t => Q t^3) (fun _ => 0) (δ,a) := by
    rcases eq_or_eq_neg_of_sq_eq_sq _ _ hs with hh | hh
    · rw [hh]
    · rw [hh,parametricSineFourthCosineMean_neg]
  have hi := circleIntegral_cubic_endpointRoot_eq_fourth_gap (fun z => Q (z-τ,a)) τ δ r R hr hrR hQ
  rw [hi,cubicRootAmplitudeFactor,hm]
  simp only [parametricSineFourthCosineMean,cosineGapPoint,add_sub_cancel_left,zero_add,←ofReal_cos]
  ring

end NLS.ComplexAnalysis
