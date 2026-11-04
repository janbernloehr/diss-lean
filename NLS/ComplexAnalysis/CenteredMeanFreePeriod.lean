import NLS.ComplexAnalysis.CenteredMeanFree
import NLS.ComplexAnalysis.CenteredQuadraticRoot
import NLS.ComplexAnalysis.EndpointRootAllCosinePeriods

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open MeasureTheory
open scoped ENNReal ComplexConjugate

namespace NLS.ComplexAnalysis



variable {A : Type}

theorem circleIntegral_centeredMeanFree_div_root_eq_zero
    (f : ℂ × A → ℂ) (s : A → ℂ) (p : A) (r R : ℝ)
    (hr : ‖sqrt (s p)‖ < r) (hrR : r < R)
    (hf : AnalyticOnNhd ℂ (fun w => f (w,p)) (closedBall (0:ℂ) R)) :
    (∮ z in C((0:ℂ),r), centeredMeanFree f s (z,p)/centeredQuadraticRoot s (z,p)) = 0 := by
  have hrpos : 0 < r := (norm_nonneg _).trans_lt hr
  have hg : AnalyticOnNhd ℂ (fun z => centeredMeanFree f s (z,p)) (closedBall (0:ℂ) R) :=
    fun z hz => by
      change AnalyticAt ℂ (fun w : ℂ => f (w,p)-parametricCosineMean f (fun _ => 0) (sqrt (s p),p)/(Real.pi : ℂ)) z
      exact (hf z hz).sub analyticAt_const
  have hcurve : ∀ θ : ℝ, sqrt (s p)*(Real.cos θ : ℂ) ∈ closedBall (0:ℂ) R := by
    intro θ
    have hcos : ‖(Real.cos θ : ℂ)‖ ≤ 1 := by simpa only [norm_real,Real.norm_eq_abs] using Real.abs_cos_le_one θ
    simp only [mem_closedBall,dist_zero_right,norm_mul]
    exact (mul_le_mul_of_nonneg_left hcos (norm_nonneg _)).trans (by simpa only [mul_one] using (hr.trans hrR).le)
  have hcont : ContinuousOn (fun θ : ℝ => f (sqrt (s p)*(Real.cos θ : ℂ),p)) (Icc 0 Real.pi) :=
    hf.continuousOn.comp (by fun_prop) (fun θ _ => hcurve θ)
  have hzero := integral_centeredMeanFree_cosine_eq_zero f s p (hcont.intervalIntegrable_of_Icc Real.pi_pos.le)
  have heq : (∮ z in C((0:ℂ),r), centeredMeanFree f s (z,p)/centeredQuadraticRoot s (z,p)) =
      ∮ z in C((0:ℂ),r), centeredMeanFree f s (z,p)/endpointRoot (0-sqrt (s p)) (0+sqrt (s p)) z := by
    apply circleIntegral.integral_congr hrpos.le
    intro z hz
    have hzn : z ≠ 0 := by
      have hnorm : ‖z‖ = r := by simpa only [mem_sphere,dist_zero_right] using hz
      exact norm_pos_iff.mp (hnorm ▸ hrpos)
    dsimp only
    rw [centeredQuadraticRoot_eq_endpointRoot s z p (sqrt (s p)) hzn (complex_sqrt_sq _)]
    simp only [zero_sub,zero_add]
  rw [heq,circleIntegral_div_endpointRoot_eq_cosine_integral_all _ 0 (sqrt (s p)) r R hr hrR hg]
  have hz : (∫ θ in (0:ℝ)..Real.pi,
      centeredMeanFree f s (cosineGapPoint 0 (sqrt (s p)) (θ : ℂ),p)) = 0 := by
    simpa only [cosineGapPoint,zero_add,← ofReal_cos] using hzero
  rw [hz,mul_zero]

end NLS.ComplexAnalysis
