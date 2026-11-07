import NLS.SequenceSpaces.AnalyticPhaseTrajectory
import NLS.SequenceSpaces.WeightedPhaseFlow

/-! Analytic phase trajectories in the full weighted Banach norm. -/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

def analyticPhaseTrajectory (hp : p ≠ ⊤) (w : Weight) (ω : ℤ → ℝ) (θ : C(K,ℝ))
    (b : Coeff ⊤) (a : WeightedCoeff w p) : C(K,WeightedCoeff w p) :=
  ((weightIsometry w p).symm.toContinuousLinearEquiv.toContinuousLinearMap.compLeftContinuous ℂ K)
    (Coeff.analyticPhaseTrajectory hp ω θ b (weightIsometry w p a))

theorem analyticAt_analyticPhaseTrajectory (hp : p ≠ ⊤) (w : Weight)
    (ω : ℤ → ℝ) (θ : C(K,ℝ)) (x : Coeff ⊤ × WeightedCoeff w p) :
    AnalyticAt ℂ (fun y : Coeff ⊤ × WeightedCoeff w p =>
      analyticPhaseTrajectory hp w ω θ y.1 y.2) x := by
  have hW : AnalyticAt ℂ (fun y : Coeff ⊤ × WeightedCoeff w p =>
      (y.1,weightIsometry w p y.2)) x :=
    analyticAt_fst.prod (((weightIsometry w p).toContinuousLinearEquiv.toContinuousLinearMap.analyticAt _).comp analyticAt_snd)
  exact (((weightIsometry w p).symm.toContinuousLinearEquiv.toContinuousLinearMap.compLeftContinuous ℂ K).analyticAt _).comp
    ((Coeff.analyticAt_analyticPhaseTrajectory hp ω θ _).comp
      (f := fun y : Coeff ⊤ × WeightedCoeff w p => (y.1,weightIsometry w p y.2)) hW)

theorem analyticPhaseTrajectory_apply (hp : p ≠ ⊤) (w : Weight)
    (ω : ℤ → ℝ) (θ : C(K,ℝ)) (b : Coeff ⊤) (a : WeightedCoeff w p) (t : K) (k : ℤ) :
    (analyticPhaseTrajectory hp w ω θ b a t).val k =
      exp ((θ t:ℂ)*I*((ω k:ℂ)+b k))*a.val k := by
  change Coeff.analyticPhaseTrajectory hp ω θ b (weightIsometry w p a) t k/(w k:ℂ) = _
  rw [Coeff.analyticPhaseTrajectory_apply]
  change (exp _*((w k:ℂ)*a.val k))/(w k:ℂ) = _
  rw [mul_left_comm,mul_div_cancel_left₀ _ (w.complex_ne_zero k)]

end NLS.WeightedCoeff
