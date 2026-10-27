import NLS.Dynamics.WeightedRealPhaseFlow
import NLS.Dynamics.AnalyticComplexPhaseTrajectory

/-! # Analytic Hamiltonian phase trajectories in native weighted norms -/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.Birkhoff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- A bounded frequency correction and the weighted initial state determine
an entire real analytic compact-time trajectory, with Hamiltonian orientation. -/
def weightedAnalyticPhaseTrajectory (hp : p ≠ ⊤) (w : Weight)
    (ω : ℤ → ℝ) (θ : C(K, ℝ)) (b : Coeff ⊤)
    (z : WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p)) :
    C(K, WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p)) :=
  (((weightedRealCoordinates w).symm.toContinuousLinearMap.comp decodeReal).compLeftContinuous ℝ K)
    (analyticPhaseTrajectory hp ω (-θ) b (encodeReal (weightedRealCoordinates w z)))

/-- Analyticity is in the uniform norm of the actual weighted trajectory space. -/
theorem analyticAt_weightedAnalyticPhaseTrajectory (hp : p ≠ ⊤) (w : Weight)
    (ω : ℤ → ℝ) (θ : C(K, ℝ))
    (x : Coeff ⊤ × WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p)) :
    AnalyticAt ℝ (fun y : Coeff ⊤ × WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p) =>
      weightedAnalyticPhaseTrajectory hp w ω θ y.1 y.2) x := by
  have hz : AnalyticAt ℝ (fun y : Coeff ⊤ × WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p) =>
      encodeReal (weightedRealCoordinates w y.2)) x :=
    ((encodeReal (p := p)).analyticAt _).comp
      (((weightedRealCoordinates (p := p) w).toContinuousLinearMap.analyticAt _).comp analyticAt_snd)
  exact ((((weightedRealCoordinates w).symm.toContinuousLinearMap.comp decodeReal).compLeftContinuous ℝ K).analyticAt _).comp
    (((analyticAt_analyticPhaseTrajectory hp ω (-θ) _).restrictScalars (𝕜 := ℝ)).comp
      (f := fun y : Coeff ⊤ × WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p) =>
        (y.1,encodeReal (weightedRealCoordinates w y.2))) (analyticAt_fst.prod hz))

/-- On real corrections this extension is exactly the original weighted
Hamiltonian rotation, including both signs of the complex coordinates. -/
theorem weightedAnalyticPhaseTrajectory_apply (hp : p ≠ ⊤) (w : Weight)
    (ω : ℤ → ℝ) (θ : C(K, ℝ)) (b : Coeff ⊤) (β : ℤ → ℝ)
    (hb : ∀ n, b n = (β n : ℂ))
    (z : WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p)) (k : K) :
    weightedAnalyticPhaseTrajectory hp w ω θ b z k =
      weightedRealPhaseFlow w (fun n => ω n+β n) (θ k) z := by
  change (weightedRealCoordinates w).symm (decodeReal
    (analyticPhaseTrajectory hp ω (-θ) b (encodeReal (weightedRealCoordinates w z)) k)) = _
  unfold weightedRealPhaseFlow
  congr 2
  apply Prod.ext <;> ext n
  · rw [analyticPhaseTrajectory_fst,hamiltonianPhaseFlow_fst,hb]
    simp only [ContinuousMap.neg_apply,Complex.ofReal_neg,Complex.ofReal_mul,Complex.ofReal_add]
    congr 2
    ring
  · rw [analyticPhaseTrajectory_snd,hamiltonianPhaseFlow_snd,hb]
    simp only [ContinuousMap.neg_apply,Complex.ofReal_neg,Complex.ofReal_mul,Complex.ofReal_add]
    congr 2
    ring

end NLS.Birkhoff
