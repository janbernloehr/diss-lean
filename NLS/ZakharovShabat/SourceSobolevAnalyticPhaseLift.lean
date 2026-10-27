import NLS.Dynamics.WeightedPhaseTrajectoryAnalytic
import NLS.ZakharovShabat.SourceSobolevInverseTrajectories
import NLS.ZakharovShabat.SourceSobolevPhaseFlow

/-! # Analytic compact-time Sobolev lifts of bounded frequency corrections -/
noncomputable section
set_option autoImplicit false
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {K : Type} [TopologicalSpace K] [CompactSpace K]
namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Lift the actual weighted Hamiltonian phase through the original Sobolev
Birkhoff inverse, using a bounded correction depending on the initial source. -/
def correctedSobolevTrajectory (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (hp2 : p ≤ 2) (σ : ℝ) (hσ : 0 ≤ σ) (ω : ℤ → ℝ) (θ : C(K, ℝ))
    (b : weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight σ hσ) → Coeff ⊤)
    (a : weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight σ hσ)) :
    C(K, weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight σ hσ)) :=
  D.sobolevInverseTrajectory hp2 σ hσ
    (Birkhoff.weightedAnalyticPhaseTrajectory hp
      (sourceFrequencyWeight (sourceSobolevSpectralWeight σ hσ)) ω θ (b a)
      (D.originalWeightedRealMap (sourceSobolevSpectralWeight σ hσ) a))

/-- Bounded analytic frequency corrections give analytic dependence in the full
compact-time norm at each nonnegative real Sobolev order. -/
theorem analytic_correctedSobolevTrajectory
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (hp2 : p ≤ 2) (σ : ℝ) (hσ : 0 ≤ σ) (ω : ℤ → ℝ) (θ : C(K, ℝ))
    (b : weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight σ hσ) → Coeff ⊤)
    (hb : AnalyticOnNhd ℝ b univ) :
    AnalyticOnNhd ℝ (D.correctedSobolevTrajectory hp2 σ hσ ω θ b) univ := by
  intro a _
  exact (D.analytic_sobolevInverseTrajectory hp2 σ hσ _ (mem_univ _)).comp
    ((Birkhoff.analyticAt_weightedAnalyticPhaseTrajectory hp _ ω θ _).comp
      (f := fun c => (b c,D.originalWeightedRealMap (sourceSobolevSpectralWeight σ hσ) c))
      ((hb a (mem_univ _)).prod (D.originalWeightedRealMap_analytic _ a (mem_univ _))))

/-- Real correction values identify the lift with the exact original phase
curve, with no change of the actual Fourier coefficients. -/
theorem correctedSobolevTrajectory_apply
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (hp2 : p ≤ 2) (σ : ℝ) (hσ : 0 ≤ σ) (ω : ℤ → ℝ) (θ : C(K, ℝ))
    (b : weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight σ hσ) → Coeff ⊤)
    (a : weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight σ hσ))
    (β : ℤ → ℝ) (hb : ∀ n, b a n = (β n : ℂ)) (k : K) :
    D.correctedSobolevTrajectory hp2 σ hσ ω θ b a k =
      D.weightedSourcePhaseFlow hp2 σ hσ (fun n => ω n+β n) a (θ k) := by
  change (D.originalWeightedRealSobolevHomeomorph hp2 σ hσ).symm
    (Birkhoff.weightedAnalyticPhaseTrajectory hp _ ω θ (b a)
      (D.originalWeightedRealMap (sourceSobolevSpectralWeight σ hσ) a) k) =
    (D.originalWeightedRealSobolevHomeomorph hp2 σ hσ).symm _
  exact congrArg (D.originalWeightedRealSobolevHomeomorph hp2 σ hσ).symm
    (Birkhoff.weightedAnalyticPhaseTrajectory_apply hp _ ω θ (b a) β hb _ k)

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
