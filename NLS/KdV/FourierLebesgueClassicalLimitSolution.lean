import NLS.KdV.PeriodOneSmoothPotential
import NLS.SequenceSpaces.PhysicalSobolevExponentInclusion

/-! # The universal classical-approximation notion of KdV solution

A solution is continuous, starts at the prescribed potential, and is
the limit for EVERY sequence of smooth real mean-zero initial data
converging in the original Fourier-Lebesgue norm. Every corresponding
actual strong classical KdV trajectory must converge at every time.
The definition has no spectral data or chosen approximation sequence.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.KdV

def IsFourierLebesgueClassicalLimitSolution (s : ℝ) (h4s : s≤4)
    (p : ℝ≥0∞) (h2p : 2≤p) [Fact (1≤p)]
    (q : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p)
    (γ : ℝ → physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p) : Prop :=
  Continuous γ ∧ γ 0=q ∧
    ∀ a : ℕ → physicalRealMeanZeroWeightedExponent (Weight.sobolev 4) 2,
      (∀ N, IsSmoothPeriodOnePotential (a N)) →
      Tendsto (fun N => physicalSobolevExponentInclusion h4s h2p (a N)) atTop (𝓝 q) →
      ∀ U : ℕ → ℝ → physicalRealMeanZeroWeightedExponent (Weight.sobolev 4) 2,
        (∀ N, IsPeriodOneClassicalKdVCurve (U N)) → (∀ N, U N 0=a N) →
        ∀ t : ℝ, Tendsto (fun N => physicalSobolevExponentInclusion h4s h2p (U N t)) atTop (𝓝 (γ t))

end NLS.KdV
