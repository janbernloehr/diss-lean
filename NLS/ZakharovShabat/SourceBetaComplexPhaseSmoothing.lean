import NLS.ZakharovShabat.SourceBetaComplexSobolevDecay
import NLS.SequenceSpaces.ComplexPhaseSmoothing

/-! # Complex beta-phase smoothing

The actual beta-phase error gains one derivative on every Banach sequence scale, locally over normalized first-order Sobolev sources.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
variable (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
include D

/-- Complex beta-phase errors gain one derivative on every sequence scale near each normalized Sobolev real source. -/
theorem exists_local_normalizedSobolevBetaCorrection_phase_smoothing (φ : realTypeSourceLocus 2) :
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ φ.val ∈ U ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ ψ ∈ U,
        ∀ (q : ℝ≥0∞) (_ : Fact (1 ≤ q)) (r t : ℝ),
          ∃ T : WeightedCoeff (Weight.sobolev r) q →L[ℂ] WeightedCoeff (Weight.sobolev (r+1)) q,
            (∀ c n, (T c).val n = (exp ((t:ℂ)*Complex.I*sourceAngularBetaCorrection (by simp) (by norm_num) n s
              (normalizedWeightedSource (SpectralWeight.sobolev 1 (by norm_num)) ψ))-1)*c.val n) ∧
            ‖T‖ ≤ |t| *K*Real.exp (|t| *K) := by
  obtain ⟨U,hU,hφ,K,hK,h⟩ := D.exists_local_normalizedSobolevBetaCorrection_decay φ
  refine ⟨U,hU,hφ,K,hK,?_⟩
  intro ψ hψ q hq r t
  exact WeightedCoeff.exists_sobolev_complex_phase_gain_multiplier r t _ K hK (h ψ hψ)

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
