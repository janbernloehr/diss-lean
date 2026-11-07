import NLS.ZakharovShabat.SourceCriticalGapSequenceAnalytic
import NLS.ZakharovShabat.NormalizedSobolevSourceCompact
import NLS.SequenceSpaces.CompactPullbackCoordinateTails

/-! # Uniform actual critical-quotient tails at positive Sobolev order

One full complex neighborhood in the normalized Sobolev source norm
works for every tail tolerance. The assertion concerns the actual
critical squared-gap quotient and includes collapsed complex gaps.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The neighborhood precedes the tolerance for every strictly positive
Sobolev order; no stronger source regularity is assumed. -/
theorem exists_local_sobolev_sourceCriticalGapQuotient_uniform_tail
    (hp : p ≠ ⊤) (hp1 : 1 < p) (t : ℝ) (ht : 0 < t)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ T : Set (CoeffPair p), IsOpen T ∧ φ ∈ T ∧
      ∀ ε > (0:ℝ), ∃ K : ℕ, ∀ ψ ∈ T, ∀ k : ℤ,
        K ≤ k.natAbs →
          ‖sourceCriticalGapQuotient hp hp1
            (normalizedWeightedSource (sourceSobolevSpectralWeight t ht.le) ψ) k‖ < ε := by
  let w := sourceSobolevSpectralWeight t ht.le
  let L := normalizedWeightedSourceCLM (p := p) w
  have hr := normalizedWeightedSource_realType w φ hφ
  obtain ⟨V,hV,hφV,ha⟩ :=
    exists_local_sourceCriticalGapQuotient_sequence_analytic hp hp1 (L φ) hr
  obtain ⟨T,hT,hφT,_,htail⟩ :=
    Coeff.exists_local_uniform_coordinate_tails_compact_pullback hp L
      (isCompactOperator_normalizedSobolevSource t ht)
      (sourceCriticalGapQuotient hp hp1) hV ha.continuousOn φ hφV
  exact ⟨T,hT,hφT,htail⟩

end NLS.ZakharovShabat
