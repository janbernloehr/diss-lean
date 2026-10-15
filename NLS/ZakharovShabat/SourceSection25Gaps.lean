import NLS.ZakharovShabat.NormalizedWeightedSourceRange
import NLS.ZakharovShabat.M1ComplexGlobalGapEstimate
import NLS.ZakharovShabat.SourceSection24Original

/-! # Original Section 25 weighted gap estimates

The tail cutoff and norm belong to the original source. The global bound
holds on one open subdomain of the retained original neighborhood, chosen
before all weights and potentials.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Proposition 25.5: the actual weighted source gap tail with constants six and 1152. -/
theorem sourceM1_gap_tail (w : SpectralWeight) (hw : w.HasLinearFactor)
    (a : CoeffPair 2) (N : ℕ) (hN : 8*‖a‖^2 ≤ 1+(N:ℝ)) :
    let ψ := normalizedWeightedSource w a
    Summable (fun n : ℤ => if N ≤ n.natAbs then
      (w (2*n)*‖sourcePeriodicGapDisplacement (by simp) (by norm_num) ψ n‖)^2 else 0) ∧
    (∑' n : ℤ, if N ≤ n.natAbs then
      (w (2*n)*‖sourcePeriodicGapDisplacement (by simp) (by norm_num) ψ n‖)^2 else 0) ≤
      6*‖sourceFourierTail N a‖^2+1152/(1+(N:ℝ))*‖a‖^6 := by
  let φ := normalizedWeightedPeriodOne w a
  have he := weightedBaseToPair_normalizedWeightedPeriodOne w a
  have heven : weightedBaseToPair w φ ∈ pairParitySubspace 0 := he ▸ periodOnePotential_mem _
  have h := M1_canonicalGap_tail_summable_and_le w hw φ heven N
    (by simpa only [φ,norm_normalizedWeightedPeriodOne] using hN)
  simpa only [φ,he,sourcePeriodicGapDisplacement_apply,
    weightedPairFourierTail_normalizedWeightedPeriodOne,norm_normalizedWeightedPeriodOne] using h

/-- Equation (5.8) for the actual source, including arbitrary superlinear M₁ weights. -/
theorem sourceM1_gap_individual (w : SpectralWeight) (hw : w.HasLinearFactor)
    (a : CoeffPair 2) (n : ℤ) (hn : 8*‖a‖^2 ≤ 1+|(n:ℝ)|) :
    w (2*n)*‖sourcePeriodicGapDisplacement (by simp) (by norm_num)
      (normalizedWeightedSource w a) n‖ ≤ Real.sqrt 12*‖a‖ := by
  let φ := normalizedWeightedPeriodOne w a
  have he := weightedBaseToPair_normalizedWeightedPeriodOne w a
  have heven : weightedBaseToPair w φ ∈ pairParitySubspace 0 := he ▸ periodOnePotential_mem _
  have h := M1_canonicalGap_weighted_le w hw φ heven n
    (by simpa only [φ,norm_normalizedWeightedPeriodOne] using hn)
  simpa only [φ,he,sourcePeriodicGapDisplacement_apply,norm_normalizedWeightedPeriodOne] using h

namespace SourceSection24Data
variable {W₀ W V Wa B U : Set (CoeffPair 2)}
  {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
  {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
  {A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s}
  (Q : SourceSection24Data D A B U)
include Q

/-- One original source neighborhood works for all weights in the global Proposition 25.5 estimate. -/
theorem section25_gap_neighborhood :
    ∃ T : Set (CoeffPair 2), IsOpen T ∧ realTypeSourceLocus 2 ⊆ T ∧ T ⊆ U ∧
      ∀ w : SpectralWeight, w.HasLinearFactor → ∀ a : CoeffPair 2,
        normalizedWeightedSource w a ∈ T →
        Summable (fun n : ℤ => (w (2*n)*‖sourcePeriodicGapDisplacement
          (by simp) (by norm_num) (normalizedWeightedSource w a) n‖)^2) ∧
        (∑' n : ℤ, (w (2*n)*‖sourcePeriodicGapDisplacement
          (by simp) (by norm_num) (normalizedWeightedSource w a) n‖)^2) ≤
          265*Real.pi^2*(w.realExtension (16*‖a‖^2))^2*(1+‖a‖^2)*‖a‖^2 := by
  let T := U ∩ sourceSpectralStripNeighborhood (by simp)
  refine ⟨T,Q.source_open.inter (isOpen_sourceSpectralStripNeighborhood (by simp)),?_,
    inter_subset_left,?_⟩
  · intro ψ hψ
    exact ⟨Q.real_subset hψ,real_mem_sourceSpectralStripNeighborhood (by simp) (by norm_num) ψ hψ⟩
  · intro w hw a ha
    simpa only [sourcePeriodicGapDisplacement_apply,norm_normalizedWeightedPeriodOne] using
      M1_source_canonicalGap_global_summable_and_le (normalizedWeightedSource w a) ha.2 w hw
        (normalizedWeightedPeriodOne w a) (weightedBaseToPair_normalizedWeightedPeriodOne w a)
end SourceSection24Data

end NLS.ZakharovShabat
