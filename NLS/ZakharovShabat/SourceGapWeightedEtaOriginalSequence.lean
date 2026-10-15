import NLS.ZakharovShabat.SourceGapWeightedEtaOriginalBound
import NLS.ZakharovShabat.SourceAngularBetaCorrectionBound
import NLS.SequenceSpaces.TwoSequenceBound
import NLS.SequenceSpaces.BoundedCoordinateAnalytic

/-!
# Original gap-weighted coordinates as analytic sequences

The uniform spectral estimate proves actual sequence membership, exact
coordinate evaluations, and a common local norm bound. Coordinatewise
analyticity then gives a Banach-valued analytic map on the original W.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual gap-weighted sequence whenever its proved spectral majorant gives membership. -/
def sourceGapWeightedEtaSequence (hp : p ≠ ⊤) (hp1 : 1 < p)
    (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) (σ : ℂ) (ψ : CoeffPair p) : Coeff p :=
  Coeff.ofFunctionOrZero p (fun n => sourceGapWeightedEtaCoordinate hp hp1 n s σ ψ)

namespace SourceLemma12_12Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- One neighborhood supplies sequence analyticity, a uniform norm bound, and exact evaluations. -/
theorem gapWeighted_original_local_sequence (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (φ : CoeffPair p) (hφ : φ ∈ W) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ W ∧
      ∃ M : ℝ, 0 ≤ M ∧
        (∀ σ : ℂ, ‖σ‖ ≤ 1 → AnalyticOnNhd ℂ (sourceGapWeightedEtaSequence hp hp1 s σ) U) ∧
        ∀ ψ ∈ U, ∀ σ : ℂ, ‖σ‖ ≤ 1 →
          ‖sourceGapWeightedEtaSequence hp hp1 s σ ψ‖ ≤ M ∧
          ∀ n : ℤ, sourceGapWeightedEtaSequence hp hp1 s σ ψ n = sourceGapWeightedEtaCoordinate hp hp1 n s σ ψ := by
  obtain ⟨Uz,hUz,hφz,hUzW,C,hC,hbound⟩ := gapWeighted_original_uniform_bound H φ hφ
  obtain ⟨Ug,hUg,hφg,_,G,A,hG,_,hseq⟩ :=
    H.original_theta_common_domain.toSourceAngularEtaLocalCommonDomainData.exists_local_uniform_betaCorrection_bound φ hφ
  let U := Uz ∩ Ug
  have hU : IsOpen U := hUz.inter hUg
  have hUW : U ⊆ W := inter_subset_left.trans hUzW
  have hmem (ψ : CoeffPair p) (hψ : ψ ∈ U) (σ : ℂ) (hσ : ‖σ‖ ≤ 1) :=
    Coeff.memℓp_and_norm_ofFunctionOrZero_le_of_two_sequence_bound
      (fun n => sourceGapWeightedEtaCoordinate hp hp1 n s σ ψ) (sourcePeriodicGapDisplacement hp hp1 ψ)
      (sourceDirichletMidpointDisplacement hp hp1 ψ) C hC.le
      (fun n => by simpa only [sourceDirichletMidpointDisplacement_apply] using hbound ψ hψ.1 n σ hσ)
  have heval (ψ : CoeffPair p) (hψ : ψ ∈ U) (σ : ℂ) (hσ : ‖σ‖ ≤ 1) (n : ℤ) :
      sourceGapWeightedEtaSequence hp hp1 s σ ψ n = sourceGapWeightedEtaCoordinate hp hp1 n s σ ψ :=
    Coeff.ofFunctionOrZero_apply_of_mem p _ (hmem ψ hψ σ hσ).1 n
  have hnorm (ψ : CoeffPair p) (hψ : ψ ∈ U) (σ : ℂ) (hσ : ‖σ‖ ≤ 1) :
      ‖sourceGapWeightedEtaSequence hp hp1 s σ ψ‖ ≤ C*G :=
    (hmem ψ hψ σ hσ).2.trans (mul_le_mul_of_nonneg_left (hseq ψ hψ.2).1 hC.le)
  refine ⟨U,hU,⟨hφz,hφg⟩,hUW,C*G,mul_nonneg hC.le hG,?_,?_⟩
  · intro σ hσ
    apply Coeff.analyticOnNhd_of_bounded_coordinatewise _ hU _ (C*G)
      (fun ψ hψ => hnorm ψ hψ σ hσ)
    intro n ψ hψ
    apply (H.gapWeightedEta_original_analytic n σ ψ (hUW hψ)).congr
    filter_upwards [hU.mem_nhds hψ] with χ hχ
    exact (heval χ hχ σ hσ n).symm
  · exact fun ψ hψ σ hσ => ⟨hnorm ψ hψ σ hσ,heval ψ hψ σ hσ⟩

/-- The actual gap-weighted sequence is analytic on the entire original angular domain. -/
theorem gapWeighted_original_sequence_analytic (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (σ : ℂ) (hσ : ‖σ‖ ≤ 1) : AnalyticOnNhd ℂ (sourceGapWeightedEtaSequence hp hp1 s σ) W := by
  intro φ hφ
  obtain ⟨U,_,hφU,_,_,_,ha,_⟩ := gapWeighted_original_local_sequence H φ hφ
  exact ha σ hσ φ hφU

/-- The sequence realization evaluates to the actual scalar coordinate everywhere in W. -/
theorem gapWeighted_original_sequence_apply (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (σ : ℂ) (hσ : ‖σ‖ ≤ 1) (n : ℤ) :
    sourceGapWeightedEtaSequence hp hp1 s σ ψ n = sourceGapWeightedEtaCoordinate hp hp1 n s σ ψ := by
  obtain ⟨U,_,hψU,_,_,_,_,he⟩ := H.gapWeighted_original_local_sequence ψ hψ
  exact (he ψ hψU σ hσ).2 n

end SourceLemma12_12Data
end NLS.ZakharovShabat
