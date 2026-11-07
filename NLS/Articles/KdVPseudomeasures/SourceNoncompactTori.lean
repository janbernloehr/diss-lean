import NLS.SequenceSpaces.FourierRealTorusExample
import NLS.Articles.KdVPseudomeasures.MainTheorem14
import NLS.Articles.KdVPseudomeasures.OriginalEndpointSourceTopology

/-! Strong noncompactness at the literal s+1/2 target order, and the
explicit existence assertion in Remark 2.3. -/
noncomputable section
open Set NLS.WeightedCoeff
namespace NLS.Articles.KdVPseudomeasures

theorem pairedSignFlip_mem_articleEndpointActionTorus (r : ℝ) (z : ArticleEndpointRealTarget r)
    (n : ℕ) : pairedSignFlip (Weight.sobolev (1/2-r)) (Weight.sobolev_neg (1/2-r)) n z ∈
      articleEndpointActionTorus r z := by
  intro k
  rw [pairedSignFlip_apply,pairedSignFlip_apply]
  simp only [Int.natAbs_neg]
  split_ifs <;> ring

theorem not_isCompact_articleEndpointActionTorus_of_not_c0 (r : ℝ) (z : ArticleEndpointRealTarget r)
    (hz : ¬PositiveWeightedC0 (Weight.sobolev (1/2-r)) z) :
    ¬IsCompact (articleEndpointActionTorus r z) := by
  intro h
  exact hz (positiveWeightedC0_of_compact_pairedFlips (Weight.sobolev (1/2-r))
    (Weight.sobolev_neg (1/2-r)) z _ h (fun n _ => pairedSignFlip_mem_articleEndpointActionTorus r z n))

/-- Intended Lemma 3.5(iii), with the same s+1/2 codomain correction as
Theorem 1.4. Non-c0 is measured in the actual literal target norm. -/
theorem sourceLemma3_5_iii_targetOrder (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r)
    (hq : ¬PositiveWeightedC0 (Weight.sobolev (1/2-r)) (articleEndpointCoordinates r hr q)) :
    ¬IsCompact (articleEndpointCoordinates r hr '' endpointIsospectralSet r hr q) := by
  rw [sourceLemma3_5_ii_articleNorm]
  exact not_isCompact_articleEndpointActionTorus_of_not_c0 r _ hq

/-- The corresponding entire original isospectral set is strongly
noncompact in the source endpoint infinity norm as well. -/
theorem sourceLemma3_5_iii_sourceNorm (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r)
    (hq : ¬PositiveWeightedC0 (Weight.sobolev (1/2-r)) (articleEndpointCoordinates r hr q)) :
    ¬IsCompact (endpointIsospectralSet r hr q) := by
  intro h
  have hc : Continuous (articleEndpointCoordinates r hr) :=
    (articleEndpointTargetEquiv r hr).continuous.comp (continuous_originalEndpointRealSignedCoordinates r hr)
  exact sourceLemma3_5_iii_targetOrder r hr q hq (h.image hc)

/-- All three parts of Lemma 3.5, with the actual target order used
consistently in part (iii). The source norm conclusion is included too. -/
theorem sourceLemma3_5_corrected (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r) :
    (∃ C : ℝ, 0≤C ∧ ∀ p ∈ endpointIsospectralSet r hr q, ‖p.val‖≤C) ∧
    (articleEndpointCoordinates r hr '' endpointIsospectralSet r hr q=
      articleEndpointActionTorus r (articleEndpointCoordinates r hr q)) ∧
    (¬PositiveWeightedC0 (Weight.sobolev (1/2-r)) (articleEndpointCoordinates r hr q) →
      ¬IsCompact (articleEndpointCoordinates r hr '' endpointIsospectralSet r hr q) ∧
      ¬IsCompact (endpointIsospectralSet r hr q)) :=
  ⟨sourceLemma3_5_i r hr q,sourceLemma3_5_ii_articleNorm r hr q,
    fun h => ⟨sourceLemma3_5_iii_targetOrder r hr q h,sourceLemma3_5_iii_sourceNorm r hr q h⟩⟩

/-- An explicit target has every positive weighted coefficient equal to
one. Surjectivity of the actual endpoint map gives the required original
physical potential for each admissible order. -/
theorem sourceRemark2_3 (r : ℝ) (hr : AdmissiblePredualOrder r) :
    ∃ q : Potential r, ¬IsCompact (endpointIsospectralSet r hr q) := by
  let z : ArticleEndpointRealTarget r := realInverseWeightCoefficients (Weight.sobolev (1/2-r))
    (Weight.sobolev_neg (1/2-r))
  obtain ⟨q,hq⟩ := (sourceTheorem1_4.bijective r hr).2 z
  refine ⟨q,sourceLemma3_5_iii_sourceNorm r hr q ?_⟩
  rw [hq]
  exact not_positiveWeightedC0_realInverseWeightCoefficients _ _

end NLS.Articles.KdVPseudomeasures
