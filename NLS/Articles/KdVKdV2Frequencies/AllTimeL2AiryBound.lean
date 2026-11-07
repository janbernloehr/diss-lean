import NLS.Articles.KdVKdV2Frequencies.OriginalL2AiryRemainder
import NLS.SequenceSpaces.PhysicalWeightedPhaseBounds

/-! The SAME inverse remainder is uniformly bounded along ALL physical
phase orbits of ALL nearby original data. Combined with the actual phase
error this proves the H1 Airy estimate for ALL times, locally uniformly
in the ORIGINAL mean-zero L2 source norm. -/
noncomputable section
open Set Metric Complex NLS.KdV
namespace NLS.Articles.KdVKdV2Frequencies

theorem exists_local_inverse_remainder_orbit_bound (D : GlobalRoughAbelianForwardData)
    (S : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (0+1/2)) →
      physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 1)) (hS : Continuous S)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 0)) :
    ∃ U : Set (physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 0)),
      IsOpen U ∧ q∈U ∧ Bornology.IsBounded U ∧ ∃ C : ℝ,0<C ∧
        ∀ p∈U,‖S (originalL2Coordinates D p)‖≤C ∧
          ∀ (G : ℕ+ → Coeff 1 → ℂ) (t : ℝ),
            ‖S (originalL2Coordinates D (originalKdVBirkhoffFlow D 0 (by norm_num) G t p))‖≤C := by
  obtain ⟨δ,C,hδ,hC,hphase⟩ := continuous_map_uniformly_bounded_on_nearby_phases
    (Weight.sobolev (0+1/2)) (Weight.sobolev_neg _) S hS (originalL2Coordinates D q)
  obtain ⟨U,hU,hq,hb,hnear⟩ := NLS.FunctionalAnalysis.exists_bounded_neighborhood_preimage_ball
    (fun p => originalL2Coordinates D p) (originalL2Coordinates D).continuous q δ hδ
  have hall (p) (hp : p∈U) (G : ℕ+ → Coeff 1 → ℂ) (t : ℝ) :
      ‖S (originalL2Coordinates D (originalKdVBirkhoffFlow D 0 (by norm_num) G t p))‖≤C := by
    have hpδ : dist (originalL2Coordinates D p) (originalL2Coordinates D q)<δ := hnear p hp
    have he := congrArg (fun z => ‖S z‖) (originalL2Coordinates_flow_phase D G t p)
    exact he.le.trans (hphase _ hpδ (originalL2SignedFrequency D G p) (originalL2SignedFrequency_odd D G p) t)
  refine ⟨U,hU,hq,hb,C,hC,?_⟩
  intro p hp
  refine ⟨?_,hall p hp⟩
  have hz := hall p hp (fun _ _ => 0) 0
  simpa only [originalKdVBirkhoffFlow_zero] using hz

theorem exists_local_alltime_originalL2AiryRemainder_bound (D : GlobalRoughAbelianForwardData)
    (G : ℕ+ → Coeff 1 → ℂ) (h : ActualNativeKdVPhaseGain D G)
    (L : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 1) ≃L[ℝ]
      physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (1+1/2)))
    (S : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (0+1/2)) →
      physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 1)) (hS : Continuous S)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 0)) :
    ∃ U : Set (physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 0)),
      IsOpen U ∧ q∈U ∧ ∃ C : ℝ,0<C ∧ ∀ p∈U,∀ t : ℝ,
        ‖originalL2AiryRemainder D G h L S t p‖≤C*(1+|t|) := by
  obtain ⟨U,hU,hq,hUb,M,hM,hSb⟩ := exists_local_inverse_remainder_orbit_bound D S hS q
  obtain ⟨A,hA,hTb⟩ := exists_bounded_originalL2StrongPhaseError_bound D G h U hUb
  let K := ‖L.symm.toContinuousLinearMap‖*A
  have hK : 0≤K := mul_nonneg (norm_nonneg L.symm.toContinuousLinearMap) hA
  refine ⟨U,hU,hq,K+2*M+1,by positivity,?_⟩
  intro p hp t
  have hT := mul_le_mul_of_nonneg_left (hTb p hp t) (norm_nonneg L.symm.toContinuousLinearMap)
  calc
    ‖originalL2AiryRemainder D G h L S t p‖≤
        ‖L.symm.toContinuousLinearMap‖*‖originalL2StrongPhaseError D G h t p‖+
          ‖S (originalL2Coordinates D (originalKdVBirkhoffFlow D 0 (by norm_num) G t p))‖+
            ‖S (originalL2Coordinates D p)‖ := norm_originalL2AiryRemainder_le D G h L S t p
    _≤‖L.symm.toContinuousLinearMap‖*(|t| * A)+M+M :=
      add_le_add (add_le_add hT ((hSb p hp).2 G t)) (hSb p hp).1
    _=K* |t| + M+M := by dsimp only [K];ring
    _≤(K+2*M+1)*(1+|t|) := by
      nlinarith [abs_nonneg t,mul_nonneg hM.le (abs_nonneg t)]

theorem exists_original_l2_alltime_airy_remainder (D : GlobalRoughAbelianForwardData)
    (G : ℕ+ → Coeff 1 → ℂ) (h : ActualNativeKdVPhaseGain D G) :
    ∃ R : ℝ → physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 0) →
        physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 1),
      (∀ t q,physicalRealMeanZeroSobolevInclusion (by norm_num : (0:ℝ)≤1) (R t q)=
        originalKdVBirkhoffFlow D 0 (by norm_num) G t q-originalAiryFlow 0 t q) ∧
      ∀ q,∃ U : Set (physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 0)),
        IsOpen U ∧ q∈U ∧ ∃ C : ℝ,0<C ∧ ∀ p∈U,∀ t : ℝ,‖R t p‖≤C*(1+|t|) := by
  obtain ⟨_F,_hF,_hFi,_hFc,_hFic,S,hSa,_hs,hSc,_hb⟩ := D.exists_original_l2_inverse_smoothing
  obtain ⟨L,_hL,_hLi,hLc⟩ := D.exists_original_native_fourier_equiv 1 (by norm_num)
  refine ⟨originalL2AiryRemainder D G h L S,?_,?_⟩
  · exact fun t q => originalL2AiryRemainder_inclusion D G h L hLc S hSc t q
  · exact exists_local_alltime_originalL2AiryRemainder_bound D G h L S hSa.continuous

end NLS.Articles.KdVKdV2Frequencies
