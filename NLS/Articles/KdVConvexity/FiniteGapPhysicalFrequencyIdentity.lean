import NLS.Articles.KdVConvexity.NativeOriginalFrequencyCompatibility
import NLS.KdV.HillPhysicalIntrinsicFrequencyMoments
import NLS.Articles.KdVKdV2Frequencies.NativeAllGapFrequencyMoments

/-! # Actual physical KdV frequencies have the finite-gap second moments

Both the physical Hamiltonian derivative and the literal canonical moment
have been identified with the article's definitions. The result includes
every selected mode, including a closed gap. An unconditional original
action realization gives the identity at every finitely supported action.
Infinite-gap physical recovery and the rough Miura sum remain open.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open NLS.KdV NLS.ZakharovShabat NLS.Articles.KdVKdV2Frequencies
namespace NLS.Articles.KdVConvexity

theorem native_finiteGap_originalPhysicalFrequency_moments (D : GlobalRoughAbelianForwardData)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1:ℕ):ℝ))) (S : Finset ℕ+)
    (hq : ∀ k : ℕ+, k∉S → hillRealGapHalfLength
      (nativeHillPhysicalSource 1 q.val q.property.1).val
      (nativeHillPhysicalSource 1 q.val q.property.1).property.1
      (nativeHillPhysicalSource 1 q.val q.property.1).property.2 k=0)
    (b : WeightedCoeff.nonnegativeLocus originalActionWeight 1)
    (ha : D.nativeSourceActionSequence 1 3 (by norm_num) q=originalPositiveActionInsertion b.val) (n : ℕ+) :
    originalPhysicalFrequency b n-((8*(n:ℝ)^3*Real.pi^3:ℝ):ℂ) =
      -12*∑' k : ℕ, (k:ℂ)*hillPhysicalFrequencyMoment
        (nativeHillPhysicalSource 1 q.val q.property.1).val
        (nativeHillPhysicalSource 1 q.val q.property.1).property.1
        (nativeHillPhysicalSource 1 q.val q.property.1).property.2 n n.pos k 2 := by
  have hh := D.native_finiteGap_kdv_frequency_moments_all_gaps q S hq n
  rw [nativeSourceFrequency_eq_originalPhysicalFrequency D q b ha n] at hh
  rw [tsum_weighted_hillPhysicalFrequencyMoment_eq_intrinsic]
  convert hh using 2
  push_cast
  ring

/-- Every actual real native H1 finite-gap source has the ORIGINAL
physical frequency formula at every mode, with no chosen Birkhoff data,
action realization, or own-gap openness among the hypotheses. -/
theorem exists_original_physical_finiteGap_frequency_moments
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1:ℕ):ℝ))) (S : Finset ℕ+)
    (hq : ∀ k : ℕ+, k∉S → hillRealGapHalfLength
      (nativeHillPhysicalSource 1 q.val q.property.1).val
      (nativeHillPhysicalSource 1 q.val q.property.1).property.1
      (nativeHillPhysicalSource 1 q.val q.property.1).property.2 k=0) :
    ∃ b : WeightedCoeff.nonnegativeLocus originalActionWeight 1,
      physicalHilbertActions hillH1SpectralWeight (nativeH1PhysicalRepresentative q)=originalActionInclusion b.val ∧
      ∀ n : ℕ+, originalPhysicalFrequency b n-((8*(n:ℝ)^3*Real.pi^3:ℝ):ℂ) =
        -12*∑' k : ℕ, (k:ℂ)*hillPhysicalFrequencyMoment
          (nativeHillPhysicalSource 1 q.val q.property.1).val
          (nativeHillPhysicalSource 1 q.val q.property.1).property.1
          (nativeHillPhysicalSource 1 q.val q.property.1).property.2 n n.pos k 2 := by
  obtain ⟨D⟩ := nonempty_globalRoughAbelianForwardData
  obtain ⟨b,ha,hb⟩ := exists_original_actions_of_native_source D q
  exact ⟨b,hb,native_finiteGap_originalPhysicalFrequency_moments D q S hq b ha⟩

/-- One genuine physical native source is chosen for EVERY point of the
original action cone. Every finitely supported action then has the exact
physical second-moment frequency formula, at ALL selected indices. -/
theorem exists_original_action_realization_with_finiteGap_frequency_moments :
    ∃ Q : WeightedCoeff.nonnegativeLocus originalActionWeight 1 →
        physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1:ℕ):ℝ)),
      (∀ b, physicalHilbertActions hillH1SpectralWeight (nativeH1PhysicalRepresentative (Q b))=originalActionInclusion b.val) ∧
      ∀ b (S : Finset ℕ+), (∀ k : ℕ+, k∉S → b.val.val (actionIndexEquiv.symm k)=0) →
        ∀ n : ℕ+, originalPhysicalFrequency b n-((8*(n:ℝ)^3*Real.pi^3:ℝ):ℂ) =
          -12*∑' k : ℕ, (k:ℂ)*hillPhysicalFrequencyMoment
            (nativeHillPhysicalSource 1 (Q b).val (Q b).property.1).val
            (nativeHillPhysicalSource 1 (Q b).val (Q b).property.1).property.1
            (nativeHillPhysicalSource 1 (Q b).val (Q b).property.1).property.2 n n.pos k 2 := by
  obtain ⟨D⟩ := nonempty_globalRoughAbelianForwardData
  refine ⟨nativeOriginalActionSource D,nativeOriginalActionSource_physical_actions D,?_⟩
  intro b S hb n
  have hgap (k : ℕ+) (hk : k∉S) : hillRealGapHalfLength
      (nativeHillPhysicalSource 1 (nativeOriginalActionSource D b).val (nativeOriginalActionSource D b).property.1).val
      (nativeHillPhysicalSource 1 (nativeOriginalActionSource D b).val (nativeOriginalActionSource D b).property.1).property.1
      (nativeHillPhysicalSource 1 (nativeOriginalActionSource D b).val (nativeOriginalActionSource D b).property.1).property.2 k=0 := by
    apply (D.nativeSourceActionSequence_zero_iff_closed_gap 1 3 (by norm_num) (nativeOriginalActionSource D b) k).mp
    rw [nativeOriginalActionSource_actions,originalPositiveActionInsertion_apply]
    exact hb k hk
  exact native_finiteGap_originalPhysicalFrequency_moments D (nativeOriginalActionSource D b) S hgap b
    (nativeOriginalActionSource_actions D b) n

end NLS.Articles.KdVConvexity
