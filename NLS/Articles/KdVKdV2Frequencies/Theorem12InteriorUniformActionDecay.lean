import NLS.Articles.KdVKdV2Frequencies.OriginalUniformActionFrequencyDecay
import NLS.Articles.KdVKdV2Frequencies.Theorem12OriginalActionDecay

/-! Theorem 1.2(iii)'s sharp UNIFORM interior asymptotic in the ORIGINAL
complex action norm. ONE global weak frequency family works before all
orders and base actions, with the literal +6I_n counterterm. The weak
endpoint s=-1 remains an essential separate obligation. -/
noncomputable section
open Set Complex Filter Topology NLS.KdV NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

def OriginalInteriorUniformSharpFrequencyDecay (V : Set (Coeff 1)) (G : ℕ+ → Coeff 1 → ℂ) : Prop :=
  ∀ s : ℝ, ∀ hs0 : -1<s, ∀ hs1 : s< -1/3,
    ∀ a₀ : WeightedCoeff (Weight.sobolev (2*s+1)) 1,
      a₀∈WeightedCoeff.positiveActionLocus (Weight.sobolev (2*s+1)) 1 →
      ∃ U : Set (WeightedCoeff (Weight.sobolev (2*s+1)) 1), IsOpen U ∧ a₀∈U ∧
        (∀ a∈U, weakActionEnumeration (weakActionNormalization
          (WeightedCoeff.sobolevInclusion (by linarith : -1≤2*s+1) a))∈V) ∧
        (∀ n, AnalyticOnNhd ℂ (originalSobolevRenormalizedFrequency (2*s+1) (by linarith) G n) U) ∧
        ∀ ε > (0:ℝ), ∃ K : ℕ, ∀ a∈U, ∀ n : ℕ+, K≤(n:ℤ).natAbs →
          Weight.sobolev (3*s+2) (n:ℤ)*‖originalSobolevRenormalizedFrequency
            (2*s+1) (by linarith) G n a‖≤ε

theorem GlobalRoughAbelianForwardData.theorem_1_2_iii_original_uniform_action_dependencies
    (D : GlobalRoughAbelianForwardData) :
    ∃ V : Set (Coeff 1), ∃ G : ℕ+ → Coeff 1 → ℂ,
      IsOpen V ∧ Coeff.nonnegativeLocus 1⊆V ∧ (∀ n, AnalyticOnNhd ℂ (G n) V) ∧
      (∀ q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1:ℕ):ℝ)), ∀ n : ℕ+,
        G n (weakActionEnumeration (D.nativeWeakActionSequence 1 q))=
          (D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n : ℂ)-(2*(n:ℂ)*Real.pi)^3) ∧
      OriginalHighRegularityFrequencyDecay V G ∧ OriginalPointwiseSharpFrequencyDecay V G ∧
        OriginalInteriorUniformSharpFrequencyDecay V G := by
  obtain ⟨V,G,hV,hCV,hG,hrec⟩ := exists_global_physical_frequency_action_corrections D
  have hn := global_physical_family_native_recovery D G hrec
  refine ⟨V,G,hV,hCV,hG,hn,?_,?_,?_⟩
  · intro s hs a₀ ha₀
    obtain ⟨U,hU,haU,hUV,hFa,K,M,hM,hb,_hd⟩ := exists_original_sharp_action_frequency_bounds
      D (s+1) (2/3) (2*s+1) (by linarith) (by norm_num) le_rfl (by linarith) (by ring)
      G V hV hCV hG hrec a₀ ha₀
    refine ⟨U,hU,haU,hUV,hFa,K,M,hM,?_⟩
    simpa only [show 3*(2/3:ℝ)-1=1 by norm_num] using hb
  · intro s hs0 hs1 a₀ ha₀
    obtain ⟨U,hU,haU,hUV,hFa,K,M,hM,hb,hd⟩ := exists_original_sharp_action_frequency_bounds
      D (s+1) (s+1) (2*s+1) (by linarith) (by linarith) (by linarith) le_rfl (by ring)
      G V hV hCV hG hrec a₀ ha₀
    refine ⟨U,hU,haU,hUV,hFa,K,M,hM,?_,?_⟩
    · simpa only [show 3*(s+1)-1=3*s+2 by ring] using hb
    · intro hs2
      simpa only [show 3*(s+1)-1=3*s+2 by ring] using hd (by linarith)

  · intro s hs0 hs1 a₀ ha₀
    obtain ⟨U,hU,haU,hUV,hFa,hb⟩ := exists_original_uniform_action_frequency_decay
      D (s+1) (2*s+1) (by linarith) (by linarith) (by ring) G V hV hCV hG hrec a₀ ha₀
    refine ⟨U,hU,haU,hUV,hFa,?_⟩
    simpa only [show 3*(s+1)-1=3*s+2 by ring] using hb

end NLS.Articles.KdVKdV2Frequencies
