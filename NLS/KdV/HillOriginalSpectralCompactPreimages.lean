import NLS.KdV.HillOriginalSpectralSequentialProperness
import NLS.KdV.HillWeightedSpectralContinuity
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.KdV

/-- Compact target sets have compact mean-zero inverse images in the
ORIGINAL real L2 Hill space, for the ACTUAL full Cartesian sequence.
This proves the compact-preimage part of properness without assuming
injectivity, surjectivity, finite-gap density or an inverse map. -/
theorem isCompact_hillOriginal_meanZero_spectral_preimage
    (K : Set (lp (fun _ : ℕ => ℂ) 2)) (hK : IsCompact K) :
    IsCompact {q : RealPeriodOneHillPotential |
      q.val.val 0 = 0 ∧ hillOriginalBaseSpectralSequence q ∈ K} := by
  apply isCompact_iff_isSeqCompact.mpr
  intro a ha
  obtain ⟨z,hz,σ,hσ,hlim⟩ := hK.tendsto_subseq (fun j => (ha j).2)
  obtain ⟨b,hbmean,hbz,τ,hτ,hstrong⟩ := exists_hillOriginal_spectral_tendsto_source_subseq
    (fun j => a (σ j)) (fun j => (ha (σ j)).1) z hlim
  refine ⟨b,⟨hbmean,?_⟩,σ ∘ τ,hσ.comp hτ,?_⟩
  · rw [hbz]
    exact hz
  · apply tendsto_subtype_rng.mpr
    exact hstrong

/-- The base spectral sequence is continuous in the ORIGINAL real L2 norm. -/
theorem continuous_hillOriginalBaseSpectralSequence : Continuous hillOriginalBaseSpectralSequence := by
  have hnative : Continuous hillOriginalNativeRealSource :=
    ((hillPeriodOneRestriction SpectralWeight.one).continuous.comp continuous_subtype_val).subtype_mk _
  exact (continuous_hillWeightedSpectralSequence (by simp) (by intro k; simp) SpectralWeight.one).comp hnative

/-- The literal original real mean-zero L2 domain. -/
abbrev HillOriginalMeanZeroSource := {q : RealPeriodOneHillPotential // q.val.val 0 = 0}

/-- The actual base spectral sequence restricted to its original mean-zero domain. -/
def hillOriginalMeanZeroBaseSpectralMap (q : HillOriginalMeanZeroSource) : lp (fun _ : ℕ => ℂ) 2 :=
  hillOriginalBaseSpectralSequence q.val

/-- The actual original mean-zero base spectral map is proper. -/
theorem isProperMap_hillOriginalMeanZeroBaseSpectralMap :
    IsProperMap hillOriginalMeanZeroBaseSpectralMap := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨continuous_hillOriginalBaseSpectralSequence.comp continuous_subtype_val,?_⟩
  intro K hK
  apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
  have he : Subtype.val '' (hillOriginalMeanZeroBaseSpectralMap ⁻¹' K) =
      {q : RealPeriodOneHillPotential | q.val.val 0 = 0 ∧ hillOriginalBaseSpectralSequence q ∈ K} := by
    ext q
    constructor
    · rintro ⟨r,hr,rfl⟩
      exact ⟨r.property,hr⟩
    · intro hq
      exact ⟨⟨q,hq.1⟩,hq.2,rfl⟩
  rw [he]
  exact isCompact_hillOriginal_meanZero_spectral_preimage K hK

end NLS.KdV
