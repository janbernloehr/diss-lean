import NLS.KdV.HillOriginalWeightedMeanZeroSource

noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.KdV

/-- A weighted target representative constructed from the actual physical
spectral sequence. The next theorem identifies ALL its raw coordinates
with the SAME fixed global real Birkhoff map. -/
def hillBirkhoffWeightedRepresentative (w : SpectralWeight) (p : RealHillWeightedPotential w) :
    HillBirkhoffWeightedSpace w :=
  (RealWeightedNatPair.normalizationEquiv _ _).symm
    (hillWeightedSpectralSequence (by simp) (by intro k; simp) w p)

theorem hillBirkhoffWeightedRepresentative_coordinates (w : SpectralWeight) (p : RealHillWeightedPotential w)
    (hmean : p.val.val 0 = 0) (k : ℕ) :
    (hillBirkhoffWeightedRepresentative w p).val k =
      (hillOriginalBirkhoffMap (hillOriginalWeightedMeanZeroSource w p hmean)).val k := by
  rw [hillOriginalBirkhoffMap_coordinates]
  apply RealWeightedNatPair.normalization_symm_apply_of_mul
  change hillWeightedSpectralCoordinate w p k =
    (hillBirkhoffWeightedWeight w k : ℂ)*hillSpectralCartesian
      (hillRealWeightedEmbedding w p).val (hillRealWeightedEmbedding w p).property.1
      (hillRealWeightedEmbedding w p).property.2 (k+1) (by omega)
  rw [hillWeightedSpectralCoordinate,hillBirkhoffWeightedWeight,ofReal_mul]
  rfl

/-- The SAME fixed physical Birkhoff map takes every original weighted
source into the paper's exact h_*^w; no unrelated output sequence is used. -/
theorem hillOriginalBirkhoffMap_mem_weighted (w : SpectralWeight) (p : RealHillWeightedPotential w)
    (hmean : p.val.val 0 = 0) :
    (hillOriginalBirkhoffMap (hillOriginalWeightedMeanZeroSource w p hmean)).val ∈
      realWeightedNatPairSubmodule (hillBirkhoffWeightedWeight w) := by
  have he : (hillOriginalBirkhoffMap (hillOriginalWeightedMeanZeroSource w p hmean)).val =
      (hillBirkhoffWeightedRepresentative w p).val :=
    funext (fun k => (hillBirkhoffWeightedRepresentative_coordinates w p hmean k).symm)
  rw [he]
  exact (hillBirkhoffWeightedRepresentative w p).property

/-- Literal restriction of the ONE fixed real Birkhoff map to a weighted
source, retaining exactly the same raw real coordinates. -/
def hillOriginalBirkhoffWeightedRestriction (w : SpectralWeight) (p : RealHillWeightedPotential w)
    (hmean : p.val.val 0 = 0) : HillBirkhoffWeightedSpace w :=
  ⟨(hillOriginalBirkhoffMap (hillOriginalWeightedMeanZeroSource w p hmean)).val,
    hillOriginalBirkhoffMap_mem_weighted w p hmean⟩

/-- The exact real weighted Birkhoff target norm is the norm of the
already verified physical weighted spectral sequence, component by component. -/
theorem norm_hillOriginalBirkhoffWeightedRestriction (w : SpectralWeight) (p : RealHillWeightedPotential w)
    (hmean : p.val.val 0 = 0) :
    ‖hillOriginalBirkhoffWeightedRestriction w p hmean‖ =
      ‖hillWeightedSpectralSequence (by simp) (by intro k; simp) w p‖ := by
  have he : hillOriginalBirkhoffWeightedRestriction w p hmean = hillBirkhoffWeightedRepresentative w p := by
    apply Subtype.ext
    exact funext (fun k => (hillBirkhoffWeightedRepresentative_coordinates w p hmean k).symm)
  rw [he]
  exact (RealWeightedNatPair.normalizationIsometry _ _).symm.norm_map _

end NLS.KdV
