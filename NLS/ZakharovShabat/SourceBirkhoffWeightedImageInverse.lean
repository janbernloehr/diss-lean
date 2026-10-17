import NLS.ZakharovShabat.SourceBirkhoffWeightedRealLocalInverse

/-! # The actual weighted inverse on its open image

Every weighted real map is a homeomorphism onto its open image. A total
extension of its image inverse is analytic there and has the actual bounded
inverse Jacobian as strict derivative. No surjectivity is assumed.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The native weighted real source is homeomorphic to its actual coordinate image. -/
def originalWeightedRealImageHomeomorph
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (w : SpectralWeight) :
    weightedRealSourceSubmodule (p := p) w ≃ₜ range (D.originalWeightedRealMap w) :=
  (D.originalWeightedRealMap_isOpenEmbedding w).toIsEmbedding.toHomeomorph

/-- Extend the actual weighted image inverse by zero outside its image. -/
def originalWeightedRealImageInverse
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (w : SpectralWeight)
    (z : WithLp p (WeightedRealCoeff (sourceFrequencyWeight w) p × WeightedRealCoeff (sourceFrequencyWeight w) p)) :
    weightedRealSourceSubmodule (p := p) w := by
  classical
  exact if hz : z ∈ range (D.originalWeightedRealMap w) then
    (D.originalWeightedRealImageHomeomorph w).symm ⟨z,hz⟩ else 0

/-- The actual weighted real coordinate image is open in the full native target. -/
theorem originalWeightedRealImage_open
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (w : SpectralWeight) :
    IsOpen (range (D.originalWeightedRealMap w)) := by
  simpa only [image_univ] using (D.originalWeightedRealMap_isOpenEmbedding w).isOpenMap univ isOpen_univ

/-- The weighted image inverse is a right inverse at every point of the image. -/
theorem originalWeightedRealMap_imageInverse
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (w : SpectralWeight)
    (z : WithLp p (WeightedRealCoeff (sourceFrequencyWeight w) p × WeightedRealCoeff (sourceFrequencyWeight w) p))
    (hz : z ∈ range (D.originalWeightedRealMap w)) :
    D.originalWeightedRealMap w (D.originalWeightedRealImageInverse w z) = z := by
  rw [originalWeightedRealImageInverse,dif_pos hz]
  exact congrArg Subtype.val ((D.originalWeightedRealImageHomeomorph w).apply_symm_apply ⟨z,hz⟩)

/-- The weighted image inverse recovers every original weighted real source. -/
@[simp] theorem originalWeightedRealImageInverse_map
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (w : SpectralWeight)
    (a : weightedRealSourceSubmodule (p := p) w) :
    D.originalWeightedRealImageInverse w (D.originalWeightedRealMap w a) = a := by
  apply D.originalWeightedRealMap_injective w
  exact D.originalWeightedRealMap_imageInverse w _ ⟨a,rfl⟩

/-- The actual image inverse is real analytic throughout the open image. -/
theorem originalWeightedRealImageInverse_analytic
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (w : SpectralWeight) :
    AnalyticOnNhd ℝ (D.originalWeightedRealImageInverse w) (range (D.originalWeightedRealMap w)) := by
  rintro z ⟨a,rfl⟩
  obtain ⟨g,hg,_,_,hr,_⟩ := D.exists_originalWeighted_real_localInverse w a
  apply hg.congr
  filter_upwards [hr,(D.originalWeightedRealImage_open w).mem_nhds (mem_range_self a)] with y hy hym
  apply D.originalWeightedRealMap_injective w
  exact hy.trans (D.originalWeightedRealMap_imageInverse w y hym).symm

/-- On the image, the strict derivative is the inverse of the actual real Jacobian. -/
theorem originalWeightedRealImageInverse_hasStrictFDerivAt
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (w : SpectralWeight)
    (z : WithLp p (WeightedRealCoeff (sourceFrequencyWeight w) p × WeightedRealCoeff (sourceFrequencyWeight w) p))
    (hz : z ∈ range (D.originalWeightedRealMap w)) :
    HasStrictFDerivAt (D.originalWeightedRealImageInverse w)
      (D.originalWeightedRealJacobianEquiv w (D.originalWeightedRealImageInverse w z)).symm.toContinuousLinearMap z := by
  let a := D.originalWeightedRealImageInverse w z
  have ha : D.originalWeightedRealMap w a = z := D.originalWeightedRealMap_imageInverse w z hz
  obtain ⟨g,_,_,_,hr,hd⟩ := D.exists_originalWeighted_real_localInverse w a
  rw [ha] at hr hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [hr,(D.originalWeightedRealImage_open w).mem_nhds hz] with y hy hym
  apply D.originalWeightedRealMap_injective w
  exact hy.trans (D.originalWeightedRealMap_imageInverse w y hym).symm

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
