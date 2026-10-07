import NLS.ZakharovShabat.SourceRenormalizedFlow
import NLS.ZakharovShabat.SourceBirkhoffFreeDifferential

/-! # The actual Birkhoff inverse on its open image

At every finite exponent above one the real map is an open embedding.
Its inverse on the image is analytic. A total extension is used for
formulas; all inverse identities and regularity assertions carry the
image condition explicitly.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W₀ B X : Set (CoeffPair p)} {t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The source is homeomorphic to the actual open coordinate image. -/
def realImageHomeomorph (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) :
    realTypeSourceSubmodule p ≃ₜ range (sourceRealBirkhoffMap hp hp1 t) :=
  D.real_map_isOpenEmbedding.toIsEmbedding.toHomeomorph

/-- Total extension of the actual image inverse, set to zero outside the image. -/
def realImageInverse (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (z : RealCoeff p × RealCoeff p) : realTypeSourceSubmodule p := by
  classical
  exact if hz : z ∈ range (sourceRealBirkhoffMap hp hp1 t) then
    D.realImageHomeomorph.symm ⟨z,hz⟩ else 0

/-- The coordinate image is open in the full real sequence space. -/
theorem real_image_open (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) :
    IsOpen (range (sourceRealBirkhoffMap hp hp1 t)) := by
  simpa only [image_univ] using D.real_map_isOpenEmbedding.isOpenMap univ isOpen_univ

theorem real_map_realImageInverse (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (z : RealCoeff p × RealCoeff p) (hz : z ∈ range (sourceRealBirkhoffMap hp hp1 t)) :
    sourceRealBirkhoffMap hp hp1 t (D.realImageInverse z) = z := by
  rw [realImageInverse,dif_pos hz]
  exact congrArg Subtype.val (D.realImageHomeomorph.apply_symm_apply ⟨z,hz⟩)

@[simp] theorem realImageInverse_real_map (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (φ : realTypeSourceSubmodule p) :
    D.realImageInverse (sourceRealBirkhoffMap hp hp1 t φ) = φ := by
  apply D.proposition17_2
  exact D.real_map_realImageInverse _ ⟨φ,rfl⟩

/-- Analyticity holds on precisely the asserted image domain. -/
theorem realImageInverse_analytic (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) :
    AnalyticOnNhd ℝ D.realImageInverse (range (sourceRealBirkhoffMap hp hp1 t)) := by
  rintro z ⟨φ,rfl⟩
  obtain ⟨g,hg,_,_,hr,_⟩ := D.proposition17_1 φ
  apply hg.congr
  filter_upwards [hr,D.real_image_open.mem_nhds (mem_range_self φ)] with y hy hmem
  apply D.proposition17_2
  exact hy.trans (D.real_map_realImageInverse y hmem).symm

/-- The original complex Birkhoff map vanishes at zero, at every finite exponent. -/
theorem birkhoff_map_zero (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) :
    sourceBirkhoffMap hp hp1 t 0 = 0 := by
  have hr : IsRealType (CoeffPair.toMax p (0 : CoeffPair p)) :=
    (0 : realTypeSourceSubmodule p).property
  have hz (n : ℤ) := D.real_closed_gap_zero 0 (D.real_subset hr) hr n
    (by simpa only [sourcePeriodicGapDisplacement_apply,map_zero] using canonicalPeriodicGap_zero hp hp1 n)
  apply Prod.ext <;> ext n
  · exact (hz n).1
  · exact (hz n).2

@[simp] theorem real_map_zero (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) :
    sourceRealBirkhoffMap hp hp1 t 0 = 0 := by
  change ((Coeff.reCLM p).prodMap (Coeff.reCLM p)) (sourceBirkhoffMap hp hp1 t 0) = 0
  rw [D.birkhoff_map_zero,map_zero]

@[simp] theorem complex_map_zero (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) :
    sourceComplexBirkhoffMap hp hp1 t 0 = 0 := by
  rw [sourceComplexBirkhoffMap,D.birkhoff_map_zero,map_zero]

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
