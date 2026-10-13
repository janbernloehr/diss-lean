import NLS.ZakharovShabat.SourceAuxiliaryCounting
import NLS.ZakharovShabat.HeightSpectralBox

/-!
# Auxiliary clusters in prescribed-height boxes for real-type input

Reality identifies the counted central cluster with a box of any nonnegative
height, including the source's printed height. The zero-potential special case
therefore refutes the proof's final 2N-1 count in its literal printed box, not
only in the separate height-N box. General complex input remains a separate
height-bound obligation.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
open BoundaryCondition
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual original auxiliary spectrum in a box with prescribed height. -/
def sourceAuxiliaryHeightSpectrum (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann) (N : ℕ) (H : ℝ) : Finset ℂ :=
  (finite_sourceAuxiliarySpectrum_inter b hp φ hφ (isBounded_heightSpectralBox N H)).toFinset

theorem mem_sourceAuxiliaryHeightSpectrum (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann) (N : ℕ) (H : ℝ) (z : ℂ) :
    z ∈ sourceAuxiliaryHeightSpectrum b hp φ hφ N H ↔
      z ∈ sourceAuxiliarySpectrum b hp φ hφ ∧ z ∈ heightSpectralBox N H := Set.Finite.mem_toFinset _

/-- A real spectrum has the same central cluster at every nonnegative height. -/
theorem sourceAuxiliaryHeightSpectrum_eq_central_of_realType (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann)
    (hr : IsRealType (CoeffPair.toMax p φ)) (N : ℕ) {H : ℝ} (hH : 0 ≤ H) :
    sourceAuxiliaryHeightSpectrum b hp φ hφ N H = sourceAuxiliaryCentralSpectrum b hp φ hφ N := by
  ext z
  rw [mem_sourceAuxiliaryHeightSpectrum, mem_sourceAuxiliaryCentralSpectrum]
  by_cases hz : z ∈ sourceAuxiliarySpectrum b hp φ hφ
  · have him := sourceAuxiliarySpectrum_im_eq_zero_of_realType b hp φ hφ hr z hz
    simp [hz, heightSpectralBox, centralSpectralBox, him, hH]
  · simp [hz]

/-- For real-type potentials the central count holds at every nonnegative height. -/
theorem SourceAuxiliaryCountingData.central_height_multiplicity_of_realType {hp : p ≠ ⊤}
    {φ : CoeffPair p} {hφ : φ ∈ sourceBoundaryBaseSubspace .neumann} {N : ℕ}
    (h : SourceAuxiliaryCountingData hp φ hφ N) (hr : IsRealType (CoeffPair.toMax p φ))
    (b : BoundaryCondition) {H : ℝ} (hH : 0 ≤ H) :
    (∑ z ∈ sourceAuxiliaryHeightSpectrum b hp φ hφ N H,
      sourceAuxiliaryAlgebraicMultiplicity b hp φ hφ z) = 2*N+1 := by
  rw [sourceAuxiliaryHeightSpectrum_eq_central_of_realType b hp φ hφ hr N hH]
  exact h.central_multiplicity b

/-- For real-type potentials the same height replacement retains exhaustive localization. -/
theorem SourceAuxiliaryCountingData.spectrum_subset_height_of_realType {hp : p ≠ ⊤}
    {φ : CoeffPair p} {hφ : φ ∈ sourceBoundaryBaseSubspace .neumann} {N : ℕ}
    (h : SourceAuxiliaryCountingData hp φ hφ N) (hr : IsRealType (CoeffPair.toMax p φ))
    (b : BoundaryCondition) {H : ℝ} (hH : 0 ≤ H) :
    sourceAuxiliarySpectrum b hp φ hφ ⊆ heightSpectralBox N H ∪ highSpectralDisks N (Real.pi/4) := by
  intro z hz
  rcases h.spectrum_subset b hz with hb | hd
  · left
    exact ⟨hb.1, by rw [sourceAuxiliarySpectrum_im_eq_zero_of_realType b hp φ hφ hr z hz, abs_zero]; exact hH⟩
  · exact Or.inr hd

/-- The final printed auxiliary N count fails even in the literal height-one box at zero input. -/
theorem exists_sourceAuxiliaryZero_printedBox_count (hp1 : 1 < p) (hp : p ≠ ⊤) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      let S := sourceAuxiliaryHeightSpectrum .neumann hp
        (sourceAuxiliaryReflectedPotential hp1 hp 0) (sourceAuxiliaryReflectedPotential_mem hp1 hp 0) N
        ((1+8*‖(0 : CoeffPair p)‖)^p.toReal)
      (∑ z ∈ S, sourceAuxiliaryAlgebraicMultiplicity .neumann hp
        (sourceAuxiliaryReflectedPotential hp1 hp 0) (sourceAuxiliaryReflectedPotential_mem hp1 hp 0) z) = 2*N+1 ∧
      (∑ z ∈ S, sourceAuxiliaryAlgebraicMultiplicity .neumann hp
        (sourceAuxiliaryReflectedPotential hp1 hp 0) (sourceAuxiliaryReflectedPotential_mem hp1 hp 0) z) ≠ 2*N-1 := by
  obtain ⟨N₀,U,hN,_,_,_,_,h0,hcount⟩ := exists_uniform_sourceAuxiliaryCountingData hp1 hp 0
  refine ⟨N₀,hN,?_⟩
  intro N hN'
  dsimp only
  rw [sourceAuxiliaryHeightSpectrum_eq_central_of_realType .neumann hp _ _
    (isRealType_sourceAuxiliaryReflectedPotential hp1 hp 0 (by intro n; simp)) N (by positivity)]
  exact ⟨(hcount 0 h0 N hN').central_multiplicity .neumann,
    (hcount 0 h0 N hN').neumann_count_ne_printed⟩

end NLS.ZakharovShabat
