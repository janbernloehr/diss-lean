import NLS.ZakharovShabat.SpatialTranslation
import NLS.ZakharovShabat.RootSpaces

/-! # Translation invariance of intrinsic periodic spectral data

Conjugacy holds on every generalized root space, so translation preserves
actual algebraic multiplicities as well as the spectral set.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Translation identifies periodic root chains of each finite length. -/
theorem mem_periodicRootSpace_spatialTranslation (hp : p ≠ ⊤) (t : ℝ)
    (φ : PairSpace p) (z : ℂ) (n : ℕ) (x : PairSpace p) :
    pairSpatialTranslation t x ∈ periodicRootSpace hp (pairSpatialTranslation t φ) z n ↔
      x ∈ periodicRootSpace hp φ z n := by
  induction n generalizing x with
  | zero =>
    change pairSpatialTranslation t x = 0 ↔ x = 0
    simpa only [map_zero] using
      ((pairSpatialTranslation t).injective.eq_iff (a := x) (b := 0))
  | succ n ih =>
    rw [mem_periodicRootSpace_succ, mem_periodicRootSpace_succ]
    constructor
    · rintro ⟨f, hf, hn⟩
      obtain ⟨g, rfl⟩ := (domainSpatialTranslation t).surjective f
      rw [domainInclusion_spatialTranslation] at hf
      rw [spectralPencil_spatialTranslation] at hn
      exact ⟨g, (pairSpatialTranslation t).injective hf, (ih _).mp hn⟩
    · rintro ⟨f, hf, hn⟩
      refine ⟨domainSpatialTranslation t f, ?_, ?_⟩
      · rw [domainInclusion_spatialTranslation, hf]
      · rw [spectralPencil_spatialTranslation]
        exact (ih _).mpr hn

/-- Translation identifies the full generalized root spaces. -/
theorem mem_periodicRootSpaceTop_spatialTranslation (hp : p ≠ ⊤) (t : ℝ)
    (φ : PairSpace p) (z : ℂ) (x : PairSpace p) :
    pairSpatialTranslation t x ∈ periodicRootSpaceTop hp (pairSpatialTranslation t φ) z ↔
      x ∈ periodicRootSpaceTop hp φ z := by
  simp only [mem_periodicRootSpaceTop, mem_periodicRootSpace_spatialTranslation]

/-- Exact image identity, retaining the original operator's root spaces. -/
theorem map_periodicRootSpaceTop_spatialTranslation (hp : p ≠ ⊤) (t : ℝ)
    (φ : PairSpace p) (z : ℂ) :
    (periodicRootSpaceTop hp φ z).map (pairSpatialTranslation t).toLinearEquiv.toLinearMap =
      periodicRootSpaceTop hp (pairSpatialTranslation t φ) z := by
  ext x
  obtain ⟨y, rfl⟩ := (pairSpatialTranslation t).surjective x
  rw [mem_periodicRootSpaceTop_spatialTranslation]
  constructor
  · rintro ⟨a, ha, he⟩
    exact (pairSpatialTranslation t).injective he ▸ ha
  · intro hy
    exact ⟨y, hy, rfl⟩

/-- Translation gives a linear equivalence of full periodic root spaces. -/
def periodicRootSpaceTopTranslationEquiv (hp : p ≠ ⊤) (t : ℝ)
    (φ : PairSpace p) (z : ℂ) :
    periodicRootSpaceTop hp φ z ≃ₗ[ℂ]
      periodicRootSpaceTop hp (pairSpatialTranslation t φ) z :=
  (pairSpatialTranslation t).toLinearEquiv.ofSubmodules _ _
    (map_periodicRootSpaceTop_spatialTranslation hp t φ z)

/-- Every actual periodic algebraic multiplicity is translation invariant. -/
theorem periodicAlgebraicMultiplicity_spatialTranslation (hp : p ≠ ⊤) (t : ℝ)
    (φ : PairSpace p) (z : ℂ) :
    periodicAlgebraicMultiplicity hp (pairSpatialTranslation t φ) z =
      periodicAlgebraicMultiplicity hp φ z :=
  (periodicRootSpaceTopTranslationEquiv hp t φ z).finrank_eq.symm

/-- Spatial translation preserves the actual periodic spectral set. -/
theorem periodicSpectrum_spatialTranslation (hp : p ≠ ⊤) (t : ℝ) (φ : PairSpace p) :
    periodicSpectrum hp (pairSpatialTranslation t φ) = periodicSpectrum hp φ := by
  ext z
  rw [← periodicAlgebraicMultiplicity_pos_iff hp (pairSpatialTranslation t φ) z,
    periodicAlgebraicMultiplicity_spatialTranslation,
    periodicAlgebraicMultiplicity_pos_iff hp φ z]

end NLS.ZakharovShabat
