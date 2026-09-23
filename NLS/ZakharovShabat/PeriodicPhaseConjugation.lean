import NLS.ZakharovShabat.AuxiliaryPhase
import NLS.ZakharovShabat.RootSpaces

/-! # Phase conjugation of the original periodic pencil

The auxiliary phase change also conjugates the unrestricted periodic pencil.
Its full generalized root spaces, spectral set, and actual algebraic
multiplicities are therefore invariant under the potential rotation.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The phase map identifies finite periodic root chains at every length. -/
theorem mem_periodicRootSpace_auxiliaryPhase (hp : p ≠ ⊤) (φ : PairSpace p)
    (z : ℂ) (n : ℕ) (x : PairSpace p) :
    auxiliaryPhase (Coeff p) x ∈ periodicRootSpace hp φ z n ↔
      x ∈ periodicRootSpace hp (auxiliaryPotential φ) z n := by
  induction n generalizing x with
  | zero =>
    change auxiliaryPhase (Coeff p) x = 0 ↔ x = 0
    simpa only [map_zero] using
      ((auxiliaryPhase (Coeff p)).injective.eq_iff (a := x) (b := 0))
  | succ n ih =>
    rw [mem_periodicRootSpace_succ, mem_periodicRootSpace_succ]
    constructor
    · rintro ⟨f, hf, hn⟩
      obtain ⟨g, rfl⟩ := (auxiliaryPhase (ScalarDomain p)).surjective f
      rw [domainInclusion_auxiliaryPhase] at hf
      rw [spectralPencil_auxiliaryPhase] at hn
      exact ⟨g, (auxiliaryPhase (Coeff p)).injective hf, (ih _).mp hn⟩
    · rintro ⟨f, hf, hn⟩
      refine ⟨auxiliaryPhase (ScalarDomain p) f, ?_, ?_⟩
      · rw [domainInclusion_auxiliaryPhase, hf]
      · rw [spectralPencil_auxiliaryPhase]
        exact (ih _).mpr hn

/-- The same phase map identifies full periodic generalized root spaces. -/
theorem mem_periodicRootSpaceTop_auxiliaryPhase (hp : p ≠ ⊤) (φ : PairSpace p)
    (z : ℂ) (x : PairSpace p) :
    auxiliaryPhase (Coeff p) x ∈ periodicRootSpaceTop hp φ z ↔
      x ∈ periodicRootSpaceTop hp (auxiliaryPotential φ) z := by
  simp only [mem_periodicRootSpaceTop, mem_periodicRootSpace_auxiliaryPhase]

/-- Exact image identity for the full periodic generalized root space. -/
theorem map_periodicRootSpaceTop_auxiliaryPhase (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) :
    (periodicRootSpaceTop hp (auxiliaryPotential φ) z).map
      (auxiliaryPhase (Coeff p)).toLinearEquiv.toLinearMap = periodicRootSpaceTop hp φ z := by
  ext x
  obtain ⟨y, rfl⟩ := (auxiliaryPhase (Coeff p)).surjective x
  rw [mem_periodicRootSpaceTop_auxiliaryPhase]
  constructor
  · rintro ⟨a, ha, he⟩
    exact (auxiliaryPhase (Coeff p)).injective he ▸ ha
  · intro hy
    exact ⟨y, hy, rfl⟩

/-- The original periodic full root spaces are phase-conjugate. -/
def periodicRootSpaceTopPhaseEquiv (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) :
    periodicRootSpaceTop hp (auxiliaryPotential φ) z ≃ₗ[ℂ]
      periodicRootSpaceTop hp φ z :=
  (auxiliaryPhase (Coeff p)).toLinearEquiv.ofSubmodules _ _
    (map_periodicRootSpaceTop_auxiliaryPhase hp φ z)

/-- Phase rotation preserves the algebraic multiplicity of every original periodic eigenvalue. -/
theorem periodicAlgebraicMultiplicity_auxiliaryPotential (hp : p ≠ ⊤)
    (φ : PairSpace p) (z : ℂ) :
    periodicAlgebraicMultiplicity hp (auxiliaryPotential φ) z =
      periodicAlgebraicMultiplicity hp φ z :=
  (periodicRootSpaceTopPhaseEquiv hp φ z).finrank_eq

/-- Phase rotation preserves the actual periodic spectral set. -/
theorem periodicSpectrum_auxiliaryPotential (hp : p ≠ ⊤) (φ : PairSpace p) :
    periodicSpectrum hp (auxiliaryPotential φ) = periodicSpectrum hp φ := by
  ext z
  rw [← periodicAlgebraicMultiplicity_pos_iff hp (auxiliaryPotential φ) z,
    periodicAlgebraicMultiplicity_auxiliaryPotential,
    periodicAlgebraicMultiplicity_pos_iff hp φ z]

end NLS.ZakharovShabat
