import NLS.SequenceSpaces.SobolevSesquilinearPairing
import NLS.SequenceSpaces.SobolevFullDuality
import NLS.SequenceSpaces.SobolevInfinityDuality

/-! # Full duality under the Section 2 sesquilinear convention

The representative is conjugate linear in the functional because the
pairing is linear in its first and conjugate linear in its second argument.
The full identification holds at every finite source exponent, including
one. No full-dual assertion at infinity is introduced.
-/
noncomputable section
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- The exact conjugate-linear Riesz isometry onto the full coefficient representative space. -/
def sobolevSesquilinearRiesz (s : ℝ) (hp : p ≠ ⊤) :
    (WeightedCoeff (Weight.sobolev s) p →L[ℂ] ℂ) ≃ₗᵢ⋆[ℂ] WeightedCoeff (Weight.sobolev (-s)) q :=
  (sobolevDualityIsometry (q := q) s hp).symm.trans (sobolevConjugation (-s))

@[simp] theorem sobolevSesquilinearRiesz_apply (s : ℝ) (hp : p ≠ ⊤)
    (L : WeightedCoeff (Weight.sobolev s) p →L[ℂ] ℂ) :
    sobolevSesquilinearRiesz (q := q) s hp L = sobolevConjugation (-s) (sobolevCotangent s hp L) := by
  simp only [sobolevSesquilinearRiesz,LinearIsometryEquiv.trans_apply,sobolevDualityIsometry_symm_apply]

theorem sobolevSesquilinearRiesz_represents (s : ℝ) (hp : p ≠ ⊤)
    (L : WeightedCoeff (Weight.sobolev s) p →L[ℂ] ℂ) (h : WeightedCoeff (Weight.sobolev s) p) :
    sobolevSesquilinearPairing s h (sobolevSesquilinearRiesz (q := q) s hp L) = L h := by
  rw [sobolevSesquilinearRiesz_apply,sobolevSesquilinearPairing_conjugation,
    sobolevBilinearPairing_sobolevCotangent]

theorem norm_sobolevSesquilinearRiesz (s : ℝ) (hp : p ≠ ⊤)
    (L : WeightedCoeff (Weight.sobolev s) p →L[ℂ] ℂ) :
    ‖sobolevSesquilinearRiesz (q := q) s hp L‖ = ‖L‖ := (sobolevSesquilinearRiesz s hp).norm_map L

/-- Full representation is unique on the whole source space. -/
theorem existsUnique_sobolevSesquilinearRepresentative (s : ℝ) (hp : p ≠ ⊤)
    (L : WeightedCoeff (Weight.sobolev s) p →L[ℂ] ℂ) :
    ∃! b : WeightedCoeff (Weight.sobolev (-s)) q, ∀ h : WeightedCoeff (Weight.sobolev s) p,
      sobolevSesquilinearPairing s h b = L h := by
  refine ⟨sobolevSesquilinearRiesz (q := q) s hp L,sobolevSesquilinearRiesz_represents (q := q) s hp L,?_⟩
  intro b hb
  apply (sobolevConjugation (p := q) (-s)).injective
  rw [sobolevSesquilinearRiesz_apply,sobolevConjugation_involutive]
  apply sobolevBilinearPairing_flip_injective (p := p) (q := q) s
  ext h
  exact (hb h).trans (sobolevBilinearPairing_sobolevCotangent (q := q) s hp L h).symm

/-- Scalar multiplication of functionals conjugates the scalar in their representatives. -/
theorem sobolevSesquilinearRiesz_smul (s : ℝ) (hp : p ≠ ⊤) (c : ℂ)
    (L : WeightedCoeff (Weight.sobolev s) p →L[ℂ] ℂ) :
    sobolevSesquilinearRiesz (q := q) s hp (c • L) = star c • sobolevSesquilinearRiesz s hp L :=
  (sobolevSesquilinearRiesz s hp).map_smulₛₗ c L

/-- The physical sesquilinear representative conjugates the functional on the same raw mode. -/
@[simp] theorem sobolevSesquilinearRiesz_val (s : ℝ) (hp : p ≠ ⊤)
    (L : WeightedCoeff (Weight.sobolev s) p →L[ℂ] ℂ) (n : ℤ) :
    (sobolevSesquilinearRiesz (q := q) s hp L).val n =
      star (L (ofFinsupp (Weight.sobolev s) p (Finsupp.single n 1))) := by
  simp only [sobolevSesquilinearRiesz_apply,sobolevConjugation_apply,sobolevCotangent_val,neg_neg]

omit [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q] in
/-- The sesquilinear convention does not remove the infinity-source obstruction. -/
theorem exists_analytic_sobolev_without_sesquilinearRepresentative (s : ℝ) :
    ∃ F : WeightedCoeff (Weight.sobolev s) ⊤ → ℂ, AnalyticOnNhd ℂ F Set.univ ∧
      ∀ x, ¬∃ b : WeightedCoeff (Weight.sobolev (-s)) 1,
        ∀ h : WeightedCoeff (Weight.sobolev s) ⊤,
          sobolevSesquilinearPairing s h b = fderiv ℂ F x h := by
  obtain ⟨F,hF,hno⟩ := exists_analytic_sobolev_without_gradient s
  refine ⟨F,hF,?_⟩
  intro x ⟨b,hb⟩
  exact hno x ⟨sobolevConjugation (-s) b,hb⟩

end NLS.WeightedCoeff
