import NLS.SequenceSpaces.SobolevBilinearPairing
import NLS.SequenceSpaces.ConjugateReflection
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-! # The Section 2 sesquilinear product on the full Sobolev scale

The first variable is complex linear and the second conjugate linear.
Physical conjugation reverses the scalar Fourier index, so composing the
corrected bilinear pairing with physical conjugation gives the printed
same-index sesquilinear sum. Both conjugate endpoints are included.
-/
noncomputable section
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- Actual scalar Fourier conjugation, as a conjugate-linear isometric involution. -/
def sobolevConjugation (s : ℝ) :
    WeightedCoeff (Weight.sobolev s) p ≃ₗᵢ⋆[ℂ] WeightedCoeff (Weight.sobolev s) p where
  toFun := conjugateReflection (Weight.sobolev s) (Weight.sobolev_neg s)
  invFun := conjugateReflection (Weight.sobolev s) (Weight.sobolev_neg s)
  left_inv := conjugateReflection_involutive _ _
  right_inv := conjugateReflection_involutive _ _
  map_add' a b := by apply Subtype.ext; funext n; simp
  map_smul' c a := by apply Subtype.ext; funext n; simp
  norm_map' := norm_conjugateReflection (Weight.sobolev s) (Weight.sobolev_neg s)

@[simp] theorem sobolevConjugation_apply (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) p) (n : ℤ) :
    (sobolevConjugation s a).val n = star (a.val (-n)) := conjugateReflection_apply _ (Weight.sobolev_neg s) a n

@[simp] theorem sobolevConjugation_involutive (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) p) : sobolevConjugation s (sobolevConjugation s a) = a :=
  conjugateReflection_involutive _ (Weight.sobolev_neg s) a

variable [p.HolderConjugate q]

/-- Linear in the first variable and conjugate linear in the second. -/
def sobolevSesquilinearPairing (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) p) (b : WeightedCoeff (Weight.sobolev (-s)) q) : ℂ :=
  sobolevBilinearPairing s a (sobolevConjugation (-s) b)

theorem sobolevSesquilinearPairing_apply (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) p) (b : WeightedCoeff (Weight.sobolev (-s)) q) :
    sobolevSesquilinearPairing s a b = ∑' n : ℤ, a.val n*star (b.val n) := by
  simp only [sobolevSesquilinearPairing,sobolevBilinearPairing_apply,sobolevConjugation_apply,neg_neg]

theorem summable_norm_sobolevSesquilinearPairing (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) p) (b : WeightedCoeff (Weight.sobolev (-s)) q) :
    Summable (fun n : ℤ => ‖a.val n*star (b.val n)‖) := by
  simpa only [sobolevConjugation_apply,neg_neg] using
    summable_norm_sobolevBilinearPairing s a (sobolevConjugation (-s) b)

theorem norm_sobolevSesquilinearPairing_le (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) p) (b : WeightedCoeff (Weight.sobolev (-s)) q) :
    ‖sobolevSesquilinearPairing s a b‖ ≤ ‖a‖*‖b‖ := by
  simpa only [sobolevSesquilinearPairing,LinearIsometryEquiv.norm_map] using
    norm_sobolevBilinearPairing_le s a (sobolevConjugation (-s) b)

/-- The original physical bilinear product is recovered by conjugating the second function. -/
theorem sobolevSesquilinearPairing_conjugation (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) p) (b : WeightedCoeff (Weight.sobolev (-s)) q) :
    sobolevSesquilinearPairing s a (sobolevConjugation (-s) b) = sobolevBilinearPairing s a b := by
  simp only [sobolevSesquilinearPairing,sobolevConjugation_involutive]

/-- Each fixed second input gives a bounded complex-linear functional. -/
def sobolevSesquilinearLeft (s : ℝ) (b : WeightedCoeff (Weight.sobolev (-s)) q) :
    WeightedCoeff (Weight.sobolev s) p →L[ℂ] ℂ :=
  (sobolevBilinearPairing s).flip (sobolevConjugation (-s) b)

/-- Each fixed first input gives a bounded conjugate-linear functional. -/
def sobolevSesquilinearRight (s : ℝ) (a : WeightedCoeff (Weight.sobolev s) p) :
    WeightedCoeff (Weight.sobolev (-s)) q →L⋆[ℂ] ℂ :=
  (sobolevBilinearPairing s a).comp (sobolevConjugation (-s)).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem sobolevSesquilinearLeft_apply (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) p) (b : WeightedCoeff (Weight.sobolev (-s)) q) :
    sobolevSesquilinearLeft s b a = sobolevSesquilinearPairing s a b := rfl

@[simp] theorem sobolevSesquilinearRight_apply (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) p) (b : WeightedCoeff (Weight.sobolev (-s)) q) :
    sobolevSesquilinearRight s a b = sobolevSesquilinearPairing s a b := rfl

theorem continuous_sobolevSesquilinearPairing (s : ℝ) :
    Continuous (fun ab : WeightedCoeff (Weight.sobolev s) p × WeightedCoeff (Weight.sobolev (-s)) q =>
      sobolevSesquilinearPairing s ab.1 ab.2) := by
  unfold sobolevSesquilinearPairing
  exact ((sobolevBilinearPairing s).continuous.comp continuous_fst).clm_apply
    ((sobolevConjugation (-s)).continuous.comp continuous_snd)

theorem sobolevSesquilinearPairing_smul_left (s : ℝ) (c : ℂ)
    (a : WeightedCoeff (Weight.sobolev s) p) (b : WeightedCoeff (Weight.sobolev (-s)) q) :
    sobolevSesquilinearPairing s (c • a) b = c*sobolevSesquilinearPairing s a b :=
  (sobolevSesquilinearLeft s b).map_smul c a

theorem sobolevSesquilinearPairing_smul_right (s : ℝ) (c : ℂ)
    (a : WeightedCoeff (Weight.sobolev s) p) (b : WeightedCoeff (Weight.sobolev (-s)) q) :
    sobolevSesquilinearPairing s a (c • b) = star c*sobolevSesquilinearPairing s a b :=
  (sobolevSesquilinearRight s a).map_smulₛₗ c b

/-- Changing both first-component signs in the pair basis preserves the scalar product. -/
theorem sobolevSesquilinearPairing_reflection (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) p) (b : WeightedCoeff (Weight.sobolev (-s)) q) :
    sobolevSesquilinearPairing s (reflection s a) (reflection (-s) b) =
      sobolevSesquilinearPairing s a b := by
  simp only [sobolevSesquilinearPairing_apply,reflection_apply]
  exact (Equiv.neg ℤ).tsum_eq (fun n => a.val n*star (b.val n))

end NLS.WeightedCoeff
