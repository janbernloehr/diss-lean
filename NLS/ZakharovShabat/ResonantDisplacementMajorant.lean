import NLS.ZakharovShabat.RootDisplacementPower
import NLS.ZakharovShabat.ResonantLeadingPowerTail
import NLS.ZakharovShabat.OffDiagonalSummability
import NLS.ZakharovShabat.DiagonalSummability

/-!
# A common power majorant for both resonant roots

The same scalar sequence bounds the sum of the two displacement powers,
for any choice of the two roots. It contains the actual diagonal and
weighted remainder suprema and the signed leading Fourier-mode powers.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Power majorant for the sum of the two resonant root displacements. -/
def resonantDisplacementMajorant (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) : ℝ :=
  2 * (2 : ℝ)^(p.toReal-1) * ((resonantDiagonalSup hp w φ n)^p.toReal +
    (2 : ℝ)^(p.toReal-1) / 2 * (resonantLeadingPower w φ n +
      (resonantBMinusRemainderSup hp w φ n)^p.toReal + (resonantBPlusRemainderSup hp w φ n)^p.toReal))

/-- Actual strip bounds turn the scalar root estimate into a common majorant for any pair of zeros. -/
theorem resonantRoots_displacement_le_majorant (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ)
    (hb : ∀ z ∈ resonantStrip n,
      ‖weightedResonantAExtension hp w φ n z‖ ≤ resonantDiagonalSup hp w φ n ∧
      ‖weightedResonantBMinusExtension hp w φ n z-φ.fst.val (-(2*n))‖ ≤ resonantBMinusRemainderSup hp w φ n ∧
      ‖weightedResonantBPlusExtension hp w φ n z-φ.snd.val (2*n)‖ ≤ resonantBPlusRemainderSup hp w φ n)
    (x y : ℂ) (hx : x ∈ resonantStrip n) (hy : y ∈ resonantStrip n)
    (hx0 : resonantDeterminantExtension hp w φ n x = 0)
    (hy0 : resonantDeterminantExtension hp w φ n y = 0) :
    ‖x-(Real.pi : ℂ)*n‖^p.toReal + ‖y-(Real.pi : ℂ)*n‖^p.toReal ≤
      resonantDisplacementMajorant hp w φ n := by
  have hlead₁ : ‖φ.fst.val (-(2*n))‖^p.toReal ≤ (w (2*n)*‖φ.fst.val (-(2*n))‖)^p.toReal :=
    Real.rpow_le_rpow (norm_nonneg _) (le_mul_of_one_le_left (norm_nonneg _) (w.one_le _)) ENNReal.toReal_nonneg
  have hlead₂ : ‖φ.snd.val (2*n)‖^p.toReal ≤ (w (2*n)*‖φ.snd.val (2*n)‖)^p.toReal :=
    Real.rpow_le_rpow (norm_nonneg _) (le_mul_of_one_le_left (norm_nonneg _) (w.one_le _)) ENNReal.toReal_nonneg
  have hpoint (z : ℂ) (hz : z ∈ resonantStrip n) (hz0 : resonantDeterminantExtension hp w φ n z = 0) :
      ‖z-(Real.pi : ℂ)*n‖^p.toReal ≤ (2 : ℝ)^(p.toReal-1) *
        ((resonantDiagonalSup hp w φ n)^p.toReal + (2 : ℝ)^(p.toReal-1)/2 *
          (resonantLeadingPower w φ n + (resonantBMinusRemainderSup hp w φ n)^p.toReal +
            (resonantBPlusRemainderSup hp w φ n)^p.toReal)) := by
    apply (resonantRoot_displacement_rpow_le hp w φ n z hz0).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply add_le_add (Real.rpow_le_rpow (norm_nonneg _) (hb z hz).1 ENNReal.toReal_nonneg)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hm' := Real.rpow_le_rpow (norm_nonneg _) (hb z hz).2.1 (ENNReal.toReal_nonneg (a := p))
    have hp'' := Real.rpow_le_rpow (norm_nonneg _) (hb z hz).2.2 (ENNReal.toReal_nonneg (a := p))
    unfold resonantLeadingPower
    linarith
  have h := add_le_add (hpoint x hx hx0) (hpoint y hy hy0)
  simpa only [← two_mul, resonantDisplacementMajorant, mul_assoc] using h

/-- Under actual nonnegative suprema, the majorant is nonnegative. -/
theorem resonantDisplacementMajorant_nonneg (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ)
    (ha : 0 ≤ resonantDiagonalSup hp w φ n)
    (hm : 0 ≤ resonantBMinusRemainderSup hp w φ n) (hp' : 0 ≤ resonantBPlusRemainderSup hp w φ n) :
    0 ≤ resonantDisplacementMajorant hp w φ n := by
  have hw : 0 ≤ w (2*n) := (w.positive _).le
  unfold resonantDisplacementMajorant resonantLeadingPower
  positivity

end NLS.ZakharovShabat
