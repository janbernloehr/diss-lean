import NLS.Articles.KdVPseudomeasures.OriginalHillGlobalDiagonalCartesian
import NLS.KdV.HillRealDiagonalCartesian
import NLS.KdV.HillOffIndexRealAbelianValue

/-! Original real-source normalization of the actual Abelian factors.
This establishes individual phase reality and exact diagonal moduli;
the infinite off-index sum and full Birkhoff amplitude remain separate. -/
noncomputable section
open Set Complex NLS.KdV
open scoped Classical
namespace NLS.Articles.KdVPseudomeasures

theorem original_Hill_offIndex_Abelian_values_real (q : OriginalHminusOnePotential) :
    ∀ n m : ℕ+, m ≠ n → (hillHminusPhysicalOffIndexAbelianValue n m (originalPeriodOneCoefficients q)).im = 0 :=
  fun n m hmn => hillHminusPhysicalOffIndexAbelianValue_im_eq_zero_of_real n m hmn _
    (originalPeriodOneCoefficients_real q)

theorem original_Hill_diagonal_factors_conjugate (q : OriginalHminusOnePotential) :
    ∀ n : ℕ+, hillHminusDiagonalCartesianMinus n (originalPeriodOneCoefficients q) =
      star (hillHminusDiagonalCartesianPlus n (originalPeriodOneCoefficients q)) :=
  fun n => hillHminusDiagonalCartesian_conjugate_of_real n _ (originalPeriodOneCoefficients_real q)

theorem original_Hill_diagonal_factor_moduli (q : OriginalHminusOnePotential) :
    ∀ n : ℕ+,
      ‖hillHminusDiagonalCartesianPlus n (originalPeriodOneCoefficients q)‖ =
        hillHminusLabels _ (originalPeriodOneCoefficients_real q) (2*(n:ℕ))-
          hillHminusLabels _ (originalPeriodOneCoefficients_real q) (2*(n:ℕ)-1) ∧
      ‖hillHminusDiagonalCartesianMinus n (originalPeriodOneCoefficients q)‖ =
        hillHminusLabels _ (originalPeriodOneCoefficients_real q) (2*(n:ℕ))-
          hillHminusLabels _ (originalPeriodOneCoefficients_real q) (2*(n:ℕ)-1) :=
  fun n => norm_hillHminusDiagonalCartesian_of_real n _ (originalPeriodOneCoefficients_real q)

theorem original_Hill_doubled_phase_unit_modulus (n : ℕ+) (q : OriginalHminusOnePotential)
    (hg : hillHminusCanonicalGapSquare n (originalPeriodOneCoefficients q) ≠ 0) :
    ‖hillHminusDiagonalPhaseSquare n (originalPeriodOneCoefficients q)‖ = 1 :=
  norm_hillHminusDiagonalPhaseSquare_of_real n _ (originalPeriodOneCoefficients_real q) hg

end NLS.Articles.KdVPseudomeasures
