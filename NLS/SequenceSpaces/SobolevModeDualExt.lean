import NLS.SequenceSpaces.SobolevFullDuality
import NLS.ZakharovShabat.Domain

/-! # Full H1 functionals are determined by all raw scalar modes

The proof uses the verified full Sobolev dual, including its exact opposite
Fourier index. Tests at every signed frequency determine the entire functional.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Every signed raw scalar mode is the same finite-coefficient H1 vector. -/
theorem scalarMode_eq_ofFinsupp (n : ℤ) (c : ℂ) :
    scalarMode (p := 2) n c =
      WeightedCoeff.ofFinsupp (Weight.sobolev 1) 2 (Finsupp.single n c) := by
  apply Subtype.ext
  funext k
  simp only [scalarMode_apply, WeightedCoeff.ofFinsupp_apply, Finsupp.single_apply, eq_comm]

/-- No bounded H1 functional is lost by testing all original scalar modes. -/
theorem scalarMode_dual_ext (F G : ScalarDomain 2 →L[ℂ] ℂ)
    (h : ∀ n : ℤ, F (scalarMode n 1) = G (scalarMode n 1)) : F = G := by
  apply (WeightedCoeff.sobolevDualityIsometry (p := 2) (q := 2) 1 (by norm_num)).symm.injective
  apply Subtype.ext
  funext n
  rw [WeightedCoeff.sobolevDualityIsometry_symm_apply,
    WeightedCoeff.sobolevDualityIsometry_symm_apply,
    WeightedCoeff.sobolevCotangent_val, WeightedCoeff.sobolevCotangent_val,
    ← scalarMode_eq_ofFinsupp]
  exact h (-n)

end NLS.ZakharovShabat
