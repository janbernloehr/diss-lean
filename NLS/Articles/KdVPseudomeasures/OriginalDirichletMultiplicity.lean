import NLS.Articles.KdVPseudomeasures.OriginalDirichletPointSpectrum
import NLS.KdV.SingularDirichletRealMultiplicity

/-! # Actual Dirichlet algebraic multiplicities on the full original real source

The actual partial operator's complete finite-chain root space is finite
dimensional and has dimension equal to normalized characteristic order.
The full original ordered labels count these exact multiplicities. This
does not assert closedness, compact resolvent or absence of other spectrum.
-/
noncomputable section
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV

/-- The entire actual native algebraic root space is finite dimensional,
for every complex energy of every original real H-minus-one potential. -/
theorem finiteDimensional_originalDirichletRootSpace
    (q : OriginalHminusOnePotential) (lambda : ℂ) :
    FiniteDimensional ℂ (singularDirichletRootSpaceTop q.val lambda) := by
  rw [← periodOneOriginal_originalPeriodOneCoefficients q]
  exact finiteDimensional_singularDirichletRootSpaceTop_of_real
    (originalPeriodOneCoefficients q) (originalPeriodOneCoefficients_real q) lambda

/-- Actual native algebraic multiplicity equals the original normalized
characteristic order, including low, zero and nonreal energies. -/
theorem originalDirichletRootSpace_finrank_eq_analyticOrder
    (q : OriginalHminusOnePotential) (lambda : ℂ) :
    Module.finrank ℂ (singularDirichletRootSpaceTop q.val lambda) =
      analyticOrderNatAt (originalDirichletCharacteristic q) lambda := by
  change Module.finrank ℂ (singularDirichletRootSpaceTop q.val lambda) =
    analyticOrderNatAt (hillHminusDirichlet (originalPeriodOneCoefficients q)) lambda
  rw [← periodOneOriginal_originalPeriodOneCoefficients q]
  exact finrank_singularDirichletRootSpaceTop_eq_analyticOrder_of_real
    (originalPeriodOneCoefficients q) (originalPeriodOneCoefficients_real q) lambda

/-- Every full original real Dirichlet label has actual algebraic multiplicity one. -/
theorem originalDirichletLabels_algebraic_multiplicity_one
    (q : OriginalHminusOnePotential) (n : ℕ+) :
    Module.finrank ℂ (singularDirichletRootSpaceTop q.val (originalDirichletLabels q n:ℂ)) = 1 := by
  have hd : hillHminusDirichlet (originalPeriodOneCoefficients q)
      (originalDirichletLabels q n:ℂ) = 0 := originalDirichletLabels_is_root q n
  rw [← periodOneOriginal_originalPeriodOneCoefficients q,
    finrank_singularDirichletRootSpaceTop_of_real (originalPeriodOneCoefficients q)
      (originalPeriodOneCoefficients_real q) (originalDirichletLabels q n:ℂ), if_pos hd]

/-- The ENTIRE positive-index original label sequence counts exactly the
actual native algebraic multiplicity at EVERY complex energy. -/
theorem originalDirichletLabels_native_global_multiplicity
    (q : OriginalHminusOnePotential) (lambda : ℂ) :
    (∑ᶠ n : ℕ+, if (originalDirichletLabels q n:ℂ) = lambda then (1:ℕ) else 0) =
      Module.finrank ℂ (singularDirichletRootSpaceTop q.val lambda) :=
  (originalDirichletLabels_global_multiplicity q lambda).trans
    (originalDirichletRootSpace_finrank_eq_analyticOrder q lambda).symm

end NLS.Articles.KdVPseudomeasures
