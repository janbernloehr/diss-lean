import NLS.Articles.KdVPseudomeasures.OriginalDirichletMultiplicity
import NLS.KdV.SingularDirichletAlgebraicMultiplicity

/-! # Original real Dirichlet labels and the actual finite algebraic multiplicity

The operator multiplicity is defined from the full native root space, whose
finite dimensionality is now proved for every complex potential. On the
article's original real source it agrees with the verified characteristic
orders and complete intrinsic label counts.
-/
noncomputable section
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV

/-- Actual operator algebraic multiplicity equals normalized characteristic
order for every original real potential and every complex energy. -/
theorem originalDirichletAlgebraicMultiplicity_eq_analyticOrder
    (q : OriginalHminusOnePotential) (lambda : ℂ) :
    singularDirichletAlgebraicMultiplicity q.val lambda =
      analyticOrderNatAt (originalDirichletCharacteristic q) lambda :=
  originalDirichletRootSpace_finrank_eq_analyticOrder q lambda

/-- Each complete original label has actual operator algebraic multiplicity one. -/
theorem originalDirichletLabels_actual_algebraic_multiplicity_one
    (q : OriginalHminusOnePotential) (n : ℕ+) :
    singularDirichletAlgebraicMultiplicity q.val (originalDirichletLabels q n:ℂ) = 1 :=
  originalDirichletLabels_algebraic_multiplicity_one q n

/-- The full intrinsic original sequence counts exactly the actual finite
operator algebraic multiplicity at every complex energy. -/
theorem originalDirichletLabels_actual_global_algebraic_multiplicity
    (q : OriginalHminusOnePotential) (lambda : ℂ) :
    (∑ᶠ n : ℕ+, if (originalDirichletLabels q n:ℂ) = lambda then (1:ℕ) else 0) =
      singularDirichletAlgebraicMultiplicity q.val lambda :=
  originalDirichletLabels_native_global_multiplicity q lambda

end NLS.Articles.KdVPseudomeasures
