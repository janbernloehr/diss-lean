import NLS.ZakharovShabat.SourcePsiDoubleOmittedProduct
import NLS.ZakharovShabat.SourcePsiDeletedIndexEquation

/-!
# Equation (2.27) on the literal deleted-index spaces

The selected-gap contour formula keeps the signed n-m factor and applies
to arbitrary numerator roots on every original period circle.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Equation (2.27) with the literal double-omitted factor and no numerator-root avoidance. -/
theorem sourcePsiEquationCoordinate_eq_zeta_circleIntegral
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ) (hmn : m ≠ n)
    (a : Coeff p) (ψ : CoeffPair p) (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ) :
    sourcePsiEquationCoordinate hp hp1 n m a ψ c R =
      ((n-m:ℤ):ℂ) * (∮ z in C(c,R),
        ((displacedRoots a m-z)/sourceStandardRoot hp hp1 ψ m z) *
          sourcePsiZeta hp hp1 n m a ψ z) := by
  rw [sourcePsiEquationCoordinate_eq_raw_circleIntegral]
  congr 1
  apply circleIntegral.integral_congr hR
  intro z hz
  exact sourcePsiContourIntegrandJoint_eq_zeta hp hp1 n m hmn a ψ z (hcircle hz)

/-- Every actual literal-index coordinate has the selected-gap contour representation. -/
theorem SourceLemma12_4Data.deletedIndexEquation_eq_zeta_circleIntegral
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_4Data hp hp1 W) (ψ : CoeffPair p) (hψ : ψ ∈ W)
    (n : ℤ) (a : DeletedIndexCoeff p n) (m : {m : ℤ // m ≠ n})
    (D : SourceCriticalRootPeriodCircle hp hp1 ψ m.val) :
    sourcePsiDeletedIndexEquation hp hp1 n ψ a m =
      ((n-m.val:ℤ):ℂ) * (∮ z in C((D.center:ℂ),D.radius),
        ((displacedRoots ((DeletedCoeff.indexEquiv hp n).symm a : Coeff p) m.val-z)/
          sourceStandardRoot hp hp1 ψ m.val z) *
            sourcePsiZeta hp hp1 n m.val ((DeletedCoeff.indexEquiv hp n).symm a : Coeff p) ψ z) := by
  rw [sourcePsiDeletedIndexEquation,DeletedCoeff.indexEquiv_apply,H.equation ψ hψ n _ m.val D]
  exact sourcePsiEquationCoordinate_eq_zeta_circleIntegral hp hp1 n m.val m.property
    ((DeletedCoeff.indexEquiv hp n).symm a : Coeff p) ψ (D.center:ℂ) D.radius
      D.radius_pos.le D.sphere_subset_rootDomain

end NLS.ZakharovShabat
