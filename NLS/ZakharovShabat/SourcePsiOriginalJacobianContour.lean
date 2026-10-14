import NLS.ZakharovShabat.SourcePsiOriginalJacobian
import NLS.ZakharovShabat.SourcePsiOriginalOmega
import NLS.ZakharovShabat.SourcePsiDoubleOmittedProduct
import NLS.ZakharovShabat.SourcePsiCoordinateVariation

/-!
# Original Jacobian contour formulas

The full root-placement condition supplies the contour avoidance needed
to differentiate every retained coordinate. The resulting formulas use
the literal double-omitted product of (2.24), including every central
index. The diagonal cancels its root factor on the original boundary.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem SourceLemma12_4Data.originalJacobianEntry_contour
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψW : ψ ∈ W) (hψV : ψ ∈ V)
    (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n m k : ℤ) (hmn : m ≠ n) (hkn : k ≠ n)
    (a : Coeff p) (ha : a ∈ sourcePsiOriginalRootPlacement D)
    (d r : ℝ) (hr : 0 < r) (he : D m = ball (d:ℂ) r) :
    sourcePsiOriginalJacobianEntry hp hp1 n m k a ψ =
      ∮ z in C((d:ℂ),r), ((displacedRoots a m-z)/(displacedRoots a k-z))*
        ((((n-m:ℤ):ℂ)*sourcePsiZeta hp hp1 n m a ψ z)/sourceStandardRoot hp hp1 ψ m z) := by
  let P := hD.periodCircle ψ hψV m d r hr he
  rw [H.originalJacobianEntry_eq_contour_deriv ψ hψW n m k a P]
  dsimp only [P, SourceIsolatingNeighborhoods.periodCircle]
  rw [(hasDerivAt_sourcePsiEquationCoordinate_rootVariation hp hp1 n m k hkn a ψ hreal
    (d:ℂ) r hr.le P.sphere_subset_rootDomain
    (hD.originalRootPlacement_avoids_sphere a ha m k d r hr he)).deriv]
  rw [← circleIntegral.integral_const_mul]
  apply circleIntegral.integral_congr hr.le
  intro z hz
  dsimp only
  unfold sourcePsiRootVariationKernel
  rw [sourcePsiContourIntegrandJoint_eq_zeta hp hp1 n m hmn a ψ z
    (P.sphere_subset_rootDomain hz)]
  ring

theorem SourceLemma12_4Data.originalJacobianEntry_diagonal_contour
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψW : ψ ∈ W) (hψV : ψ ∈ V)
    (hreal : IsRealType (CoeffPair.toMax p ψ)) (n m : ℤ) (hmn : m ≠ n)
    (a : Coeff p) (ha : a ∈ sourcePsiOriginalRootPlacement D)
    (d r : ℝ) (hr : 0 < r) (he : D m = ball (d:ℂ) r) :
    sourcePsiOriginalJacobianEntry hp hp1 n m m a ψ =
      ∮ z in C((d:ℂ),r),
        (((n-m:ℤ):ℂ)*sourcePsiZeta hp hp1 n m a ψ z)/sourceStandardRoot hp hp1 ψ m z := by
  rw [H.originalJacobianEntry_contour hD ψ hψW hψV hreal n m m hmn hmn a ha d r hr he]
  apply circleIntegral.integral_congr hr.le
  intro z hz
  dsimp only
  rw [div_self (sub_ne_zero.mpr
    (hD.originalRootPlacement_avoids_sphere a ha m m d r hr he z hz).symm), one_mul]

end NLS.ZakharovShabat
