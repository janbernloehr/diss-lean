import NLS.ZakharovShabat.SourcePsiOriginalJacobianComparison
import NLS.ZakharovShabat.SourcePsiOriginalJacobianContour
import NLS.ZakharovShabat.SourcePsiLimitScalarJacobianEntry

/-!
# Scalar limits on the original root domain

Every entry of the actual original Jacobian converges to its literal
Q* contour entry as the deleted index escapes in either direction.
Original disk separation supplies contour avoidance for all root inputs,
including complex roots outside the spectral gaps.
-/

noncomputable section
open Set Complex Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Coordinate lines commute with deletion of the unused root. -/
theorem sourcePsiEquationCoordinate_deletedLine
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m k : ℤ) (hkn : k ≠ n)
    (a : Coeff p) (φ : CoeffPair p) (d : ℂ) (r : ℝ) (hr : 0 ≤ r) (z : ℂ) :
    sourcePsiEquationCoordinate hp hp1 n m (a+lp.single p k z) φ d r =
      sourcePsiDeletedEquationCoordinate hp hp1 n m
        (Coeff.deleteCoordinateTo n a+Coeff.deletedSingleCLM n k hkn z) φ d r := by
  calc
    _ = sourcePsiDeletedEquationCoordinate hp hp1 n m
        (Coeff.deleteCoordinateTo n (a+lp.single p k z)) φ d r :=
      sourcePsiEquationCoordinate_eq_deletedCoordinate hp hp1 n m _ φ d r hr
    _ = _ := by rw [map_add,Coeff.deleteCoordinateTo_single_other n k hkn]

/-- The original matrix entry is the derivative of the deleted scalar equation. -/
theorem SourceLemma12_4Data.originalJacobianEntry_eq_deletedScalar
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_4Data hp hp1 W) (φ : CoeffPair p) (hφW : φ ∈ W)
    (n m k : ℤ) (a : Coeff p) (P : SourceCriticalRootPeriodCircle hp hp1 φ m) :
    sourcePsiOriginalJacobianEntry hp hp1 n m k a φ =
      sourcePsiDeletedScalarMatrixEntry hp hp1 n m k a φ (P.center:ℂ) P.radius := by
  by_cases hkn : k = n
  · subst k
    rw [sourcePsiOriginalJacobianEntry_deleted_column]
    simp only [sourcePsiDeletedScalarMatrixEntry,dif_neg (not_ne_iff.mpr rfl)]
  rw [H.originalJacobianEntry_eq_contour_deriv φ hφW n m k a P]
  unfold sourcePsiDeletedScalarMatrixEntry
  rw [dif_pos hkn]
  exact congrArg (fun f : ℂ → ℂ => deriv f 0) (funext (fun z =>
    sourcePsiEquationCoordinate_deletedLine hp hp1 n m k hkn a φ
      (P.center:ℂ) P.radius P.radius_pos.le z))

/-- Entrywise convergence for all original placed roots at a real-type source. -/
theorem SourceLemma12_4Data.originalJacobianEntry_tendsto
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (a : Coeff p) (ha : a ∈ sourcePsiOriginalRootPlacement D)
    (m k : ℤ) (d r : ℝ) (hr : 0 < r) (he : D m = ball (d:ℂ) r) :
    Tendsto (fun n : ℤ => sourcePsiOriginalJacobianEntry hp hp1 n m k a φ)
      (Filter.comap Int.natAbs atTop)
      (𝓝 (sourcePsiLimitMatrixEntry hp hp1 m k a φ (d:ℂ) r)) := by
  let P := hD.periodCircle φ hφV m d r hr he
  have hlim := tendsto_sourcePsiDeletedScalarMatrixEntry_at_natAbs hp hp1 m k a φ hφ
    (d:ℂ) r hr.le P.closedBall_subset_omittedDomain P.sphere_subset_rootDomain
    (fun z hz => sub_ne_zero.mpr (hD.originalRootPlacement_avoids_sphere a ha m k d r hr he z hz).symm)
  have heq : (fun n : ℤ => sourcePsiOriginalJacobianEntry hp hp1 n m k a φ) =
      (fun n : ℤ => sourcePsiDeletedScalarMatrixEntry hp hp1 n m k a φ (d:ℂ) r) :=
    funext (fun n => H.originalJacobianEntry_eq_deletedScalar φ hφW n m k a P)
  rwa [heq]

end NLS.ZakharovShabat
