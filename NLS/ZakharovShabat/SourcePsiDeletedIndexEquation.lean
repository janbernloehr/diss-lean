import NLS.SequenceSpaces.DeletedCoordinateEquiv
import NLS.ZakharovShabat.SourceLemma12_4

/-!
# Equation (2.22) on the literal deleted-index spaces

Transport both input and output through the exact linear isometry between
lp on the retained integers and the zero-at-n realization. The resulting
map has the original contour coordinates, unchanged norms and exactly the
same solutions on the full original source domain.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The source-first functional F^n on the literal input and output spaces. -/
def sourcePsiDeletedIndexEquation (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (ψ : CoeffPair p) (a : DeletedIndexCoeff p n) : DeletedIndexCoeff p n :=
  DeletedCoeff.indexEquiv hp n
    (sourcePsiOriginalEquation hp hp1 n ((DeletedCoeff.indexEquiv hp n).symm a) ψ)

/-- Every retained coordinate is precisely the original unnormalized contour equation. -/
theorem SourceLemma12_4Data.deletedIndexEquation_apply
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_4Data hp hp1 W) (ψ : CoeffPair p) (hψ : ψ ∈ W)
    (n : ℤ) (a : DeletedIndexCoeff p n) (m : {m : ℤ // m ≠ n})
    (D : SourceCriticalRootPeriodCircle hp hp1 ψ m.val) :
    sourcePsiDeletedIndexEquation hp hp1 n ψ a m =
      ((n-m.val : ℤ) : ℂ) *
        (∮ z in C((D.center : ℂ),D.radius),
          sourcePsiCandidate n (z,((DeletedCoeff.indexEquiv hp n).symm a : Coeff p)) /
            sourceCanonicalRoot hp hp1 ψ z) := by
  rw [sourcePsiDeletedIndexEquation,DeletedCoeff.indexEquiv_apply,
    H.equation ψ hψ n _ m.val D,sourcePsiEquationCoordinate_eq_raw_circleIntegral]
  rfl

/-- Transport preserves the exact norm of the full sequence-valued equation. -/
theorem norm_sourcePsiDeletedIndexEquation (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (ψ : CoeffPair p) (a : DeletedIndexCoeff p n) :
    ‖sourcePsiDeletedIndexEquation hp hp1 n ψ a‖ =
      ‖sourcePsiOriginalEquation hp hp1 n ((DeletedCoeff.indexEquiv hp n).symm a) ψ‖ :=
  (DeletedCoeff.indexEquiv hp n).norm_map _

/-- No solutions are added or lost by the closed-kernel representation. -/
theorem sourcePsiDeletedIndexEquation_eq_zero_iff (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (ψ : CoeffPair p) (a : DeletedIndexCoeff p n) :
    sourcePsiDeletedIndexEquation hp hp1 n ψ a = 0 ↔
      sourcePsiOriginalEquation hp hp1 n ((DeletedCoeff.indexEquiv hp n).symm a) ψ = 0 :=
  (DeletedCoeff.indexEquiv hp n).map_eq_zero_iff

/-- The simultaneous root family solves the literal deleted-index equation on the same W. -/
theorem SourceTheorem12_1Data.deletedIndexEquation_zero
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (H : SourceTheorem12_1Data hp hp1 W₀ W s) (hW₀ : IsOpen W₀)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ) :
    sourcePsiDeletedIndexEquation hp hp1 n ψ (DeletedCoeff.indexEquiv hp n (s n ψ)) = 0 := by
  rw [sourcePsiDeletedIndexEquation_eq_zero_iff,
    (DeletedCoeff.indexEquiv hp n).symm_apply_apply]
  exact H.originalEquation_zero hW₀ ψ hψ n

end NLS.ZakharovShabat
