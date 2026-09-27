import NLS.ZakharovShabat.SourcePsiCoordinateVariation
import NLS.ZakharovShabat.SourcePsiFreeJacobian

/-!
# Nonfree root variations on free-centered psi contours

If the displacement sequence is small in `ℓᵖ` norm, every displaced
root stays away from a free-centered circle whose radius leaves room
both to the center and to the next lattice point. The nonfree scalar
Jacobian integral can then be used on all such circles with the source
potential fixed at zero.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A free-centered circle avoids every root displaced by a sequence
smaller than the circle's inner and outer margins. -/
theorem freeCircle_avoids_displacedRoots_of_norm_small
    (a : Coeff p) (m k : ℤ) (r : ℝ)
    (hinner : ‖a‖ < r) (houter : ‖a‖+r < Real.pi)
    (z : ℂ) (hz : z ∈ sphere ((Real.pi : ℂ)*m) r) :
    z ≠ displacedRoots a k := by
  have hcoord : ‖a k‖ ≤ ‖a‖ :=
    lp.norm_apply_le_norm (ne_of_gt (zero_lt_one.trans_le Fact.out)) a k
  intro he
  by_cases hmk : m = k
  · subst k
    have hrad : dist (displacedRoots a m) ((Real.pi : ℂ)*m) = r := by
      rw [← he]
      exact mem_sphere.mp hz
    have hdist : dist (displacedRoots a m) ((Real.pi : ℂ)*m) = ‖a m‖ := by
      rw [dist_eq_norm]
      change ‖((Real.pi : ℂ)*m+a m)-((Real.pi : ℂ)*m)‖ = ‖a m‖
      ring_nf
    linarith
  · have hπ : r+‖a‖ < Real.pi := by linarith
    have hdist : dist ((Real.pi : ℂ)*k) z = ‖a k‖ := by
      rw [he,dist_eq_norm]
      change ‖((Real.pi : ℂ)*k)-(((Real.pi : ℂ)*k)+a k)‖ = ‖a k‖
      rw [sub_add_cancel_left, norm_neg]
    have hfreeIn : (Real.pi : ℂ)*k ∈
        closedBall ((Real.pi : ℂ)*m) (r+‖a‖) := by
      apply mem_closedBall.mpr
      calc
        dist ((Real.pi : ℂ)*k) ((Real.pi : ℂ)*m) ≤
            dist ((Real.pi : ℂ)*k) z + dist z ((Real.pi : ℂ)*m) :=
          dist_triangle _ _ _
        _ = ‖a k‖+r := by rw [hdist, mem_sphere.mp hz]
        _ ≤ r+‖a‖ := by linarith
    exact (freeCenter_not_mem_closedBall_other m k hmk
      (r+‖a‖) hπ) hfreeIn

/-- At zero source potential, every sufficiently small root sequence
has the explicit nonfree scalar Jacobian entry on a free-centered
circle. -/
theorem hasDerivAt_sourcePsiEquationCoordinate_freeCircle_smallRoots
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m k : ℤ) (hkn : k ≠ n)
    (a : Coeff p) (r : ℝ)
    (hinner : ‖a‖ < r) (houter : ‖a‖+r < Real.pi) :
    HasDerivAt
      (fun t : ℂ => sourcePsiEquationCoordinate hp hp1 n m
        (a+lp.single p k t) (0 : CoeffPair p)
        ((Real.pi : ℂ)*m) r)
      (((n-m : ℤ) : ℂ) *
        (∮ z in C((Real.pi : ℂ)*m,r),
          sourcePsiRootVariationKernel hp hp1 n k a
            (0 : CoeffPair p) z)) 0 := by
  have hr : 0 < r := by nlinarith [norm_nonneg a]
  have hrπ : r < Real.pi := by nlinarith [norm_nonneg a]
  have hcircle := freeCircle_subset_sourceCanonicalRootDomain
    hp hp1 m r hr hrπ
  have havoid (z : ℂ)
      (hz : z ∈ sphere ((Real.pi : ℂ)*m) r) :
      z ≠ displacedRoots a k :=
    freeCircle_avoids_displacedRoots_of_norm_small
      a m k r hinner houter z hz
  exact hasDerivAt_sourcePsiEquationCoordinate_rootVariation
    hp hp1 n m k hkn a (0 : CoeffPair p) (by simp)
      ((Real.pi : ℂ)*m) r hr.le hcircle havoid

/-- The same free-circle formula on the deleted-coordinate Banach
space used for the unknown root displacements. -/
theorem hasDerivAt_sourcePsiDeletedEquationCoordinate_freeCircle_smallRoots
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m k : ℤ) (hkn : k ≠ n)
    (a : DeletedCoeff p n) (r : ℝ)
    (hinner : ‖a‖ < r) (houter : ‖a‖+r < Real.pi) :
    HasDerivAt
      (fun t : ℂ => sourcePsiDeletedEquationCoordinate hp hp1 n m
        (a+Coeff.deletedSingleCLM n k hkn t) (0 : CoeffPair p)
        ((Real.pi : ℂ)*m) r)
      (((n-m : ℤ) : ℂ) *
        (∮ z in C((Real.pi : ℂ)*m,r),
          sourcePsiRootVariationKernel hp hp1 n k (a : Coeff p)
            (0 : CoeffPair p) z)) 0 := by
  have hr : 0 < r := by nlinarith [norm_nonneg a]
  have hrπ : r < Real.pi := by nlinarith [norm_nonneg a]
  have hcircle := freeCircle_subset_sourceCanonicalRootDomain
    hp hp1 m r hr hrπ
  have havoid (z : ℂ)
      (hz : z ∈ sphere ((Real.pi : ℂ)*m) r) :
      z ≠ displacedRoots (a : Coeff p) k :=
    freeCircle_avoids_displacedRoots_of_norm_small
      (a : Coeff p) m k r hinner houter z hz
  exact hasDerivAt_sourcePsiDeletedEquationCoordinate_rootVariation
    hp hp1 n m k hkn a (0 : CoeffPair p) (by simp)
      ((Real.pi : ℂ)*m) r hr.le hcircle havoid

end NLS.ZakharovShabat
