import NLS.ZakharovShabat.SourcePsiCoordinateVariation
import NLS.ZakharovShabat.SourcePsiGapFactorization

/-!
# Gap-factorized formulas for nonfree psi Jacobian entries

The retained-root variation kernel is written using the selected
standard root and regular factor. The off-diagonal ratio is the one
estimated in Lemma 12.5; on the diagonal it cancels exactly.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The root-variation kernel in the local form used in the proof of
Lemma 12.5. -/
theorem sourcePsiRootVariationKernel_eq_gap_factor
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m k : ℤ) (a : Coeff p) (ψ : CoeffPair p) (z : ℂ)
    (hz : z ∈ sourceCanonicalRootDomain hp hp1 ψ)
    (hzn : z ≠ displacedRoots a n) :
    sourcePsiRootVariationKernel hp hp1 n k a ψ z =
      ((displacedRoots a m-z)/(displacedRoots a k-z)) *
        (sourcePsiGapRegularFactor hp hp1 n m a ψ z /
          sourceStandardRoot hp hp1 ψ m z) := by
  unfold sourcePsiRootVariationKernel
  rw [sourcePsiContourIntegrandJoint_eq_gap_factor
    hp hp1 n m a ψ z hz hzn]
  ring

/-- On the diagonal, differentiation removes the selected numerator
root factor exactly. -/
theorem sourcePsiRootVariationKernel_diagonal_eq_gap_factor
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m : ℤ) (a : Coeff p) (ψ : CoeffPair p) (z : ℂ)
    (hz : z ∈ sourceCanonicalRootDomain hp hp1 ψ)
    (hzn : z ≠ displacedRoots a n)
    (hzm : z ≠ displacedRoots a m) :
    sourcePsiRootVariationKernel hp hp1 n m a ψ z =
      sourcePsiGapRegularFactor hp hp1 n m a ψ z /
        sourceStandardRoot hp hp1 ψ m z := by
  rw [sourcePsiRootVariationKernel_eq_gap_factor
    hp hp1 n m m a ψ z hz hzn]
  rw [div_self (sub_ne_zero.mpr (Ne.symm hzm)),one_mul]

/-- The weighted variation integral is the selected-gap integral with
its explicit moved-root ratio. -/
theorem sourcePsiRootVariation_slope_eq_gap_factor_circleIntegral
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m k : ℤ) (a : Coeff p) (ψ : CoeffPair p)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ)
    (havoidn : ∀ z ∈ sphere c R, z ≠ displacedRoots a n) :
    ((n-m : ℤ) : ℂ) *
      (∮ z in C(c,R), sourcePsiRootVariationKernel hp hp1 n k a ψ z) =
      ∮ z in C(c,R),
        ((displacedRoots a m-z)/(displacedRoots a k-z)) *
          ((((n-m : ℤ) : ℂ) *
            sourcePsiGapRegularFactor hp hp1 n m a ψ z) /
              sourceStandardRoot hp hp1 ψ m z) := by
  rw [← circleIntegral.integral_const_mul]
  apply circleIntegral.integral_congr hR
  intro z hz
  dsimp only
  rw [sourcePsiRootVariationKernel_eq_gap_factor
    hp hp1 n m k a ψ z (hcircle hz) (havoidn z hz)]
  ring

/-- The diagonal variation integral has no extra Cauchy ratio. -/
theorem sourcePsiRootVariation_diagonal_slope_eq_gap_circleIntegral
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m : ℤ) (a : Coeff p) (ψ : CoeffPair p)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ)
    (havoidn : ∀ z ∈ sphere c R, z ≠ displacedRoots a n)
    (havoidm : ∀ z ∈ sphere c R, z ≠ displacedRoots a m) :
    ((n-m : ℤ) : ℂ) *
      (∮ z in C(c,R), sourcePsiRootVariationKernel hp hp1 n m a ψ z) =
      ∮ z in C(c,R),
        (((n-m : ℤ) : ℂ) *
          sourcePsiGapRegularFactor hp hp1 n m a ψ z) /
            sourceStandardRoot hp hp1 ψ m z := by
  rw [← circleIntegral.integral_const_mul]
  apply circleIntegral.integral_congr hR
  intro z hz
  dsimp only
  rw [sourcePsiRootVariationKernel_diagonal_eq_gap_factor
    hp hp1 n m a ψ z (hcircle hz) (havoidn z hz) (havoidm z hz)]
  ring

/-- The scalar deleted-coordinate Jacobian entry equals the
gap-factorized integral whenever the contour avoids both relevant
roots. -/
theorem deriv_sourcePsiDeletedEquationCoordinate_eq_gap_factor_circleIntegral
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m k : ℤ) (hkn : k ≠ n)
    (a : DeletedCoeff p n) (ψ : CoeffPair p)
    (hψ : IsRealType (CoeffPair.toMax p ψ))
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ)
    (havoidn : ∀ z ∈ sphere c R,
      z ≠ displacedRoots (a : Coeff p) n)
    (havoidk : ∀ z ∈ sphere c R,
      z ≠ displacedRoots (a : Coeff p) k) :
    deriv (fun t : ℂ => sourcePsiDeletedEquationCoordinate hp hp1 n m
      (a+Coeff.deletedSingleCLM n k hkn t) ψ c R) 0 =
      ∮ z in C(c,R),
        ((displacedRoots (a : Coeff p) m-z)/
          (displacedRoots (a : Coeff p) k-z)) *
          ((((n-m : ℤ) : ℂ) *
            sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p) ψ z) /
              sourceStandardRoot hp hp1 ψ m z) := by
  rw [(hasDerivAt_sourcePsiDeletedEquationCoordinate_rootVariation
    hp hp1 n m k hkn a ψ hψ c R hR hcircle havoidk).deriv]
  exact sourcePsiRootVariation_slope_eq_gap_factor_circleIntegral
    hp hp1 n m k (a : Coeff p) ψ c R hR hcircle havoidn

/-- The diagonal scalar Jacobian entry is a single weighted
standard-root integral. -/
theorem deriv_sourcePsiDeletedEquationCoordinate_diagonal_eq_gap_circleIntegral
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m : ℤ) (hmn : m ≠ n)
    (a : DeletedCoeff p n) (ψ : CoeffPair p)
    (hψ : IsRealType (CoeffPair.toMax p ψ))
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ)
    (havoidn : ∀ z ∈ sphere c R,
      z ≠ displacedRoots (a : Coeff p) n)
    (havoidm : ∀ z ∈ sphere c R,
      z ≠ displacedRoots (a : Coeff p) m) :
    deriv (fun t : ℂ => sourcePsiDeletedEquationCoordinate hp hp1 n m
      (a+Coeff.deletedSingleCLM n m hmn t) ψ c R) 0 =
      ∮ z in C(c,R),
        (((n-m : ℤ) : ℂ) *
          sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p) ψ z) /
            sourceStandardRoot hp hp1 ψ m z := by
  rw [(hasDerivAt_sourcePsiDeletedEquationCoordinate_rootVariation
    hp hp1 n m m hmn a ψ hψ c R hR hcircle havoidm).deriv]
  exact sourcePsiRootVariation_diagonal_slope_eq_gap_circleIntegral
    hp hp1 n m (a : Coeff p) ψ c R hR hcircle havoidn havoidm

end NLS.ZakharovShabat
