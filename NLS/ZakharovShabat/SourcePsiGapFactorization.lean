import NLS.ZakharovShabat.SourcePsiContourAnalytic
import NLS.ZakharovShabat.SourceSingleRootQuotientAnalytic

/-!
# Separating one gap factor in the psi integrand

Equation (2.24) rewrites the psi integrand near gap `m` as its local
root factor over the standard root times a regular quotient. This
connects the contour equation in Section 12 to the quotient estimates
of Lemma 10.8.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Changing the deleted index in the psi numerator gives an exact
cross-multiplied identity, including at root collisions. -/
theorem sourcePsiCandidate_change_deleted_index
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m : ℤ) (a : Coeff p) (z : ℂ) :
    (displacedRoots a n-z)*sourcePsiCandidate n (z,a) =
      (displacedRoots a m-z)*sourcePsiCandidate m (z,a) := by
  have hn := jointSingleSpectralProduct_eq_deleted hp hp1 n (z,a)
  have hm := jointSingleSpectralProduct_eq_deleted hp hp1 m (z,a)
  unfold sourcePsiCandidate
  linear_combination hn - hm

/-- The regular factor in the local psi contour integrand of (2.24). -/
def sourcePsiGapRegularFactor (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m : ℤ) (a : Coeff p) (ψ : CoeffPair p) (z : ℂ) : ℂ :=
  I * sourceSingleRootQuotientJointProduct hp hp1 m (z,(a,ψ)) /
    (displacedRoots a n-z)

/-- Equation (2.24), on the full gap complement and away from the
deleted numerator root. -/
theorem sourcePsiContourIntegrandJoint_eq_gap_factor
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m : ℤ) (a : Coeff p) (ψ : CoeffPair p) (z : ℂ)
    (hz : z ∈ sourceCanonicalRootDomain hp hp1 ψ)
    (hzn : z ≠ displacedRoots a n) :
    sourcePsiContourIntegrandJoint hp hp1 n (z,(a,ψ)) =
      ((displacedRoots a m-z) /
        sourceStandardRoot hp hp1 ψ m z) *
        sourcePsiGapRegularFactor hp hp1 n m a ψ z := by
  have hnum := sourcePsiCandidate_change_deleted_index hp hp1 n m a z
  have hroot := sourceCanonicalRoot_eq_omitted hp hp1 m ψ z
  have hstd : sourceStandardRoot hp hp1 ψ m z ≠ 0 :=
    sourceStandardRoot_ne_zero_off_segment hp hp1 ψ m z (hz m)
  have homit : sourceStandardRootOmittedProduct hp hp1 m ψ z ≠ 0 :=
    sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ z m
      (fun k _ => hz k)
  have hn : displacedRoots a n-z ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm hzn)
  change sourcePsiCandidate n (z,a) /
      sourceCanonicalRoot hp hp1 ψ z =
    ((displacedRoots a m-z) / sourceStandardRoot hp hp1 ψ m z) *
      (I * (jointDeletedSingleSpectralProduct m (z,a) /
        sourceStandardRootOmittedProduct hp hp1 m ψ z) /
          (displacedRoots a n-z))
  rw [hroot]
  unfold sourcePsiCandidate at hnum ⊢
  field_simp [hstd,homit,hn, Complex.I_ne_zero]
  simp only [Complex.I_sq] at *
  linear_combination ((1 : ℂ)/2)*hnum

/-- The psi contour equation in the local form (2.27). This is the
form to which the selected-gap integral estimate of Lemma 12.3
applies. -/
theorem sourcePsiEquationCoordinate_eq_gap_factor_circleIntegral
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m : ℤ) (a : Coeff p) (ψ : CoeffPair p)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ)
    (havoid : ∀ z ∈ sphere c R, z ≠ displacedRoots a n) :
    sourcePsiEquationCoordinate hp hp1 n m a ψ c R =
      ((n-m : ℤ) : ℂ) *
        (∮ z in C(c,R),
          ((displacedRoots a m-z) /
            sourceStandardRoot hp hp1 ψ m z) *
              sourcePsiGapRegularFactor hp hp1 n m a ψ z) := by
  rw [sourcePsiEquationCoordinate_eq_raw_circleIntegral]
  congr 1
  apply circleIntegral.integral_congr hR
  intro z hz
  exact sourcePsiContourIntegrandJoint_eq_gap_factor
    hp hp1 n m a ψ z (hcircle hz) (havoid z hz)

end NLS.ZakharovShabat
