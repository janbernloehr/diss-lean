import NLS.SequenceSpaces.DeletedExponentEmbedding
import NLS.ZakharovShabat.SourceCanonicalRootExponent
import NLS.ZakharovShabat.SourcePsiDeletedCoordinate

/-! # Exponent compatibility of the actual psi contour equations

Coefficient inclusion preserves every literal numerator factor and
the normalized canonical root. Therefore the contour equations agree
on the same circles, including their original normalization factors.
-/

noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

theorem sourcePsiCandidate_exponent (hpq : p ≤ q) (n : ℤ) (a : Coeff p) (z : ℂ) :
    sourcePsiCandidate n (z,a) = sourcePsiCandidate n (z,Coeff.exponentInclusion hpq a) := by
  have hpartial : (fun N => jointDeletedSingleSpectralPartialProduct n N (z,a)) =
      (fun N => jointDeletedSingleSpectralPartialProduct n N (z,Coeff.exponentInclusion hpq a)) := by
    funext N
    unfold jointDeletedSingleSpectralPartialProduct
    apply congrArg (fun x : ℂ => x / singleSpectralDenominator n)
    apply Finset.prod_congr rfl
    intro m _
    simp only [singleSpectralFactor, displacedRoots, Coeff.exponentInclusion_apply]
  exact congrArg (fun f : ℕ → ℂ => -2 * limUnder atTop f) hpartial

theorem sourcePsiContour_exponent
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (hpq : p ≤ q)
    (n : ℤ) (a : Coeff p) (φ : CoeffPair p) (c : ℂ) (R : ℝ) :
    sourcePsiContour hp hp1 n a φ c R =
      sourcePsiContour hq hq1 n (Coeff.exponentInclusion hpq a) (CoeffPair.exponentInclusion hpq φ) c R := by
  have heq : (fun z => sourcePsiContourIntegrandJoint hp hp1 n (z,(a,φ))) =
      (fun z => sourcePsiContourIntegrandJoint hq hq1 n
        (z,(Coeff.exponentInclusion hpq a,CoeffPair.exponentInclusion hpq φ))) := by
    funext z
    exact congrArg₂ (fun x y : ℂ => x / y) (sourcePsiCandidate_exponent hpq n a z)
      (sourceCanonicalRoot_exponent hp hq hp1 hq1 hpq φ z)
  exact congrArg (fun f : ℂ → ℂ => (2*Real.pi : ℂ)⁻¹ * (∮ z in C(c,R), f z)) heq

theorem sourcePsiEquationCoordinate_exponent
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (hpq : p ≤ q)
    (n m : ℤ) (a : Coeff p) (φ : CoeffPair p) (c : ℂ) (R : ℝ) :
    sourcePsiEquationCoordinate hp hp1 n m a φ c R =
      sourcePsiEquationCoordinate hq hq1 n m (Coeff.exponentInclusion hpq a)
        (CoeffPair.exponentInclusion hpq φ) c R := by
  rw [sourcePsiEquationCoordinate, sourcePsiEquationCoordinate,
    sourcePsiContour_exponent hp hq hp1 hq1 hpq]

theorem sourcePsiDeletedContour_exponent
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (hpq : p ≤ q)
    (n : ℤ) (a : DeletedCoeff p n) (φ : CoeffPair p) (c : ℂ) (R : ℝ) :
    sourcePsiDeletedContour hp hp1 n a φ c R =
      sourcePsiDeletedContour hq hq1 n (Coeff.deletedExponentInclusion hpq n a)
        (CoeffPair.exponentInclusion hpq φ) c R :=
  sourcePsiContour_exponent hp hq hp1 hq1 hpq n (a : Coeff p) φ c R

end NLS.ZakharovShabat
