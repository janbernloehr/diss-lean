import NLS.ZakharovShabat.SourcePsiContourExponent
import NLS.ZakharovShabat.SourcePsiGapRootMap
import NLS.ZakharovShabat.SourceBoundaryExponentDifferential
import NLS.ZakharovShabat.SourcePsiLemma12_10

/-! # The canonical real psi roots are independent of the exponent

Source inclusion preserves gap placement and every actual normalized
contour equation. The zero equation really has all its coordinates
zero in the larger sequence space, so no out-of-domain default is
used. Uniqueness identifies the included root vector with the actual
selected gap root at the new exponent.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- An actual gap-contained solution remains a solution after
coefficient-preserving exponent inclusion, on the same contour family. -/
theorem SourcePsiGapSolution.exponent
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (hpq : p ≤ q)
    (n : ℤ) (φ : CoeffPair p) (a : DeletedCoeff p n)
    (ha : SourcePsiGapSolution hp hp1 n φ a) :
    SourcePsiGapSolution hq hq1 n (CoeffPair.exponentInclusion hpq φ)
      (Coeff.deletedExponentInclusion hpq n a) := by
  obtain ⟨hgap,c,R,hcenter,hgeom,hcoord,hzero⟩ := ha
  have heq (m : ℤ) : sourcePsiEquationCoordinate hq hq1 n m
      (Coeff.exponentInclusion hpq (a : Coeff p)) (CoeffPair.exponentInclusion hpq φ) (c m) (R m) = 0 := by
    rw [← sourcePsiEquationCoordinate_exponent hp hq hp1 hq1 hpq n m (a : Coeff p) φ,
      ← hcoord m, hzero]
    rfl
  have hex : ∃ F : DeletedCoeff q n, ∀ m : ℤ, (F : Coeff q) m =
      sourcePsiEquationCoordinate hq hq1 n m
        (Coeff.deletedExponentInclusion hpq n a : Coeff q) (CoeffPair.exponentInclusion hpq φ) (c m) (R m) := by
    refine ⟨0,?_⟩
    intro m
    exact (heq m).symm
  have hcoords (m : ℤ) := sourcePsiSelectedEquationSequence_apply_of_exists hq hq1 n c R
    (Coeff.deletedExponentInclusion hpq n a) (CoeffPair.exponentInclusion hpq φ) hex m
  refine ⟨?_,c,R,hcenter,?_,hcoords,?_⟩
  · intro m hm
    rw [← sourcePeriodicSegment_exponent hp hq hp1 hq1 hpq φ m]
    exact hgap m hm
  · intro m
    rw [← sourcePeriodicSegment_exponent hp hq hp1 hq1 hpq φ m,
      ← sourceStandardRootOmittedDomain_exponent hp hq hp1 hq1 hpq φ m]
    exact hgeom m
  · apply Subtype.ext
    ext m
    rw [hcoords m]
    exact heq m

/-- The selected real gap psi root vector is the same coefficient
sequence at every larger finite source exponent. -/
theorem sourcePsiGapRoot_exponent
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (hpq : p ≤ q)
    (n : ℤ) (φ : realTypeSourceLocus p) :
    Coeff.deletedExponentInclusion hpq n (sourcePsiGapRoot hp hp1 n φ) =
      sourcePsiGapRoot hq hq1 n (realTypeSourceExponentInclusion hpq φ) := by
  apply SourcePsiGapSolution.eq_sourcePsiGapRoot hq hq1 n
  exact (sourcePsiGapRoot_solution hp hp1 n φ).exponent hp hq hp1 hq1 hpq n φ.val _

/-- The entire normalized psi numerator chosen by the actual real
gap-root construction is independent of the source exponent. -/
theorem sourcePsiCandidate_gapRoot_exponent
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (hpq : p ≤ q)
    (n : ℤ) (φ : realTypeSourceLocus p) (z : ℂ) :
    sourcePsiCandidate n (z,(sourcePsiGapRoot hp hp1 n φ : Coeff p)) =
      sourcePsiCandidate n
        (z,(sourcePsiGapRoot hq hq1 n (realTypeSourceExponentInclusion hpq φ) : Coeff q)) := by
  rw [← sourcePsiGapRoot_exponent hp hq hp1 hq1 hpq n φ]
  exact sourcePsiCandidate_exponent hpq n _ z

/-- Any of the actual common-domain complex psi extensions have the
same real-source root values after exponent inclusion. -/
theorem SourcePsiIsolatingComplexExtension.real_exponent_agreement
    {hp : p ≠ ⊤} {hq : q ≠ ⊤} {hp1 : 1 < p} {hq1 : 1 < q}
    {W : Set (CoeffPair p)} {V : Set (CoeffPair q)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    {t : (n : ℤ) → CoeffPair q → DeletedCoeff q n}
    (D : SourcePsiIsolatingComplexExtension hp hp1 W s)
    (E : SourcePsiIsolatingComplexExtension hq hq1 V t)
    (hpq : p ≤ q) (n : ℤ) (φ : realTypeSourceLocus p) :
    Coeff.deletedExponentInclusion hpq n (s n φ.val) =
      t n (CoeffPair.exponentInclusion hpq φ.val) := by
  rw [D.real_agreement n φ]
  exact (sourcePsiGapRoot_exponent hp hq hp1 hq1 hpq n φ).trans
    (E.real_agreement n (realTypeSourceExponentInclusion hpq φ)).symm

end NLS.ZakharovShabat
