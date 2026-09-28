import NLS.ZakharovShabat.SourcePsiCandidateEntireVariation
import NLS.ZakharovShabat.SourcePsiDeletedCoordinate
import NLS.SequenceSpaces.DeletedCoordinate

/-!
# Filling the deleted root for interpolation

The psi numerator omits root index `n`. Its deleted-`ℓᵖ` parameter is
represented with zero at `n`, but the interpolation proof may fill that
unused root with any chosen spectral point, as in Section 12 of the
dissertation. The numerator and its deleted-direction variation are
unchanged by this fill.
-/

noncomputable section
open Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Put a chosen spectral point at the omitted index of a deleted root
sequence, keeping every retained displacement fixed. -/
def sourcePsiFillDeletedRoot
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (n : ℤ) (a : DeletedCoeff p n) (ξ : ℂ) : Coeff p :=
  (a : Coeff p) + lp.single p n (ξ - (Real.pi : ℂ) * n)

@[simp] theorem displacedRoots_sourcePsiFillDeletedRoot_same
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (n : ℤ) (a : DeletedCoeff p n) (ξ : ℂ) :
    displacedRoots (sourcePsiFillDeletedRoot n a ξ) n = ξ := by
  change (Real.pi : ℂ)*n +
    ((a : Coeff p) n + (lp.single p n (ξ-(Real.pi : ℂ)*n) : Coeff p) n) = ξ
  have hn : (a : Coeff p) n = 0 := a.property
  rw [hn]
  simp

theorem sourcePsiFillDeletedRoot_apply_other
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (n m : ℤ) (hmn : m ≠ n) (a : DeletedCoeff p n) (ξ : ℂ) :
    sourcePsiFillDeletedRoot n a ξ m = (a : Coeff p) m := by
  change (a : Coeff p) m +
    (lp.single p n (ξ-(Real.pi : ℂ)*n) : Coeff p) m = (a : Coeff p) m
  rw [lp.single_apply_ne _ _ _ hmn]
  simp

@[simp] theorem displacedRoots_sourcePsiFillDeletedRoot_other
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (n m : ℤ) (hmn : m ≠ n) (a : DeletedCoeff p n) (ξ : ℂ) :
    displacedRoots (sourcePsiFillDeletedRoot n a ξ) m =
      displacedRoots (a : Coeff p) m := by
  simp [displacedRoots, sourcePsiFillDeletedRoot_apply_other n m hmn]

/-- A deleted-direction variation depends only on the retained base
root coordinates. -/
theorem sourcePsiCandidateVariation_eq_of_off_index
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (a b h : Coeff p)
    (hab : ∀ m : ℤ, m ≠ n → a m = b m) (z : ℂ) :
    sourcePsiCandidateVariation n a h z =
      sourcePsiCandidateVariation n b h z := by
  have heq :
      (fun t : ℂ => sourcePsiCandidate n (z,a+t • h)) =
        (fun t : ℂ => sourcePsiCandidate n (z,b+t • h)) := by
    funext t
    apply sourcePsiCandidate_eq_of_off_index hp hp1 n z
    intro m hmn
    simp only [lp.coeFn_add, lp.coeFn_smul, Pi.add_apply,
      Pi.smul_apply]
    rw [hab m hmn]
  rw [sourcePsiCandidateVariation_eq_line_deriv hp hp1 n a h z,
    sourcePsiCandidateVariation_eq_line_deriv hp hp1 n b h z, heq]

/-- Filling the omitted root leaves every deleted-direction psi
variation unchanged. -/
theorem sourcePsiCandidateVariation_fillDeletedRoot
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (a : DeletedCoeff p n) (h : Coeff p)
    (ξ z : ℂ) :
    sourcePsiCandidateVariation n
      (sourcePsiFillDeletedRoot n a ξ) h z =
        sourcePsiCandidateVariation n (a : Coeff p) h z := by
  apply sourcePsiCandidateVariation_eq_of_off_index hp hp1
  intro m hmn
  exact sourcePsiFillDeletedRoot_apply_other n m hmn a ξ

/-- Deleting the filled root recovers the original deleted parameter. -/
@[simp] theorem deleteCoordinateTo_sourcePsiFillDeletedRoot
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (n : ℤ) (a : DeletedCoeff p n) (ξ : ℂ) :
    Coeff.deleteCoordinateTo n (sourcePsiFillDeletedRoot n a ξ) = a := by
  apply Subtype.ext
  ext m
  by_cases hmn : m = n
  · subst m
    change Coeff.deleteCoordinate n (sourcePsiFillDeletedRoot n a ξ) n =
      (a : Coeff p) n
    rw [Coeff.deleteCoordinate_apply_same]
    exact (show (a : Coeff p) n = 0 from a.property).symm
  · change Coeff.deleteCoordinate n (sourcePsiFillDeletedRoot n a ξ) m =
      (a : Coeff p) m
    rw [Coeff.deleteCoordinate_apply_other n m hmn]
    exact sourcePsiFillDeletedRoot_apply_other n m hmn a ξ

/-- The scalar psi equation is invariant under filling the omitted
root, on every circle of nonnegative radius. -/
theorem sourcePsiEquationCoordinate_fillDeletedRoot
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m : ℤ) (a : DeletedCoeff p n) (ξ : ℂ)
    (ψ : CoeffPair p) (c : ℂ) (R : ℝ) (hR : 0 ≤ R) :
    sourcePsiEquationCoordinate hp hp1 n m
      (sourcePsiFillDeletedRoot n a ξ) ψ c R =
        sourcePsiDeletedEquationCoordinate hp hp1 n m a ψ c R := by
  rw [sourcePsiEquationCoordinate_eq_deletedCoordinate hp hp1 n m
    (sourcePsiFillDeletedRoot n a ξ) ψ c R hR]
  simp

/-- Varying a retained root commutes with the arbitrary fill at the
omitted index. -/
theorem sourcePsiEquationCoordinate_fillDeletedRoot_selectedLine
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m : ℤ) (hmn : m ≠ n)
    (a : DeletedCoeff p n) (ξ t : ℂ)
    (ψ : CoeffPair p) (c : ℂ) (R : ℝ) (hR : 0 ≤ R) :
    sourcePsiEquationCoordinate hp hp1 n m
      (sourcePsiFillDeletedRoot n a ξ + lp.single p m t) ψ c R =
        sourcePsiDeletedEquationCoordinate hp hp1 n m
          (a + Coeff.deletedSingleCLM n m hmn t) ψ c R := by
  have hfill : sourcePsiFillDeletedRoot n
      (a + Coeff.deletedSingleCLM n m hmn t) ξ =
        sourcePsiFillDeletedRoot n a ξ + lp.single p m t := by
    simp only [sourcePsiFillDeletedRoot, Submodule.coe_add,
      Coeff.deletedSingleCLM_coe]
    abel
  rw [← hfill]
  exact sourcePsiEquationCoordinate_fillDeletedRoot hp hp1 n m
    (a + Coeff.deletedSingleCLM n m hmn t) ξ ψ c R hR

/-- The diagonal scalar derivative may be computed using any filled
omitted root. -/
theorem deriv_sourcePsiEquationCoordinate_fillDeletedRoot_selectedLine
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m : ℤ) (hmn : m ≠ n)
    (a : DeletedCoeff p n) (ξ : ℂ)
    (ψ : CoeffPair p) (c : ℂ) (R : ℝ) (hR : 0 ≤ R) :
    deriv (fun t : ℂ => sourcePsiEquationCoordinate hp hp1 n m
      (sourcePsiFillDeletedRoot n a ξ + lp.single p m t) ψ c R) 0 =
    deriv (fun t : ℂ => sourcePsiDeletedEquationCoordinate hp hp1 n m
      (a + Coeff.deletedSingleCLM n m hmn t) ψ c R) 0 := by
  have heq :
      (fun t : ℂ => sourcePsiEquationCoordinate hp hp1 n m
        (sourcePsiFillDeletedRoot n a ξ + lp.single p m t) ψ c R) =
      (fun t : ℂ => sourcePsiDeletedEquationCoordinate hp hp1 n m
        (a + Coeff.deletedSingleCLM n m hmn t) ψ c R) := by
    funext t
    exact sourcePsiEquationCoordinate_fillDeletedRoot_selectedLine
      hp hp1 n m hmn a ξ t ψ c R hR
  exact congrArg (fun f : ℂ → ℂ => deriv f 0) heq

end NLS.ZakharovShabat
