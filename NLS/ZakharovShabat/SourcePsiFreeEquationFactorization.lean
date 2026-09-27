import NLS.ZakharovShabat.SourcePsiFreeSequence
import NLS.ZakharovShabat.SourcePsiFreeOperator

/-!
# Exact factorization of the free-source psi equation

At the free source and with the `n`th root fixed, the selected-gap
Cauchy residue cancels the prefactor `n-m` against the distance
between free centers. The entire sequence-valued equation is therefore
coordinatewise twice the root displacement times the omitted-root
quotient. This is the algebraic form needed to estimate its derivative.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The free-source psi equation at an off-deleted index is exactly
twice the root displacement times the single-root quotient. -/
theorem sourcePsiEquationCoordinate_freeCircle_eq_two_mul_quotient
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m : ℤ) (hnm : n ≠ m) (a : DeletedCoeff p n)
    (R : ℝ) (hR : 0 < R) (hRπ : R < Real.pi) :
    sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p)
      (0 : CoeffPair p) ((Real.pi : ℂ)*m) R =
      2 * (a : Coeff p) m *
        sourceSingleRootQuotientJointProduct hp hp1 m
          (((Real.pi : ℂ)*m),((a : Coeff p),(0 : CoeffPair p))) := by
  rw [sourcePsiEquationCoordinate_freeCircle_residue_of_deleted
    hp hp1 n m hnm a R hR hRπ]
  have ha : (a : Coeff p) n = 0 := a.property
  have hn : displacedRoots (a : Coeff p) n = (Real.pi : ℂ)*n := by
    simp [displacedRoots,ha]
  rw [sourcePsiGapRegularFactor,hn]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hδ : (((n-m : ℤ) : ℂ)) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr hnm
  have hden : (Real.pi : ℂ)*n - (Real.pi : ℂ)*m =
      (Real.pi : ℂ)*((n-m : ℤ) : ℂ) := by
    push_cast
    ring
  rw [hden]
  field_simp [hπ,hδ]
  simp only [Complex.I_sq]
  ring

/-- The same factorization holds at the deleted index: both sides
vanish because that displacement coordinate is zero. -/
theorem sourcePsiFreeEquationSequence_apply_factorized
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m : ℤ) (a : DeletedCoeff p n)
    (R : ℝ) (hR : 0 < R) (hRquarter : R ≤ Real.pi/4) :
    ((sourcePsiFreeEquationSequence hp hp1 n R hR hRquarter a :
      DeletedCoeff p n) : Coeff p) m =
      2 * (a : Coeff p) m *
        sourceSingleRootQuotientJointProduct hp hp1 m
          (((Real.pi : ℂ)*m),((a : Coeff p),(0 : CoeffPair p))) := by
  rw [sourcePsiFreeEquationSequence_apply]
  by_cases hnm : n = m
  · subst m
    have ha : (a : Coeff p) n = 0 := a.property
    simp [sourcePsiEquationCoordinate,ha]
  · have hRπ : R < Real.pi := by nlinarith [Real.pi_pos]
    exact sourcePsiEquationCoordinate_freeCircle_eq_two_mul_quotient
      hp hp1 n m hnm a R hR hRπ

/-- At the zero displacement, the omitted-root quotient equals one
at every free center, including the filled selected center. -/
theorem sourceSingleRootQuotient_freeCenter_zero_eq_one
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (m : ℤ) :
    sourceSingleRootQuotientJointProduct hp hp1 m
      (((Real.pi : ℂ)*m),((0 : Coeff p),(0 : CoeffPair p))) = 1 := by
  have hdomain : (Real.pi : ℂ)*m ∈
      sourceStandardRootOmittedDomain hp hp1 (0 : CoeffPair p) m := by
    intro k hkm
    rw [sourcePeriodicSegment_zero_source hp hp1 k]
    intro he
    exact (freeCenter_not_mem_closedBall_other m k (Ne.symm hkm)
      0 Real.pi_pos) (he ▸ mem_closedBall_self le_rfl)
  have hden : sourceStandardRootOmittedProduct hp hp1 m
      (0 : CoeffPair p) ((Real.pi : ℂ)*m) ≠ 0 :=
    sourceStandardRootOmittedProduct_ne_zero hp hp1 0
      ((Real.pi : ℂ)*m) m hdomain
  unfold sourceSingleRootQuotientJointProduct
  change jointDeletedSingleSpectralProduct m
      (((Real.pi : ℂ)*m),(0 : Coeff p)) /
    sourceStandardRootOmittedProduct hp hp1 m (0 : CoeffPair p)
      ((Real.pi : ℂ)*m) = 1
  rw [← sourceStandardRootOmittedProduct_zero_source_eq_deleted hp hp1 m]
  exact div_self hden

/-- The errors of the free-center quotient form an `ℓᵖ` sequence
for every root-displacement input. -/
def sourcePsiFreeQuotientError
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (a : Coeff p) : Coeff p :=
  ⟨fun m => sourceSingleRootQuotientJointProduct hp hp1 m
      (((Real.pi : ℂ)*m),(a,(0 : CoeffPair p)))-1,
    by
      obtain ⟨B,hB⟩ := exists_sourcePsiQuotient_freeCenter_lpMajorant hp hp1 a
      exact (lp.memℓp B).mono' hB⟩

@[simp] theorem sourcePsiFreeQuotientError_apply
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (a : Coeff p) (m : ℤ) :
    sourcePsiFreeQuotientError hp hp1 a m =
      sourceSingleRootQuotientJointProduct hp hp1 m
        (((Real.pi : ℂ)*m),(a,(0 : CoeffPair p)))-1 := rfl

@[simp] theorem sourcePsiFreeQuotientError_zero
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    sourcePsiFreeQuotientError hp hp1 (0 : Coeff p) = 0 := by
  ext m
  simp [sourceSingleRootQuotient_freeCenter_zero_eq_one hp hp1 m]

/-- The nonlinear remainder from the free Jacobian is exactly the
pointwise product of the displacement and quotient error. -/
theorem sourcePsiFreeEquationSequence_sub_linear_apply
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m : ℤ) (a : DeletedCoeff p n)
    (R : ℝ) (hR : 0 < R) (hRquarter : R ≤ Real.pi/4) :
    (((sourcePsiFreeEquationSequence hp hp1 n R hR hRquarter a -
        (2 : ℂ) • a : DeletedCoeff p n) : Coeff p) m) =
      2 * (a : Coeff p) m *
        sourcePsiFreeQuotientError hp hp1 (a : Coeff p) m := by
  simp only [Submodule.coe_sub, lp.coeFn_sub, Pi.sub_apply,
    Submodule.coe_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  rw [sourcePsiFreeEquationSequence_apply_factorized]
  simp only [sourcePsiFreeQuotientError_apply]
  ring

/-- The exact nonlinear remainder is bounded by the norm of the
quotient-error sequence times the input norm. -/
theorem norm_sourcePsiFreeEquationSequence_sub_linear_le
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (a : DeletedCoeff p n)
    (R : ℝ) (hR : 0 < R) (hRquarter : R ≤ Real.pi/4) :
    ‖sourcePsiFreeEquationSequence hp hp1 n R hR hRquarter a -
        (2 : ℂ) • a‖ ≤
      2 * ‖sourcePsiFreeQuotientError hp hp1 (a : Coeff p)‖ * ‖a‖ := by
  let E := sourcePsiFreeQuotientError hp hp1 (a : Coeff p)
  let M : Coeff ⊤ := Coeff.exponentInclusion le_top E
  have heq : ((sourcePsiFreeEquationSequence hp hp1 n R hR hRquarter a -
      (2 : ℂ) • a : DeletedCoeff p n) : Coeff p) =
      (2 : ℂ) • Coeff.multiplier M (a : Coeff p) := by
    ext m
    rw [sourcePsiFreeEquationSequence_sub_linear_apply hp hp1 n m a R hR hRquarter]
    simp [M,E]
    ring
  change ‖((sourcePsiFreeEquationSequence hp hp1 n R hR hRquarter a -
      (2 : ℂ) • a : DeletedCoeff p n) : Coeff p)‖ ≤
      2 * ‖E‖ * ‖(a : Coeff p)‖
  rw [heq, norm_smul]
  norm_num
  calc
    2 * ‖Coeff.multiplier M (a : Coeff p)‖ ≤
        2 * (‖M‖ * ‖(a : Coeff p)‖) := by
      gcongr
      exact Coeff.norm_multiplier_le M (a : Coeff p)
    _ ≤ 2 * (‖E‖ * ‖(a : Coeff p)‖) := by
      gcongr
      exact Coeff.norm_exponentInclusion_le le_top E
    _ = 2 * ‖E‖ * ‖(a : Coeff p)‖ := by ring

end NLS.ZakharovShabat
