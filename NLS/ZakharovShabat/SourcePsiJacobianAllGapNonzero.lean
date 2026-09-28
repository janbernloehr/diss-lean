import NLS.ZakharovShabat.SourcePsiJacobianCollapsedDiagonal
import NLS.ZakharovShabat.SourcePsiDeletedProductNonzero

/-!
# Nonvanishing of every selected diagonal psi Jacobian entry

The zero set of the deleted product identifies the remaining
geometric condition in Lemma 12.5: no retained root may lie on the
selected periodic gap. Once this holds, the real-gap mean-value and
collapsed-gap residue formulas both yield a nonzero diagonal entry.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The diagonal Jacobian is nonzero for open and collapsed real
gaps when the selected gap misses all roots other than its own. The
selected root itself may lie anywhere, including on the contour. -/
theorem sourcePsi_diagonalJacobian_ne_zero_all_real_gaps
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n m : ℤ) (hmn : m ≠ n) (a : DeletedCoeff p n)
    (hroots : ∀ k : ℤ, (displacedRoots (a : Coeff p) k).im = 0)
    (x R : ℝ) (hR : 0 < R)
    (hseg : sourcePeriodicSegment hp hp1 ψ m ⊆ ball (x:ℂ) R)
    (hdom : closedBall (x:ℂ) R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hcircle : sphere (x:ℂ) R ⊆
      sourceCanonicalRootDomain hp hp1 ψ)
    (havoidn : ∀ z ∈ sphere (x:ℂ) R,
      z ≠ displacedRoots (a : Coeff p) n)
    (hreg : AnalyticOnNhd ℂ
      (fun z => (((n-m : ℤ) : ℂ) *
        sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p) ψ z))
      (closedBall (x:ℂ) R))
    (hother : ∀ z ∈ standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m),
      ∀ k : ℤ, k ≠ m → z ≠ displacedRoots (a : Coeff p) k) :
    deriv (fun t : ℂ => sourcePsiDeletedEquationCoordinate hp hp1 n m
      (a+Coeff.deletedSingleCLM n m hmn t) ψ (x:ℂ) R) 0 ≠ 0 := by
  have hgapdom : ∀ z ∈ standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m),
      z ∈ sourceStandardRootOmittedDomain hp hp1 ψ m := by
    intro z hz
    exact hdom (ball_subset_closedBall
      (hseg (sourceStandardRoot_gapSegment_subset_periodicSegment
        hp hp1 ψ m hz)))
  have hQ : ∀ z ∈ standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m),
      sourceSingleRootQuotientJointProduct hp hp1 m
        (z,((a : Coeff p),ψ)) ≠ 0 := by
    intro z hz
    exact sourceSingleRootQuotientJointProduct_ne_zero_of_off_other
      hp hp1 m z (a : Coeff p) ψ (hother z hz) (hgapdom z hz)
  have hsep : ∀ z ∈ standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m),
      z ≠ displacedRoots (a : Coeff p) n := by
    intro z hz
    exact hother z hz n (Ne.symm hmn)
  by_cases hopen :
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) m).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) m).re
  · exact sourcePsi_diagonalJacobian_ne_zero_of_quotient_nonvanishing
      hp hp1 ψ hreal n m hmn a hroots hopen x R hR hseg hdom
        hcircle havoidn hreg hQ hsep
  · have hgap := sourcePeriodicGap_eq_zero_of_real_not_open
      hp hp1 ψ hreal m hopen
    let τ := sourceStandardRootMidpoint hp hp1 ψ m
    have hmid : τ ∈ ball (x:ℂ) R :=
      hseg (sourcePeriodicMidpoint_mem_segment hp hp1 ψ m)
    have hmidGap : τ ∈ standardRootGapSegment τ
        (sourceStandardRootHalfGap hp hp1 ψ m) := by
      refine ⟨0,by norm_num,?_⟩
      simp
    rw [sourcePsi_diagonalJacobian_collapsedGap_eq_quotient
      hp hp1 ψ n m hmn a hgap (x:ℂ) R hR hmid hcircle havoidn hreg]
    have hπ : (2 * (Real.pi : ℂ)) ≠ 0 :=
      mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
    have hnm : (((n-m : ℤ) : ℂ)) ≠ 0 := by
      exact_mod_cast sub_ne_zero.mpr (Ne.symm hmn)
    have hden : displacedRoots (a : Coeff p) n-τ ≠ 0 :=
      sub_ne_zero.mpr (Ne.symm (hsep τ hmidGap))
    exact mul_ne_zero hπ (div_ne_zero
      (mul_ne_zero hnm (hQ τ hmidGap)) hden)

end NLS.ZakharovShabat
