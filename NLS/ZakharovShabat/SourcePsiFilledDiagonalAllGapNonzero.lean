import NLS.ZakharovShabat.SourcePsiFilledDiagonalMeanValue
import NLS.ZakharovShabat.SourcePsiJacobianAllGapNonzero

/-!
# Filled-root diagonal psi nonvanishing for every real gap

The collapsed-gap residue formula and the open-gap mean-value formula
both hold when the omitted root is freely chosen inside its disc.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The collapsed-gap diagonal quotient formula for an arbitrary full root sequence. -/
theorem sourcePsi_diagonalJacobian_collapsedGap_eq_quotient_full
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p)
    (n m : ℤ) (hmn : m ≠ n) (a : Coeff p)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m = 0)
    (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hmid : sourceStandardRootMidpoint hp hp1 ψ m ∈ ball c R)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ)
    (havoidn : ∀ z ∈ sphere c R,
      z ≠ displacedRoots a n)
    (hreg : AnalyticOnNhd ℂ
      (fun z => (((n-m : ℤ) : ℂ) *
        sourcePsiGapRegularFactor hp hp1 n m a ψ z))
      (closedBall c R)) :
    deriv (fun t : ℂ => sourcePsiEquationCoordinate hp hp1 n m
      (a+lp.single p m t) ψ c R) 0 =
        2*(Real.pi : ℂ) *
          ((((n-m : ℤ) : ℂ) *
            sourceSingleRootQuotientJointProduct hp hp1 m
              (sourceStandardRootMidpoint hp hp1 ψ m,
                (a,ψ))) /
              (displacedRoots a n-
                sourceStandardRootMidpoint hp hp1 ψ m)) := by
  let τ := sourceStandardRootMidpoint hp hp1 ψ m
  let F : ℂ → ℂ := fun z => (((n-m : ℤ) : ℂ) *
    sourcePsiGapRegularFactor hp hp1 n m a ψ z)
  have hJ := (hasDerivAt_sourcePsiEquationCoordinate_diagonal_no_avoid
    hp hp1 n m hmn a ψ c R hR.le hcircle havoidn hreg).deriv
  have hτsphere : ∀ z ∈ sphere c R, z ≠ τ := by
    intro z hz he
    have hlt := mem_ball.mp hmid
    have heq := mem_sphere.mp hz
    rw [he] at heq
    exact (ne_of_lt hlt) heq
  have hCauchy :
      (∮ z in C(c,R), (z-τ)⁻¹ * F z) =
        2*(Real.pi:ℂ)*I*F τ := by
    simpa only [F, smul_eq_mul] using
      (hreg.differentiableOn.circleIntegral_sub_inv_smul hmid)
  have hInt :
      (∮ z in C(c,R), F z / sourceStandardRoot hp hp1 ψ m z) =
        -(2*(Real.pi:ℂ)*I)*F τ := by
    have heq :
        (∮ z in C(c,R), F z / sourceStandardRoot hp hp1 ψ m z) =
          ∮ z in C(c,R), (-1:ℂ)*((z-τ)⁻¹*F z) := by
      apply circleIntegral.integral_congr hR.le
      intro z hz
      have hzt : z-τ ≠ 0 := sub_ne_zero.mpr (hτsphere z hz)
      have htz : τ-z ≠ 0 := sub_ne_zero.mpr (Ne.symm (hτsphere z hz))
      dsimp only
      rw [sourceStandardRoot_of_zeroGap hp hp1 ψ m z hgap]
      change F z / (τ-z) = (-1:ℂ)*((z-τ)⁻¹*F z)
      field_simp [hzt,htz]
      ring
    rw [heq, circleIntegral.integral_const_mul, hCauchy]
    ring
  rw [hJ]
  change (∮ z in C(c,R), F z / sourceStandardRoot hp hp1 ψ m z) = _
  rw [hInt]
  have hfactor := sourcePsi_diagonal_rotatedFactor_eq_quotient
    hp hp1 n m a ψ τ
  calc
    -(2 * (Real.pi : ℂ) * I) * F τ =
        2*(Real.pi : ℂ) *
          ((-I) * (((n-m : ℤ) : ℂ) *
            sourcePsiGapRegularFactor hp hp1 n m a ψ τ)) := by
              dsimp [F]
              ring
    _ = _ := by rw [hfactor]

/-- The diagonal derivative does not vanish on any real gap for a full root sequence. -/
theorem sourcePsi_diagonalJacobian_ne_zero_all_real_gaps_full
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n m : ℤ) (hmn : m ≠ n) (a : Coeff p)
    (hroots : ∀ k : ℤ, (displacedRoots a k).im = 0)
    (x R : ℝ) (hR : 0 < R)
    (hseg : sourcePeriodicSegment hp hp1 ψ m ⊆ ball (x:ℂ) R)
    (hdom : closedBall (x:ℂ) R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hcircle : sphere (x:ℂ) R ⊆
      sourceCanonicalRootDomain hp hp1 ψ)
    (havoidn : ∀ z ∈ sphere (x:ℂ) R,
      z ≠ displacedRoots a n)
    (hreg : AnalyticOnNhd ℂ
      (fun z => (((n-m : ℤ) : ℂ) *
        sourcePsiGapRegularFactor hp hp1 n m a ψ z))
      (closedBall (x:ℂ) R))
    (hother : ∀ z ∈ standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m),
      ∀ k : ℤ, k ≠ m → z ≠ displacedRoots a k) :
    deriv (fun t : ℂ => sourcePsiEquationCoordinate hp hp1 n m
      (a+lp.single p m t) ψ (x:ℂ) R) 0 ≠ 0 := by
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
        (z,(a,ψ)) ≠ 0 := by
    intro z hz
    exact sourceSingleRootQuotientJointProduct_ne_zero_of_off_other
      hp hp1 m z a ψ (hother z hz) (hgapdom z hz)
  have hsep : ∀ z ∈ standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m),
      z ≠ displacedRoots a n := by
    intro z hz
    exact hother z hz n (Ne.symm hmn)
  by_cases hopen :
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) m).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) m).re
  · exact sourcePsi_diagonalJacobian_ne_zero_of_quotient_nonvanishing_full
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
    rw [sourcePsi_diagonalJacobian_collapsedGap_eq_quotient_full
      hp hp1 ψ n m hmn a hgap (x:ℂ) R hR hmid hcircle havoidn hreg]
    have hπ : (2 * (Real.pi : ℂ)) ≠ 0 :=
      mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
    have hnm : (((n-m : ℤ) : ℂ)) ≠ 0 := by
      exact_mod_cast sub_ne_zero.mpr (Ne.symm hmn)
    have hden : displacedRoots a n-τ ≠ 0 :=
      sub_ne_zero.mpr (Ne.symm (hsep τ hmidGap))
    exact mul_ne_zero hπ (div_ne_zero
      (mul_ne_zero hnm (hQ τ hmidGap)) hden)

/-- Nonvanishing of the deleted-coordinate diagonal derivative for
both open and collapsed gaps, using a freely filled omitted root. -/
theorem sourcePsi_diagonalJacobian_ne_zero_all_real_gaps_filled
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n m : ℤ) (hmn : m ≠ n) (a : DeletedCoeff p n) (ξ : ℂ)
    (hroots : ∀ k : ℤ,
      (displacedRoots (sourcePsiFillDeletedRoot n a ξ) k).im = 0)
    (x R : ℝ) (hR : 0 < R)
    (hseg : sourcePeriodicSegment hp hp1 ψ m ⊆ ball (x:ℂ) R)
    (hdom : closedBall (x:ℂ) R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hcircle : sphere (x:ℂ) R ⊆
      sourceCanonicalRootDomain hp hp1 ψ)
    (havoidn : ∀ z ∈ sphere (x:ℂ) R,
      z ≠ displacedRoots (sourcePsiFillDeletedRoot n a ξ) n)
    (hreg : AnalyticOnNhd ℂ
      (fun z => (((n-m : ℤ) : ℂ) *
        sourcePsiGapRegularFactor hp hp1 n m
          (sourcePsiFillDeletedRoot n a ξ) ψ z))
      (closedBall (x:ℂ) R))
    (hother : ∀ z ∈ standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m),
      ∀ k : ℤ, k ≠ m →
        z ≠ displacedRoots (sourcePsiFillDeletedRoot n a ξ) k) :
    deriv (fun t : ℂ => sourcePsiDeletedEquationCoordinate hp hp1 n m
      (a+Coeff.deletedSingleCLM n m hmn t) ψ (x:ℂ) R) 0 ≠ 0 := by
  rw [← deriv_sourcePsiEquationCoordinate_fillDeletedRoot_selectedLine
    hp hp1 n m hmn a ξ ψ (x:ℂ) R hR.le]
  exact sourcePsi_diagonalJacobian_ne_zero_all_real_gaps_full
    hp hp1 ψ hreal n m hmn (sourcePsiFillDeletedRoot n a ξ)
      hroots x R hR hseg hdom hcircle havoidn hreg hother

end NLS.ZakharovShabat
