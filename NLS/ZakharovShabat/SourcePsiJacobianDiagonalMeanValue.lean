import NLS.ZakharovShabat.SourcePsiJacobianGapFactorization
import NLS.ZakharovShabat.SourcePsiDiagonalVariationNoAvoid
import NLS.ZakharovShabat.SourcePsiRealGapQuotient
import NLS.ZakharovShabat.SourceStandardRootWeightedLocalRealMeanValue

/-!
# Real-gap mean value for the diagonal psi Jacobian entry

On an open real gap, differentiating in the selected retained root
removes its linear factor. The gap-side mean-value theorem then turns
the diagonal Jacobian entry into an attained value of the regular
quotient on that gap.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The diagonal scalar Jacobian entry on an open real gap is twice
π times the real rotated regular factor at some point of that gap. -/
theorem exists_sourcePsi_diagonalJacobian_realGap_meanValue
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n m : ℤ) (hmn : m ≠ n) (a : DeletedCoeff p n)
    (hroots : ∀ k : ℤ, (displacedRoots (a : Coeff p) k).im = 0)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) m).re)
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
      (closedBall (x:ℂ) R)) :
    ∃ μ ∈ standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m),
      deriv (fun t : ℂ => sourcePsiDeletedEquationCoordinate hp hp1 n m
        (a+Coeff.deletedSingleCLM n m hmn t) ψ (x:ℂ) R) 0 =
        2 * (Real.pi : ℂ) *
          ((-I) * (((n-m : ℤ) : ℂ) *
            sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p) ψ μ)) := by
  let F : ℂ → ℂ := fun z => (((n-m : ℤ) : ℂ) *
    sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p) ψ z)
  let g : ℂ → ℂ := fun z => (-I)*F z
  let J : ℂ := deriv (fun t : ℂ => sourcePsiDeletedEquationCoordinate hp hp1 n m
    (a+Coeff.deletedSingleCLM n m hmn t) ψ (x:ℂ) R) 0
  have hgap : standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m) ⊆ ball (x:ℂ) R :=
    (sourceStandardRoot_gapSegment_subset_periodicSegment hp hp1 ψ m).trans hseg
  have hg : AnalyticOnNhd ℂ g (closedBall (x:ℂ) R) := by
    intro z hz
    exact analyticAt_const.mul (hreg z hz)
  have hgreal : ∀ z ∈ standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m), (g z).im = 0 := by
    intro z hz
    have hzPeriod : z ∈ sourcePeriodicSegment hp hp1 ψ m :=
      sourceStandardRoot_gapSegment_subset_periodicSegment hp hp1 ψ m hz
    have hzIm : z.im = 0 :=
      sourcePeriodicSegment_im_eq_zero_of_realType hp hp1 ψ hreal m z hzPeriod
    have hzReal : (z.re:ℂ) = z := by
      apply Complex.ext
      · rfl
      · simpa using hzIm.symm
    have hzDom : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ m :=
      hdom (ball_subset_closedBall (hseg hzPeriod))
    have hFRe : (F z).re = 0 := by
      have h := sourcePsiGapRegularFactor_weighted_re_eq_zero_of_real_roots
        hp hp1 ψ hreal (a : Coeff p) hroots n m z.re
          (hzReal ▸ hzDom)
      simpa only [F,hzReal] using h
    simp [g,Complex.mul_im,hFRe]
  obtain ⟨μ,hμ,hvalue⟩ :=
    weighted_sourceStandardRoot_realCenteredCircle_real_mean_value
      hp hp1 ψ hreal m hopen g hgreal x R hR hseg hgap hg
  have hJ : J = ∮ z in C((x:ℂ),R),
      F z / sourceStandardRoot hp hp1 ψ m z := by
    exact (hasDerivAt_sourcePsiDeletedEquationCoordinate_diagonal_no_avoid
      hp hp1 n m hmn a ψ (x:ℂ) R hR.le hcircle havoidn hreg).deriv
  have hInt :
      (∮ z in C((x:ℂ),R),
        g z / sourceStandardRoot hp hp1 ψ m z) = (-I)*J := by
    rw [hJ, ← circleIntegral.integral_const_mul]
    apply circleIntegral.integral_congr hR.le
    intro z hz
    dsimp [g,F]
    ring
  let K : ℂ := 2 * (Real.pi : ℂ) * I
  have hK : K ≠ 0 := by
    dsimp [K]
    exact mul_ne_zero (mul_ne_zero (by norm_num)
      (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  have hvalueJ : K⁻¹ * ((-I)*J) = -g μ := by
    simpa only [K,hInt] using hvalue
  have hstep := congrArg (fun w : ℂ => K*w) hvalueJ
  have hstep' : (-I)*J = -(K*g μ) := by
    simpa [mul_assoc,hK] using hstep
  refine ⟨μ,hμ,?_⟩
  change J = 2 * (Real.pi : ℂ) * g μ
  calc
    J = I*((-I)*J) := by simp [← mul_assoc,Complex.I_mul_I]
    _ = I*(-(K*g μ)) := congrArg (fun w : ℂ => I*w) hstep'
    _ = 2 * (Real.pi : ℂ) * g μ := by
      dsimp [K]
      calc
        I * (-(2 * (Real.pi : ℂ) * I * g μ)) =
            -(2 * (Real.pi : ℂ) * (I*I) * g μ) := by ring
        _ = 2 * (Real.pi : ℂ) * g μ := by simp [Complex.I_mul_I]

/-- The rotated regular factor is the unrotated omitted-root quotient
with the expected spectral index weight. -/
theorem sourcePsi_diagonal_rotatedFactor_eq_quotient
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m : ℤ) (a : Coeff p) (ψ : CoeffPair p) (z : ℂ) :
    (-I) * (((n-m : ℤ) : ℂ) *
      sourcePsiGapRegularFactor hp hp1 n m a ψ z) =
      (((n-m : ℤ) : ℂ) *
        sourceSingleRootQuotientJointProduct hp hp1 m (z,(a,ψ))) /
          (displacedRoots a n-z) := by
  unfold sourcePsiGapRegularFactor
  simp only [div_eq_mul_inv]
  calc
    (-I) * (((n-m : ℤ) : ℂ) *
      (I * sourceSingleRootQuotientJointProduct hp hp1 m (z,(a,ψ)) *
        (displacedRoots a n-z)⁻¹)) =
          (-(I*I)) * (((n-m : ℤ) : ℂ) *
            sourceSingleRootQuotientJointProduct hp hp1 m (z,(a,ψ)) *
              (displacedRoots a n-z)⁻¹) := by ring
    _ = _ := by simp [Complex.I_mul_I]

/-- The diagonal mean value in the quotient form appearing in the
dissertation. -/
theorem exists_sourcePsi_diagonalJacobian_quotient_meanValue
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n m : ℤ) (hmn : m ≠ n) (a : DeletedCoeff p n)
    (hroots : ∀ k : ℤ, (displacedRoots (a : Coeff p) k).im = 0)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) m).re)
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
      (closedBall (x:ℂ) R)) :
    ∃ μ ∈ standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m),
      deriv (fun t : ℂ => sourcePsiDeletedEquationCoordinate hp hp1 n m
        (a+Coeff.deletedSingleCLM n m hmn t) ψ (x:ℂ) R) 0 =
        2 * (Real.pi : ℂ) *
          ((((n-m : ℤ) : ℂ) *
            sourceSingleRootQuotientJointProduct hp hp1 m
              (μ,((a : Coeff p),ψ))) /
              (displacedRoots (a : Coeff p) n-μ)) := by
  obtain ⟨μ,hμ,hvalue⟩ :=
    exists_sourcePsi_diagonalJacobian_realGap_meanValue
      hp hp1 ψ hreal n m hmn a hroots hopen x R hR hseg hdom
        hcircle havoidn hreg
  refine ⟨μ,hμ,?_⟩
  rw [hvalue,sourcePsi_diagonal_rotatedFactor_eq_quotient]

/-- The diagonal entry cannot vanish when the omitted quotient and
deleted root have no zeros on the selected real gap. -/
theorem sourcePsi_diagonalJacobian_ne_zero_of_quotient_nonvanishing
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n m : ℤ) (hmn : m ≠ n) (a : DeletedCoeff p n)
    (hroots : ∀ k : ℤ, (displacedRoots (a : Coeff p) k).im = 0)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) m).re)
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
    (hQ : ∀ z ∈ standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m),
      sourceSingleRootQuotientJointProduct hp hp1 m
        (z,((a : Coeff p),ψ)) ≠ 0)
    (hsep : ∀ z ∈ standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m),
      z ≠ displacedRoots (a : Coeff p) n) :
    deriv (fun t : ℂ => sourcePsiDeletedEquationCoordinate hp hp1 n m
      (a+Coeff.deletedSingleCLM n m hmn t) ψ (x:ℂ) R) 0 ≠ 0 := by
  obtain ⟨μ,hμ,hvalue⟩ :=
    exists_sourcePsi_diagonalJacobian_quotient_meanValue
      hp hp1 ψ hreal n m hmn a hroots hopen x R hR hseg hdom
        hcircle havoidn hreg
  rw [hvalue]
  have hπ : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  have hnm : (((n-m : ℤ) : ℂ)) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr (Ne.symm hmn)
  have hden : displacedRoots (a : Coeff p) n-μ ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (hsep μ hμ))
  exact mul_ne_zero hπ (div_ne_zero (mul_ne_zero hnm (hQ μ hμ)) hden)

end NLS.ZakharovShabat
