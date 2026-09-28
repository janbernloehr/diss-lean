import NLS.ZakharovShabat.SourcePsiJacobianCollapsedDiagonal

/-!
# Real-gap mean value for off-diagonal psi Jacobian entries

For distinct selected and varied roots, the Jacobian kernel has an
extra factor `(σ_m-z)/(σ_k-z)`. The weighted real-gap mean-value
theorem evaluates the resulting integral at a point of the gap.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A real rotated analytic numerator has an attained value on the
selected open gap equal to its weighted contour integral. -/
theorem exists_sourceStandardRoot_imaginaryNumerator_meanValue
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (m : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) m).re)
    (F : ℂ → ℂ)
    (hFreal : ∀ z ∈ standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m),
      ((-I)*F z).im = 0)
    (x R : ℝ) (hR : 0 < R)
    (hseg : sourcePeriodicSegment hp hp1 ψ m ⊆ ball (x:ℂ) R)
    (hF : AnalyticOnNhd ℂ F (closedBall (x:ℂ) R)) :
    ∃ μ ∈ standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m),
      (∮ z in C((x:ℂ),R), F z / sourceStandardRoot hp hp1 ψ m z) =
        2*(Real.pi : ℂ)*((-I)*F μ) := by
  let g : ℂ → ℂ := fun z => (-I)*F z
  have hgap : standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m) ⊆ ball (x:ℂ) R :=
    (sourceStandardRoot_gapSegment_subset_periodicSegment hp hp1 ψ m).trans hseg
  have hg : AnalyticOnNhd ℂ g (closedBall (x:ℂ) R) := by
    intro z hz
    exact analyticAt_const.mul (hF z hz)
  obtain ⟨μ,hμ,hvalue⟩ :=
    weighted_sourceStandardRoot_realCenteredCircle_real_mean_value
      hp hp1 ψ hreal m hopen g hFreal x R hR hseg hgap hg
  let J : ℂ := ∮ z in C((x:ℂ),R), F z /
    sourceStandardRoot hp hp1 ψ m z
  have hInt :
      (∮ z in C((x:ℂ),R),
        g z / sourceStandardRoot hp hp1 ψ m z) = (-I)*J := by
    rw [← circleIntegral.integral_const_mul]
    apply circleIntegral.integral_congr hR.le
    intro z hz
    dsimp [g,J]
    ring
  let K : ℂ := 2*(Real.pi : ℂ)*I
  have hK : K ≠ 0 := by
    dsimp [K]
    exact mul_ne_zero (mul_ne_zero (by norm_num)
      (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  have hvalueJ : K⁻¹*((-I)*J) = -g μ := by
    simpa only [K,hInt] using hvalue
  have hstep := congrArg (fun w : ℂ => K*w) hvalueJ
  have hstep' : (-I)*J = -(K*g μ) := by
    simpa [mul_assoc,hK] using hstep
  refine ⟨μ,hμ,?_⟩
  change J = 2*(Real.pi : ℂ)*g μ
  calc
    J = I*((-I)*J) := by simp [← mul_assoc,Complex.I_mul_I]
    _ = I*(-(K*g μ)) := congrArg (fun w : ℂ => I*w) hstep'
    _ = 2*(Real.pi : ℂ)*g μ := by
      dsimp [K]
      calc
        I * (-(2*(Real.pi : ℂ)*I*g μ)) =
            -(2*(Real.pi : ℂ)*(I*I)*g μ) := by ring
        _ = 2*(Real.pi : ℂ)*g μ := by simp [Complex.I_mul_I]

/-- On an open real gap, the off-diagonal Jacobian entry is an
attained value of the root ratio times the regular quotient. -/
theorem exists_sourcePsi_offDiagonalJacobian_quotient_meanValue
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n m k : ℤ) (hkn : k ≠ n)
    (a : DeletedCoeff p n)
    (hroots : ∀ j : ℤ, (displacedRoots (a : Coeff p) j).im = 0)
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
    (havoidk : ∀ z ∈ sphere (x:ℂ) R,
      z ≠ displacedRoots (a : Coeff p) k)
    (hF : AnalyticOnNhd ℂ
      (fun z =>
        ((displacedRoots (a : Coeff p) m-z) /
          (displacedRoots (a : Coeff p) k-z)) *
          (((n-m : ℤ) : ℂ) *
            sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p) ψ z))
      (closedBall (x:ℂ) R)) :
    ∃ μ ∈ standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m),
      deriv (fun t : ℂ => sourcePsiDeletedEquationCoordinate hp hp1 n m
        (a+Coeff.deletedSingleCLM n k hkn t) ψ (x:ℂ) R) 0 =
        2*(Real.pi : ℂ)*
          (((displacedRoots (a : Coeff p) m-μ) /
            (displacedRoots (a : Coeff p) k-μ)) *
              ((((n-m : ℤ) : ℂ) *
                sourceSingleRootQuotientJointProduct hp hp1 m
                  (μ,((a : Coeff p),ψ))) /
                (displacedRoots (a : Coeff p) n-μ))) := by
  let F : ℂ → ℂ := fun z =>
    ((displacedRoots (a : Coeff p) m-z) /
      (displacedRoots (a : Coeff p) k-z)) *
      (((n-m : ℤ) : ℂ) *
        sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p) ψ z)
  have hFreal : ∀ z ∈ standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m),
        ((-I)*F z).im = 0 := by
    intro z hz
    have hnum := sourcePsiGapNumerator_rotated_im_eq_zero_on_selectedGap
      hp hp1 ψ hreal (a : Coeff p) hroots n m (x:ℂ) R hseg hdom z hz
    have hzPeriod : z ∈ sourcePeriodicSegment hp hp1 ψ m :=
      sourceStandardRoot_gapSegment_subset_periodicSegment hp hp1 ψ m hz
    have hzIm : z.im = 0 :=
      sourcePeriodicSegment_im_eq_zero_of_realType hp hp1 ψ hreal m z hzPeriod
    have hden : (displacedRoots (a : Coeff p) k-z).im = 0 := by
      simp [Complex.sub_im,hroots k,hzIm]
    have hrewrite : (-I)*F z =
        ((-I)*(displacedRoots (a : Coeff p) m-z)*
          (((n-m : ℤ) : ℂ) *
            sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p) ψ z)) /
            (displacedRoots (a : Coeff p) k-z) := by
      dsimp [F]
      ring
    rw [hrewrite]
    rw [Complex.div_im, hnum, hden]
    ring
  obtain ⟨μ,hμ,hvalue⟩ :=
    exists_sourceStandardRoot_imaginaryNumerator_meanValue
      hp hp1 ψ hreal m hopen F hFreal x R hR hseg hF
  have hJ := deriv_sourcePsiDeletedEquationCoordinate_eq_gap_factor_circleIntegral
    hp hp1 n m k hkn a ψ hreal (x:ℂ) R hR.le hcircle havoidn havoidk
  have hJ' :
      deriv (fun t : ℂ => sourcePsiDeletedEquationCoordinate hp hp1 n m
        (a+Coeff.deletedSingleCLM n k hkn t) ψ (x:ℂ) R) 0 =
      ∮ z in C((x:ℂ),R), F z /
        sourceStandardRoot hp hp1 ψ m z := by
    rw [hJ]
    apply circleIntegral.integral_congr hR.le
    intro z hz
    dsimp [F]
    ring
  refine ⟨μ,hμ,?_⟩
  rw [hJ']
  rw [hvalue]
  calc
    2*(Real.pi : ℂ)*((-I)*F μ) =
        2*(Real.pi : ℂ)*
          (((displacedRoots (a : Coeff p) m-μ) /
            (displacedRoots (a : Coeff p) k-μ)) *
              ((-I)*(((n-m : ℤ) : ℂ) *
                sourcePsiGapRegularFactor hp hp1 n m
                  (a : Coeff p) ψ μ))) := by dsimp [F]; ring
    _ = _ := by
      rw [sourcePsi_diagonal_rotatedFactor_eq_quotient]

end NLS.ZakharovShabat
