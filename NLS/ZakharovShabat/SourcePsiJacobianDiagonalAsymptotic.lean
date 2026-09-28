import NLS.ZakharovShabat.SourcePsiJacobianDiagonalMeanValue

/-!
# Quantitative denominator estimate for the diagonal psi Jacobian

The diagonal mean-value formula compares a quotient at a moving gap
point with its free value. The error splits into the quotient error
and the displacement of that point from the free lattice center.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- An elementary form of the diagonal Jacobian estimate. If the
denominator perturbation is at most half the free denominator, the
result differs from two by the quotient and denominator errors. -/
theorem norm_two_ratio_sub_two_le
    (A q e : ℂ) (hA : A ≠ 0)
    (he : 2*‖e‖ ≤ ‖A‖) :
    ‖2*(A*q/(A-e))-2‖ ≤
      4*‖q-1‖ + 4*‖e‖/‖A‖ := by
  have hApos : 0 < ‖A‖ := norm_pos_iff.mpr hA
  have htri : ‖A‖ ≤ ‖A-e‖+‖e‖ := by
    have hsplit : A = (A-e)+e := by ring
    conv_lhs => rw [hsplit]
    exact norm_add_le _ _
  have hDpos : 0 < ‖A-e‖ := by linarith
  have hD : A-e ≠ 0 := norm_pos_iff.mp hDpos
  have hAle : ‖A‖ ≤ 2*‖A-e‖ := by linarith
  have hrat : ‖A‖/‖A-e‖ ≤ 2 := by
    apply (div_le_iff₀ hDpos).2
    linarith
  have herr : ‖e‖/‖A-e‖ ≤ 2*‖e‖/‖A‖ := by
    apply (div_le_div_iff₀ hDpos hApos).2
    have h := mul_le_mul_of_nonneg_right hAle (norm_nonneg e)
    nlinarith
  have hEq : 2*(A*q/(A-e))-2 =
      (2*A*(q-1)+2*e)/(A-e) := by
    field_simp [hD]
    ring
  rw [hEq,norm_div]
  have hnum : ‖2*A*(q-1)+2*e‖ ≤
      2*‖A‖*‖q-1‖+2*‖e‖ := by
    calc
      _ ≤ ‖2*A*(q-1)‖+‖2*e‖ := norm_add_le _ _
      _ = 2*‖A‖*‖q-1‖+2*‖e‖ := by simp
  calc
    ‖2*A*(q-1)+2*e‖/‖A-e‖ ≤
        (2*‖A‖*‖q-1‖+2*‖e‖)/‖A-e‖ :=
      div_le_div_of_nonneg_right hnum (norm_nonneg _)
    _ = 2*‖q-1‖*(‖A‖/‖A-e‖)+2*(‖e‖/‖A-e‖) := by ring
    _ ≤ 2*‖q-1‖*2+2*(2*‖e‖/‖A‖) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hrat (by positivity))
        (mul_le_mul_of_nonneg_left herr (by norm_num))
    _ = 4*‖q-1‖+4*‖e‖/‖A‖ := by ring

/-- The free lattice denominator is the diagonal mean-value
denominator with the selected gap's displacement subtracted. -/
theorem sourcePsi_diagonal_freeDenominator_identity
    (n m : ℤ) (μ : ℂ) :
    ((Real.pi : ℂ)*((n-m : ℤ) : ℂ)) -
      (μ-(Real.pi : ℂ)*m) =
        (Real.pi : ℂ)*n-μ := by
  push_cast
  ring

/-- Every point of the selected periodic gap is controlled by the
midpoint and gap displacement coefficients at that index. -/
theorem norm_sourceStandardRoot_gapPoint_sub_free_le
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (m : ℤ) (μ : ℂ)
    (hμ : μ ∈ standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m)) :
    ‖μ-(Real.pi : ℂ)*m‖ ≤
      ‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
        ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2 := by
  obtain ⟨r,hr,rfl⟩ := hμ
  have hrabs : |r| ≤ 1 := abs_le.mpr hr
  have htri :
      ‖(sourceStandardRootMidpoint hp hp1 ψ m +
          sourceStandardRootHalfGap hp hp1 ψ m*(r:ℂ))-
            (Real.pi : ℂ)*m‖ ≤
        ‖sourceStandardRootMidpoint hp hp1 ψ m-(Real.pi : ℂ)*m‖ +
          ‖sourceStandardRootHalfGap hp hp1 ψ m*(r:ℂ)‖ := by
    have heq :
        (sourceStandardRootMidpoint hp hp1 ψ m +
          sourceStandardRootHalfGap hp hp1 ψ m*(r:ℂ))-
            (Real.pi : ℂ)*m =
        (sourceStandardRootMidpoint hp hp1 ψ m-(Real.pi : ℂ)*m) +
          sourceStandardRootHalfGap hp hp1 ψ m*(r:ℂ) := by ring
    rw [heq]
    exact norm_add_le _ _
  have hmul :
      ‖sourceStandardRootHalfGap hp hp1 ψ m*(r:ℂ)‖ ≤
        ‖sourceStandardRootHalfGap hp hp1 ψ m‖ := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hrabs (norm_nonneg _)
  have hmid :
      ‖sourceStandardRootMidpoint hp hp1 ψ m-(Real.pi : ℂ)*m‖ =
        ‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ := by
    simp only [sourcePeriodicMidpointDisplacement_apply,
      sourceStandardRootMidpoint]
  have hgap :
      ‖sourceStandardRootHalfGap hp hp1 ψ m‖ =
        ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2 := by
    simp [sourceStandardRootHalfGap,sourcePeriodicGapDisplacement_apply]
  rw [hmid] at htri
  rw [hgap] at hmul
  linarith

/-- A selected gap with small midpoint and gap displacement stays
within half the free denominator for every other lattice index. -/
theorem sourcePsi_gapPoint_halfDenominator_of_smallDisplacements
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n m : ℤ) (hmn : m ≠ n) (μ : ℂ)
    (hμ : μ ∈ standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m))
    (hsmall : 2*(‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
      ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2) ≤ Real.pi) :
    2*‖μ-(Real.pi : ℂ)*m‖ ≤
      ‖(Real.pi : ℂ)*((n-m : ℤ) : ℂ)‖ := by
  have hgap := norm_sourceStandardRoot_gapPoint_sub_free_le
    hp hp1 ψ m μ hμ
  have hidx : (1:ℝ) ≤ |((n-m : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr (Ne.symm hmn))
  have hnorm : ‖(Real.pi : ℂ)*((n-m : ℤ) : ℂ)‖ =
      Real.pi*|((n-m : ℤ) : ℝ)| := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_intCast]
    simp [abs_of_pos Real.pi_pos]
  rw [hnorm]
  nlinarith [Real.pi_pos]

/-- Quantitative diagonal estimate at an arbitrary gap point. The
quotient and gap-location errors are left visible for the spectral
majorants of Lemma 10.8. -/
theorem norm_sourcePsi_diagonal_meanValue_sub_two_le
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m : ℤ) (hmn : m ≠ n)
    (a : DeletedCoeff p n) (ψ : CoeffPair p) (μ : ℂ)
    (hnear : 2*‖μ-(Real.pi : ℂ)*m‖ ≤
      ‖(Real.pi : ℂ)*((n-m : ℤ) : ℂ)‖) :
    ‖2*(Real.pi : ℂ) *
        ((((n-m : ℤ) : ℂ) *
          sourceSingleRootQuotientJointProduct hp hp1 m
            (μ,((a : Coeff p),ψ))) /
            (displacedRoots (a : Coeff p) n-μ))-2‖ ≤
      4*‖sourceSingleRootQuotientJointProduct hp hp1 m
        (μ,((a : Coeff p),ψ))-1‖ +
        4*‖μ-(Real.pi : ℂ)*m‖ /
          ‖(Real.pi : ℂ)*((n-m : ℤ) : ℂ)‖ := by
  have ha : (a : Coeff p) n = 0 := a.property
  have hroot : displacedRoots (a : Coeff p) n = (Real.pi : ℂ)*n := by
    simp [displacedRoots,ha]
  have hnm : (((n-m : ℤ) : ℂ)) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr (Ne.symm hmn)
  have hA : (Real.pi : ℂ)*((n-m : ℤ) : ℂ) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) hnm
  have h := norm_two_ratio_sub_two_le
    ((Real.pi : ℂ)*((n-m : ℤ) : ℂ))
    (sourceSingleRootQuotientJointProduct hp hp1 m
      (μ,((a : Coeff p),ψ)))
    (μ-(Real.pi : ℂ)*m) hA hnear
  rw [sourcePsi_diagonal_freeDenominator_identity] at h
  rw [hroot]
  convert h using 1
  ring

/-- The diagonal derivative differs from two by a quotient error and
an index-decaying gap-location error. This is the pointwise interface
for the uniform `ℓᵖ` estimates in Lemma 12.5. -/
theorem norm_sourcePsi_diagonalJacobian_sub_two_le_of_gap_bounds
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
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
    (E D : ℝ)
    (hnear : ∀ μ ∈ standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m),
      2*‖μ-(Real.pi : ℂ)*m‖ ≤
        ‖(Real.pi : ℂ)*((n-m : ℤ) : ℂ)‖)
    (hQ : ∀ μ ∈ standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m),
      ‖sourceSingleRootQuotientJointProduct hp hp1 m
        (μ,((a : Coeff p),ψ))-1‖ ≤ E)
    (hgap : ∀ μ ∈ standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m),
      ‖μ-(Real.pi : ℂ)*m‖ ≤ D) :
    ‖deriv (fun t : ℂ => sourcePsiDeletedEquationCoordinate hp hp1 n m
      (a+Coeff.deletedSingleCLM n m hmn t) ψ (x:ℂ) R) 0-2‖ ≤
      4*E + 4*D/‖(Real.pi : ℂ)*((n-m : ℤ) : ℂ)‖ := by
  obtain ⟨μ,hμ,hvalue⟩ :=
    exists_sourcePsi_diagonalJacobian_quotient_meanValue
      hp hp1 ψ hreal n m hmn a hroots hopen x R hR hseg hdom
        hcircle havoidn hreg
  rw [hvalue]
  calc
    ‖2 * (Real.pi : ℂ) *
        ((((n-m : ℤ) : ℂ) *
          sourceSingleRootQuotientJointProduct hp hp1 m
            (μ,((a : Coeff p),ψ))) /
            (displacedRoots (a : Coeff p) n-μ))-2‖ ≤
      4*‖sourceSingleRootQuotientJointProduct hp hp1 m
        (μ,((a : Coeff p),ψ))-1‖ +
        4*‖μ-(Real.pi : ℂ)*m‖ /
          ‖(Real.pi : ℂ)*((n-m : ℤ) : ℂ)‖ :=
            norm_sourcePsi_diagonal_meanValue_sub_two_le
              hp hp1 n m hmn a ψ μ (hnear μ hμ)
    _ ≤ 4*E + 4*D/‖(Real.pi : ℂ)*((n-m : ℤ) : ℂ)‖ := by
      gcongr
      · exact hQ μ hμ
      · exact hgap μ hμ

/-- The diagonal `2 + error` bound in terms of the actual `ℓᵖ`
quotient, midpoint, and gap coefficients. -/
theorem norm_sourcePsi_diagonalJacobian_sub_two_le_of_lp_majorant
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
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
    (B : Coeff p)
    (hsmall : 2*(‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
      ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2) ≤ Real.pi)
    (hQ : ∀ μ ∈ standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m),
      ‖sourceSingleRootQuotientJointProduct hp hp1 m
        (μ,((a : Coeff p),ψ))-1‖ ≤ ‖B m‖) :
    ‖deriv (fun t : ℂ => sourcePsiDeletedEquationCoordinate hp hp1 n m
      (a+Coeff.deletedSingleCLM n m hmn t) ψ (x:ℂ) R) 0-2‖ ≤
      4*‖B m‖ +
        4*(‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
          ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2) /
          ‖(Real.pi : ℂ)*((n-m : ℤ) : ℂ)‖ := by
  exact norm_sourcePsi_diagonalJacobian_sub_two_le_of_gap_bounds
    hp hp1 ψ hreal n m hmn a hroots hopen x R hR hseg hdom
      hcircle havoidn hreg ‖B m‖
        (‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
          ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2)
      (fun μ hμ => sourcePsi_gapPoint_halfDenominator_of_smallDisplacements
        hp hp1 ψ n m hmn μ hμ hsmall)
      hQ
      (fun μ hμ => norm_sourceStandardRoot_gapPoint_sub_free_le
        hp hp1 ψ m μ hμ)

end NLS.ZakharovShabat
