import NLS.ZakharovShabat.SourcePsiJacobianDiagonalTail
import NLS.ZakharovShabat.SourcePsiNearFreeCollapsedGap

/-!
# Diagonal psi Jacobian at a collapsed periodic gap

At a collapsed gap, the standard root is linear. Differentiating in
the selected retained root leaves a Cauchy kernel, so the diagonal
entry is the regular quotient evaluated at the gap midpoint. This is
the collapsed-gap counterpart of the open-gap mean-value formula.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The diagonal Jacobian entry at a collapsed gap is the quotient
evaluated at the moving periodic midpoint. -/
theorem sourcePsi_diagonalJacobian_collapsedGap_eq_quotient
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n m : ℤ) (hmn : m ≠ n) (a : DeletedCoeff p n)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m = 0)
    (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hmid : sourceStandardRootMidpoint hp hp1 ψ m ∈ ball c R)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ)
    (havoidn : ∀ z ∈ sphere c R,
      z ≠ displacedRoots (a : Coeff p) n)
    (havoidm : ∀ z ∈ sphere c R,
      z ≠ displacedRoots (a : Coeff p) m)
    (hreg : AnalyticOnNhd ℂ
      (fun z => (((n-m : ℤ) : ℂ) *
        sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p) ψ z))
      (closedBall c R)) :
    deriv (fun t : ℂ => sourcePsiDeletedEquationCoordinate hp hp1 n m
      (a+Coeff.deletedSingleCLM n m hmn t) ψ c R) 0 =
        2*(Real.pi : ℂ) *
          ((((n-m : ℤ) : ℂ) *
            sourceSingleRootQuotientJointProduct hp hp1 m
              (sourceStandardRootMidpoint hp hp1 ψ m,
                ((a : Coeff p),ψ))) /
              (displacedRoots (a : Coeff p) n-
                sourceStandardRootMidpoint hp hp1 ψ m)) := by
  let τ := sourceStandardRootMidpoint hp hp1 ψ m
  let F : ℂ → ℂ := fun z => (((n-m : ℤ) : ℂ) *
    sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p) ψ z)
  have hJ := deriv_sourcePsiDeletedEquationCoordinate_diagonal_eq_gap_circleIntegral
    hp hp1 n m hmn a ψ hreal c R hR.le hcircle havoidn havoidm
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
    hp hp1 n m (a : Coeff p) ψ τ
  calc
    -(2 * (Real.pi : ℂ) * I) * F τ =
        2*(Real.pi : ℂ) *
          ((-I) * (((n-m : ℤ) : ℂ) *
            sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p) ψ τ)) := by
              dsimp [F]
              ring
    _ = _ := by rw [hfactor]

/-- The collapsed-gap diagonal entry obeys the same quantitative
`2 + error` estimate as the open-gap entry. -/
theorem norm_sourcePsi_diagonalJacobian_collapsedGap_sub_two_le
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n m : ℤ) (hmn : m ≠ n) (a : DeletedCoeff p n)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m = 0)
    (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hmid : sourceStandardRootMidpoint hp hp1 ψ m ∈ ball c R)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ)
    (havoidn : ∀ z ∈ sphere c R,
      z ≠ displacedRoots (a : Coeff p) n)
    (havoidm : ∀ z ∈ sphere c R,
      z ≠ displacedRoots (a : Coeff p) m)
    (hreg : AnalyticOnNhd ℂ
      (fun z => (((n-m : ℤ) : ℂ) *
        sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p) ψ z))
      (closedBall c R))
    (B : Coeff p)
    (hsmall : 2*(‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
      ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2) ≤ Real.pi)
    (hQ : ‖sourceSingleRootQuotientJointProduct hp hp1 m
      (sourceStandardRootMidpoint hp hp1 ψ m,
        ((a : Coeff p),ψ))-1‖ ≤ ‖B m‖) :
    ‖deriv (fun t : ℂ => sourcePsiDeletedEquationCoordinate hp hp1 n m
      (a+Coeff.deletedSingleCLM n m hmn t) ψ c R) 0-2‖ ≤
        4*‖B m‖ +
          4*(‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
            ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2) /
              ‖(Real.pi : ℂ)*((n-m : ℤ) : ℂ)‖ := by
  let τ := sourceStandardRootMidpoint hp hp1 ψ m
  have hmidNorm : ‖τ-(Real.pi : ℂ)*m‖ =
      ‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ := by
    simp only [τ, sourcePeriodicMidpointDisplacement_apply,
      sourceStandardRootMidpoint]
  have hsep := pi_le_norm_free_lattice_difference n m hmn
  have hnear : 2*‖τ-(Real.pi : ℂ)*m‖ ≤
      ‖(Real.pi : ℂ)*((n-m : ℤ) : ℂ)‖ := by
    rw [hmidNorm]
    have hgapNonneg := norm_nonneg
      (sourcePeriodicGapDisplacement hp hp1 ψ m)
    nlinarith
  rw [sourcePsi_diagonalJacobian_collapsedGap_eq_quotient
    hp hp1 ψ hreal n m hmn a hgap c R hR hmid hcircle havoidn
      havoidm hreg]
  have hpoint := norm_sourcePsi_diagonal_meanValue_sub_two_le
    hp hp1 n m hmn a ψ τ hnear
  change ‖2 * (Real.pi : ℂ) *
        ((((n-m : ℤ) : ℂ) *
          sourceSingleRootQuotientJointProduct hp hp1 m
            (τ,((a : Coeff p),ψ))) /
            (displacedRoots (a : Coeff p) n-τ))-2‖ ≤ _
  calc
    _ ≤ 4*‖sourceSingleRootQuotientJointProduct hp hp1 m
          (τ,((a : Coeff p),ψ))-1‖ +
        4*‖τ-(Real.pi : ℂ)*m‖ /
          ‖(Real.pi : ℂ)*((n-m : ℤ) : ℂ)‖ := hpoint
    _ ≤ 4*‖B m‖ +
        4*(‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
          ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2) /
            ‖(Real.pi : ℂ)*((n-m : ℤ) : ℂ)‖ := by
      gcongr
      rw [hmidNorm]
      have := norm_nonneg (sourcePeriodicGapDisplacement hp hp1 ψ m)
      linarith

/-- A quotient majorant on the selected contour disc controls the
diagonal Jacobian entry for both open and collapsed real gaps. -/
theorem norm_sourcePsi_diagonalJacobian_sub_two_le_all_real_gaps
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
    (havoidm : ∀ z ∈ sphere (x:ℂ) R,
      z ≠ displacedRoots (a : Coeff p) m)
    (hreg : AnalyticOnNhd ℂ
      (fun z => (((n-m : ℤ) : ℂ) *
        sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p) ψ z))
      (closedBall (x:ℂ) R))
    (B : Coeff p)
    (hsmall : 2*(‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
      ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2) ≤ Real.pi)
    (hQ : ∀ z ∈ closedBall (x:ℂ) R,
      ‖sourceSingleRootQuotientJointProduct hp hp1 m
        (z,((a : Coeff p),ψ))-1‖ ≤ ‖B m‖) :
    ‖deriv (fun t : ℂ => sourcePsiDeletedEquationCoordinate hp hp1 n m
      (a+Coeff.deletedSingleCLM n m hmn t) ψ (x:ℂ) R) 0-2‖ ≤
        4*‖B m‖ +
          4*(‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
            ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2) /
              ‖(Real.pi : ℂ)*((n-m : ℤ) : ℂ)‖ := by
  by_cases hopen :
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) m).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) m).re
  · exact norm_sourcePsi_diagonalJacobian_sub_two_le_of_lp_majorant
      hp hp1 ψ hreal n m hmn a hroots hopen x R hR hseg hdom
        hcircle havoidn havoidm hreg B hsmall
        (fun μ hμ => hQ μ (ball_subset_closedBall
          (hseg (sourceStandardRoot_gapSegment_subset_periodicSegment
            hp hp1 ψ m hμ))))
  · have hgap := sourcePeriodicGap_eq_zero_of_real_not_open
      hp hp1 ψ hreal m hopen
    have hmid : sourceStandardRootMidpoint hp hp1 ψ m ∈
        ball (x:ℂ) R := by
      exact hseg (sourcePeriodicMidpoint_mem_segment hp hp1 ψ m)
    exact norm_sourcePsi_diagonalJacobian_collapsedGap_sub_two_le
      hp hp1 ψ hreal n m hmn a hgap (x:ℂ) R hR hmid hcircle
        havoidn havoidm hreg B hsmall
        (hQ _ (ball_subset_closedBall hmid))

end NLS.ZakharovShabat
