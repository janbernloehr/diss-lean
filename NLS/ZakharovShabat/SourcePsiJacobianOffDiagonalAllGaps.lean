import NLS.ZakharovShabat.SourcePsiJacobianOffDiagonalCollapsed

/-!
# Off-diagonal psi Jacobian estimate for both real gap types

The open-gap mean value and collapsed-gap Cauchy residue yield the
same pointwise quotient expression. On free-centered selected discs,
quarter-π root localization and the regular quotient majorant bound
every off-diagonal entry by a row `ℓᵖ` scale over lattice distance.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The off-diagonal quotient expression obeys the displacement-over-
lattice-distance bound at every selected gap point. -/
theorem norm_sourcePsi_offDiagonal_gapValue_le
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m k : ℤ) (hmn : m ≠ n) (hmk : m ≠ k)
    (a : DeletedCoeff p n) (ψ : CoeffPair p)
    (B : Coeff p) (R : ℝ) (hRquarter : R ≤ Real.pi/4)
    (μ : ℂ)
    (hμ : μ ∈ standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m))
    (hμclosed : μ ∈ closedBall ((Real.pi : ℂ)*m) R)
    (hroot : ‖(a : Coeff p) k‖ ≤ Real.pi/4)
    (hsmall : ‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
      ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2 ≤ Real.pi/4)
    (hQ : ‖sourceSingleRootQuotientJointProduct hp hp1 m
      (μ,((a : Coeff p),ψ))-1‖ ≤ ‖B m‖) :
    ‖2*(Real.pi : ℂ)*
      (((displacedRoots (a : Coeff p) m-μ) /
        (displacedRoots (a : Coeff p) k-μ)) *
        ((((n-m : ℤ) : ℂ) *
          sourceSingleRootQuotientJointProduct hp hp1 m
            (μ,((a : Coeff p),ψ))) /
          (displacedRoots (a : Coeff p) n-μ)))‖ ≤
      (8/Real.pi) *
        (‖(a : Coeff p) m‖ +
          ‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
          ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2) *
        (1+‖B m‖) / ‖((m-k : ℤ) : ℂ)‖ := by
  have hratio := norm_offDiagonal_rootRatio_le_of_smallGapDisplacements
    hp hp1 (a : Coeff p) ψ m k hmk μ hμ hroot hsmall
  have hfac := norm_deletedPsi_gapRegularFactor_weighted_le
    hp hp1 n m (Ne.symm hmn) a ψ B R hRquarter μ hμclosed hQ
  have hfac' :
      ‖(((n-m : ℤ) : ℂ) *
          sourceSingleRootQuotientJointProduct hp hp1 m
            (μ,((a : Coeff p),ψ))) /
          (displacedRoots (a : Coeff p) n-μ)‖ ≤
        (2/Real.pi)*(1+‖B m‖) := by
    rw [←sourcePsi_diagonal_rotatedFactor_eq_quotient]
    simpa only [norm_mul,Complex.norm_I,mul_one,norm_neg,one_mul] using hfac
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hidx : (((m-k : ℤ) : ℂ)) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr hmk
  have hdist : ‖((m-k : ℤ) : ℂ)‖ ≠ 0 :=
    ne_of_gt (norm_pos_iff.mpr hidx)
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos Real.pi_pos,norm_ofNat]
  calc
    2*Real.pi *
        (‖(displacedRoots (a : Coeff p) m-μ) /
          (displacedRoots (a : Coeff p) k-μ)‖ *
        ‖(((n-m : ℤ) : ℂ) *
          sourceSingleRootQuotientJointProduct hp hp1 m
            (μ,((a : Coeff p),ψ))) /
          (displacedRoots (a : Coeff p) n-μ)‖) ≤
      2*Real.pi *
        ((‖(a : Coeff p) m‖ +
          ‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
          ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2) /
            ((Real.pi/2)*‖((m-k : ℤ) : ℂ)‖)) *
        ((2/Real.pi)*(1+‖B m‖)) := by
      have hprod :
          ‖(displacedRoots (a : Coeff p) m-μ) /
              (displacedRoots (a : Coeff p) k-μ)‖ *
            ‖(((n-m : ℤ) : ℂ) *
              sourceSingleRootQuotientJointProduct hp hp1 m
                (μ,((a : Coeff p),ψ))) /
              (displacedRoots (a : Coeff p) n-μ)‖ ≤
            ((‖(a : Coeff p) m‖ +
              ‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
              ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2) /
                ((Real.pi/2)*‖((m-k : ℤ) : ℂ)‖)) *
            ((2/Real.pi)*(1+‖B m‖)) := by
        calc
          _ ≤ ((‖(a : Coeff p) m‖ +
                ‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
                ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2) /
                  ((Real.pi/2)*‖((m-k : ℤ) : ℂ)‖)) *
              ‖(((n-m : ℤ) : ℂ) *
                sourceSingleRootQuotientJointProduct hp hp1 m
                  (μ,((a : Coeff p),ψ))) /
                (displacedRoots (a : Coeff p) n-μ)‖ :=
                  mul_le_mul_of_nonneg_right hratio (norm_nonneg _)
          _ ≤ _ := mul_le_mul_of_nonneg_left hfac' (by positivity)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hprod
        (by positivity : 0 ≤ 2*Real.pi)
    _ = (8/Real.pi) *
        (‖(a : Coeff p) m‖ +
          ‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
          ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2) *
        (1+‖B m‖) / ‖((m-k : ℤ) : ℂ)‖ := by
      field_simp
      ring

/-- At a collapsed gap, the Cauchy residue satisfies the same
off-diagonal estimate as an open real gap. -/
theorem norm_sourcePsi_offDiagonalJacobian_collapsedGap_le
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n m k : ℤ) (hmn : m ≠ n) (hkn : k ≠ n) (hmk : m ≠ k)
    (a : DeletedCoeff p n)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m = 0)
    (R : ℝ) (hR : 0 < R) (hRquarter : R ≤ Real.pi/4)
    (hseg : sourcePeriodicSegment hp hp1 ψ m ⊆
      ball ((Real.pi : ℂ)*m) R)
    (hcircle : sphere ((Real.pi : ℂ)*m) R ⊆
      sourceCanonicalRootDomain hp hp1 ψ)
    (havoidn : ∀ z ∈ sphere ((Real.pi : ℂ)*m) R,
      z ≠ displacedRoots (a : Coeff p) n)
    (hreg : AnalyticOnNhd ℂ
      (fun z => (((n-m : ℤ) : ℂ) *
        sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p) ψ z))
      (closedBall ((Real.pi : ℂ)*m) R))
    (B : Coeff p)
    (hroot : ‖(a : Coeff p) k‖ ≤ Real.pi/4)
    (hsmall : ‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
      ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2 ≤ Real.pi/4)
    (hQ : ∀ z ∈ closedBall ((Real.pi : ℂ)*m) R,
      ‖sourceSingleRootQuotientJointProduct hp hp1 m
        (z,((a : Coeff p),ψ))-1‖ ≤ ‖B m‖) :
    ‖deriv (fun t : ℂ => sourcePsiDeletedEquationCoordinate hp hp1 n m
      (a+Coeff.deletedSingleCLM n k hkn t) ψ
        ((Real.pi : ℂ)*m) R) 0‖ ≤
      (8/Real.pi) *
        (‖(a : Coeff p) m‖ +
          ‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
          ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2) *
        (1+‖B m‖) / ‖((m-k : ℤ) : ℂ)‖ := by
  let τ := sourceStandardRootMidpoint hp hp1 ψ m
  have hmid : τ ∈ ball ((Real.pi : ℂ)*m) R :=
    hseg (sourcePeriodicMidpoint_mem_segment hp hp1 ψ m)
  have havoidk : ∀ z ∈ closedBall ((Real.pi : ℂ)*m) R,
      z ≠ displacedRoots (a : Coeff p) k := by
    intro z hz
    exact sourcePsi_variedRoot_ne_on_other_freeDisc
      (a : Coeff p) m k hmk R hRquarter hroot z hz
  have hμ : τ ∈ standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m) := by
    change τ ∈ (fun r : ℝ => τ +
      sourceStandardRootHalfGap hp hp1 ψ m*(r:ℂ)) '' Set.Icc (-1:ℝ) 1
    refine ⟨0,by norm_num,?_⟩
    simp
  have hμclosed : τ ∈ closedBall ((Real.pi : ℂ)*m) R :=
    ball_subset_closedBall hmid
  rw [sourcePsi_offDiagonalJacobian_collapsedGap_eq_quotient
    hp hp1 ψ hreal n m k hkn a hgap ((Real.pi : ℂ)*m) R hR hmid
      hcircle havoidn havoidk hreg]
  exact norm_sourcePsi_offDiagonal_gapValue_le
    hp hp1 n m k hmn hmk a ψ B R hRquarter τ hμ hμclosed
      hroot hsmall (hQ τ hμclosed)

/-- The free-centered off-diagonal Jacobian bound covers both open
and collapsed real periodic gaps. -/
theorem norm_sourcePsi_offDiagonalJacobian_all_realGaps_le
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n m k : ℤ) (hmn : m ≠ n) (hkn : k ≠ n) (hmk : m ≠ k)
    (a : DeletedCoeff p n)
    (hroots : ∀ j : ℤ, (displacedRoots (a : Coeff p) j).im = 0)
    (R : ℝ) (hR : 0 < R) (hRquarter : R ≤ Real.pi/4)
    (hseg : sourcePeriodicSegment hp hp1 ψ m ⊆
      ball ((Real.pi : ℂ)*m) R)
    (hdom : closedBall ((Real.pi : ℂ)*m) R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hcircle : sphere ((Real.pi : ℂ)*m) R ⊆
      sourceCanonicalRootDomain hp hp1 ψ)
    (havoidn : ∀ z ∈ sphere ((Real.pi : ℂ)*m) R,
      z ≠ displacedRoots (a : Coeff p) n)
    (hreg : AnalyticOnNhd ℂ
      (fun z => (((n-m : ℤ) : ℂ) *
        sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p) ψ z))
      (closedBall ((Real.pi : ℂ)*m) R))
    (B : Coeff p)
    (hroot : ‖(a : Coeff p) k‖ ≤ Real.pi/4)
    (hsmall : ‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
      ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2 ≤ Real.pi/4)
    (hQ : ∀ z ∈ closedBall ((Real.pi : ℂ)*m) R,
      ‖sourceSingleRootQuotientJointProduct hp hp1 m
        (z,((a : Coeff p),ψ))-1‖ ≤ ‖B m‖) :
    ‖deriv (fun t : ℂ => sourcePsiDeletedEquationCoordinate hp hp1 n m
      (a+Coeff.deletedSingleCLM n k hkn t) ψ
        ((Real.pi : ℂ)*m) R) 0‖ ≤
      (8/Real.pi) *
        (‖(a : Coeff p) m‖ +
          ‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
          ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2) *
        (1+‖B m‖) / ‖((m-k : ℤ) : ℂ)‖ := by
  by_cases hopen :
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) m).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) m).re
  · exact norm_sourcePsi_offDiagonalJacobian_le_of_discMajorant
      hp hp1 ψ hreal n m k hmn hkn hmk a hroots hopen R hR
        hRquarter hseg hdom hcircle havoidn hreg B hroot hsmall hQ
  · have hgap := sourcePeriodicGap_eq_zero_of_real_not_open
      hp hp1 ψ hreal m hopen
    exact norm_sourcePsi_offDiagonalJacobian_collapsedGap_le
      hp hp1 ψ hreal n m k hmn hkn hmk a hgap R hR hRquarter
        hseg hcircle havoidn hreg B hroot hsmall hQ

end NLS.ZakharovShabat
