import NLS.ZakharovShabat.SourcePsiJacobianOffDiagonalGapGeometry
import NLS.ZakharovShabat.SourcePsiFreeLatticeBound

/-!
# Quantitative off-diagonal psi Jacobian estimate

The real-gap mean-value formula, quarter-π root separation, and the
regular quotient majorant give an `ℓᵖ` row numerator divided by the
distance between selected and varied lattice indices.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A varied root in its quarter-π disc cannot meet a different
free-centered quarter-π disc. -/
theorem sourcePsi_variedRoot_ne_on_other_freeDisc
    {p : ℝ≥0∞} (a : Coeff p)
    (m k : ℤ) (hmk : m ≠ k)
    (R : ℝ) (hR : R ≤ Real.pi/4)
    (hroot : ‖a k‖ ≤ Real.pi/4)
    (z : ℂ) (hz : z ∈ closedBall ((Real.pi : ℂ)*m) R) :
    z ≠ displacedRoots a k := by
  have hzNear : ‖z-(Real.pi : ℂ)*m‖ ≤ Real.pi/4 := by
    have hd : ‖z-(Real.pi : ℂ)*m‖ ≤ R := by
      simpa only [mem_closedBall,dist_eq_norm] using hz
    exact hd.trans hR
  have hsep := half_pi_lattice_separation_le_root_sub_gapPoint
    a m k hmk z hroot hzNear
  have hidx : (((m-k : ℤ) : ℂ)) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr hmk
  have hpos : 0 < ‖displacedRoots a k-z‖ :=
    lt_of_lt_of_le
      (mul_pos (by positivity) (norm_pos_iff.mpr hidx)) hsep
  exact (sub_ne_zero.mp (norm_pos_iff.mp hpos)).symm

/-- Analyticity of the weighted regular factor extends to the
off-diagonal kernel on a free-centered disc when the varied root is
localized in its distinct quarter-π disc. -/
theorem analyticOnNhd_sourcePsi_offDiagonal_factor_freeDisc
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m k : ℤ) (hmk : m ≠ k)
    (a : Coeff p) (ψ : CoeffPair p)
    (R : ℝ) (hR : R ≤ Real.pi/4)
    (hroot : ‖a k‖ ≤ Real.pi/4)
    (hreg : AnalyticOnNhd ℂ
      (fun z => (((n-m : ℤ) : ℂ) *
        sourcePsiGapRegularFactor hp hp1 n m a ψ z))
      (closedBall ((Real.pi : ℂ)*m) R)) :
    AnalyticOnNhd ℂ
      (fun z =>
        ((displacedRoots a m-z)/(displacedRoots a k-z)) *
          (((n-m : ℤ) : ℂ) *
            sourcePsiGapRegularFactor hp hp1 n m a ψ z))
      (closedBall ((Real.pi : ℂ)*m) R) := by
  intro z hz
  have havoid := sourcePsi_variedRoot_ne_on_other_freeDisc
    a m k hmk R hR hroot z hz
  have hden : displacedRoots a k-z ≠ 0 :=
    sub_ne_zero.mpr havoid.symm
  have hnumAnalytic : AnalyticAt ℂ
      (fun w => displacedRoots a m-w) z :=
    analyticAt_const.sub analyticAt_id
  have hdenAnalytic : AnalyticAt ℂ
      (fun w => displacedRoots a k-w) z :=
    analyticAt_const.sub analyticAt_id
  exact (hnumAnalytic.div hdenAnalytic hden).mul (hreg z hz)

/-- On a free-centered selected contour disc, the off-diagonal
Jacobian entry has the expected `1/|m-k|` decay. The remaining
analyticity assumption concerns the moved-root denominator. -/
theorem norm_sourcePsi_offDiagonalJacobian_le_of_discMajorant
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n m k : ℤ) (hmn : m ≠ n) (hkn : k ≠ n) (hmk : m ≠ k)
    (a : DeletedCoeff p n)
    (hroots : ∀ j : ℤ, (displacedRoots (a : Coeff p) j).im = 0)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) m).re)
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
  have havoidk : ∀ z ∈ sphere ((Real.pi : ℂ)*m) R,
      z ≠ displacedRoots (a : Coeff p) k := by
    intro z hz
    exact sourcePsi_variedRoot_ne_on_other_freeDisc
      (a : Coeff p) m k hmk R hRquarter hroot z
        (sphere_subset_closedBall hz)
  have hF := analyticOnNhd_sourcePsi_offDiagonal_factor_freeDisc
    hp hp1 n m k hmk (a : Coeff p) ψ R hRquarter hroot hreg
  obtain ⟨μ,hμ,hvalue⟩ :=
    exists_sourcePsi_offDiagonalJacobian_quotient_meanValue
      hp hp1 ψ hreal n m k hkn a hroots hopen (Real.pi*m) R hR
        (by simpa only [Complex.ofReal_mul,Complex.ofReal_intCast] using hseg)
        (by simpa only [Complex.ofReal_mul,Complex.ofReal_intCast] using hdom)
        (by simpa only [Complex.ofReal_mul,Complex.ofReal_intCast] using hcircle)
        (by simpa only [Complex.ofReal_mul,Complex.ofReal_intCast] using havoidn)
        (by simpa only [Complex.ofReal_mul,Complex.ofReal_intCast] using havoidk)
        (by simpa only [Complex.ofReal_mul,Complex.ofReal_intCast] using hF)
  have hratio := norm_offDiagonal_rootRatio_le_of_smallGapDisplacements
    hp hp1 (a : Coeff p) ψ m k hmk μ hμ hroot hsmall
  have hμclosed : μ ∈ closedBall ((Real.pi : ℂ)*m) R :=
    ball_subset_closedBall (hseg
      (sourceStandardRoot_gapSegment_subset_periodicSegment hp hp1 ψ m hμ))
  have hfac := norm_deletedPsi_gapRegularFactor_weighted_le
    hp hp1 n m (Ne.symm hmn) a ψ B R hRquarter μ hμclosed
      (hQ μ hμclosed)
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
  have hvalue' :
      deriv (fun t : ℂ => sourcePsiDeletedEquationCoordinate hp hp1 n m
        (a+Coeff.deletedSingleCLM n k hkn t) ψ
          ((Real.pi : ℂ)*m) R) 0 =
        2*(Real.pi : ℂ)*
          (((displacedRoots (a : Coeff p) m-μ) /
            (displacedRoots (a : Coeff p) k-μ)) *
              ((((n-m : ℤ) : ℂ) *
                sourceSingleRootQuotientJointProduct hp hp1 m
                  (μ,((a : Coeff p),ψ))) /
                (displacedRoots (a : Coeff p) n-μ))) := by
    simpa only [Complex.ofReal_mul,Complex.ofReal_intCast] using hvalue
  rw [hvalue']
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

end NLS.ZakharovShabat
