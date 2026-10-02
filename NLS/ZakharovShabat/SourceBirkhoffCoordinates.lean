import NLS.ZakharovShabat.SourceGapWeightedEtaLemma15_1
import NLS.ZakharovShabat.SourceNormalizedActionRootAnalytic

/-! # The rectangular Birkhoff coordinates of formula (3.2)

The signed gap-weighted eta coordinates are multiplied by the actual
normalized-action root and beta phase. Their sum and difference give
`x` and `y`, respectively. These definitions do not divide by a gap and
remain meaningful at complex collapsed gaps.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The weighted signed phase entering formula (3.2). -/
def sourceBirkhoffWeightedCoordinate (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (sign : ℂ) (ψ : CoeffPair p) : ℂ :=
  sourceNormalizedActionRoot hp hp1 n ψ * sourceGapWeightedEtaCoordinate hp hp1 n s sign ψ *
    Complex.exp (sign*I*sourceAngularBetaCorrection hp hp1 n s ψ)

def sourceBirkhoffX (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p) : ℂ :=
  (sourceBirkhoffWeightedCoordinate hp hp1 n s 1 ψ +
    sourceBirkhoffWeightedCoordinate hp hp1 n s (-1) ψ) / (Real.sqrt 8 : ℂ)

def sourceBirkhoffY (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p) : ℂ :=
  (sourceBirkhoffWeightedCoordinate hp hp1 n s 1 ψ -
    sourceBirkhoffWeightedCoordinate hp hp1 n s (-1) ψ) / ((Real.sqrt 8 : ℂ)*I)

theorem analyticAt_sourceBirkhoffWeightedCoordinate
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (sign : ℂ) (ψ : CoeffPair p)
    (hξ : AnalyticAt ℂ (sourceNormalizedActionRoot hp hp1 n) ψ)
    (hz : AnalyticAt ℂ (sourceGapWeightedEtaCoordinate hp hp1 n s sign) ψ)
    (hβ : AnalyticAt ℂ (sourceAngularBetaCorrection hp hp1 n s) ψ) :
    AnalyticAt ℂ (sourceBirkhoffWeightedCoordinate hp hp1 n s sign) ψ :=
  (hξ.mul hz).mul ((analyticAt_const.mul hβ).cexp')

theorem analyticAt_sourceBirkhoffXY
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p)
    (hξ : AnalyticAt ℂ (sourceNormalizedActionRoot hp hp1 n) ψ)
    (hz : ∀ sign : ℂ, AnalyticAt ℂ (sourceGapWeightedEtaCoordinate hp hp1 n s sign) ψ)
    (hβ : AnalyticAt ℂ (sourceAngularBetaCorrection hp hp1 n s) ψ) :
    AnalyticAt ℂ (sourceBirkhoffX hp hp1 n s) ψ ∧ AnalyticAt ℂ (sourceBirkhoffY hp hp1 n s) ψ := by
  have hplus := analyticAt_sourceBirkhoffWeightedCoordinate hp hp1 n s 1 ψ hξ (hz 1) hβ
  have hminus := analyticAt_sourceBirkhoffWeightedCoordinate hp hp1 n s (-1) ψ hξ (hz (-1)) hβ
  have hd : (Real.sqrt 8 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))
  exact ⟨(hplus.add hminus).div analyticAt_const hd,
    (hplus.sub hminus).div analyticAt_const (mul_ne_zero hd I_ne_zero)⟩

/-- The beta phases cancel in the signed product, also at zero gaps. -/
theorem sourceBirkhoffWeightedCoordinate_mul
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p)
    (hprod : sourceGapWeightedEtaCoordinate hp hp1 n s 1 ψ *
      sourceGapWeightedEtaCoordinate hp hp1 n s (-1) ψ = (sourcePeriodicGapDisplacement hp hp1 ψ n)^2) :
    sourceBirkhoffWeightedCoordinate hp hp1 n s 1 ψ *
      sourceBirkhoffWeightedCoordinate hp hp1 n s (-1) ψ =
        (sourceNormalizedActionRoot hp hp1 n ψ)^2 * (sourcePeriodicGapDisplacement hp hp1 ψ n)^2 := by
  let β := sourceAngularBetaCorrection hp hp1 n s ψ
  have he : Complex.exp (I*β)*Complex.exp (-(I*β)) = 1 := by
    rw [← Complex.exp_add,add_neg_cancel,Complex.exp_zero]
  calc
    _ = (sourceNormalizedActionRoot hp hp1 n ψ)^2 *
        (sourceGapWeightedEtaCoordinate hp hp1 n s 1 ψ * sourceGapWeightedEtaCoordinate hp hp1 n s (-1) ψ) *
        (Complex.exp (I*β)*Complex.exp (-(I*β))) := by
      simp only [sourceBirkhoffWeightedCoordinate,one_mul,neg_mul]
      dsimp only [β]
      ring
    _ = _ := by rw [he,hprod,mul_one]

/-- The normalization and the difference in `y` give the exact action
identity. Both input identities hold throughout the constructed domain. -/
theorem sourceBirkhoffX_sq_add_Y_sq
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p)
    (hprod : sourceGapWeightedEtaCoordinate hp hp1 n s 1 ψ *
      sourceGapWeightedEtaCoordinate hp hp1 n s (-1) ψ = (sourcePeriodicGapDisplacement hp hp1 ψ n)^2)
    (hξ : (sourceNormalizedActionRoot hp hp1 n ψ)^2 = 4*sourceNormalizedActionComplexExtension hp hp1 n ψ)
    (hI : sourceComplexAction hp hp1 n ψ =
      (sourcePeriodicGapDisplacement hp hp1 ψ n)^2 * sourceNormalizedActionComplexExtension hp hp1 n ψ) :
    (sourceBirkhoffX hp hp1 n s ψ)^2 + (sourceBirkhoffY hp hp1 n s ψ)^2 =
      2*sourceComplexAction hp hp1 n ψ := by
  have hd : (Real.sqrt 8 : ℂ)^2 = 8 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  have hu := sourceBirkhoffWeightedCoordinate_mul hp hp1 n s ψ hprod
  rw [hξ] at hu
  rw [sourceBirkhoffX,sourceBirkhoffY,div_pow,div_pow,mul_pow,hd,I_sq,hI]
  linear_combination (1/2:ℂ)*hu

/-- Real closed-gap vanishing of both eta coordinates transfers to
both rectangular coordinates, independently of the beta value. -/
theorem sourceBirkhoffXY_eq_zero_of_gapWeighted_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p)
    (hplus : sourceGapWeightedEtaCoordinate hp hp1 n s 1 ψ = 0)
    (hminus : sourceGapWeightedEtaCoordinate hp hp1 n s (-1) ψ = 0) :
    sourceBirkhoffX hp hp1 n s ψ = 0 ∧ sourceBirkhoffY hp hp1 n s ψ = 0 := by
  simp only [sourceBirkhoffX,sourceBirkhoffY,sourceBirkhoffWeightedCoordinate,
    hplus,hminus,mul_zero,zero_mul,add_zero,sub_self,zero_div,and_self]

end NLS.ZakharovShabat
