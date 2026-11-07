import NLS.KdV.HillActionAngleFactors

/-! The actual scalar Cartesian action-angle coordinates, including
the action amplitude and complete Abelian phase. Exact identities hold
through complex collapsed gaps. Sequence mapping and canonicality are
not inferred from these scalar analytic formulas. -/
noncomputable section
open Set Complex
open scoped Classical
namespace NLS.KdV

def hillHminusActionAngleX (n : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  (hillHminusActionAngleFactorPlus n q+hillHminusActionAngleFactorMinus n q)/2

def hillHminusActionAngleY (n : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  (hillHminusActionAngleFactorPlus n q-hillHminusActionAngleFactorMinus n q)/(2*I)

theorem analyticOnNhd_hillHminusActionAngleX (n : ℕ+) :
    AnalyticOnNhd ℂ (hillHminusActionAngleX n) hillHminusActionAmplitudeDomain := by
  intro q hq
  exact ((analyticOnNhd_hillHminusActionAngleFactorPlus n q hq).add
    (analyticOnNhd_hillHminusActionAngleFactorMinus n q hq)).div_const

theorem analyticOnNhd_hillHminusActionAngleY (n : ℕ+) :
    AnalyticOnNhd ℂ (hillHminusActionAngleY n) hillHminusActionAmplitudeDomain := by
  intro q hq
  exact ((analyticOnNhd_hillHminusActionAngleFactorPlus n q hq).sub
    (analyticOnNhd_hillHminusActionAngleFactorMinus n q hq)).div_const

theorem hillHminusActionAngle_factor_reconstruction (n : ℕ+) (q : PeriodOneHminusOne) :
    hillHminusActionAngleX n q+I*hillHminusActionAngleY n q = hillHminusActionAngleFactorPlus n q ∧
      hillHminusActionAngleX n q-I*hillHminusActionAngleY n q = hillHminusActionAngleFactorMinus n q := by
  unfold hillHminusActionAngleX hillHminusActionAngleY
  constructor <;> field_simp <;> ring

theorem hillHminusActionAngle_sum_squares (n : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusActionAmplitudeDomain) :
    (hillHminusActionAngleX n q)^2+(hillHminusActionAngleY n q)^2 = 2*hillHminusCanonicalAction n q := by
  have h := hillHminusActionAngle_factor_reconstruction n q
  calc
    _ = (hillHminusActionAngleX n q+I*hillHminusActionAngleY n q)*
      (hillHminusActionAngleX n q-I*hillHminusActionAngleY n q) := by
        linear_combination (hillHminusActionAngleY n q)^2*Complex.I_sq
    _ = _ := by rw [h.1,h.2,hillHminusActionAngleFactor_product n q hq]

theorem hillHminusActionAngle_real (n : ℕ+) (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) :
    (hillHminusActionAngleX n q).im = 0 ∧ (hillHminusActionAngleY n q).im = 0 := by
  have hm := hillHminusActionAngleFactor_conjugate_of_real n q hr
  change hillHminusActionAngleFactorMinus n q = (starRingEnd ℂ) (hillHminusActionAngleFactorPlus n q) at hm
  have hx : hillHminusActionAngleX n q = ((hillHminusActionAngleFactorPlus n q).re:ℂ) := by
    rw [hillHminusActionAngleX,hm]
    exact (Complex.re_eq_add_conj _).symm
  have hy : hillHminusActionAngleY n q = ((hillHminusActionAngleFactorPlus n q).im:ℂ) := by
    rw [hillHminusActionAngleY,hm]
    exact (Complex.im_eq_sub_conj _).symm
  rw [hx,hy]
  exact ⟨Complex.ofReal_im _,Complex.ofReal_im _⟩

theorem hillHminusActionAngle_zero_of_real_closed_gap (n : ℕ+) (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (hg : hillHminusCanonicalGapSquare n q = 0) :
    hillHminusActionAngleX n q = 0 ∧ hillHminusActionAngleY n q = 0 := by
  have hz := hillHminusAbelianCartesian_zero_of_real_closed_gap n q hr hg
  simp only [hillHminusActionAngleX,hillHminusActionAngleY,hillHminusActionAngleFactorPlus,
    hillHminusActionAngleFactorMinus,hz.1,hz.2,mul_zero,add_zero,sub_zero,zero_div,and_self]

end NLS.KdV
