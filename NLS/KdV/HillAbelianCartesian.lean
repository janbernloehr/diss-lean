import NLS.KdV.HillCanonicalOffIndexAnalyticCorrection
import NLS.KdV.HillRealDiagonalCartesian

/-! Actual Abelian gap-times-phase factors INCLUDING the infinite
off-index correction. They are analytic through complex collapse and
retain the exact original gap-square product. The action-ratio amplitude
needed for full Birkhoff coordinates is not included here. -/
noncomputable section
open Set Complex
open scoped Classical
namespace NLS.KdV

def hillHminusAbelianCartesianPlus (n : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  hillHminusDiagonalCartesianPlus n q*Complex.exp (I*hillHminusOffIndexAbelianCorrection n q)

def hillHminusAbelianCartesianMinus (n : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  hillHminusDiagonalCartesianMinus n q*Complex.exp (-I*hillHminusOffIndexAbelianCorrection n q)

theorem analyticOnNhd_hillHminusAbelianCartesianPlus (n : ℕ+) :
    AnalyticOnNhd ℂ (hillHminusAbelianCartesianPlus n) hillHminusOffIndexAnalyticDomain := by
  intro q hq
  exact (analyticOnNhd_hillHminusDiagonalCartesianPlus n q (hillHminusOffIndexAnalyticDomain_subset_physical hq)).mul
    (analyticAt_const.mul (analyticOnNhd_hillHminusOffIndexAbelianCorrection n q hq)).cexp

theorem analyticOnNhd_hillHminusAbelianCartesianMinus (n : ℕ+) :
    AnalyticOnNhd ℂ (hillHminusAbelianCartesianMinus n) hillHminusOffIndexAnalyticDomain := by
  intro q hq
  exact (analyticOnNhd_hillHminusDiagonalCartesianMinus n q (hillHminusOffIndexAnalyticDomain_subset_physical hq)).mul
    (analyticAt_const.mul (analyticOnNhd_hillHminusOffIndexAbelianCorrection n q hq)).cexp

theorem hillHminusAbelianCartesian_product (n : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusOffIndexAnalyticDomain) :
    hillHminusAbelianCartesianPlus n q*hillHminusAbelianCartesianMinus n q = hillHminusCanonicalGapSquare n q := by
  unfold hillHminusAbelianCartesianPlus hillHminusAbelianCartesianMinus
  calc
    _ = (hillHminusDiagonalCartesianPlus n q*hillHminusDiagonalCartesianMinus n q)*
      (Complex.exp (I*hillHminusOffIndexAbelianCorrection n q)*Complex.exp (-I*hillHminusOffIndexAbelianCorrection n q)) := by ring
    _ = _ := by
      rw [← Complex.exp_add,show I*hillHminusOffIndexAbelianCorrection n q+-I*hillHminusOffIndexAbelianCorrection n q = 0 by ring,
        Complex.exp_zero,mul_one]
      exact hillHminusDiagonalCartesian_product n q (hillHminusOffIndexAnalyticDomain_subset_physical hq)

theorem hillHminusAbelianCartesian_conjugate_of_real (n : ℕ+) (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) :
    hillHminusAbelianCartesianMinus n q = star (hillHminusAbelianCartesianPlus n q) := by
  have hb := hillHminusOffIndexAbelianCorrection_im_eq_zero_of_real n q hr
  unfold hillHminusAbelianCartesianPlus hillHminusAbelianCartesianMinus
  rw [hillHminusDiagonalCartesian_conjugate_of_real n q hr]
  change _ = (starRingEnd ℂ) _
  rw [map_mul,← Complex.exp_conj]
  rw [map_mul,Complex.conj_I,Complex.conj_eq_iff_im.mpr hb]
  rfl

theorem norm_hillHminusAbelianCartesian_of_real (n : ℕ+) (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) :
    ‖hillHminusAbelianCartesianPlus n q‖ = hillHminusLabels q hr (2*(n:ℕ))-hillHminusLabels q hr (2*(n:ℕ)-1) ∧
    ‖hillHminusAbelianCartesianMinus n q‖ = hillHminusLabels q hr (2*(n:ℕ))-hillHminusLabels q hr (2*(n:ℕ)-1) := by
  have hb := hillHminusOffIndexAbelianCorrection_im_eq_zero_of_real n q hr
  have hp : ‖Complex.exp (I*hillHminusOffIndexAbelianCorrection n q)‖ = 1 := by simp [Complex.norm_exp,Complex.mul_re,hb]
  have hm : ‖Complex.exp (-I*hillHminusOffIndexAbelianCorrection n q)‖ = 1 := by simp [Complex.norm_exp,Complex.mul_re,hb]
  simpa only [hillHminusAbelianCartesianPlus,hillHminusAbelianCartesianMinus,norm_mul,hp,hm,mul_one] using
    norm_hillHminusDiagonalCartesian_of_real n q hr

theorem hillHminusAbelianCartesian_zero_of_real_closed_gap (n : ℕ+) (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (hg : hillHminusCanonicalGapSquare n q = 0) :
    hillHminusAbelianCartesianPlus n q = 0 ∧ hillHminusAbelianCartesianMinus n q = 0 := by
  have hz := hillHminusDiagonalCartesian_zero_of_real_closed_gap n q hr hg
  simp only [hillHminusAbelianCartesianPlus,hillHminusAbelianCartesianMinus,hz.1,hz.2,zero_mul,and_self]

end NLS.KdV
