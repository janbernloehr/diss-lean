import NLS.KdV.HillAbelianCartesian

/-! The complete Abelian phase modulo pi, including its infinite
correction, on the common open complex original-gap domain. -/
noncomputable section
open Set Complex
open scoped Classical
namespace NLS.KdV

def hillHminusAbelianPhaseSquare (n : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  hillHminusAbelianCartesianPlus n q/hillHminusAbelianCartesianMinus n q

theorem hillHminusAbelianCartesian_ne_zero_of_gap (n : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusOffIndexAnalyticDomain) (hg : hillHminusCanonicalGapSquare n q ≠ 0) :
    hillHminusAbelianCartesianPlus n q ≠ 0 ∧ hillHminusAbelianCartesianMinus n q ≠ 0 :=
  mul_ne_zero_iff.mp ((hillHminusAbelianCartesian_product n q hq).symm ▸ hg)

theorem isOpen_hillHminusAbelianPhaseDomain (n : ℕ+) :
    IsOpen {q | q ∈ hillHminusOffIndexAnalyticDomain ∧ hillHminusCanonicalGapSquare n q ≠ 0} :=
  ((analyticOnNhd_hillHminusCanonicalGapSquare n).mono
    (hillHminusOffIndexAnalyticDomain_subset_physical.trans hillHminusPhysicalAbelianDomain_subset_gapDomain)).continuousOn.isOpen_inter_preimage
      isOpen_hillHminusOffIndexAnalyticDomain (isOpen_ne (x := (0:ℂ)))

theorem analyticOnNhd_hillHminusAbelianPhaseSquare (n : ℕ+) :
    AnalyticOnNhd ℂ (hillHminusAbelianPhaseSquare n)
      {q | q ∈ hillHminusOffIndexAnalyticDomain ∧ hillHminusCanonicalGapSquare n q ≠ 0} := by
  intro q hq
  exact (analyticOnNhd_hillHminusAbelianCartesianPlus n q hq.1).div
    (analyticOnNhd_hillHminusAbelianCartesianMinus n q hq.1) (hillHminusAbelianCartesian_ne_zero_of_gap n q hq.1 hq.2).2

theorem hillHminusAbelianPhaseSquare_ne_zero (n : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusOffIndexAnalyticDomain) (hg : hillHminusCanonicalGapSquare n q ≠ 0) :
    hillHminusAbelianPhaseSquare n q ≠ 0 := by
  have h := hillHminusAbelianCartesian_ne_zero_of_gap n q hq hg
  exact div_ne_zero h.1 h.2

theorem hillHminusAbelianPhaseSquare_eq_diagonal_mul_correction (n : ℕ+) (q : PeriodOneHminusOne) :
    hillHminusAbelianPhaseSquare n q = hillHminusDiagonalPhaseSquare n q*
      Complex.exp (2*I*hillHminusOffIndexAbelianCorrection n q) := by
  unfold hillHminusAbelianPhaseSquare hillHminusAbelianCartesianPlus hillHminusAbelianCartesianMinus hillHminusDiagonalPhaseSquare
  rw [mul_div_mul_comm,← Complex.exp_sub]
  congr 2
  ring

theorem norm_hillHminusAbelianPhaseSquare_of_real (n : ℕ+) (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (hg : hillHminusCanonicalGapSquare n q ≠ 0) :
    ‖hillHminusAbelianPhaseSquare n q‖ = 1 := by
  rw [hillHminusAbelianPhaseSquare_eq_diagonal_mul_correction,norm_mul,
    norm_hillHminusDiagonalPhaseSquare_of_real n q hr hg]
  have hb := hillHminusOffIndexAbelianCorrection_im_eq_zero_of_real n q hr
  simp [Complex.norm_exp,Complex.mul_re,hb]

end NLS.KdV
