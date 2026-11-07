import NLS.KdV.HillProductSelectedGapNonvanishing
import NLS.KdV.HillProductColumnMeanValue
import NLS.KdV.HillMiuraEnergyGapCoordinates

/-! Reality and nonvanishing on the full selected positive frequency
gap, and the resulting nonzero diagonal PERIOD column. Every original
positive index and every collapsed gap are retained. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

theorem hillProductColumnGapNumerator_actual_real (n m : ℕ+) (q : PeriodOneRealHminusOne)
    (u : PeriodOneRealL2) (c : ℝ)
    (hi : periodOneMiura u.val = q.val+periodOneL2Inclusion (lp.single 2 0 (c:ℂ)))
    (hc : -(c:ℂ) ∉ singularHillSpectrum (periodOneOriginal q.val))
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (hillMiuraDiagonal u.val) ((m:ℕ):ℤ))
    (z : ℂ) (hz : z ∈ sourcePeriodicSegment (by norm_num) (by norm_num)
      (hillMiuraDiagonal u.val) ((m:ℕ):ℤ)) :
    (hillProductColumnGapNumerator n m (c:ℂ) (hillMiuraDiagonal u.val) ((m:ℕ):ℤ)
      (hillHminusPsiZeroDisplacement n q) z).im = 0 := by
  obtain ⟨E,_,he⟩ := hillMiura_gap_energy_mem_original q.val q.property u c hi hc m z hz
  have him := sourcePeriodicSegment_im_eq_zero_of_realType (by norm_num) (by norm_num)
    (hillMiuraDiagonal u.val) (hillMiuraRealSource u).property ((m:ℕ):ℤ) z hz
  have hzr : (z.re:ℂ) = z := Complex.ext rfl him.symm
  have ho := sourceStandardRootOmittedProduct_im_eq_zero_on_real_domain (by norm_num) (by norm_num)
    (hillMiuraDiagonal u.val) (hillMiuraRealSource u).property ((m:ℕ):ℤ) z.re
    (by rw [hzr]; exact D.closedBall_subset_omittedDomain (ball_subset_closedBall (D.gap hz)))
  rw [hzr] at ho
  have hd := hillEnergyProductCoordinateDerivative_im_eq_zero n m (E:ℂ) (by simp)
    (hillHminusPsiZeroDisplacement n q) (fun k => hillHminusPsiZeroDisplacement_im_eq_zero n k q)
  unfold hillProductColumnGapNumerator
  rw [he]
  simp only [div_im,mul_im,him,hd,ho,mul_zero,zero_mul,add_zero,sub_zero,zero_div]

theorem hillProductColumnGapNumerator_actual_ne_zero (n m : ℕ+) (hmn : m ≠ n)
    (q : PeriodOneRealHminusOne) (u : PeriodOneRealL2) (c : ℝ)
    (hi : periodOneMiura u.val = q.val+periodOneL2Inclusion (lp.single 2 0 (c:ℂ)))
    (hc : -(c:ℂ) ∉ singularHillSpectrum (periodOneOriginal q.val))
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (hillMiuraDiagonal u.val) ((m:ℕ):ℤ))
    (z : ℂ) (hz : z ∈ sourcePeriodicSegment (by norm_num) (by norm_num)
      (hillMiuraDiagonal u.val) ((m:ℕ):ℤ)) :
    hillProductColumnGapNumerator n m (c:ℂ) (hillMiuraDiagonal u.val) ((m:ℕ):ℤ)
      (hillHminusPsiZeroDisplacement n q) z ≠ 0 := by
  obtain ⟨E,hE,he⟩ := hillMiura_gap_energy_mem_original q.val q.property u c hi hc m z hz
  have hx := sourcePeriodicSegment_re_mem_Icc (by norm_num) (by norm_num)
    (hillMiuraDiagonal u.val) ((m:ℕ):ℤ) z hz
  have ha := hillMiura_positive_gap_left_pos u ((m:ℕ):ℤ) (by exact_mod_cast m.pos)
  have hzpos : 0 < z.re := ha.trans_le hx.1
  have hzn : z ≠ 0 := fun h => (by simpa only [h,zero_re] using hzpos : (0:ℝ) < 0).false
  unfold hillProductColumnGapNumerator
  rw [he]
  exact div_ne_zero (mul_ne_zero hzn
    (hillEnergyProductCoordinateDerivative_ne_zero_on_real_gap n m hmn q E hE))
    (sourceStandardRootOmittedProduct_ne_zero (by norm_num) (by norm_num) (hillMiuraDiagonal u.val) z
      ((m:ℕ):ℤ) (D.closedBall_subset_omittedDomain (ball_subset_closedBall (D.gap hz))))

theorem hillEnergyProductPeriodColumn_actual_diagonal_ne_zero (n m : ℕ+) (hmn : m ≠ n)
    (q : PeriodOneRealHminusOne) (u : PeriodOneRealL2) (c : ℝ)
    (hi : periodOneMiura u.val = q.val+periodOneL2Inclusion (lp.single 2 0 (c:ℂ)))
    (hc : -(c:ℂ) ∉ singularHillSpectrum (periodOneOriginal q.val))
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (hillMiuraDiagonal u.val) ((m:ℕ):ℤ)) :
    hillEnergyProductPeriodColumn n m (c:ℂ) (hillMiuraDiagonal u.val) D
      (hillHminusPsiZeroDisplacement n q) ≠ 0 := by
  obtain ⟨μ,hμ,he⟩ := hillEnergyProductPeriodColumn_real_mean_value n m (c:ℂ)
    (hillMiuraDiagonal u.val) (hillMiuraRealSource u).property ((m:ℕ):ℤ)
    (hillHminusPsiZeroDisplacement n q) D
    (fun z hz => hillProductColumnGapNumerator_actual_real n m q u c hi hc D z hz)
  rw [he]
  exact neg_ne_zero.mpr (hillProductColumnGapNumerator_actual_ne_zero n m hmn q u c hi hc D μ hμ)

end NLS.KdV
