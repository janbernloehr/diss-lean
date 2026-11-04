import NLS.KdV.HillProductOffDiagonalNumerator
import NLS.KdV.HillRealGapWidthDisplacement
import NLS.KdV.HillProductRealGapColumns

/-! Actual off-diagonal Hill period columns have an l2 energy-width
row majorant times the quadratic interaction kernel, with all original
indices and the physical normalization retained. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

theorem hillProductColumnGapNumerator_actual_column_real (n r m : ℕ+) (q : PeriodOneRealHminusOne)
    (u : PeriodOneRealL2) (c : ℝ)
    (hi : periodOneMiura u.val = q.val+periodOneL2Inclusion (lp.single 2 0 (c:ℂ)))
    (hc : -(c:ℂ) ∉ singularHillSpectrum (periodOneOriginal q.val))
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (hillMiuraDiagonal u.val) ((m:ℕ):ℤ))
    (z : ℂ) (hz : z ∈ sourcePeriodicSegment (by norm_num) (by norm_num)
      (hillMiuraDiagonal u.val) ((m:ℕ):ℤ)) :
    (hillProductColumnGapNumerator n r (c:ℂ) (hillMiuraDiagonal u.val) ((m:ℕ):ℤ)
      (hillHminusPsiZeroDisplacement n q) z).im = 0 := by
  obtain ⟨E,_,he⟩ := hillMiura_gap_energy_mem_original q.val q.property u c hi hc m z hz
  have him := sourcePeriodicSegment_im_eq_zero_of_realType (by norm_num) (by norm_num)
    (hillMiuraDiagonal u.val) (hillMiuraRealSource u).property ((m:ℕ):ℤ) z hz
  have hzr : (z.re:ℂ) = z := Complex.ext rfl him.symm
  have ho := sourceStandardRootOmittedProduct_im_eq_zero_on_real_domain (by norm_num) (by norm_num)
    (hillMiuraDiagonal u.val) (hillMiuraRealSource u).property ((m:ℕ):ℤ) z.re
    (by rw [hzr]; exact D.closedBall_subset_omittedDomain (ball_subset_closedBall (D.gap hz)))
  rw [hzr] at ho
  have hd := hillEnergyProductCoordinateDerivative_im_eq_zero n r (E:ℂ) (by simp)
    (hillHminusPsiZeroDisplacement n q) (fun k => hillHminusPsiZeroDisplacement_im_eq_zero n k q)
  unfold hillProductColumnGapNumerator
  rw [he]
  simp only [div_im,mul_im,him,hd,ho,mul_zero,zero_mul,add_zero,sub_zero,zero_div]

theorem hillEnergyProductPeriodColumn_actual_im_eq_zero (n r m : ℕ+) (q : PeriodOneRealHminusOne)
    (u : PeriodOneRealL2) (c : ℝ)
    (hi : periodOneMiura u.val = q.val+periodOneL2Inclusion (lp.single 2 0 (c:ℂ)))
    (hc : -(c:ℂ) ∉ singularHillSpectrum (periodOneOriginal q.val))
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (hillMiuraDiagonal u.val) ((m:ℕ):ℤ)) :
    (hillEnergyProductPeriodColumn n r (c:ℂ) (hillMiuraDiagonal u.val) D
      (hillHminusPsiZeroDisplacement n q)).im = 0 := by
  obtain ⟨μ,hμ,he⟩ := hillEnergyProductPeriodColumn_real_mean_value n r (c:ℂ)
    (hillMiuraDiagonal u.val) (hillMiuraRealSource u).property ((m:ℕ):ℤ)
    (hillHminusPsiZeroDisplacement n q) D
    (fun z hz => hillProductColumnGapNumerator_actual_column_real n r m q u c hi hc D z hz)
  rw [he,neg_im,hillProductColumnGapNumerator_actual_column_real n r m q u c hi hc D μ hμ,neg_zero]

theorem hillWeightedProductPeriodColumn_actual_off_diagonal_bound
    {V : Set (CoeffPair 2)} {D : ℤ → Set ℂ} {C : ℝ}
    (hD : SourceIsolatingNeighborhoods (by norm_num) (by norm_num) V D C)
    (q : PeriodOneRealHminusOne) (u : PeriodOneRealL2) (c : ℝ)
    (hi : periodOneMiura u.val = q.val+periodOneL2Inclusion (lp.single 2 0 (c:ℂ)))
    (hc : -(c:ℂ) ∉ singularHillSpectrum (periodOneOriginal q.val))
    (hψ : hillMiuraDiagonal u.val ∈ V)
    (n m r : ℕ+) (hmn : m ≠ n) (hrn : r ≠ n) (hrm : r ≠ m)
    (hplace : ∀ k : ℤ, hillIndependentFrequency ((c:ℂ),hillHminusPsiZeroDisplacement n q) k ∈ D k)
    (a R : ℝ) (hR : 0 < R) (he : D ((m:ℕ):ℤ) = ball (a:ℂ) R)
    (Q : ℝ) (hq : ∀ z ∈ D ((m:ℕ):ℤ),
      ‖sourceSingleRootQuotientJointProduct (by norm_num) (by norm_num) ((m:ℕ):ℤ)
        (z,(hillIndependentFrequencyDisplacement ((c:ℂ),hillHminusPsiZeroDisplacement n q),hillMiuraDiagonal u.val))‖ ≤ Q) :
    ‖hillPeriodEquationWeight n m*hillEnergyProductPeriodColumn n r (c:ℂ) (hillMiuraDiagonal u.val)
      (hD.periodCircle (hillMiuraDiagonal u.val) hψ ((m:ℕ):ℤ) a R hR he) (hillHminusPsiZeroDisplacement n q)‖ ≤
      ‖hillHminusGapWidthDisplacement q m‖*(2*Real.pi^5*C^5*Q)*‖hillFreeInteractionKernel m ((r:ℕ):ℤ)‖ := by
  let P := hD.periodCircle (hillMiuraDiagonal u.val) hψ ((m:ℕ):ℤ) a R hR he
  obtain ⟨z,hz,hcol⟩ := hillEnergyProductPeriodColumn_real_mean_value n r (c:ℂ)
    (hillMiuraDiagonal u.val) (hillMiuraRealSource u).property ((m:ℕ):ℤ)
    (hillHminusPsiZeroDisplacement n q) P
    (fun z hz => hillProductColumnGapNumerator_actual_column_real n r m q u c hi hc P z hz)
  rw [hcol,mul_neg,norm_neg]
  have hzD : z ∈ D ((m:ℕ):ℤ) := hD.gap _ hψ _ hz
  have hgap : ‖(hillEnergySequenceZero m (hillHminusPsiZeroDisplacement n q)-(z^2-(c:ℂ)))/(m:ℕ)‖ ≤
      ‖hillHminusGapWidthDisplacement q m‖ := by
    obtain ⟨E,hE,hEeq⟩ := hillMiura_gap_energy_mem_original q.val q.property u c hi hc m z hz
    rw [hillEnergySequenceZero_real,hEeq]
    exact hillHminusGapWidthDisplacement_gap_difference_bound q m _ E
      (hillHminusCanonicalPsiRealZero_mem_gap n m q.val q.property) hE
  exact hillWeightedColumnGapNumerator_off_diagonal_bound hD _ (c:ℂ) _ hplace n m r hmn hrn hrm z
    (subset_closure hzD) (P.closedBall_subset_omittedDomain (ball_subset_closedBall (P.gap hz))) Q _
    (norm_nonneg _) (hq z hzD) hgap

end NLS.KdV
