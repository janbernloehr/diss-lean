import NLS.KdV.HminusOneDirichletBranches

/-! Actual scalar Dirichlet roots in the intrinsic original Hill high gaps.
The cutoff is chosen before the index; both endpoints retain the original
full H-minus-one labels, including collapsed periodic pairs. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
namespace NLS.KdV

/-- Every sufficiently high positive auxiliary coordinate gives a simple
scalar Dirichlet zero inside the SAME original Hill gap. Its midpoint
deviation is at most half the gap, with no regularity hypothesis beyond
the original real H-minus-one potential and a literal real Miura lift. -/
theorem exists_hillMiuraDirichletEnergy_in_high_gap
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (u : PeriodOneRealL2) (c : ℝ)
    (hi : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c:ℂ))) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      hillHminusDirichlet q (hillMiuraDirichletEnergy u.val c n) = 0 ∧
      analyticOrderNatAt (hillHminusDirichlet q) (hillMiuraDirichletEnergy u.val c n) = 1 ∧
      hillHminusLabels q hq (2*n-1) ≤ (hillMiuraDirichletEnergy u.val c n).re ∧
      (hillMiuraDirichletEnergy u.val c n).re ≤ hillHminusLabels q hq (2*n) ∧
      ‖(((hillHminusLabels q hq (2*n-1)+hillHminusLabels q hq (2*n))/2:ℝ):ℂ)-
          hillMiuraDirichletEnergy u.val c n‖ ≤
        ‖((hillHminusLabels q hq (2*n)-hillHminusLabels q hq (2*n-1):ℝ):ℂ)‖/2 := by
  obtain ⟨L,hL,hlabels⟩ := exists_hillHminusLabels_squared_miuraDirac q hq u c hi
  obtain ⟨K,hK,hpos⟩ := exists_miuraDirac_high_square_localization u c 1 (by norm_num)
  obtain ⟨M,hM,hsimple⟩ := exists_simple_hillMiuraDirichletEnergy_tail q u.val (c:ℂ) hi
  refine ⟨max L (max K M),hL.trans (le_max_left _ _),fun n hn => ?_⟩
  have hnL : L ≤ n := (le_max_left _ _).trans hn
  have hnK : K ≤ n := (le_max_left K M).trans ((le_max_right _ _).trans hn)
  have hnM : M ≤ n := (le_max_right K M).trans ((le_max_right _ _).trans hn)
  obtain ⟨hl,hr,_⟩ := hlabels n hnL
  have hpositive := (hpos n hnK).1
  obtain ⟨hleft,hright⟩ := hillMiuraDiracDirichlet_mem_gap u n
  obtain ⟨_,hz,horder⟩ := hsimple n (by simpa using hnM)
  have hreal := hillMiuraDiracDirichlet_im_eq_zero u n
  have he : hillMiuraDirichletEnergy u.val (c:ℂ) n =
      (((hillMiuraDiracDirichlet u.val n).re^2-c:ℝ):ℂ) := by
    apply Complex.ext <;>
      simp only [hillMiuraDirichletEnergy,pow_two,Complex.sub_re,Complex.sub_im,
        Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,hreal,
        mul_zero,zero_mul,sub_zero,add_zero]
  have hle : hillHminusLabels q hq (2*n-1) ≤ (hillMiuraDirichletEnergy u.val c n).re := by
    rw [hl,he,Complex.ofReal_re]
    nlinarith
  have hge : (hillMiuraDirichletEnergy u.val c n).re ≤ hillHminusLabels q hq (2*n) := by
    rw [hr,he,Complex.ofReal_re]
    nlinarith
  refine ⟨hz,horder,hle,hge,?_⟩
  have hgap : 0 ≤ hillHminusLabels q hq (2*n)-hillHminusLabels q hq (2*n-1) := by
    linarith
  rw [he,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg hgap]
  rw [he,Complex.ofReal_re] at hle hge
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end NLS.KdV
