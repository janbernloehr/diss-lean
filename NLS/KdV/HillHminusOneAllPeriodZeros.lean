import NLS.KdV.HillHminusOneRealPeriodFormulas
import NLS.KdV.HillHminusOneAllCubicSigns
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Positivity and exact zero-gap criteria for all actual H^-1 periods

Every Arnold action is nonnegative and is positive exactly on an open gap.
Every cubic period is strictly negative there. Both vanish on closed gaps,
so their zero sets agree, at all positive indices and through collisions.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex MeasureTheory
namespace NLS.KdV

theorem hillHminusRealGapContourMoment_eq_zero_of_closed
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) (m : ℕ)
    (hc : hillHminusRealLabels q hr (2*(n : ℕ)-1) = hillHminusRealLabels q hr (2*(n : ℕ))) :
    hillHminusRealGapContourMoment q hr n m = 0 := by
  rw [hillHminusRealGapContourMoment_eq_profile_integral,hc,intervalIntegral.integral_same,mul_zero,ofReal_zero]

theorem hillHminusRealGapCubicContourMoment_eq_zero_of_closed
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+)
    (hc : hillHminusRealLabels q hr (2*(n : ℕ)-1) = hillHminusRealLabels q hr (2*(n : ℕ))) :
    hillHminusRealGapCubicContourMoment q hr n = 0 := by
  rw [hillHminusRealGapCubicContourMoment_eq_profile_integral,hc,intervalIntegral.integral_same,mul_zero,ofReal_zero]

theorem hillHminusRealGapContourMoment_even_nonneg
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) (m : ℕ) :
    0 ≤ (hillHminusRealGapContourMoment q hr n (2*m)).re := by
  rw [hillHminusRealGapContourMoment_eq_profile_integral,ofReal_re]
  apply mul_nonneg (by positivity)
  apply intervalIntegral.integral_nonneg
    (monotone_hillHminusRealLabels q hr (show 2*(n : ℕ)-1 ≤ 2*(n : ℕ) by omega))
  intro x hx
  exact mul_nonneg (by rw [pow_mul]; exact pow_nonneg (sq_nonneg x) m)
    (hillHminusRealGapProfile_nonneg q hr (n : ℕ) n.property x hx)

theorem hillHminusRealGapProfile_odd_integral_pos
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) (k : ℕ)
    (ho : hillHminusRealLabels q hr (2*(n : ℕ)-1) < hillHminusRealLabels q hr (2*(n : ℕ))) :
    0 < ∫ x in (hillHminusRealLabels q hr (2*(n : ℕ)-1))..(hillHminusRealLabels q hr (2*(n : ℕ))),
      hillHminusRealGapProfile q (n : ℕ) x^(2*k+1) := by
  apply intervalIntegral.integral_pos ho
    ((continuousOn_hillHminusRealGapProfile q hr (n : ℕ) n.property).pow (2*k+1))
  · intro x hx
    exact pow_nonneg (hillHminusRealGapProfile_nonneg q hr (n : ℕ) n.property x ⟨hx.1.le,hx.2⟩) _
  · let c := (hillHminusRealLabels q hr (2*(n : ℕ)-1)+hillHminusRealLabels q hr (2*(n : ℕ)))/2
    have hc : c ∈ Ioo (hillHminusRealLabels q hr (2*(n : ℕ)-1)) (hillHminusRealLabels q hr (2*(n : ℕ))) :=
      ⟨by dsimp only [c]; linarith,by dsimp only [c]; linarith⟩
    exact ⟨c,⟨hc.1.le,hc.2.le⟩,pow_pos (hillHminusRealGapProfile_pos q hr (n : ℕ) n.property c hc) _⟩

theorem hillHminusRealGapContourMoment_zero_pos_iff_open
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    0 < (hillHminusRealGapContourMoment q hr n 0).re ↔
      hillHminusRealLabels q hr (2*(n : ℕ)-1) < hillHminusRealLabels q hr (2*(n : ℕ)) := by
  constructor
  · intro hp
    apply lt_of_le_of_ne (monotone_hillHminusRealLabels q hr (show 2*(n : ℕ)-1 ≤ 2*(n : ℕ) by omega))
    intro hc
    rw [hillHminusRealGapContourMoment_eq_zero_of_closed q hr n 0 hc,zero_re] at hp
    exact lt_irrefl _ hp
  · intro ho
    rw [hillHminusRealGapContourMoment_eq_profile_integral,ofReal_re]
    simp only [pow_zero,one_mul]
    apply mul_pos (by positivity)
    simpa only [Nat.mul_zero,zero_add,pow_one] using hillHminusRealGapProfile_odd_integral_pos q hr n 0 ho

theorem hillHminusRealGapContourMoment_zero_eq_zero_iff_closed
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    hillHminusRealGapContourMoment q hr n 0 = 0 ↔
      hillHminusRealLabels q hr (2*(n : ℕ)-1) = hillHminusRealLabels q hr (2*(n : ℕ)) := by
  constructor
  · intro hz
    by_contra hc
    have ho := lt_of_le_of_ne
      (monotone_hillHminusRealLabels q hr (show 2*(n : ℕ)-1 ≤ 2*(n : ℕ) by omega)) hc
    have hp := (hillHminusRealGapContourMoment_zero_pos_iff_open q hr n).mpr ho
    rw [hz,zero_re] at hp
    exact lt_irrefl _ hp
  · exact hillHminusRealGapContourMoment_eq_zero_of_closed q hr n 0

theorem hillHminusRealGapCubicContourMoment_neg_iff_open
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    (hillHminusRealGapCubicContourMoment q hr n).re < 0 ↔
      hillHminusRealLabels q hr (2*(n : ℕ)-1) < hillHminusRealLabels q hr (2*(n : ℕ)) := by
  constructor
  · intro hp
    apply lt_of_le_of_ne (monotone_hillHminusRealLabels q hr (show 2*(n : ℕ)-1 ≤ 2*(n : ℕ) by omega))
    intro hc
    rw [hillHminusRealGapCubicContourMoment_eq_zero_of_closed q hr n hc,zero_re] at hp
    exact lt_irrefl _ hp
  · intro ho
    rw [hillHminusRealGapCubicContourMoment_eq_profile_integral,ofReal_re]
    apply mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos (by norm_num) Real.pi_pos)
    simpa only [show 2*1+1=3 by norm_num] using hillHminusRealGapProfile_odd_integral_pos q hr n 1 ho

theorem hillHminusRealGapCubicContourMoment_eq_zero_iff_closed
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    hillHminusRealGapCubicContourMoment q hr n = 0 ↔
      hillHminusRealLabels q hr (2*(n : ℕ)-1) = hillHminusRealLabels q hr (2*(n : ℕ)) := by
  constructor
  · intro hz
    by_contra hc
    have ho := lt_of_le_of_ne
      (monotone_hillHminusRealLabels q hr (show 2*(n : ℕ)-1 ≤ 2*(n : ℕ) by omega)) hc
    have hp := (hillHminusRealGapCubicContourMoment_neg_iff_open q hr n).mpr ho
    rw [hz,zero_re] at hp
    exact lt_irrefl _ hp
  · exact hillHminusRealGapCubicContourMoment_eq_zero_of_closed q hr n

theorem hillHminusRealGapCubicContourMoment_eq_zero_iff_Arnold_zero
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    hillHminusRealGapCubicContourMoment q hr n = 0 ↔ hillHminusRealGapContourMoment q hr n 0 = 0 :=
  (hillHminusRealGapCubicContourMoment_eq_zero_iff_closed q hr n).trans
    (hillHminusRealGapContourMoment_zero_eq_zero_iff_closed q hr n).symm

end NLS.KdV
