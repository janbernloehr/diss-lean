import NLS.KdV.HillHminusOneMiuraAllLabels
import NLS.ComplexAnalysis.EnergySqrtCoordinates
import NLS.RealAnalysis.QuadraticIntegralPullback

/-! Exact square-root coordinates on EVERY original real positive Hill
gap, for every valid real shifted Miura representation. Full original
endpoint labels, low indices and collapsed gaps are retained. -/
noncomputable section
open Set Complex NLS.ZakharovShabat NLS.ComplexAnalysis NLS.RealAnalysis
open scoped ENNReal
namespace NLS.KdV

theorem hillMiura_frequency_of_original_gap (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (u : PeriodOneRealL2) (c : ℝ)
    (hi : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c:ℂ)))
    (hc : -(c:ℂ) ∉ singularHillSpectrum (periodOneOriginal q)) (m : ℕ+) (E : ℝ)
    (hE : E ∈ Icc (hillHminusLabels q hq (2*(m:ℕ)-1)) (hillHminusLabels q hq (2*(m:ℕ)))) :
    (E:ℂ) ∈ energyFrequencyDomain (c:ℂ) ∧
      energyFrequency (c:ℂ) (E:ℂ) ∈ sourcePeriodicSegment (by norm_num) (by norm_num)
        (hillMiuraDiagonal u.val) ((m:ℕ):ℤ) ∧
      0 < (energyFrequency (c:ℂ) (E:ℂ)).re := by
  let a := (hillMiuraDiracLeft u.val ((m:ℕ):ℤ)).re
  let b := (hillMiuraDiracRight u.val ((m:ℕ):ℤ)).re
  have ha : 0 < a := hillMiura_positive_gap_left_pos u ((m:ℕ):ℤ) (by exact_mod_cast m.pos)
  have hab : a ≤ b := hillMiuraDiracPair_ordered u.val ((m:ℕ):ℤ)
  have he := hillHminusLabels_pair_eq_squared_miuraDirac q hq u c hi hc (m:ℕ) m.pos
  have hEI : E ∈ Icc (a^2-c) (b^2-c) := by rw [← he.1,← he.2]; exact hE
  obtain ⟨hx,hxE⟩ := sqrt_add_mem_of_mem_squared_interval a b c E ha.le hab hEI
  let x := Real.sqrt (E+c)
  have hxpos : 0 < x := ha.trans_le hx.1
  have hs : (x:ℂ)^2 = (E:ℂ)+(c:ℂ) := by
    have hh : x^2 = E+c := by linear_combination hxE
    exact_mod_cast hh
  have hsqrt : energyFrequency (c:ℂ) (E:ℂ) = (x:ℂ) :=
    (eq_principalSqrt_of_sq_of_re_pos (x:ℂ) ((E:ℂ)+(c:ℂ)) hs hxpos).symm
  refine ⟨?_,?_,?_⟩
  · change (E:ℂ)+(c:ℂ) ∈ slitPlane
    rw [← hs]
    exact sq_mem_slitPlane_of_re_pos (x:ℂ) hxpos
  · rw [hsqrt]
    exact sourcePeriodicSegment_mem_of_realIcc (by norm_num) (by norm_num) (hillMiuraDiagonal u.val)
      (hillMiuraRealSource u).property ((m:ℕ):ℤ) x hx
  · simpa only [hsqrt,Complex.ofReal_re] using hxpos

theorem hillMiura_gap_energy_mem_original (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (u : PeriodOneRealL2) (c : ℝ)
    (hi : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c:ℂ)))
    (hc : -(c:ℂ) ∉ singularHillSpectrum (periodOneOriginal q)) (m : ℕ+) (z : ℂ)
    (hz : z ∈ sourcePeriodicSegment (by norm_num) (by norm_num) (hillMiuraDiagonal u.val) ((m:ℕ):ℤ)) :
    ∃ E : ℝ, E ∈ Icc (hillHminusLabels q hq (2*(m:ℕ)-1)) (hillHminusLabels q hq (2*(m:ℕ))) ∧
      z^2-(c:ℂ) = (E:ℂ) := by
  have hx := sourcePeriodicSegment_re_mem_Icc (by norm_num) (by norm_num) (hillMiuraDiagonal u.val) ((m:ℕ):ℤ) z hz
  change z.re ∈ Icc (hillMiuraDiracLeft u.val ((m:ℕ):ℤ)).re (hillMiuraDiracRight u.val ((m:ℕ):ℤ)).re at hx
  have him := sourcePeriodicSegment_im_eq_zero_of_realType (by norm_num) (by norm_num)
    (hillMiuraDiagonal u.val) (hillMiuraRealSource u).property ((m:ℕ):ℤ) z hz
  have hzreal : (z.re:ℂ) = z := Complex.ext rfl him.symm
  have ha := hillMiura_positive_gap_left_pos u ((m:ℕ):ℤ) (by exact_mod_cast m.pos)
  change 0 < (hillMiuraDiracLeft u.val ((m:ℕ):ℤ)).re at ha
  have hl : (hillMiuraDiracLeft u.val ((m:ℕ):ℤ)).re^2 ≤ z.re^2 := by
    simpa only [pow_two] using mul_self_le_mul_self ha.le hx.1
  have hr : z.re^2 ≤ (hillMiuraDiracRight u.val ((m:ℕ):ℤ)).re^2 := by
    simpa only [pow_two] using mul_self_le_mul_self (ha.le.trans hx.1) hx.2
  have he := hillHminusLabels_pair_eq_squared_miuraDirac q hq u c hi hc (m:ℕ) m.pos
  refine ⟨z.re^2-c,?_,?_⟩
  · rw [he.1,he.2]
    exact ⟨sub_le_sub_right hl _,sub_le_sub_right hr _⟩
  · rw [Complex.ofReal_sub,Complex.ofReal_pow,hzreal]

end NLS.KdV
