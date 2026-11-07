import NLS.KdV.HillMiuraPositiveGaps
import NLS.KdV.HillHminusOneMiuraPositiveActions

/-! # Positive-index Miura action and contour theorems without a cutoff

Every positive integer Dirac index of every real L2 scalar Miura source
has a positive isolating circle, a real nonnegative transferred Hill
action, and exact zero-gap detection. Full Abelian charts and mapped
winding-one contours are constructed from verified source results.
The assignment of original low Hill slots and Miura-chart independence
are not inferred from these Dirac-indexed statements.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

theorem hillHminusMiuraIndexedAction_positive_index_spec
    (u : PeriodOneRealL2) (n : ℤ) (hn : 0 < n) :
    0 ≤ (hillHminusMiuraIndexedAction u.val n).re ∧
      (hillHminusMiuraIndexedAction u.val n).im = 0 ∧
      (hillHminusMiuraIndexedAction u.val n = 0 ↔
        canonicalPeriodicGap (by simp) (by norm_num)
          (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _) n = 0) := by
  have hpos := hillMiura_positive_gap_left_pos u n hn
  have hz := hillHminusMiuraIndexedAction_eq_zero_iff_of_positive_left u n hpos
  refine ⟨?_,hillHminusMiuraIndexedAction_real u n,hz⟩
  by_cases hgap : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _) n = 0
  · rw [hz.mpr hgap,zero_re]
  · exact (hillHminusMiuraIndexedAction_pos_of_positive_left u n hpos hgap).le

theorem hillHminusMiuraIndexedAction_positive_index_pos_iff
    (u : PeriodOneRealL2) (n : ℤ) (hn : 0 < n) :
    0 < (hillHminusMiuraIndexedAction u.val n).re ↔
      canonicalPeriodicGap (by simp) (by norm_num)
        (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _) n ≠ 0 := by
  constructor
  · intro h hgap
    have hz := (hillHminusMiuraIndexedAction_positive_index_spec u n hn).2.2.mpr hgap
    rw [hz,zero_re] at h
    exact lt_irrefl 0 h
  · intro hgap
    exact hillHminusMiuraIndexedAction_pos_of_positive_left u n
      (hillMiura_positive_gap_left_pos u n hn) hgap

theorem exists_miura_action_contour_positive_index
    (q : PeriodOneHminusOne) (u : PeriodOneRealL2) (c : ℝ)
    (himage : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c : ℂ)))
    (n : ℤ) (hn : 0 < n) :
    ∃ C : SourceCriticalRootPeriodCircle (by simp) (by norm_num) (hillMiuraDiagonal u.val) n,
      0 < C.center-C.radius ∧
      hillHminusMiuraContourAction q u.val (c : ℂ)
        (quadraticEnergyLoop (PiecewiseC1Loop.circle (C.center : ℂ) C.radius) (c : ℂ)) =
        hillHminusMiuraIndexedAction u.val n ∧
      (quadraticEnergyLoop (PiecewiseC1Loop.circle (C.center : ℂ) C.radius) (c : ℂ)).windingIntegral
        ((sourceStandardRootMidpoint (by simp) (by norm_num) (hillMiuraDiagonal u.val) n)^2-(c : ℂ)) = 1 := by
  obtain ⟨W,V,_,_,_,hreal,_,_,_,hcharts⟩ :=
    exists_sourceAbelian_almostReal_spectral_charts (p := 2) (by simp) (by norm_num)
  obtain ⟨D,hψ,hE⟩ := hcharts (hillMiuraDiagonal u.val) (hreal (hillMiuraRealSource u).property)
  obtain ⟨E,_⟩ := hE (hillMiuraDiagonal u.val) hψ
  exact exists_positive_miura_action_contour q u c himage W E n
    (hillMiura_positive_gap_left_pos u n hn)

end NLS.KdV
