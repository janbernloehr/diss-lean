import NLS.KdV.HillHminusOneRealGapSigns
import Mathlib.Analysis.SpecialFunctions.Arcosh

/-! # The intrinsic real H^-1 Hill gap profile -/

noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.KdV

def hillHminusRealGapProfile (q : PeriodOneHminusOne) (n : ℕ) (x : ℝ) : ℝ :=
  Real.arcosh (((-1 : ℝ)^n*(hillHminusDiscriminant q x).re)/2)

theorem hillHminusRealGapProfile_nonneg
    (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ) (hn : 1 ≤ n) (x : ℝ)
    (hx : x ∈ Icc (hillHminusRealLabels q hr (2*n-1)) (hillHminusRealLabels q hr (2*n))) :
    0 ≤ hillHminusRealGapProfile q n x := by
  apply Real.arcosh_nonneg
  have h := hillHminusDiscriminant_signed_gap_ge_two q hr n hn x hx
  linarith

theorem hillHminusRealGapProfile_pos
    (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ) (hn : 1 ≤ n) (x : ℝ)
    (hx : x ∈ Ioo (hillHminusRealLabels q hr (2*n-1)) (hillHminusRealLabels q hr (2*n))) :
    0 < hillHminusRealGapProfile q n x := by
  apply Real.arcosh_pos
  have h := hillHminusDiscriminant_signed_gap_gt_two q hr n hn x hx
  linarith

theorem hillHminusRealGapProfile_endpoints
    (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ) (hn : 1 ≤ n) :
    hillHminusRealGapProfile q n (hillHminusRealLabels q hr (2*n-1)) = 0 ∧
      hillHminusRealGapProfile q n (hillHminusRealLabels q hr (2*n)) = 0 := by
  dsimp only [hillHminusRealGapProfile]
  rw [(hillHminusRealLabels_signed_pair_trace q hr n hn).1,
    (hillHminusRealLabels_signed_pair_trace q hr n hn).2]
  norm_num

theorem continuousOn_hillHminusRealGapProfile
    (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ) (hn : 1 ≤ n) :
    ContinuousOn (hillHminusRealGapProfile q n)
      (Icc (hillHminusRealLabels q hr (2*n-1)) (hillHminusRealLabels q hr (2*n))) := by
  have hD : Continuous (fun x : ℝ => hillHminusDiscriminant q x) :=
    (analyticOnNhd_hillHminusDiscriminant _).continuous.comp Complex.continuous_ofReal
  have ha : Continuous (fun x : ℝ => ((-1 : ℝ)^n*
      (hillHminusDiscriminant q x).re)/2) :=
    ((Complex.continuous_re.comp hD).const_mul _).div_const _
  apply Real.continuousOn_arcosh.comp ha.continuousOn
  intro x hx
  have h := hillHminusDiscriminant_signed_gap_ge_two q hr n hn x hx
  change (1 : ℝ) ≤ ((-1 : ℝ)^n*(hillHminusDiscriminant q x).re)/2
  linarith


end NLS.KdV
