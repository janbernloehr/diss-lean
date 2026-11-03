import NLS.KdV.HillRootPeriodContinuity

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

def hillAbelianGapRootMap (n : ℕ) (hn : 1 ≤ n) (roots : hillGapRootBox q hq hr) :
    hillGapRootBox q hq hr :=
  ⟨fun j => if j+1 = n then roots.val j else
      (hillAbelianPeriodRoot q hq hr roots.val roots.property n (j+1)).re,by
    intro j
    dsimp only []
    split_ifs with hj
    · exact roots.property j
    · exact hillAbelianPeriodRoot_re_mem_gap q hq hr roots.val roots.property n (j+1) hn (by omega) hj⟩

theorem continuous_hillAbelianGapRootMap (n : ℕ) (hn : 1 ≤ n) :
    Continuous (hillAbelianGapRootMap q hq hr n hn) := by
  have hc : Continuous (fun roots : hillGapRootBox q hq hr => fun j : ℕ =>
      if j+1 = n then roots.val j else
        (hillAbelianPeriodRoot q hq hr roots.val roots.property n (j+1)).re) := by
    apply continuous_pi
    intro j
    by_cases hj : j+1 = n
    · simpa only [if_pos hj,Function.comp_def] using (continuous_apply j).comp continuous_subtype_val
    · simpa only [if_neg hj] using continuous_hillAbelianPeriodRoot_re q hq hr n (j+1) hn (by omega) hj
  exact hc.subtype_mk (fun roots => (hillAbelianGapRootMap q hq hr n hn roots).property)

theorem hillAbelianGapRootMap_fixed_point_periods
    (n : ℕ) (hn : 1 ≤ n) (roots : hillGapRootBox q hq hr)
    (hfix : hillAbelianGapRootMap q hq hr n hn roots = roots) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≠ n) :
    hillAbelianCandidatePeriod q hq hr roots.val n m = 0 := by
  have he := congrArg (fun r : hillGapRootBox q hq hr => r.val (m-1)) hfix
  change (if m-1+1 = n then roots.val (m-1) else
    (hillAbelianPeriodRoot q hq hr roots.val roots.property n (m-1+1)).re) = roots.val (m-1) at he
  rw [Nat.sub_add_cancel hm,if_neg hmn] at he
  have hs : hillAbelianPeriodRoot q hq hr roots.val roots.property n m = (roots.val (m-1):ℂ) := by
    apply Complex.ext
    · simpa only [ofReal_re] using he
    · simpa only [ofReal_im] using hillAbelianPeriodRoot_im_eq_zero q hq hr roots.val roots.property n m hm
  have hp := hillAbelianPeriodRoot_period_eq_zero q hq hr roots.val roots.property n m hn hm hmn
  rw [hs,hillIntrinsicGapPeriod_rootUpdate_eq_candidate_update q hq hr roots.val roots.property n m m hm hm,
    Function.update_eq_self] at hp
  exact hp

end NLS.KdV
