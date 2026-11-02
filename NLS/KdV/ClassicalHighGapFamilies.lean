import NLS.KdV.ClassicalHighGapPairs
import NLS.KdV.ClassicalHighContourMoments
import NLS.KdV.ClassicalHillReality

/-! # A common complex neighborhood for actual high Hill gap data

At every continuous complex potential, one cutoff and one open
neighborhood support the entire tail of actual two-root energy pairs,
their exact multiplicities and parity trace levels, analytic midpoints,
analytic squared gaps and the constructed cubic contour moments.

This does not yet assign the central labels or identify these unordered
high pairs with a complete globally ordered rough Hill spectrum.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat
namespace NLS.KdV

/-- The cutoff and open potential neighborhood precede every tail index
and every potential in the neighborhood, including collapsed pairs. -/
theorem exists_analytic_classicalHillHighGapFamilies (q : NLS.LinearVolterra.Curve ℂ) :
    ∃ N : ℕ, ∃ V : Set (NLS.LinearVolterra.Curve ℂ), 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N < (n : ℕ) →
        AnalyticOnNhd ℂ (fun a => classicalHillHighMidpoint a n) V ∧
        AnalyticOnNhd ℂ (fun a => classicalHillHighSquaredGap a n) V ∧
        AnalyticOnNhd ℂ (classicalHillHighContourMoment n) V ∧
        ∀ a ∈ V, ∃ l r : ℂ, ClassicalHillHighGapPair a n l r := by
  obtain ⟨Nc,Uc,hNc,hUc,hqc,hdata⟩ :=
    exists_classicalHillCounting_near_compact {q} isCompact_singleton
  obtain ⟨Nr,Ur,hNr,hUr,hqr,hR⟩ := exists_analytic_classicalHillHighContourMoments q
  refine ⟨max Nc Nr,Uc ∩ Ur,hNc.trans_le (le_max_left _ _),hUc.inter hUr,
    ⟨hqc (mem_singleton q),hqr⟩,?_⟩
  intro n hn
  have hnc : Nc < (n : ℕ) := (le_max_left Nc Nr).trans_lt hn
  have hnr : Nr < (n : ℕ) := (le_max_right Nc Nr).trans_lt hn
  refine ⟨?_,?_,(hR n hnr).mono inter_subset_right,?_⟩
  · intro a ha
    exact (analyticAt_classicalHillHigh_symmetric a Nc (hdata a ha.1 Nc le_rfl) n hnc).1
  · intro a ha
    exact (analyticAt_classicalHillHigh_symmetric a Nc (hdata a ha.1 Nc le_rfl) n hnc).2
  · intro a ha
    exact exists_classicalHillHighGapPair_of_counting a Nc (hdata a ha.1 Nc le_rfl) n hnc

/-- One complex neighborhood supports the analytic high families and
real ordered pairs at every real potential in that neighborhood. The
ordering assertion includes double endpoints and uses the actual flow. -/
theorem exists_analytic_ordered_classicalHillHighGapFamilies
    (q : NLS.LinearVolterra.Curve ℂ) :
    ∃ N : ℕ, ∃ V : Set (NLS.LinearVolterra.Curve ℂ), 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N < (n : ℕ) →
        AnalyticOnNhd ℂ (fun a => classicalHillHighMidpoint a n) V ∧
        AnalyticOnNhd ℂ (fun a => classicalHillHighSquaredGap a n) V ∧
        AnalyticOnNhd ℂ (classicalHillHighContourMoment n) V ∧
        ∀ a ∈ V, (∀ t, (a t).im = 0) → ∃ l r : ℂ,
          ClassicalHillHighGapPair a n l r ∧ l.im = 0 ∧ r.im = 0 ∧ l.re ≤ r.re := by
  obtain ⟨N,V,hN,hV,hq,hfamily⟩ := exists_analytic_classicalHillHighGapFamilies q
  refine ⟨N,V,hN,hV,hq,?_⟩
  intro n hn
  obtain ⟨hm,hg,hR,hpairs⟩ := hfamily n hn
  refine ⟨hm,hg,hR,?_⟩
  intro a ha hreal
  obtain ⟨l,r,hpair⟩ := hpairs a ha
  obtain ⟨hl,hr⟩ := hpair.im_eq_zero hreal
  by_cases he : l.re ≤ r.re
  · exact ⟨l,r,hpair,hl,hr,he⟩
  · exact ⟨r,l,hpair.swap,hr,hl,le_of_lt (lt_of_not_ge he)⟩

end NLS.KdV
