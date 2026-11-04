import NLS.KdV.HillFilledFreeGapAnalytic
import NLS.KdV.HillFilledFreeGapBase
import NLS.KdV.HillUniformComplexUnitRatio

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillFilledFreeGapUnit_bounded_complex_closed_ratio_bound (B : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ p : Coeff 2, ‖p‖ ≤ B → ∀ k : ℕ, N ≤ k →
      ∀ E ∈ closedBall (hillRealGapCenter 0 h0q h0r k : ℂ)
        (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
        ‖hillFilledFreeGapUnit h0q h0r k (E,p)/hillFilledFreeGapUnit h0q h0r k (E,0)-1‖ ≤ 1/4 ∧
          hillFilledFreeGapUnit h0q h0r k (E,p)≠0 := by
  obtain ⟨Nr,hNr,hratio⟩ := exists_hillFreeGap_bounded_complex_unit_ratio_bound h0q h0r B
  obtain ⟨Na,hNa,han⟩ := exists_hillFilledFreeGapUnit_bounded_complex_analytic h0q h0r (B+1)
  refine ⟨max Nr Na,hNr.trans (le_max_left _ _),?_⟩
  intro p hp k hk
  have hkr : Nr ≤ k := (le_max_left _ _).trans hk
  have hka : Na ≤ k := (le_max_right _ _).trans hk
  have hk1 : 1 ≤ k := hNr.trans hkr
  let c : ℂ := hillRealGapCenter 0 h0q h0r k
  let R := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
  have hR : 0 < R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk1).1
    (hillRealGapContour_geometry 0 h0q h0r k hk1).2.1
  have hpB : p ∈ ball (0 : Coeff 2) (B+1) := by rw [mem_ball,dist_zero_right];linarith
  have h0B : (0 : Coeff 2) ∈ ball 0 (B+1) := by
    rw [mem_ball,dist_self]
    linarith [norm_nonneg p]
  have hslice (a : Coeff 2) (ha : a ∈ ball (0 : Coeff 2) (B+1)) :
      AnalyticOnNhd ℂ (fun E => hillFilledFreeGapUnit h0q h0r k (E,a)) univ := by
    intro E _
    exact (han k hka (E,a) ⟨mem_univ _,ha⟩).comp (f := fun z : ℂ => (z,a)) (analyticAt_id.prod analyticAt_const)
  have hc : ContinuousOn (fun E => ‖hillFilledFreeGapUnit h0q h0r k (E,p)/hillFilledFreeGapUnit h0q h0r k (E,0)-1‖) (closedBall c R) :=
    ((((hslice p hpB).continuousOn.mono (subset_univ _)).div
      ((hslice 0 h0B).continuousOn.mono (subset_univ _))
      (fun E hE => hillFilledFreeGapUnit_zero_ne_zero h0q h0r k hk1 E hE)).sub continuousOn_const).norm
  have hb (E : ℂ) (hE : E ∈ ball c R) :
      ‖hillFilledFreeGapUnit h0q h0r k (E,p)/hillFilledFreeGapUnit h0q h0r k (E,0)-1‖ ≤ 1/4 := by
    rw [hillFilledFreeGapUnit_eq_local h0q h0r k p E hE,hillFilledFreeGapUnit_eq_local h0q h0r k 0 E hE]
    exact hratio p hp k hkr E hE
  intro E hE
  have hle := le_on_closure hb (by rw [closure_ball c hR.ne'];exact hc) continuousOn_const
    (show E ∈ closure (ball c R) by rw [closure_ball c hR.ne'];exact hE)
  refine ⟨hle,?_⟩
  intro hz
  rw [hz,zero_div,zero_sub,norm_neg,norm_one] at hle
  norm_num at hle

end NLS.KdV
