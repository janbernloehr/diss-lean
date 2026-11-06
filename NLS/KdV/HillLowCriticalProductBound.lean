import NLS.KdV.HillHighCriticalFactorBounds
import NLS.KdV.HillOmittedEnergyCriticalProduct
import NLS.ComplexAnalysis.RealCriticalProducts
import NLS.SequenceSpaces.PositiveQuotientProducts

/-! # The finite low Hill critical-root product has a telescoping endpoint bound. -/

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
open NLS.ZakharovShabat NLS.ComplexAnalysis
open NLS.SequenceSpaces
namespace NLS.KdV

theorem hillLowCriticalRootProduct_bound
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n K : ℕ) (hK : 1 ≤ K) (hKn : K < n)
    (x : ℝ) (hx : x ∈ Icc (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n))) :
    ‖∏ k ∈ Finset.range K, hillEnergyCriticalRootRatio q hq hr (k+1) x‖ ≤
      ‖(hillGapCriticalPoint q hq hr 1 : ℂ)-(x : ℂ)‖ /
        ‖endpointRoot (hillRealLabels q hq hr (2*K-1)) (hillRealLabels q hq hr (2*K)) x‖ := by
  have hfar (m : ℕ) (hmn : m < n) : hillRealLabels q hq hr (2*m) < x :=
    (hillRealLabels_band_strict q hq hr m).trans_le
      ((monotone_hillRealLabels q hq hr (by omega)).trans hx.1)
  let a : ℕ → ℝ := fun k => ‖(hillGapCriticalPoint q hq hr (k+1) : ℂ)-(x : ℂ)‖
  let b : ℕ → ℝ := fun k => ‖endpointRoot (hillRealLabels q hq hr (2*(k+1)-1)) (hillRealLabels q hq hr (2*(k+1))) x‖
  have hb (k : ℕ) (hk : k < K) : 0 < b k := by
    have hpos := sub_pos.mpr (hfar (k+1) (by omega))
    exact hpos.trans_le (norm_endpointRoot_ge_right_distance _ _ x
      (monotone_hillRealLabels q hq hr (by omega : 2*(k+1)-1 ≤ 2*(k+1))) (hfar (k+1) (by omega)))
  have hstep (k : ℕ) (hk : k+1 < K) : a (k+1) ≤ b k := by
    have hc := (hillGapCriticalPoint_spec q hq hr (k+2) (by omega)).1
    have hcx : hillGapCriticalPoint q hq hr (k+2) < x := hc.2.trans_lt (hfar (k+2) (by omega))
    have horder : hillRealLabels q hq hr (2*(k+1)) ≤ hillGapCriticalPoint q hq hr (k+2) := by
      have hband := hillRealLabels_band_strict q hq hr (k+1)
      have hidx : 2*(k+1)+1 = 2*(k+2)-1 := by omega
      rw [hidx] at hband
      exact hband.le.trans hc.1
    have hroot := norm_endpointRoot_ge_right_distance _ _ x
      (monotone_hillRealLabels q hq hr (by omega : 2*(k+1)-1 ≤ 2*(k+1))) (hfar (k+1) (by omega))
    change ‖(hillGapCriticalPoint q hq hr (k+1+1) : ℂ)-(x : ℂ)‖ ≤ _
    rw [show k+1+1 = k+2 by omega,← ofReal_sub,norm_real,Real.norm_eq_abs,
      abs_of_neg (sub_neg.mpr hcx)]
    exact (by linarith : -(hillGapCriticalPoint q hq hr (k+2)-x) ≤ x-hillRealLabels q hq hr (2*(k+1))).trans hroot
  have h := prod_range_div_telescope_le a b K hK (fun k _ => norm_nonneg _) hb hstep
  rw [norm_prod]
  simp only [hillEnergyCriticalRootRatio,norm_div]
  convert! h using 1
  dsimp only [a,b]
  have hidx : K-1+1 = K := by omega
  rw [hidx]

end NLS.KdV
