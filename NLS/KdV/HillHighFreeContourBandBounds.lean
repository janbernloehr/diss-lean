import NLS.KdV.HillHighFreeContourGapContainment

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV

variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillHighFreeContour_physical_band_bounds_of_control (Ncut : ℕ) (hNcut : 1 ≤ Ncut) (B D : ℝ)
    (hc : HillComplexTailPeriodControl h0q h0r Ncut B D)
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (hp : ‖SpectralWeight.one.toCoeff q‖ ≤ B) (k : ℕ) (hk : Ncut ≤ k) :
    hillRealLabels q hq hr (2*k-2) < hillRealGapCenter 0 h0q h0r k-
      (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k) ∧
    hillRealGapCenter 0 h0q h0r k+
      (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k) <
      hillRealLabels q hq hr (2*k+1) := by
  have hk1 : 1 ≤ k := hNcut.trans hk
  let c := hillRealGapCenter 0 h0q h0r k
  let r := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
  have hrad : 0 < r := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk1).1
    (hillRealGapContour_geometry 0 h0q h0r k hk1).2.1
  have hsL : ((c-r:ℝ):ℂ) ∈ sphere (c:ℂ) r := by
    rw [mem_sphere,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs,
      show c-r-c = -r by ring,abs_neg,abs_of_pos hrad]
  have hsU : ((c+r:ℝ):ℂ) ∈ sphere (c:ℂ) r := by
    rw [mem_sphere,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs,
      add_sub_cancel_left,abs_of_pos hrad]
  have hb := hillRealGapContour_band_bounds 0 h0q h0r k hk1
  have hcL : hillRealLabels 0 h0q h0r (2*k-1) = c :=
    (hillFreeGapEndpoints h0q h0r k hk1).1.trans (hillFreeGapCenter h0q h0r k hk1).symm
  have hcU : hillRealLabels 0 h0q h0r (2*k) = c :=
    (hillFreeGapEndpoints h0q h0r k hk1).2.trans (hillFreeGapCenter h0q h0r k hk1).symm
  have hiL : 2*(k-1) = 2*k-2 := by omega
  have hiU : 2*(k-1)+1 = 2*k-1 := by omega
  have hbandL : c-r ∈ Ioo (hillRealLabels 0 h0q h0r (2*(k-1)))
      (hillRealLabels 0 h0q h0r (2*(k-1)+1)) := by
    rw [hiU,hiL,hcL]
    exact ⟨hb.1,by linarith⟩
  have hbandU : c+r ∈ Ioo (hillRealLabels 0 h0q h0r (2*k))
      (hillRealLabels 0 h0q h0r (2*k+1)) := by
    rw [hcU]
    exact ⟨by linarith,hb.2⟩
  have hL := mem_same_hillRealBand_of_free_and_source h0q h0r q hq hr (k-1) (c-r) hbandL
    (hillHighFreeGapContour_source_compatibility h0q h0r Ncut hNcut B D hc _ hp k hk _ hsL).1
  have hU := mem_same_hillRealBand_of_free_and_source h0q h0r q hq hr k (c+r) hbandU
    (hillHighFreeGapContour_source_compatibility h0q h0r Ncut hNcut B D hc _ hp k hk _ hsU).1
  rw [hiL] at hL
  exact ⟨hL.1,hU.2⟩

end NLS.KdV
