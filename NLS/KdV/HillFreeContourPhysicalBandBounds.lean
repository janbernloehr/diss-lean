import NLS.KdV.HillSourceBandLabelPreservation
import NLS.KdV.HillFreeContourSpectralGapIsolation

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate unitInterval

namespace NLS.KdV

variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillFreeContour_physical_band_bounds_of_control (ε D : ℝ)
    (hc : HillComplexPeriodControl h0q h0r ε D)
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (hp : ‖SpectralWeight.one.toCoeff q‖ ≤ ε) (k : ℕ) (hk : 1 ≤ k) :
    hillRealLabels q hq hr (2*k-2) < hillRealGapCenter 0 h0q h0r k-
      (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k) ∧
    hillRealGapCenter 0 h0q h0r k+
      (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k) <
      hillRealLabels q hq hr (2*k+1) := by
  let c := hillRealGapCenter 0 h0q h0r k
  let r := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
  have hrad : 0 < r := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk).1
    (hillRealGapContour_geometry 0 h0q h0r k hk).2.1
  have hsL : ((c-r:ℝ):ℂ) ∈ sphere (c:ℂ) r := by
    rw [mem_sphere,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs,
      show c-r-c = -r by ring,abs_neg,abs_of_pos hrad]
  have hsU : ((c+r:ℝ):ℂ) ∈ sphere (c:ℂ) r := by
    rw [mem_sphere,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs,
      add_sub_cancel_left,abs_of_pos hrad]
  have hb := hillRealGapContour_band_bounds 0 h0q h0r k hk
  have hcL : hillRealLabels 0 h0q h0r (2*k-1) = c :=
    (hillFreeGapEndpoints h0q h0r k hk).1.trans (hillFreeGapCenter h0q h0r k hk).symm
  have hcU : hillRealLabels 0 h0q h0r (2*k) = c :=
    (hillFreeGapEndpoints h0q h0r k hk).2.trans (hillFreeGapCenter h0q h0r k hk).symm
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
    (hillFreeGapContour_source_compatibility h0q h0r ε D hc _ hp k hk _ hsL).1
  have hU := mem_same_hillRealBand_of_free_and_source h0q h0r q hq hr k (c+r) hbandU
    (hillFreeGapContour_source_compatibility h0q h0r ε D hc _ hp k hk _ hsU).1
  rw [hiL] at hL
  exact ⟨hL.1,hU.2⟩

theorem exists_hillFreeContour_enlarged_disc_in_filledDomain (ε D : ℝ)
    (hc : HillComplexPeriodControl h0q h0r ε D)
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (hp : ‖SpectralWeight.one.toCoeff q‖ ≤ ε) (k : ℕ) (hk : 1 ≤ k) :
    ∃ R : ℝ, hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k < R ∧
      closedBall (hillRealGapCenter 0 h0q h0r k : ℂ) R ⊆ hillGapFilledDomain q hq hr k := by
  let c := hillRealGapCenter 0 h0q h0r k
  let r := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
  have hb := hillFreeContour_physical_band_bounds_of_control h0q h0r ε D hc q hq hr hp k hk
  have hmargin : r < min (c-hillRealLabels q hq hr (2*k-2))
      (hillRealLabels q hq hr (2*k+1)-c) :=
    lt_min (by linarith [hb.1]) (by linarith [hb.2])
  obtain ⟨R,hrR,hR⟩ := exists_between hmargin
  refine ⟨R,hrR,?_⟩
  intro z hz
  have hdist : ‖z-(c:ℂ)‖ ≤ R := by simpa only [mem_closedBall,dist_eq_norm] using hz
  have hre := abs_le.mp ((abs_re_le_norm (z-(c:ℂ))).trans hdist)
  simp only [Complex.sub_re,Complex.ofReal_re] at hre
  have hm := lt_min_iff.mp hR
  exact Or.inr ⟨by linarith [hre.1,hm.1],by linarith [hre.2,hm.2]⟩

end NLS.KdV
