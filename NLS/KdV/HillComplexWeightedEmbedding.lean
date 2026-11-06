import NLS.KdV.HillCanonicalGapBounds
import NLS.KdV.HillFreeGapContourGeometry

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

def hillPeriodOneCoefficientMap (w : SpectralWeight) :
    WeightedCoeff w.doubleIndex.toWeight 2 →L[ℂ] Coeff 2 :=
  w.toCoeff.comp (hillPeriodOnePotential w).toContinuousLinearMap

theorem hillPeriodOneCoefficientMap_eq_unit (w : SpectralWeight)
    (q : WeightedCoeff w.doubleIndex.toWeight 2) :
    hillPeriodOneCoefficientMap w q=SpectralWeight.one.toCoeff (hillPeriodOneUnitPotential w q) :=
  (toCoeff_hillPeriodOneUnitPotential w q).symm

theorem norm_hillPeriodOneCoefficientMap_le (w : SpectralWeight)
    (q : WeightedCoeff w.doubleIndex.toWeight 2) : ‖hillPeriodOneCoefficientMap w q‖≤‖q‖ := by
  exact (SpectralWeight.norm_toCoeff_le w (hillPeriodOnePotential w q)).trans_eq (norm_hillPeriodOnePotential w q)

theorem hillFreeGap_smallClosedBall_subset_reducedStrip (n : ℕ) (hn : 1≤n) :
    closedBall (hillRealGapCenter 0 h0q h0r n:ℂ)
      ((hillRealGapHalfLength 0 h0q h0r n+hillRealGapCollar 0 h0q h0r n)/16)⊆reducedHillStrip n := by
  have hnR : (1:ℝ)≤n := by exact_mod_cast hn
  have hpi : Real.pi^2≤16 := by
    have hh := (sq_lt_sq₀ Real.pi_pos.le (by norm_num : (0:ℝ)≤4)).mpr Real.pi_lt_four
    norm_num at hh ⊢
    exact hh.le
  have hrad : (hillRealGapHalfLength 0 h0q h0r n+hillRealGapCollar 0 h0q h0r n)/16≤(n:ℝ) := by
    rw [hillFreeGapHalfLength h0q h0r n hn,hillFreeGapCollar h0q h0r n hn,zero_add]
    have hh := mul_le_mul_of_nonneg_left hpi (by linarith : 0≤2*(n:ℝ)-1)
    nlinarith
  intro E hE
  have he : ‖E-(freeHillValue n:ℂ)‖≤(n:ℝ) := by
    have hh : ‖E-(hillRealGapCenter 0 h0q h0r n:ℂ)‖≤
        (hillRealGapHalfLength 0 h0q h0r n+hillRealGapCollar 0 h0q h0r n)/16 := by
      simpa only [mem_closedBall,dist_eq_norm] using hE
    rw [hillFreeGapCenter h0q h0r n hn] at hh
    exact hh.trans hrad
  have hr : |E.re-freeHillValue n|≤‖E-(freeHillValue n:ℂ)‖ := by
    simpa only [sub_re,ofReal_re] using abs_re_le_norm (E-(freeHillValue n:ℂ))
  change |E.re-freeHillValue n|≤6*(n:ℝ)
  linarith

end NLS.KdV
