import NLS.KdV.HillOmittedEnergyCriticalProduct
import NLS.ComplexAnalysis.RealCriticalProducts
import NLS.ComplexAnalysis.RealGapDiscIsolation

/-! # Positivity of the omitted Hill critical product and chi on each closed real gap. -/

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
open NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillRealGap_exterior_to_other_gap
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hmn : m ≠ n)
    (x : ℝ) (hx : x ∈ Icc (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n))) :
    x < hillRealLabels q hq hr (2*m-1) ∨ hillRealLabels q hq hr (2*m) < x := by
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · right
    exact (hillRealLabels_band_strict q hq hr m).trans_le
      ((monotone_hillRealLabels q hq hr (by omega)).trans hx.1)
  · left
    exact hx.2.trans_lt ((hillRealLabels_band_strict q hq hr n).trans_le
      (monotone_hillRealLabels q hq hr (by omega)))

theorem hillOmittedEnergyCriticalRootFactor_real_positive
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) (x : ℝ)
    (hx : x ∈ Icc (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n))) (k : ℕ) :
    0 < (hillOmittedEnergyCriticalRootFactor q hq hr n k x).re ∧
      (hillOmittedEnergyCriticalRootFactor q hq hr n k x).im = 0 := by
  unfold hillOmittedEnergyCriticalRootFactor
  split_ifs with hk
  · norm_num
  · exact critical_endpoint_ratio_real_positive _ _ _ _
      (monotone_hillRealLabels q hq hr (by omega : 2*(k+1)-1 ≤ 2*(k+1)))
      (hillGapCriticalPoint_spec q hq hr (k+1) (by omega)).1
      (hillRealGap_exterior_to_other_gap q hq hr n (k+1) hn (by omega) hk x hx)

theorem summable_norm_hillOmittedEnergyCriticalRootFactor_sub_one
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (z : ℂ) :
    Summable (fun k : ℕ => ‖hillOmittedEnergyCriticalRootFactor q hq hr n k z-1‖) := by
  obtain ⟨N,u,hu,hbound⟩ := exists_hillOmittedEnergyCriticalRootFactor_bounded_majorant q hq hr n ‖z‖ (norm_nonneg z)
  apply hu.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop N] with k hk
  simpa only [norm_norm] using hbound k hk z le_rfl

theorem hillOmittedEnergyCriticalRootProduct_real_positive
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) (x : ℝ)
    (hx : x ∈ Icc (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n))) :
    0 < (hillOmittedEnergyCriticalRootProduct q hq hr n x).re ∧
      (hillOmittedEnergyCriticalRootProduct q hq hr n x).im = 0 := by
  have hfilled := hillGapSegment_subset_filledDomain q hq hr n hn
    (ofReal_mem_ordered_segment _ _ x (monotone_hillRealLabels q hq hr (by omega : 2*n-1 ≤ 2*n)) hx)
  have hp := (hasProdLocallyUniformlyOn_hillOmittedEnergyCriticalRootFactors q hq hr n).hasProd hfilled
  have hf := hillOmittedEnergyCriticalRootFactor_real_positive q hq hr n hn x hx
  have hs := summable_norm_hillOmittedEnergyCriticalRootFactor_sub_one q hq hr n (x : ℂ)
  have he (k : ℕ) : 1+(hillOmittedEnergyCriticalRootFactor q hq hr n k x-1) = hillOmittedEnergyCriticalRootFactor q hq hr n k x := by ring
  have hne := (tprod_one_add_ne_zero_iff (fun k => hillOmittedEnergyCriticalRootFactor q hq hr n k x-1) hs)
  simp only [he] at hne
  have hprodne : hillOmittedEnergyCriticalRootProduct q hq hr n x ≠ 0 := by
    convert! hne.mpr (fun k => by intro heq; have hh := (hf k).1; rw [heq] at hh; norm_num at hh) using 1
  exact hp.positive_real_of_each _ _ hf hprodne

theorem hillEnergyChi_real_positive
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) (x : ℝ)
    (hx : x ∈ Icc (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n))) :
    0 < (hillEnergyChi q hq hr n x).re ∧ (hillEnergyChi q hq hr n x).im = 0 := by
  obtain ⟨hp,hi⟩ := hillOmittedEnergyCriticalRootProduct_real_positive q hq hr n hn x hx
  have hx0 : hillRealLabels q hq hr 0 < x := by
    have hband := hillRealLabels_band_strict q hq hr 0
    simp only [mul_zero,zero_add] at hband
    exact hband.trans_le ((monotone_hillRealLabels q hq hr (by omega)).trans hx.1)
  have hs : Complex.sqrt ((x : ℂ)-hillRealLabels q hq hr 0) = (Real.sqrt (x-hillRealLabels q hq hr 0) : ℂ) := by
    rw [← ofReal_sub,Complex.sqrt_of_nonneg (by exact_mod_cast (show 0 ≤ x-hillRealLabels q hq hr 0 by linarith))]
    simp only [ofReal_re]
  have he : hillOmittedEnergyCriticalRootProduct q hq hr n x =
      ((hillOmittedEnergyCriticalRootProduct q hq hr n x).re : ℂ) := by
    apply Complex.ext <;> simp [hi]
  rw [hillEnergyChi,hs,he,← ofReal_inv,← ofReal_mul]
  simp only [ofReal_re,ofReal_im]
  exact ⟨mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr (sub_pos.mpr hx0))) hp,trivial⟩

end NLS.KdV
