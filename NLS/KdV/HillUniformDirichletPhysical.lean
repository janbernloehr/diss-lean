import NLS.KdV.HillUniformComplexDirichlet
import NLS.KdV.HillHighFreeContourBandBounds
import NLS.KdV.HillDirichletAnalyticLabels

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillScaledDirichletRoot_bounded_real_physical_matching
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (B : ℝ) :
    ∃ N : ℕ, ∃ hN : 1 ≤ N, ∀ q : WeightedCoeff SpectralWeight.one.toWeight 2,
      ∀ hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0,
      ∀ hr : IsRealHillPotential (SpectralWeight.one.toCoeff q), ‖SpectralWeight.one.toCoeff q‖ ≤ B →
        ∀ k : ℕ, ∀ hk : N ≤ k,
          hillScaledDirichletRoot h0q h0r ρ k (SpectralWeight.one.toCoeff q) =
            (hillDirichletEnergy q hq hr k (hN.trans hk) : ℂ) := by
  obtain ⟨N0,hN0,hchart⟩ := exists_hillScaledDirichletRoot_bounded_complex_analytic_chart h0q h0r ρ hρ hρ1 B
  obtain ⟨N1,hN1,D,hD,hcontrol⟩ := exists_hillComplexTailPeriodControl h0q h0r B
  refine ⟨max N0 N1,hN0.trans (le_max_left _ _),?_⟩
  intro q hq hr hp k hk
  have hk0 : N0 ≤ k := (le_max_left _ _).trans hk
  have hk1 : N1 ≤ k := (le_max_right _ _).trans hk
  have hkpos : 1 ≤ k := hN0.trans hk0
  let a := hillScaledDirichletRoot h0q h0r ρ k (SpectralWeight.one.toCoeff q)
  let c := hillRealGapCenter 0 h0q h0r k
  let R := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
  obtain ⟨ha,haz,haorder,haunique⟩ := (hchart k hk0).2 _ hp
  have hreal : a.im=0 := hillL2DirichletCharacteristic_zero_real _ hr a haz
  have he : (a.re : ℂ)=a := by apply Complex.ext <;> simp only [ofReal_re,ofReal_im,hreal]
  have hz : hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) (a.re : ℂ)=0 := by rw [he];exact haz
  have hR : 0 < R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hkpos).1
    (hillRealGapContour_geometry 0 h0q h0r k hkpos).2.1
  have habs : |a.re-c| < R := by
    have hb : ‖a-(c : ℂ)‖ < ρ*R := by simpa only [mem_ball,dist_eq_norm] using ha
    have hre : |a.re-c| ≤ ‖a-(c : ℂ)‖ := by simpa only [sub_re,ofReal_re] using abs_re_le_norm (a-(c : ℂ))
    exact (hre.trans_lt hb).trans_le (mul_le_of_le_one_left hR.le hρ1)
  have hband := hillHighFreeContour_physical_band_bounds_of_control h0q h0r N1 hN1 B D hcontrol q hq hr hp k hk1
  have hbetween : a.re ∈ Ioo (hillRealLabels q hq hr (2*k-2)) (hillRealLabels q hq hr (2*k+1)) := by
    obtain ⟨hl,hu⟩ := abs_lt.mp habs
    constructor <;> linarith [hband.1,hband.2]
  have hmem := hillDirichlet_zero_mem_gap_of_between_neighbor_bands q hq hr k hkpos a.re hbetween hz
  have hEq := hillDirichletEnergy_eq_of_zero_in_gap q hq hr k hkpos a.re hmem hz
  exact he.symm.trans (congrArg Complex.ofReal hEq.symm)

end NLS.KdV
