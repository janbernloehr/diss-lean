import NLS.KdV.HillComplexRegularDensityBounds
import NLS.KdV.HillCommonComplexHighChart

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

def HillRegularGapAnalyticChart (G : ℂ × Coeff 2 → ℂ) (U : Set (Coeff 2)) (k : ℕ) (C : ℝ) : Prop :=
  let c : ℂ := hillRealGapCenter 0 h0q h0r k
  let R := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
  AnalyticOnNhd ℂ (hillComplexRegularGapNumerator h0q h0r G k) (closedBall c R ×ˢ U) ∧
    AnalyticOnNhd ℂ (hillComplexRegularGapDensity h0q h0r G k) ((closedBall c R \ ball c (R/2)) ×ˢ U) ∧
    ∀ p ∈ U,
      (∀ E ∈ sphere c R, hillComplexRegularGapDensity h0q h0r G k (E,p)=
        (-I)*(G (E,p)/hillAbelianComplexRoot 0 h0q h0r (E,p))) ∧
      (∮ E in C(c,R), hillComplexRegularGapDensity h0q h0r G k (E,p))=0 ∧
      (∮ E in C(c,R/2), hillComplexRegularGapDensity h0q h0r G k (E,p))=0 ∧
      (∀ E ∈ closedBall c R, ‖hillComplexRegularGapNumerator h0q h0r G k (E,p)‖ ≤ 2*R*C/(k : ℝ)^3) ∧
      ∀ E ∈ sphere c (3*R/4), ‖hillComplexRegularGapDensity h0q h0r G k (E,p)‖ ≤ 8*C/(k : ℝ)^3

theorem exists_hillSelectedPsi_common_complex_regular_annulus_chart
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) :
    ∃ G : ℂ × Coeff 2 → ℂ, ∃ U : Set (Coeff 2), IsOpen U ∧ SpectralWeight.one.toCoeff q ∈ U ∧
      ∃ B : ℝ, 0 < B ∧ U ⊆ ball (0 : Coeff 2) B ∧
      ∃ N : ℕ, 1 ≤ N ∧ ∃ C : ℝ, 0 < C ∧ AnalyticOnNhd ℂ G (univ ×ˢ U) ∧
        (∀ k : ℕ, N ≤ k → HillRegularGapAnalyticChart h0q h0r G U k C) ∧
        ∀ᶠ r : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
          SpectralWeight.one.toCoeff r.val ∈ U ∧ ∀ E : ℂ,
            G (E,SpectralWeight.one.toCoeff r.val)=hillAbelianSelectedGlobalPsi r.val r.property.1 r.property.2 n hn E := by
  obtain ⟨G,U,hU,hqU,N0,hN0,C,hC,hG,hdata,hmatch⟩ :=
    exists_hillSelectedPsi_common_complex_high_contour_chart q hq hr h0q h0r n hn
  let B : ℝ := ‖SpectralWeight.one.toCoeff q‖+1
  let V := U ∩ ball (0 : Coeff 2) B
  have hqB : SpectralWeight.one.toCoeff q ∈ ball (0 : Coeff 2) B := by
    rw [mem_ball,dist_zero_right]
    dsimp only [B]
    linarith
  have hVG : AnalyticOnNhd ℂ G (univ ×ˢ V) := hG.mono (prod_mono Subset.rfl inter_subset_left)
  have hVB : V ⊆ ball (0 : Coeff 2) B := inter_subset_right
  have hz : ∀ p ∈ V, ∀ k : ℕ, N0 ≤ k →
      (∮ E in C((hillRealGapCenter 0 h0q h0r k : ℂ),hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
        G (E,p)/hillAbelianComplexRoot 0 h0q h0r (E,p))=0 := fun p hp k hk => (hdata p hp.1 k hk).2
  have hb : ∀ p ∈ V, ∀ k : ℕ, N0 ≤ k → ∀ E ∈ sphere (hillRealGapCenter 0 h0q h0r k : ℂ)
      (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
      ‖G (E,p)/hillAbelianComplexRoot 0 h0q h0r (E,p)‖ ≤ C/(k : ℝ)^3 :=
    fun p hp k hk E hE => ((hdata p hp.1 k hk).1 E hE).2
  obtain ⟨Na,hNa,hNa0,ha⟩ := exists_hillComplexRegularGapDensity_analytic_zero_periods h0q h0r G V B hVB hVG N0 hz
  obtain ⟨Nb,hNb,hNb0,hbounds⟩ := exists_hillComplexRegularGapDensity_uniform_contour_bounds h0q h0r G V B hVB hVG N0 C hC.le hb
  refine ⟨G,V,hU.inter isOpen_ball,⟨hqU,hqB⟩,B,(by dsimp only [B];positivity),hVB,max Na Nb,hNa.trans (le_max_left _ _),C,hC,hVG,?_,?_⟩
  · intro k hk
    have hka : Na ≤ k := (le_max_left _ _).trans hk
    have hkb : Nb ≤ k := (le_max_right _ _).trans hk
    obtain ⟨hg,hD,hperiod⟩ := ha k hka
    refine ⟨hg,hD,?_⟩
    intro p hp
    obtain ⟨hpoint,houter,hinner⟩ := hperiod p hp
    obtain ⟨hdisc,hcircle⟩ := hbounds k hkb p hp
    exact ⟨hpoint,houter,hinner,hdisc,hcircle⟩
  · have hmap : Continuous (fun r : RealPeriodOneHillPotential => SpectralWeight.one.toCoeff r.val) :=
      SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
    have hnear : ∀ᶠ r : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
        SpectralWeight.one.toCoeff r.val ∈ ball (0 : Coeff 2) B :=
      hmap.continuousAt.tendsto.eventually (isOpen_ball.mem_nhds hqB)
    filter_upwards [hmatch,hnear] with r hr' hrB
    exact ⟨⟨hr'.1,hrB⟩,hr'.2⟩

end NLS.KdV
