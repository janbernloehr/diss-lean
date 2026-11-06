import NLS.KdV.HillFilledFreeGapRoot
import NLS.KdV.HillCommonDeflatedRootPhysical

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillFilledFreeGapRoot_bounded_real_physical_matching (B : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ q : WeightedCoeff SpectralWeight.one.toWeight 2,
      ∀ hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0,
      ∀ hr : IsRealHillPotential (SpectralWeight.one.toCoeff q), ‖SpectralWeight.one.toCoeff q‖ ≤ B →
        ∀ k : ℕ, N ≤ k → ∀ E ∈ closedBall (hillRealGapCenter 0 h0q h0r k : ℂ)
          (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
          hillFilledFreeGapRoot h0q h0r k (E,SpectralWeight.one.toCoeff q)=
            hillDeflatedEnergyCanonicalRoot q hq hr k E := by
  obtain ⟨Na,hNa,han⟩ := exists_hillFilledFreeGapRoot_bounded_complex_analytic h0q h0r (B+1)
  obtain ⟨Nm,hNm,hmatch⟩ := exists_hillFreeGap_bounded_real_normalized_root_matching h0q h0r B
  obtain ⟨Nc,hNc,D,hD,hcontrol⟩ := exists_hillComplexTailPeriodControl h0q h0r B
  refine ⟨max Na (max Nm Nc),hNa.trans (le_max_left _ _),?_⟩
  intro q hq hr hp k hk
  have hka : Na ≤ k := (le_max_left _ _).trans hk
  have hkm : Nm ≤ k := (le_max_left _ _).trans ((le_max_right _ _).trans hk)
  have hkc : Nc ≤ k := (le_max_right _ _).trans ((le_max_right _ _).trans hk)
  have hk1 : 1 ≤ k := hNa.trans hka
  let c : ℂ := hillRealGapCenter 0 h0q h0r k
  let R := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
  have hR : 0 < R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk1).1
    (hillRealGapContour_geometry 0 h0q h0r k hk1).2.1
  have hpB : SpectralWeight.one.toCoeff q ∈ ball (0 : Coeff 2) (B+1) := by rw [mem_ball,dist_zero_right];linarith
  have hband := hillHighFreeContour_physical_band_bounds_of_control h0q h0r Nc hNc B D hcontrol q hq hr hp k hkc
  have hfilled (E : ℂ) (hE : E ∈ closedBall c R) : E ∈ hillGapFilledDomain q hq hr k := by
    have hre := re_bounds_of_mem_realCenteredClosedBall hE
    exact Or.inr ⟨by linarith [hband.1,hre.1],by linarith [hband.2,hre.2]⟩
  have hleft : ContinuousOn (fun E : ℂ => hillFilledFreeGapRoot h0q h0r k (E,SpectralWeight.one.toCoeff q)) (closedBall c R) :=
    (han k hka).1.continuousOn.comp (by fun_prop) (fun E hE => ⟨hE,hpB⟩)
  have hright : ContinuousOn (hillDeflatedEnergyCanonicalRoot q hq hr k) (closedBall c R) :=
    (analyticOnNhd_hillDeflatedEnergyCanonicalRoot q hq hr k).continuousOn.mono hfilled
  have heq : EqOn (fun E : ℂ => hillFilledFreeGapRoot h0q h0r k (E,SpectralWeight.one.toCoeff q))
      (hillDeflatedEnergyCanonicalRoot q hq hr k) (ball c R) := by
    intro E hE
    exact (hillFilledFreeGapRoot_eq_local h0q h0r k _ E hE).trans (hmatch q hq hr hp k hkm E hE)
  exact heq.of_subset_closure hleft hright ball_subset_closedBall
    (by rw [closure_ball c hR.ne'])

end NLS.KdV
