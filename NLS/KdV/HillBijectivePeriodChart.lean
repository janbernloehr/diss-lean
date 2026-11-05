import NLS.KdV.HillSupportedPeriodFredholm
import NLS.ComplexAnalysis.AnalyticImplicitBanachRoot

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillMixedSupportedPeriodMap_analytic_with_bijective_root_derivative :
    ∃ N : ℕ, ∃ B D : ℝ, ∃ U : Set (Coeff 2),
      1 ≤ N ∧ 0 < D ∧ HillComplexTailPeriodControl h0q h0r N B D ∧
        IsOpen U ∧ SpectralWeight.one.toCoeff q ∈ U ∧ U ⊆ ball 0 B ∧
          ∀ n : ℕ, 1 ≤ n → ∀ roots : ℕ → ℝ, ∀ hroots : roots ∈ hillGapRootBox q hq hr,
            (∀ k : ℕ, 1 ≤ k → k ≠ n → hillAbelianCandidatePeriod q hq hr roots n k = 0) →
            AnalyticAt ℂ (hillMixedSupportedPeriodMap q hq hr h0q h0r N n
              (hillGapRootHilbertCoordinates q hq hr roots hroots)) (0,SpectralWeight.one.toCoeff q) ∧
            hillMixedSupportedPeriodMap q hq hr h0q h0r N n
              (hillGapRootHilbertCoordinates q hq hr roots hroots) (0,SpectralWeight.one.toCoeff q) = 0 ∧
            Function.Bijective ((fderiv ℂ (hillMixedSupportedPeriodMap q hq hr h0q h0r N n
              (hillGapRootHilbertCoordinates q hq hr roots hroots)) (0,SpectralWeight.one.toCoeff q)).comp
                (ContinuousLinearMap.inl ℂ (PositiveDeletedCoeff 2 (n : ℤ)) (Coeff 2))) := by
  obtain ⟨N,B,D,U,hN,hD,hcontrol,hU,hqU,hsub,hMixed⟩ :=
    exists_hillMixedComplexPeriodSequence_analytic_neighborhood q hq hr h0q h0r
  have hp : ‖SpectralWeight.one.toCoeff q‖ ≤ B :=
    (show ‖SpectralWeight.one.toCoeff q‖ < B by simpa only [mem_ball,dist_zero_right] using hsub hqU).le
  refine ⟨N,B,D,U,hN,hD,hcontrol,hU,hqU,hsub,?_⟩
  intro n hn roots hroots hperiods
  have hF := (analyticOnNhd_hillMixedSupportedPeriodMap q hq hr h0q h0r N n
    (hillGapRootHilbertCoordinates q hq hr roots hroots) U (hMixed n hn)) (0,SpectralWeight.one.toCoeff q)
      ⟨mem_univ _,hqU⟩
  have hsec : AnalyticOnNhd ℂ (fun b : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N n
      (b,SpectralWeight.one.toCoeff q)) univ := by
    intro b _
    exact ((hMixed n hn) (b,SpectralWeight.one.toCoeff q) ⟨mem_univ _,hqU⟩).comp
      (f := fun b : Coeff 2 => (b,SpectralWeight.one.toCoeff q)) (analyticAt_id.prod analyticAt_const)
  exact ⟨hF,hillMixedSupportedPeriodMap_at_global_roots_eq_zero q hq hr h0q h0r N n hN hn B D hcontrol hp
    roots hroots hperiods,hillMixedSupportedPeriodMap_partial_derivative_bijective q hq hr h0q h0r N n hN hn B D hD.le hcontrol hp
      roots hroots hperiods hF hsec⟩

theorem exists_hillMixedSupportedPeriodMap_analytic_implicit_root :
    ∃ N : ℕ, ∃ B D : ℝ, ∃ U : Set (Coeff 2),
      1 ≤ N ∧ 0 < D ∧ HillComplexTailPeriodControl h0q h0r N B D ∧
        IsOpen U ∧ SpectralWeight.one.toCoeff q ∈ U ∧ U ⊆ ball 0 B ∧
          ∀ n : ℕ, 1 ≤ n → ∀ roots : ℕ → ℝ, ∀ hroots : roots ∈ hillGapRootBox q hq hr,
            (∀ k : ℕ, 1 ≤ k → k ≠ n → hillAbelianCandidatePeriod q hq hr roots n k = 0) →
            ∃ s : Coeff 2 → PositiveDeletedCoeff 2 (n : ℤ),
              AnalyticAt ℂ s (SpectralWeight.one.toCoeff q) ∧ s (SpectralWeight.one.toCoeff q) = 0 ∧
                ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff q), hillMixedSupportedPeriodMap q hq hr h0q h0r N n
                  (hillGapRootHilbertCoordinates q hq hr roots hroots) (s p,p) = 0 := by
  obtain ⟨N,B,D,U,hN,hD,hc,hU,hqU,hsub,hcharts⟩ :=
    exists_hillMixedSupportedPeriodMap_analytic_with_bijective_root_derivative q hq hr h0q h0r
  refine ⟨N,B,D,U,hN,hD,hc,hU,hqU,hsub,?_⟩
  intro n hn roots hroots hperiods
  obtain ⟨hF,hzero,hbij⟩ := hcharts n hn roots hroots hperiods
  exact exists_analytic_implicitBanachRoot
    (hillMixedSupportedPeriodMap q hq hr h0q h0r N n (hillGapRootHilbertCoordinates q hq hr roots hroots))
    0 (SpectralWeight.one.toCoeff q) hF hzero hbij

end NLS.KdV
