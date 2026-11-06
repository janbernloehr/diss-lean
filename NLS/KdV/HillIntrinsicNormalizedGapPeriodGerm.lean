import NLS.KdV.HillIntrinsicComplexPeriods
import NLS.KdV.HillPhysicalNormalizedGapPeriodGerm

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate unitInterval

namespace NLS.KdV

variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem analyticOnNhd_hillAbelianNormalizedComplexPsi_energy (n : ℕ) (t : Coeff 2 × Coeff 2) :
    AnalyticOnNhd ℂ (hillAbelianNormalizedComplexPsi h0q h0r n t) univ := by
  intro E _
  change AnalyticAt ℂ (fun E => hillAbelianHilbertPsi n (E,t.1)/
    hillAbelianComplexPeriod 0 h0q h0r n n t) E
  exact ((analyticOnNhd_hillAbelianHilbertPsi n (E,t.1) (mem_univ _)).comp
    (f := fun E : ℂ => (E,t.1)) (analyticAt_id.prod analyticAt_const)).div_const

theorem exists_hillAbelianIntrinsicNormalizedGapPeriod_germ (n : ℕ) (hn : 1 ≤ n) :
    ∃ a : Coeff 2 → PositiveDeletedCoeff 2 (n:ℤ), AnalyticAt ℂ a 0 ∧ a 0 = 0 ∧
      ∀ᶠ q : RealPeriodOneHillPotential in 𝓝 (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential),
        star (a (SpectralWeight.one.toCoeff q.val) : Coeff 2) =
          (a (SpectralWeight.one.toCoeff q.val) : Coeff 2) ∧
        (∀ k : ℕ, 1 ≤ k → k ≠ n →
          hillAbelianHilbertRootEnergy (a (SpectralWeight.one.toCoeff q.val) : Coeff 2) k ∈
            segment ℝ (hillRealLabels q.val q.property.1 q.property.2 (2*k-1) : ℂ)
              (hillRealLabels q.val q.property.1 q.property.2 (2*k) : ℂ)) ∧
        ∀ k : ℕ, 1 ≤ k →
          ((2*(Real.pi:ℂ))⁻¹ * ∮ E in C((hillRealGapCenter q.val q.property.1 q.property.2 k : ℂ),
            hillRealGapHalfLength q.val q.property.1 q.property.2 k+
              hillRealGapCollar q.val q.property.1 q.property.2 k),
            hillAbelianNormalizedComplexPsi h0q h0r n
              ((a (SpectralWeight.one.toCoeff q.val) : Coeff 2),SpectralWeight.one.toCoeff q.val) E/
                hillEnergyCanonicalRootProduct q.val q.property.1 q.property.2 E) = if k = n then 1 else 0 := by
  obtain ⟨a,ha,ha0,hperiods⟩ := exists_hillAbelianPhysicalNormalizedGapPeriod_germ h0q h0r n hn
  obtain ⟨ε,D,hε,_,hc⟩ := exists_hillComplexPeriodControl h0q h0r
  let P : RealPeriodOneHillPotential → Coeff 2 := fun q => SpectralWeight.one.toCoeff q.val
  have hP : Continuous P := SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  have ht : Tendsto P (𝓝 (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential)) (𝓝 (0:Coeff 2)) := by
    have hP0 : P (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential) = 0 := map_zero _
    simpa only [hP0] using hP.tendsto (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential)
  refine ⟨a,ha,ha0,?_⟩
  filter_upwards [hperiods,ht.eventually (Metric.ball_mem_nhds (0:Coeff 2) hε)] with q hqdata hpball
  refine ⟨hqdata.1,hqdata.2.1,?_⟩
  intro k hk
  have hp : ‖P q‖ ≤ ε := (show ‖P q‖ < ε by
    simpa only [mem_ball,dist_zero_right] using hpball).le
  have he := hillPhysicalContour_period_eq_free_contour h0q h0r ε D hc q.val q.property.1 q.property.2 hp k hk
    (hillAbelianNormalizedComplexPsi h0q h0r n ((a (P q) : Coeff 2),P q))
    (analyticOnNhd_hillAbelianNormalizedComplexPsi_energy h0q h0r n _)
  rw [← he]
  exact hqdata.2.2 k hk

end NLS.KdV
