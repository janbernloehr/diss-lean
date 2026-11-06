import NLS.KdV.HillPhysicalGapRootGerm
import NLS.KdV.HillComplexNormalizedPeriodGerm

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate unitInterval

namespace NLS.KdV

variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillAbelianPhysicalNormalizedGapPeriod_germ (n : ℕ) (hn : 1 ≤ n) :
    ∃ a : Coeff 2 → PositiveDeletedCoeff 2 (n : ℤ), AnalyticAt ℂ a 0 ∧ a 0 = 0 ∧
      ∀ᶠ q : RealPeriodOneHillPotential in 𝓝 (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential),
        star (a (SpectralWeight.one.toCoeff q.val) : Coeff 2) =
          (a (SpectralWeight.one.toCoeff q.val) : Coeff 2) ∧
        (∀ k : ℕ, 1 ≤ k → k ≠ n →
          hillAbelianHilbertRootEnergy (a (SpectralWeight.one.toCoeff q.val) : Coeff 2) k ∈
            segment ℝ (hillRealLabels q.val q.property.1 q.property.2 (2*k-1) : ℂ)
              (hillRealLabels q.val q.property.1 q.property.2 (2*k) : ℂ)) ∧
        ∀ k : ℕ, 1 ≤ k →
          ((2*(Real.pi : ℂ))⁻¹ * ∮ E in C((hillRealGapCenter 0 h0q h0r k : ℂ),
            hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
            hillAbelianNormalizedComplexPsi h0q h0r n
              ((a (SpectralWeight.one.toCoeff q.val) : Coeff 2),SpectralWeight.one.toCoeff q.val) E/
                hillEnergyCanonicalRootProduct q.val q.property.1 q.property.2 E) = if k = n then 1 else 0 := by
  obtain ⟨a,ha,ha0,hroots⟩ := exists_hillAbelianPhysicalGapRoot_germ h0q h0r n hn
  obtain ⟨ε,D,hε,_,hc⟩ := exists_hillComplexPeriodControl h0q h0r
  let P : RealPeriodOneHillPotential → Coeff 2 := fun q => SpectralWeight.one.toCoeff q.val
  have hP : Continuous P := SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  have hP0 : P (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential) = 0 := map_zero _
  have ht : Tendsto P (𝓝 (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential)) (𝓝 (0 : Coeff 2)) := by
    simpa only [hP0] using hP.tendsto (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential)
  refine ⟨a,ha,ha0,?_⟩
  filter_upwards [hroots,ht.eventually (Metric.ball_mem_nhds (0 : Coeff 2) hε)] with q hqdata hpball
  refine ⟨hqdata.2.2,(fun k hk hkn => (hqdata.1 k hk hkn).2),?_⟩
  intro k hk
  have hp : ‖P q‖ ≤ ε := (show ‖P q‖ < ε by simpa only [mem_ball,dist_zero_right] using hpball).le
  have hIntegral : (∮ E in C((hillRealGapCenter 0 h0q h0r k : ℂ),
      hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
      hillAbelianNormalizedComplexPsi h0q h0r n ((a (P q) : Coeff 2),P q) E/
        hillEnergyCanonicalRootProduct q.val q.property.1 q.property.2 E) =
      ∮ E in C((hillRealGapCenter 0 h0q h0r k : ℂ),
        hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
        hillAbelianNormalizedComplexPsi h0q h0r n ((a (P q) : Coeff 2),P q) E/
          hillAbelianComplexRoot 0 h0q h0r (E,P q) := by
    apply circleIntegral.integral_congr
      (add_nonneg (hillRealGapContour_geometry 0 h0q h0r k hk).1 (hillRealGapContour_geometry 0 h0q h0r k hk).2.1.le)
    intro E hE
    dsimp only []
    rw [(hillFreeGapContour_physical_root_matching h0q h0r ε D hc q.val q.property.1 q.property.2 hp k hk E hE).2]
  change (2*(Real.pi : ℂ))⁻¹ * _ = _
  rw [hIntegral,hillAbelianNormalizedComplexPsi_period_eq_ratio]
  by_cases hkn : k = n
  · subst k
    rw [if_pos rfl,div_self hqdata.2.1]
  · rw [if_neg hkn,(hqdata.1 k hk hkn).1,zero_div]

end NLS.KdV
