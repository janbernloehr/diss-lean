import NLS.KdV.HillAbelianImplicitRootReality
import NLS.KdV.HillComplexNormalizedPeriodGerm

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate

namespace NLS.KdV

variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillAbelianPhysicalNormalizedPeriod_germ (n : ℕ) (hn : 1 ≤ n) :
    ∃ a : Coeff 2 → PositiveDeletedCoeff 2 (n : ℤ), AnalyticAt ℂ a 0 ∧ a 0 = 0 ∧
      ∀ᶠ q : RealPeriodOneHillPotential in 𝓝 (⟨0,hq,hr⟩ : RealPeriodOneHillPotential),
        star (a (SpectralWeight.one.toCoeff q.val) : Coeff 2) =
          (a (SpectralWeight.one.toCoeff q.val) : Coeff 2) ∧
        ∀ k : ℕ, 1 ≤ k →
          ((2*(Real.pi : ℂ))⁻¹ * ∮ E in C((hillRealGapCenter 0 hq hr k : ℂ),
            hillRealGapHalfLength 0 hq hr k+hillRealGapCollar 0 hq hr k),
            hillAbelianNormalizedComplexPsi hq hr n
              ((a (SpectralWeight.one.toCoeff q.val) : Coeff 2),SpectralWeight.one.toCoeff q.val) E/
                hillEnergyCanonicalRootProduct q.val q.property.1 q.property.2 E) = if k = n then 1 else 0 := by
  obtain ⟨a,ha,ha0,hroots⟩ := exists_hillAbelianComplexPeriod_real_root_germ hq hr n hn
  obtain ⟨ε,D,hε,_,hc⟩ := exists_hillComplexPeriodControl hq hr
  let P : RealPeriodOneHillPotential → Coeff 2 := fun q => SpectralWeight.one.toCoeff q.val
  have hP : Continuous P := SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  have hP0 : P (⟨0,hq,hr⟩ : RealPeriodOneHillPotential) = 0 := map_zero _
  have ht : Tendsto P (𝓝 (⟨0,hq,hr⟩ : RealPeriodOneHillPotential)) (𝓝 (0 : Coeff 2)) := by
    simpa only [hP0] using hP.tendsto (⟨0,hq,hr⟩ : RealPeriodOneHillPotential)
  refine ⟨a,ha,ha0,?_⟩
  filter_upwards [ht.eventually hroots,ht.eventually (Metric.ball_mem_nhds (0 : Coeff 2) hε)] with q hqdata hpball
  refine ⟨hqdata.2.2 q.property.2,?_⟩
  intro k hk
  have hp : ‖P q‖ ≤ ε := (show ‖P q‖ < ε by simpa only [mem_ball,dist_zero_right] using hpball).le
  have hIntegral : (∮ E in C((hillRealGapCenter 0 hq hr k : ℂ),
      hillRealGapHalfLength 0 hq hr k+hillRealGapCollar 0 hq hr k),
      hillAbelianNormalizedComplexPsi hq hr n ((a (P q) : Coeff 2),P q) E/
        hillEnergyCanonicalRootProduct q.val q.property.1 q.property.2 E) =
      ∮ E in C((hillRealGapCenter 0 hq hr k : ℂ),
        hillRealGapHalfLength 0 hq hr k+hillRealGapCollar 0 hq hr k),
        hillAbelianNormalizedComplexPsi hq hr n ((a (P q) : Coeff 2),P q) E/
          hillAbelianComplexRoot 0 hq hr (E,P q) := by
    apply circleIntegral.integral_congr
      (add_nonneg (hillRealGapContour_geometry 0 hq hr k hk).1 (hillRealGapContour_geometry 0 hq hr k hk).2.1.le)
    intro E hE
    dsimp only []
    rw [(hillFreeGapContour_physical_root_matching hq hr ε D hc q.val q.property.1 q.property.2 hp k hk E hE).2]
  change (2*(Real.pi : ℂ))⁻¹ * _ = _
  rw [hIntegral,hillAbelianNormalizedComplexPsi_period_eq_ratio]
  by_cases hkn : k = n
  · subst k
    rw [if_pos rfl,div_self hqdata.2.1]
  · rw [if_neg hkn,hqdata.1 k hk hkn,zero_div]

end NLS.KdV
