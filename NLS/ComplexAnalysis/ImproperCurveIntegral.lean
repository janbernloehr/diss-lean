import NLS.ComplexAnalysis.ImproperPrimitivePathIntegral
import NLS.ComplexAnalysis.TwoEndpointSquareRootIntegrability

/-! # Agreement between proper and improper curve integrals -/

noncomputable section
open Set Filter Topology Complex MeasureTheory
namespace NLS.ComplexAnalysis

/-- Absolute curve integrability implies convergence of the derivative-based truncations. -/
theorem tendsto_truncatedPathIntegral_of_curveIntegrable (f : ℂ → ℂ)
    {a b : ℂ} (γ : Path a b) (hint : CurveIntegrable (holomorphicOneForm f) γ) :
    Tendsto (fun u : ℝ × ℝ => truncatedPathIntegral f γ u.1 u.2)
      ((𝓝[>] (0:ℝ)) ×ˢ (𝓝[<] (1:ℝ))) (𝓝 (∫ᶜ z in γ, holomorphicOneForm f z)) := by
  apply (tendsto_curveIntegral_truncations _ γ hint).congr'
  have hu : ∀ᶠ u in 𝓝[>] (0:ℝ), u ∈ Ioo (0:ℝ) (1/2) := Ioo_mem_nhdsGT (by norm_num)
  have hv : ∀ᶠ v in 𝓝[<] (1:ℝ), v ∈ Ioo (1/2:ℝ) 1 := Ioo_mem_nhdsLT (by norm_num)
  filter_upwards [hu.prod_mk hv] with u hu
  apply intervalIntegral.integral_congr
  intro t ht
  have huv : u.1 ≤ u.2 := by linarith [hu.1.2,hu.2.1]
  rw [uIcc_of_le huv] at ht
  have hi : t ∈ Ioo (0:ℝ) 1 := ⟨hu.1.1.trans_le ht.1,ht.2.trans_lt hu.2.2⟩
  rw [curveIntegralFun_def,derivWithin_of_mem_nhds
    (Filter.mem_of_superset (Ioo_mem_nhds hi.1 hi.2) Ioo_subset_Icc_self)]
  rfl

/-- No primitive assumption is needed for agreement with an absolutely integrable curve. -/
theorem improperPathIntegral_eq_curveIntegral_of_integrable (f : ℂ → ℂ)
    {a b : ℂ} (γ : Path a b) (hint : CurveIntegrable (holomorphicOneForm f) γ) :
    improperPathIntegral f γ = ∫ᶜ z in γ, holomorphicOneForm f z :=
  (tendsto_truncatedPathIntegral_of_curveIntegrable f γ hint).limUnder_eq

end NLS.ComplexAnalysis
