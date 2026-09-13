import NLS.FunctionalAnalysis.LinearVolterraSolution
import NLS.FunctionalAnalysis.ComplexAbsoluteContinuity

/-!
# From absolutely continuous weak solutions to classical solutions

An absolutely continuous curve whose derivative satisfies the continuous
linear ODE almost everywhere is the constructed initial-value solution.
Consequently the equation holds classically at every interior point.
-/

noncomputable section
open Set Filter Topology MeasureTheory intervalIntegral
namespace NLS.LinearVolterra
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Almost-everywhere ODE solutions in the absolutely continuous class satisfy the same uniqueness theorem. -/
theorem solution_unique_of_ac (A : Curve (E →L[ℝ] E)) (u : ℝ → E)
    (hu : AbsolutelyContinuousOnInterval u 0 1)
    (hd : ∀ᵐ s : ℝ, s ∈ Icc (0 : ℝ) 1 → HasDerivAt u (extend A s (u s)) s) :
    EqOn u (solution A (u 0)) (Icc 0 1) := by
  have hc : ContinuousOn u (Icc 0 1) := by simpa using hu.continuousOn
  let v : Curve E := ⟨fun t => u t,hc.comp_continuous continuous_subtype_val (fun t => t.property)⟩
  have hv (t : Icc (0 : ℝ) 1) : v t = u 0 + ∫ s in (0 : ℝ)..t.val, integrand A v s := by
    have hs : uIcc 0 t.val ⊆ Icc (0 : ℝ) 1 := by
      rw [uIcc_of_le t.property.1]
      exact Icc_subset_Icc le_rfl t.property.2
    have hi := NLS.FunctionalAnalysis.integral_eq_sub_of_ac_of_ae_hasDerivAt
      (hu.mono (by simpa using hs)) ((continuous_integrand A v).intervalIntegrable 0 t.val) (by
        filter_upwards [hd] with s hds
        intro hst
        have hs' := hs hst
        simpa only [integrand,extend,projIcc_of_mem _ hs',v,ContinuousMap.coe_mk] using hds hs')
    rw [hi]
    change u t = u 0 + (u t-u 0)
    abel
  have he : v = solutionCurve A (u 0) :=
    (existsUnique_solution A (u 0)).unique hv (solutionCurve_eq A (u 0))
  intro t ht
  have he' := congrArg (fun v : Curve E => v ⟨t,ht⟩) he
  simpa only [v,ContinuousMap.coe_mk,← solution_coe] using he'

/-- With continuous coefficients, an absolutely continuous almost-everywhere solution is classical in the interior. -/
theorem hasDerivAt_of_ac_solution (A : Curve (E →L[ℝ] E)) (u : ℝ → E)
    (hu : AbsolutelyContinuousOnInterval u 0 1)
    (hd : ∀ᵐ s : ℝ, s ∈ Icc (0 : ℝ) 1 → HasDerivAt u (extend A s (u s)) s)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : HasDerivAt u (extend A t (u t)) t := by
  have he := solution_unique_of_ac A u hu hd
  have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le,ht.2.le⟩
  have hn : u =ᶠ[𝓝 t] solution A (u 0) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact he ⟨hs.1.le,hs.2.le⟩
  have h := (hasDerivAt_solution_coe A (u 0) ⟨t,ht'⟩).congr_of_eventuallyEq hn
  simpa only [extend,projIcc_of_mem _ ht',← he ht'] using h

end NLS.LinearVolterra
