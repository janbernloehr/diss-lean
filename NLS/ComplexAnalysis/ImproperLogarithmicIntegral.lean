import NLS.ComplexAnalysis.ImproperPrimitivePathIntegral
import NLS.ComplexAnalysis.NormalizedLogChart
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Complex.CoveringMap

/-!
# Improper logarithmic integrals without absolute integrability

A nonvanishing continuous coordinate along a closed parameter interval
has a continuous logarithm. Its logarithmic derivative therefore has an
improper integral with independently varying endpoint cutoffs.
-/

noncomputable section
open Set Filter Topology Complex MeasureTheory
open scoped unitInterval
namespace NLS.ComplexAnalysis

/-- Lift a nonvanishing coordinate to a logarithm, including both endpoints. -/
theorem exists_continuous_log_on_unit_interval (g : ℝ → ℂ)
    (hg : ContinuousOn g (Icc (0:ℝ) 1)) (hne : ∀ t ∈ Icc (0:ℝ) 1, g t ≠ 0) :
    ∃ F : ℝ → ℂ, Continuous F ∧ ∀ t ∈ Icc (0:ℝ) 1, Complex.exp (F t) = g t := by
  have hgc : Continuous (fun t : I => g (t:ℝ)) := continuousOn_iff_continuous_domRestrict.mp hg
  let γ : C(I,{z : ℂ // z ≠ 0}) := ⟨fun t => ⟨g t,hne t t.property⟩,hgc.subtype_mk _⟩
  obtain ⟨G,hG,_⟩ := Complex.isCoveringMap_exp.exists_path_lifts γ (Complex.log (g 0))
    (Subtype.ext (Complex.exp_log (hne 0 (by norm_num))).symm)
  let L : Path (G 0) (G 1) := ⟨G,rfl,rfl⟩
  refine ⟨L.extend,L.continuous_extend,?_⟩
  intro t ht
  rw [Path.extend_apply _ ht]
  exact congrArg Subtype.val (congrFun hG ⟨t,ht⟩)

/-- The actual truncated integrals converge and satisfy the endpoint exponential identity. -/
theorem exists_improper_integral_of_logarithmic_derivative
    (q g : ℝ → ℂ) (hq : ContinuousOn q (Ioo (0:ℝ) 1))
    (hg : ContinuousOn g (Icc (0:ℝ) 1)) (hne : ∀ t ∈ Icc (0:ℝ) 1, g t ≠ 0)
    (hgd : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt g (q t*g t) t) :
    ∃ L : ℂ, Tendsto (fun u : ℝ × ℝ => ∫ t in u.1..u.2, q t)
      ((𝓝[>] (0:ℝ)) ×ˢ (𝓝[<] (1:ℝ))) (𝓝 L) ∧ Complex.exp L*g 0 = g 1 := by
  obtain ⟨F,hF,he⟩ := exists_continuous_log_on_unit_interval g hg hne
  have hd (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) : HasDerivAt F (q t) t := by
    have htcc := Ioo_subset_Icc_self ht
    have hevent : (fun x => Complex.exp (F x)) =ᶠ[𝓝 t] g := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
      exact he x (Ioo_subset_Icc_self hx)
    have hmatch := normalizedLogChart_eventually_eq g F t hF.continuousAt hevent
    have hslit : g t/g t ∈ slitPlane := by rw [div_self (hne t htcc)]; exact one_mem_slitPlane
    have hh := ((Complex.hasDerivAt_log hslit).scomp t ((hgd t ht).div_const (g t))).const_add (F t)
    have hnorm : HasDerivAt (normalizedLogChart g t (F t)) (q t) t := by
      convert! hh using 1
      simp [smul_eq_mul, hne t htcc]
    exact hnorm.congr_of_eventuallyEq hmatch.symm
  refine ⟨F 1-F 0,tendsto_intervalIntegral_of_primitive_limits q F hq hd
    ((hF.tendsto 0).mono_left nhdsWithin_le_nhds)
    ((hF.tendsto 1).mono_left nhdsWithin_le_nhds),?_⟩
  rw [Complex.exp_sub,he 1 (by norm_num),he 0 (by norm_num)]
  exact div_mul_cancel₀ _ (hne 0 (by norm_num))

end NLS.ComplexAnalysis
