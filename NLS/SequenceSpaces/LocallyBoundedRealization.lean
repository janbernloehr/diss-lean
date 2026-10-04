import NLS.SequenceSpaces.FunctionOrZero
import NLS.SequenceSpaces.BoundedCoordinateAnalytic

/-! # Analytic realization of locally bounded scalar sequences

Local norm bounds for actual coefficient sequences identify the total
constructor and upgrade scalar coordinate analyticity to Banach analyticity.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {r : ℝ≥0∞} [Fact (1 ≤ r)]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

omit [Fact (1 ≤ r)] in
/-- The total constructor agrees with any sequence realizing its coordinates. -/
theorem ofFunctionOrZero_eq_of_coordinates (f : ℤ → ℂ) (b : Coeff r)
    (hb : ∀ n, b n = f n) : ofFunctionOrZero r f = b := by
  have hmem : Memℓp f r := by
    have he : (fun n => b n) = f := funext hb
    rw [← he]
    exact lp.memℓp b
  ext n
  exact (ofFunctionOrZero_apply_of_mem r f hmem n).trans (hb n).symm

/-- Local realizations with uniform norm bounds give the actual analytic
sequence map on an open parameter domain. -/
theorem analytic_realization_of_local_bounds (f : E → ℤ → ℂ) {U : Set E}
    (hU : IsOpen U) (ha : ∀ n, AnalyticOnNhd ℂ (fun ψ => f ψ n) U)
    (hb : ∀ φ ∈ U, ∃ T : Set E, IsOpen T ∧ φ ∈ T ∧ T ⊆ U ∧
      ∃ C : ℝ, ∀ ψ ∈ T, ∃ b : Coeff r, (∀ n, b n = f ψ n) ∧ ‖b‖ ≤ C) :
    (∀ ψ ∈ U, ∀ n, ofFunctionOrZero r (f ψ) n = f ψ n) ∧
      AnalyticOnNhd ℂ (fun ψ => ofFunctionOrZero r (f ψ)) U := by
  have he (ψ : E) (hψ : ψ ∈ U) (n : ℤ) : ofFunctionOrZero r (f ψ) n = f ψ n := by
    obtain ⟨T,_,hψT,_,_,hb⟩ := hb ψ hψ
    obtain ⟨b,hb,_⟩ := hb ψ hψT
    rw [ofFunctionOrZero_eq_of_coordinates _ b hb]
    exact hb n
  refine ⟨he,?_⟩
  intro φ hφ
  obtain ⟨T,hT,hφT,hTU,C,hb⟩ := hb φ hφ
  have hc (n : ℤ) : AnalyticOnNhd ℂ (fun ψ => ofFunctionOrZero r (f ψ) n) T := by
    intro ψ hψ
    apply (ha n ψ (hTU hψ)).congr
    filter_upwards [hU.mem_nhds (hTU hψ)] with χ hχ
    exact (he χ hχ n).symm
  apply analyticOnNhd_of_bounded_coordinatewise _ hT hc C _ φ hφT
  intro ψ hψ
  obtain ⟨b,hb,hbn⟩ := hb ψ hψ
  rwa [ofFunctionOrZero_eq_of_coordinates _ b hb]

end NLS.Coeff
