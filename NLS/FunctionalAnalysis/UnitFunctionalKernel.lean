import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! A unit vector in the kernel of an actual complex functional on a
space of dimension at least two. -/
noncomputable section
namespace NLS.FunctionalAnalysis

/-- Every scalar trace on a finite dimensional space of dimension above one
has an ACTUAL norm-one zero-trace vector. -/
theorem exists_unit_mem_functional_kernel {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (hE : 1 < Module.finrank ℂ E) (L : E →L[ℂ] ℂ) :
    ∃ x : E, ‖x‖=1 ∧ L x=0 := by
  have hker : L.ker ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt
    (f := L.toLinearMap) (by simpa only [Module.finrank_self] using hE)
  obtain ⟨x,hx,hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
  refine ⟨(‖x‖:ℂ)⁻¹ • x,?_,?_⟩
  · rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),inv_mul_cancel₀ hnorm]
  · rw [map_smul,show L x=0 from hx,smul_zero]

end NLS.FunctionalAnalysis
