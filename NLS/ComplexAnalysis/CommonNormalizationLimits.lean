import Mathlib.Analysis.Complex.Liouville
import Mathlib.Topology.Algebra.Field

/-!
# Comparing functions with the same asymptotic normalization

An eventual nonzero denominator follows from its normalized limit one.
The comparison also applies to a quotient filled in at common zeros.
-/

noncomputable section
open Filter Topology
namespace NLS.ComplexAnalysis

theorem eventually_ne_zero_of_div_tendsto_one {α : Type*} {l : Filter α}
    (g h : α → ℂ) (hg : Tendsto (fun i => g i / h i) l (𝓝 1)) :
    ∀ᶠ i in l, g i ≠ 0 ∧ h i ≠ 0 := by
  filter_upwards [hg.eventually_ne one_ne_zero] with i hi
  exact div_ne_zero_iff.mp hi

/-- Any extension of ordinary division across denominator zeros has limit one
when numerator and denominator share a normalization with limit one. -/
theorem tendsto_filled_quotient_of_common_normalization {α : Type*} {l : Filter α}
    (f g h q : α → ℂ)
    (hf : Tendsto (fun i => f i / h i) l (𝓝 1))
    (hg : Tendsto (fun i => g i / h i) l (𝓝 1))
    (hq : ∀ i, g i ≠ 0 → q i = f i / g i) :
    Tendsto q l (𝓝 1) := by
  have hr := hf.div hg (one_ne_zero : (1 : ℂ) ≠ 0)
  change Tendsto (fun i => (f i / h i) / (g i / h i)) l (𝓝 ((1 : ℂ)/1)) at hr
  have he : (fun i => (f i / h i) / (g i / h i)) =ᶠ[l] q := by
    filter_upwards [eventually_ne_zero_of_div_tendsto_one g h hg] with i hi
    rw [hq i hi.1, div_div_div_cancel_right₀ hi.2]
  have hr' : Tendsto (fun i => (f i / h i) / (g i / h i)) l (𝓝 1) := by
    simpa only [div_one] using hr
  exact hr'.congr' he

/-- A bounded entire function is fixed by its limit along any nontrivial filter. -/
theorem eq_const_of_bounded_entire_of_tendsto_path {α : Type*} {l : Filter α} [NeBot l]
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hb : Bornology.IsBounded (Set.range f))
    (z : α → ℂ) (c : ℂ) (hl : Tendsto (fun i => f (z i)) l (𝓝 c)) : ∀ w, f w = c := by
  obtain ⟨d, hd⟩ := hf.exists_const_forall_eq_of_bounded hb
  have hlim : Tendsto (fun _ : α => d) l (𝓝 c) := by simpa only [hd] using hl
  have he : d = c := tendsto_nhds_unique tendsto_const_nhds hlim
  intro w
  exact (hd w).trans he

end NLS.ComplexAnalysis
