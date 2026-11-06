import NLS.SequenceSpaces.NonnegativeActions
import NLS.SequenceSpaces.Truncation

/-! # Continuity extends agreement from finite nonnegative action data

The distinguished zero entry can be retained exactly while finite
truncations approach every full sequence in norm.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Nonnegative finite truncations retaining the zero coefficient are
dense in the full nonnegative locus at every finite exponent. -/
theorem exists_nonnegative_finite_approximation (hp : p ≠ ⊤) (b : Coeff p)
    (hb : b ∈ nonnegativeLocus p) :
    ∃ q : Finset ℤ → Coeff p, Tendsto q atTop (𝓝 b) ∧
      ∀ S, HasFiniteSupport (q S) ∧ q S ∈ nonnegativeLocus p ∧ q S 0 = b 0 := by
  let q := fun S : Finset ℤ => truncate (S ∪ {0}) b
  have hconv : Tendsto q atTop (𝓝 b) := by
    apply (tendsto_truncate hp b).congr'
    filter_upwards [Filter.eventually_ge_atTop ({0} : Finset ℤ)] with S hS
    simp only [q,Finset.union_eq_left.mpr hS]
  refine ⟨q,hconv,?_⟩
  intro S
  refine ⟨truncate_hasFiniteSupport _ b,?_,?_⟩
  · intro n
    rw [truncate_apply]
    split_ifs
    · exact hb n
    · simp
  · rw [truncate_apply,if_pos (Finset.mem_union_right _ (Finset.mem_singleton_self 0))]

variable {F : Type*} [TopologicalSpace F] [T2Space F]

/-- Two continuous germs agree at a nonnegative point if they agree on
nearby finite nonnegative data with the same zero entry. -/
theorem eq_of_finite_nonnegative_agreement (hp : p ≠ ⊤) (f g : Coeff p → F)
    (U : Set (Coeff p)) (hU : IsOpen U) (b : Coeff p) (hbU : b ∈ U)
    (hb : b ∈ nonnegativeLocus p) (hf : ContinuousAt f b) (hg : ContinuousAt g b)
    (he : ∀ q ∈ U, HasFiniteSupport q → q ∈ nonnegativeLocus p → q 0 = b 0 → f q = g q) :
    f b = g b := by
  obtain ⟨q,hq,hgood⟩ := exists_nonnegative_finite_approximation hp b hb
  have heq : (fun S => f (q S)) =ᶠ[atTop] (fun S => g (q S)) := by
    filter_upwards [hq.eventually (hU.mem_nhds hbU)] with S hS
    exact he (q S) hS (hgood S).1 (hgood S).2.1 (hgood S).2.2
  exact tendsto_nhds_unique ((hf.tendsto.comp hq).congr' heq) (hg.tendsto.comp hq)

end NLS.Coeff
