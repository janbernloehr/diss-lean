import NLS.SequenceSpaces.UniformFrequencyFiniteHeads

/-! Local bounds for all frequency coordinates give one bound on an
entire compact source set by a finite open cover. -/
noncomputable section
open Set
namespace NLS.Coeff

theorem exists_uniform_frequency_bound_on_compact
    {E : Type*} [TopologicalSpace E] (K : Set E) (hK : IsCompact K)
    (f : ℕ+ → E → ℂ) (w : ℤ → ℝ)
    (hloc : ∀ a∈K, ∃ U : Set E, IsOpen U ∧ a∈U ∧ ∃ B : ℝ, 0≤B ∧
      ∀ b∈U, ∀ n : ℕ+, w (n:ℤ)*‖f n b‖≤B) :
    ∃ B : ℝ, 0≤B ∧ ∀ a∈K, ∀ n : ℕ+, w (n:ℤ)*‖f n a‖≤B := by
  classical
  choose U hU haU B hB hb using fun a : K => hloc a.val a.property
  obtain ⟨S,hS⟩ := hK.elim_finite_subcover U hU (by
    intro a ha
    exact mem_iUnion.mpr ⟨⟨a,ha⟩,haU ⟨a,ha⟩⟩)
  refine ⟨∑ i∈S, B i,Finset.sum_nonneg (fun i _ => hB i),?_⟩
  intro a ha n
  obtain ⟨i,hiS,hai⟩ := mem_iUnion₂.mp (hS ha)
  exact (hb i a hai n).trans (Finset.single_le_sum (fun j _ => hB j) hiS)

end NLS.Coeff
