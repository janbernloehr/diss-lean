import NLS.SequenceSpaces.WeightedFrequencyRemainders

/-! Finitely many continuous frequency coordinates extend a locally
uniform tail bound to every positive label on a common neighborhood. -/
noncomputable section
open Set Filter Topology
namespace NLS.Coeff

theorem exists_uniform_all_frequency_bound_of_tail
    {E : Type*} [TopologicalSpace E] (U : Set E) (hU : IsOpen U) (a₀ : E) (ha₀ : a₀∈U)
    (f : ℕ+ → E → ℂ) (hf : ∀ n, ContinuousOn (f n) U)
    (w : ℤ → ℝ) (hw : ∀ n : ℕ+, 0≤w (n:ℤ)) (K : ℕ) (M : ℝ) (hM : 0≤M)
    (hb : ∀ a∈U, ∀ n : ℕ+, K≤(n:ℤ).natAbs → w (n:ℤ)*‖f n a‖≤M) :
    ∃ T : Set E, IsOpen T ∧ a₀∈T ∧ T⊆U ∧ ∃ B : ℝ, 0≤B ∧
      ∀ a∈T, ∀ n : ℕ+, w (n:ℤ)*‖f n a‖≤B := by
  classical
  let g := fun j : ℕ => fun a : E => w ((j+1:ℕ):ℤ)*‖f ⟨j+1,by omega⟩ a‖
  let H := (∑ j∈Finset.range K, g j a₀)+1
  have hg0 (j : ℕ) : 0≤g j a₀ := mul_nonneg (hw ⟨j+1,by omega⟩) (norm_nonneg _)
  have hhead : ∀ᶠ a in 𝓝 a₀, ∀ j∈Finset.range K, g j a≤H := by
    rw [Finset.eventually_all]
    intro j hj
    have hc : ContinuousAt (g j) a₀ :=
      ((hf ⟨j+1,by omega⟩).continuousAt (hU.mem_nhds ha₀)).norm.const_mul _
    filter_upwards [hc.eventually_lt_const (lt_add_one (g j a₀))] with a ha
    have hs : g j a₀≤∑ i∈Finset.range K, g i a₀ := Finset.single_le_sum (fun i _ => hg0 i) hj
    exact ha.le.trans (by dsimp only [H];linarith)
  have hev : ∀ᶠ a in 𝓝 a₀, a∈U ∧ ∀ j∈Finset.range K, g j a≤H :=
    Filter.Eventually.and (hU.mem_nhds ha₀) hhead
  obtain ⟨T,hTU,hT,haT⟩ := _root_.mem_nhds_iff.mp hev
  refine ⟨T,hT,haT,(fun a ha => (hTU ha).1),max M H,hM.trans (le_max_left _ _),?_⟩
  intro a ha n
  have hn0 := n.pos
  by_cases hn : K≤(n:ℤ).natAbs
  · exact (hb a (hTU ha).1 n hn).trans (le_max_left _ _)
  · let j := (n:ℕ)-1
    have hj : j∈Finset.range K := by simp only [Finset.mem_range];change (n:ℕ)-1<K;simp only [Int.natAbs_natCast] at hn;omega
    have he : (⟨j+1,by omega⟩:ℕ+)=n := by apply Subtype.ext;change (n:ℕ)-1+1=(n:ℕ);omega
    have h := (hTU ha).2 j hj
    change w (((⟨j+1,by omega⟩:ℕ+):ℤ))*‖f ⟨j+1,by omega⟩ a‖≤H at h
    rw [he] at h
    exact h.trans (le_max_right _ _)

end NLS.Coeff
