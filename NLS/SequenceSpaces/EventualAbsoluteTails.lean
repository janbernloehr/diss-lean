import NLS.SequenceSpaces.UniformHolderSums

/-! Uniform Cauchy convergence needs tail control only beyond one cutoff. -/
noncomputable section
open Filter Topology
namespace NLS.Coeff

theorem uniformCauchySeqOn_sum_of_eventual_absolute_tails {X : Type*}
    (u : X → ℤ → ℂ) (S : Set X) (D : ℕ → ℝ)
    (hD : Tendsto D atTop (𝓝 0)) (K : ℕ)
    (htail : ∀ N : ℕ, K ≤ N → ∀ x ∈ S, ∀ s : Finset ℤ,
      (∀ m ∈ s, N ≤ m.natAbs) → (∑ m ∈ s, ‖u x m‖) ≤ D N) :
    UniformCauchySeqOn
      (fun (N : ℕ) x => ∑ m ∈ Finset.Icc (-(N : ℤ)) N, u x m) atTop S := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hD.eventually (gt_mem_nhds hε))
  let L := max N K
  have hNL : N ≤ L := le_max_left _ _
  have hKL : K ≤ L := le_max_right _ _
  refine ⟨L,fun i hi j hj x hx => ?_⟩
  have hle (a b : ℕ) (hab : a ≤ b) (ha : L ≤ a) :
      dist (∑ m ∈ Finset.Icc (-(b : ℤ)) b, u x m)
        (∑ m ∈ Finset.Icc (-(a : ℤ)) a, u x m) < ε := by
    have hs : Finset.Icc (-(a : ℤ)) a ⊆ Finset.Icc (-(b : ℤ)) b := by
      intro m hm
      simp only [Finset.mem_Icc] at hm ⊢
      constructor <;> omega
    rw [dist_eq_norm, ← Finset.sum_sdiff hs, add_sub_cancel_right]
    apply (norm_sum_le _ _).trans_lt
    apply (htail L hKL x hx _ ?_).trans_lt (hN L hNL)
    intro m hm
    simp only [Finset.mem_sdiff, Finset.mem_Icc] at hm
    omega
  rcases le_total i j with hij | hji
  · rw [dist_comm]
    exact hle i j hij hi
  · exact hle j i hji hj

end NLS.Coeff
