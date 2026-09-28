import NLS.SequenceSpaces.Compact
import Mathlib.Topology.Sequences

/-!
# Subsequences from uniformly small coefficient tails

Finite Fourier truncations are compact operators. A bounded sequence
whose tails become uniformly small after a finite initial block is
therefore totally bounded and has a norm-convergent subsequence.
-/

noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.Coeff

/-- A bounded `ℓᵖ` sequence with eventually uniformly small finite
tails has a norm-convergent subsequence. -/
theorem exists_tendsto_subseq_of_bounded_uniform_tails
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (a : ℕ → Coeff p)
    (hbounded : Bornology.IsBounded (range a))
    (htail : ∀ ε : ℝ, 0 < ε →
      ∃ s : Finset ℤ, ∃ N : ℕ,
        ∀ k : ℕ, N ≤ k →
          ‖a k-truncate s (a k)‖ ≤ ε) :
    ∃ b : Coeff p, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (a ∘ φ) atTop (𝓝 b) := by
  classical
  have htot : TotallyBounded (range a) := by
    apply Metric.totallyBounded_iff.mpr
    intro ε hε
    obtain ⟨s,N,hs⟩ := htail (ε/2) (half_pos hε)
    let K : Set (Coeff p) := closure ((truncateCLM (p := p) s) '' range a)
    have hK : IsCompact K :=
      (isCompactOperator_truncateCLM (p := p) s).isCompact_closure_image_of_bounded
        hbounded
    obtain ⟨t,htfinite,htcover⟩ :=
      Metric.totallyBounded_iff.mp hK.totallyBounded (ε/2) (half_pos hε)
    let initial : Set (Coeff p) := a '' (Finset.range N : Set ℕ)
    have hinitial : initial.Finite :=
      (Finset.finite_toSet (Finset.range N)).image a
    refine ⟨t ∪ initial,htfinite.union hinitial,?_⟩
    intro x hx
    obtain ⟨k,rfl⟩ := hx
    by_cases hk : k < N
    · have hi : a k ∈ initial :=
        ⟨k,Finset.mem_range.mpr hk,rfl⟩
      simp only [mem_iUnion]
      exact ⟨a k,Or.inr hi,mem_ball_self hε⟩
    · have htrunc : truncate s (a k) ∈ K :=
        subset_closure ⟨a k,⟨k,rfl⟩,rfl⟩
      have hcov := htcover htrunc
      simp only [mem_iUnion] at hcov ⊢
      obtain ⟨y,hy,hnear⟩ := hcov
      refine ⟨y,Or.inl hy,?_⟩
      have htailk := hs k (Nat.le_of_not_gt hk)
      have htri := dist_triangle (a k) (truncate s (a k)) y
      rw [mem_ball] at hnear ⊢
      have hdist : dist (a k) (truncate s (a k)) ≤ ε/2 := by
        simpa only [dist_eq_norm] using htailk
      linarith
  have hcompact : IsCompact (closure (range a)) :=
    htot.closure.isCompact_of_isClosed isClosed_closure
  obtain ⟨b,_,φ,hφ,htend⟩ :=
    hcompact.tendsto_subseq (fun k => subset_closure ⟨k,rfl⟩)
  exact ⟨b,φ,hφ,htend⟩

end NLS.Coeff
