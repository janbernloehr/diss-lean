import NLS.DifferentialPolynomial.RealMonomialBounds

/-! # Selecting two factors from a finite monomial

Selection allows repetition of an index. This uniformly covers the two
factorization cases in the proof of Lemma 26.3.
-/
noncomputable section
namespace NLS.DifferentialPolynomial

/-- A monomial of degree at least two can be split into two selected factors
and a nonnegative residual multi-index, even when both selected indices coincide. -/
theorem exists_two_factor_split {ι : Type*} [DecidableEq ι] (S : Finset ι) (μ : ι → ℕ)
    (hμ : 2 ≤ ∑ i ∈ S, μ i) :
    ∃ i ∈ S, ∃ j ∈ S, ∃ ν : ι → ℕ,
      ∀ k ∈ S, μ k = ν k+(if k=i then 1 else 0)+(if k=j then 1 else 0) := by
  classical
  obtain ⟨i,hi,hpos⟩ := (Finset.sum_pos_iff_of_nonneg (fun k _ => Nat.zero_le (μ k))).mp (by omega : 0 < ∑ k ∈ S, μ k)
  let μ₁ := fun k => μ k-(if k=i then 1 else 0)
  have he (k : ι) : μ k = μ₁ k+(if k=i then 1 else 0) := by
    dsimp only [μ₁]
    by_cases hk : k=i
    · subst k; simp only [↓reduceIte]; omega
    · simp [hk]
  have hs : (∑ k ∈ S, μ k) = (∑ k ∈ S, μ₁ k)+1 := by
    calc
      _ = ∑ k ∈ S, (μ₁ k+(if k=i then 1 else 0)) := Finset.sum_congr rfl (fun k _ => he k)
      _ = _ := by rw [Finset.sum_add_distrib]; simp [hi]
  obtain ⟨j,hj,hposj⟩ := (Finset.sum_pos_iff_of_nonneg (fun k _ => Nat.zero_le (μ₁ k))).mp (by omega : 0 < ∑ k ∈ S, μ₁ k)
  refine ⟨i,hi,j,hj,fun k => μ₁ k-(if k=j then 1 else 0),?_⟩
  intro k _
  rw [he k]
  by_cases hk : k=j
  · subst k; simp only [↓reduceIte]; omega
  · simp [hk]

/-- The split extracts exactly two factors from the actual product. -/
theorem prod_pow_two_factor_split {ι : Type*} [DecidableEq ι] (S : Finset ι) (μ ν : ι → ℕ)
    (i j : ι) (hi : i ∈ S) (hj : j ∈ S)
    (hμ : ∀ k ∈ S, μ k = ν k+(if k=i then 1 else 0)+(if k=j then 1 else 0)) (f : ι → ℝ) :
    (∏ k ∈ S, f k^μ k) = (∏ k ∈ S, f k^ν k)*f i*f j := by
  classical
  calc
    _ = ∏ k ∈ S, (f k^ν k*f k^(if k=i then 1 else 0)*f k^(if k=j then 1 else 0)) := by
      apply Finset.prod_congr rfl
      intro k hk
      rw [hμ k hk,pow_add,pow_add]
    _ = _ := by
      rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib]
      simp [hi,hj]

/-- The split preserves every weighted sum and records the two removed weights. -/
theorem sum_weight_two_factor_split {ι : Type*} [DecidableEq ι] (S : Finset ι) (μ ν : ι → ℕ)
    (i j : ι) (hi : i ∈ S) (hj : j ∈ S)
    (hμ : ∀ k ∈ S, μ k = ν k+(if k=i then 1 else 0)+(if k=j then 1 else 0)) (w : ι → ℝ) :
    (∑ k ∈ S, w k*μ k) = (∑ k ∈ S, w k*ν k)+w i+w j := by
  classical
  calc
    _ = ∑ k ∈ S, (w k*ν k+w k*(if k=i then 1 else 0)+w k*(if k=j then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hμ k hk]
      push_cast
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
      simp [hi,hj,mul_ite]

end NLS.DifferentialPolynomial
