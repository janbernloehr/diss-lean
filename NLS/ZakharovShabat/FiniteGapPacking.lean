import NLS.ZakharovShabat.M1CanonicalGap
import NLS.SequenceSpaces.SpectralWeightInterpolation

/-! # Finite ordered gap estimates

Ordered disjoint intervals in a bounded real interval have total length at
most the enclosing width. The same budget controls real gaps, or complex
gaps whose endpoints lie in the corresponding real-centered discs.
-/
noncomputable section
open scoped Classical
namespace NLS.ZakharovShabat

/-- A finite ordered family of nonoverlapping intervals fits in its enclosing interval. -/
theorem sum_ordered_interval_lengths_le (s : Finset ℤ) (x y : ℤ → ℝ) (a b : ℝ)
    (hab : a ≤ b) (hb : ∀ i ∈ s, a ≤ x i ∧ x i ≤ y i ∧ y i ≤ b)
    (ho : ∀ i ∈ s, ∀ j ∈ s, i < j → y i ≤ x j) :
    ∑ i ∈ s, (y i-x i) ≤ b-a := by
  induction s using Finset.induction_on_min generalizing a with
  | empty => simpa using sub_nonneg.mpr hab
  | insert i s hi ih =>
    have hi' : i ∉ s := fun h => (lt_irrefl i) (hi i h)
    have hbi := hb i (Finset.mem_insert_self _ _)
    have hs := ih (y i) hbi.2.2
      (fun j hj => ⟨ho i (by simp) j (by simp [hj]) (hi j hj),
        (hb j (by simp [hj])).2⟩)
      (fun j hj k hk hjk => ho j (by simp [hj]) k (by simp [hk]) hjk)
    rw [Finset.sum_insert hi']
    linarith

/-- Squared lengths cost at most the square of the total enclosing width. -/
theorem sum_ordered_interval_sq_le (s : Finset ℤ) (x y : ℤ → ℝ) (a b : ℝ)
    (hab : a ≤ b) (hb : ∀ i ∈ s, a ≤ x i ∧ x i ≤ y i ∧ y i ≤ b)
    (ho : ∀ i ∈ s, ∀ j ∈ s, i < j → y i ≤ x j) :
    ∑ i ∈ s, (y i-x i)^2 ≤ (b-a)^2 := by
  have hn : ∀ i ∈ s, 0 ≤ y i-x i := fun i hi => sub_nonneg.mpr (hb i hi).2.1
  exact (Finset.sum_sq_le_sq_sum_of_nonneg hn).trans
    (pow_le_pow_left₀ (Finset.sum_nonneg hn) (sum_ordered_interval_lengths_le s x y a b hab hb ho) 2)

/-- Ordered real-centered discs bound even complex gap lengths by their total diameter.
The enclosing interval and ordering are explicit hypotheses, not consequences of
pairwise disjointness alone. -/
theorem sum_gap_sq_le_of_ordered_discs (s : Finset ℤ) (ξ η : ℤ → ℂ)
    (c r : ℤ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hr : ∀ i ∈ s, 0 ≤ r i)
    (hb : ∀ i ∈ s, a ≤ c i-r i ∧ c i+r i ≤ b)
    (ho : ∀ i ∈ s, ∀ j ∈ s, i < j → c i+r i ≤ c j-r j)
    (hx : ∀ i ∈ s, ‖ξ i-(c i : ℂ)‖ ≤ r i)
    (hy : ∀ i ∈ s, ‖η i-(c i : ℂ)‖ ≤ r i) :
    ∑ i ∈ s, ‖η i-ξ i‖^2 ≤ (b-a)^2 := by
  apply le_trans (Finset.sum_le_sum (fun i hi => ?_))
    (sum_ordered_interval_sq_le s (fun i => c i-r i) (fun i => c i+r i) a b hab
      (fun i hi => ⟨(hb i hi).1,by linarith [hr i hi],(hb i hi).2⟩) ho)
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  have h := norm_sub_le_norm_sub_add_norm_sub (η i) (c i : ℂ) (ξ i)
  rw [norm_sub_rev (c i : ℂ) (ξ i)] at h
  linarith [hx i hi,hy i hi]

/-- The interpolated weight converts an unweighted finite gap budget into the source weight. -/
theorem weighted_finite_gap_sq_le (w : SpectralWeight) (s : Finset ℤ) (γ : ℤ → ℂ)
    (t B : ℝ) (ht : ∀ n ∈ s, |((2*n : ℤ) : ℝ)| ≤ t)
    (hB : ∑ n ∈ s, ‖γ n‖^2 ≤ B) :
    ∑ n ∈ s, (w (2*n)*‖γ n‖)^2 ≤ w.realExtension t^2*B := by
  calc
    _ ≤ ∑ n ∈ s, w.realExtension t^2*‖γ n‖^2 := by
      apply Finset.sum_le_sum
      intro n hn
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (w.positive _).le (w.le_realExtension (2*n) t (ht n hn)) 2) (sq_nonneg _)
    _ = w.realExtension t^2*(∑ n ∈ s, ‖γ n‖^2) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hB (sq_nonneg _)

end NLS.ZakharovShabat
