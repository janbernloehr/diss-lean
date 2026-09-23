import NLS.SequenceSpaces.FiniteExponentTail

/-!
# Uniform tails of weighted lattice rows

A summable nonnegative kernel gives uniformly small translated rows
when the input weights are uniformly small outside one finite block.
The finite block is controlled by cofinite decay of each translated
kernel coordinate.
-/

noncomputable section
open Filter
namespace NLS

/-- Uniform control of a translated weighted row from a global weight
bound and a smaller bound outside one finite set. -/
theorem exists_uniform_weighted_row_bound {X : Type*}
    (b : ℤ → ℝ) (hb : Summable b) (hb0 : ∀ k, 0 ≤ b k)
    (s : Finset ℤ) (R η θ : ℝ) (hR : 0 ≤ R) (hη : 0 ≤ η) (hθ : 0 < θ)
    (a : X → ℤ → ℝ)
    (ha0 : ∀ x m, 0 ≤ a x m)
    (haR : ∀ x m, a x m ≤ R)
    (haη : ∀ x m, m ∉ s → a x m ≤ η) :
    ∃ K : ℕ, ∀ x : X, ∀ n : ℤ, K ≤ n.natAbs →
      (∑' m : ℤ, a x m * b (m-n)) ≤
        η*(∑' k : ℤ, b k) + (s.card:ℝ)*R*θ := by
  have hkernel (m : ℤ) : Summable (fun n : ℤ => b (m-n)) := by
    change Summable (b ∘ (Equiv.subLeft m))
    exact (Equiv.subLeft m).summable_iff.mpr hb
  have hevent : ∀ᶠ n : ℤ in cofinite, ∀ m ∈ s, b (m-n) < θ := by
    rw [Finset.eventually_all]
    intro m _
    exact (hkernel m).tendsto_cofinite_zero.eventually_lt_const hθ
  obtain ⟨K,hK⟩ := exists_natAbs_ge_of_eventually_cofinite hevent
  refine ⟨K,?_⟩
  intro x n hn
  have hnθ := hK n hn
  have hshift : Summable (fun m : ℤ => b (m-n)) := by
    change Summable (b ∘ (Equiv.addRight (-n)))
    exact (Equiv.addRight (-n)).summable_iff.mpr hb
  have hrow : Summable (fun m : ℤ => a x m*b (m-n)) :=
    (hshift.mul_left R).of_nonneg_of_le
      (fun m => mul_nonneg (ha0 x m) (hb0 _))
      (fun m => mul_le_mul_of_nonneg_right (haR x m) (hb0 _))
  have hsmall : Summable (fun m : ℤ => η*b (m-n)) := hshift.mul_left η
  have hfinite : Summable (fun m : ℤ => if m ∈ s then R*b (m-n) else 0) :=
    summable_of_ne_finset_zero (s := s) (fun m hm => by simp [hm])
  have hpoint (m : ℤ) : a x m*b (m-n) ≤
      η*b (m-n) + (if m ∈ s then R*b (m-n) else 0) := by
    by_cases hm : m ∈ s
    · rw [if_pos hm]
      have hle := mul_le_mul_of_nonneg_right (haR x m) (hb0 (m-n))
      nlinarith [mul_nonneg hη (hb0 (m-n))]
    · rw [if_neg hm, add_zero]
      exact mul_le_mul_of_nonneg_right (haη x m hm) (hb0 (m-n))
  have hshift_sum : (∑' m : ℤ, b (m-n)) = ∑' k : ℤ, b k := by
    simpa [sub_eq_add_neg] using (Equiv.addRight (-n)).tsum_eq b
  have hfinite_sum :
      (∑' m : ℤ, if m ∈ s then R*b (m-n) else 0) =
        ∑ m ∈ s, R*b (m-n) := by
    rw [tsum_eq_sum (s := s) (fun m hm => by simp [hm])]
    apply Finset.sum_congr rfl
    intro m hm
    simp [hm]
  calc
    (∑' m : ℤ, a x m*b (m-n)) ≤
        ∑' m : ℤ, (η*b (m-n) +
          (if m ∈ s then R*b (m-n) else 0)) :=
            Summable.tsum_le_tsum hpoint hrow (hsmall.add hfinite)
    _ = η*(∑' k : ℤ, b k) + ∑ m ∈ s, R*b (m-n) := by
      rw [Summable.tsum_add hsmall hfinite, tsum_mul_left,
        hshift_sum, hfinite_sum]
    _ ≤ η*(∑' k : ℤ, b k) + ∑ m ∈ s, R*θ := by
      apply add_le_add_right
      apply Finset.sum_le_sum
      intro m hm
      exact mul_le_mul_of_nonneg_left (hnθ m hm).le hR
    _ = η*(∑' k : ℤ, b k) + (s.card:ℝ)*R*θ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

end NLS
