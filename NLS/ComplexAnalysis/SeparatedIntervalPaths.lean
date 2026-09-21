import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

/-! # Preserving indices in moving separated intervals
Midpoints between neighboring intervals cannot be crossed by a continuous
selection from their union. Thus an initial interval index stays fixed,
even if individual intervals collapse to points.
-/

open Set
namespace NLS.ComplexAnalysis

/-- Ordered separated intervals have monotone lower and upper endpoints. -/
theorem monotone_endpoints_of_separated (L R : ℤ → ℝ) (hLR : ∀ n, L n ≤ R n)
    (hsep : ∀ i j, i < j → R i < L j) : Monotone L ∧ Monotone R := by
  constructor <;> intro i j hij
  · rcases lt_or_eq_of_le hij with h | rfl
    · exact (hLR i).trans (hsep i j h).le
    · rfl
  · rcases lt_or_eq_of_le hij with h | rfl
    · exact (hsep i j h).le.trans (hLR j)
    · rfl

/-- No point in the union can lie at the midpoint between two consecutive intervals. -/
theorem ne_separating_midpoint_of_mem_union (L R : ℤ → ℝ) (hLR : ∀ n, L n ≤ R n)
    (hsep : ∀ i j, i < j → R i < L j) (y : ℝ) (hy : ∃ k, y ∈ Icc (L k) (R k)) (n : ℤ) :
    y ≠ (R (n-1)+L n)/2 := by
  obtain ⟨k,hk⟩ := hy
  have hm := monotone_endpoints_of_separated L R hLR hsep
  have hs := hsep (n-1) n (by omega)
  intro he
  by_cases hkn : k < n
  · have hb := hk.2.trans (hm.2 (show k ≤ n-1 by omega))
    linarith
  · have hb := (hm.1 (show n ≤ k by omega)).trans hk.1
    linarith

/-- Two neighboring midpoints identify the original index of a point in the union. -/
theorem mem_interval_of_between_separating_midpoints (L R : ℤ → ℝ) (hLR : ∀ n, L n ≤ R n)
    (hsep : ∀ i j, i < j → R i < L j) (y : ℝ) (hy : ∃ k, y ∈ Icc (L k) (R k)) (n : ℤ)
    (hlo : (R (n-1)+L n)/2 < y) (hhi : y < (R n+L (n+1))/2) : y ∈ Icc (L n) (R n) := by
  obtain ⟨k,hk⟩ := hy
  have hm := monotone_endpoints_of_separated L R hLR hsep
  have he : k = n := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hn | hn
    · have hb := hk.2.trans (hm.2 (show k ≤ n-1 by omega))
      have hs := hsep (n-1) n (by omega)
      linarith
    · have hb := (hm.1 (show n+1 ≤ k by omega)).trans hk.1
      have hs := hsep n (n+1) (by omega)
      linarith
  simpa only [he] using hk

/-- A continuous real function initially positive and nowhere zero stays positive on an interval. -/
theorem positive_on_Icc_of_ne_zero (f : ℝ → ℝ) {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (ha : 0 < f a) (hne : ∀ t ∈ Icc a b, f t ≠ 0) :
    ∀ t ∈ Icc a b, 0 < f t := by
  intro t ht
  by_contra hpos
  obtain ⟨s,hs,he⟩ := intermediate_value_Icc' ht.1
    (hf.mono (Icc_subset_Icc le_rfl ht.2)) (show 0 ∈ Icc (f t) (f a) from ⟨le_of_not_gt hpos,ha.le⟩)
  exact hne s ⟨hs.1,hs.2.trans ht.2⟩ he

/-- A continuous selection from separated moving intervals retains its initial signed index. -/
theorem mem_interval_on_Icc_of_separated (L R : ℝ → ℤ → ℝ) (y : ℝ → ℝ) {a b : ℝ}
    (hab : a ≤ b) (hL : ∀ n, ContinuousOn (fun t => L t n) (Icc a b))
    (hR : ∀ n, ContinuousOn (fun t => R t n) (Icc a b)) (hy : ContinuousOn y (Icc a b))
    (hLR : ∀ t ∈ Icc a b, ∀ n, L t n ≤ R t n)
    (hsep : ∀ t ∈ Icc a b, ∀ i j, i < j → R t i < L t j)
    (hmem : ∀ t ∈ Icc a b, ∃ k, y t ∈ Icc (L t k) (R t k))
    (n : ℤ) (ha : y a ∈ Icc (L a n) (R a n)) :
    ∀ t ∈ Icc a b, y t ∈ Icc (L t n) (R t n) := by
  let m : ℤ → ℝ → ℝ := fun k t => (R t (k-1)+L t k)/2
  have hm (k : ℤ) : ContinuousOn (m k) (Icc a b) := ((hR (k-1)).add (hL k)).div_const 2
  have hn (k : ℤ) (t : ℝ) (ht : t ∈ Icc a b) : y t ≠ m k t :=
    ne_separating_midpoint_of_mem_union (L t) (R t) (hLR t ht) (hsep t ht) (y t) (hmem t ht) k
  have hlo := positive_on_Icc_of_ne_zero (fun t => y t-m n t) (hy.sub (hm n))
    (by dsimp [m]; have hs := hsep a ⟨le_rfl,hab⟩ (n-1) n (by omega); linarith [ha.1])
    (fun t ht => sub_ne_zero.mpr (hn n t ht))
  have hhi := positive_on_Icc_of_ne_zero (fun t => m (n+1) t-y t) ((hm (n+1)).sub hy)
    (by
      dsimp [m]
      simp only [add_sub_cancel_right]
      have hs := hsep a ⟨le_rfl,hab⟩ n (n+1) (by omega)
      linarith [ha.2])
    (fun t ht => sub_ne_zero.mpr (Ne.symm (hn (n+1) t ht)))
  intro t ht
  apply mem_interval_of_between_separating_midpoints (L t) (R t) (hLR t ht) (hsep t ht) (y t) (hmem t ht) n
  · exact sub_pos.mp (hlo t ht)
  · simpa only [m,add_sub_cancel_right] using sub_pos.mp (hhi t ht)

end NLS.ComplexAnalysis
