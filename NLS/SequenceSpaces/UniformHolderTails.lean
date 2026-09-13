import NLS.SequenceSpaces.HolderEmbedding
import NLS.SequenceSpaces.FourierTail
import NLS.ComplexAnalysis.UniformProductTails

/-!
# Uniform absolute tails on bounded Hölder families

Multiplication by a fixed sequence in a finite conjugate exponent has uniformly
small `ℓ1` tails on bounded `ℓp` sets. The family itself need not have uniform
coordinatewise tails. These estimates imply uniform convergence of products.
-/

noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple q 1]

/-- Finite absolute sums obey the scalar Hölder inequality. -/
theorem sum_norm_holderProduct_le (a : Coeff p) (b : Coeff q) (s : Finset ℤ) :
    (∑ n ∈ s, ‖a n*b n‖) ≤ ‖a‖*‖b‖ := by
  have h := lp.sum_rpow_le_norm_rpow (p := (1 : ℝ≥0∞)) (by norm_num)
    (holderProduct (q := 1) a b) s
  have hs : (∑ n ∈ s, ‖a n*b n‖) ≤ ‖holderProduct (q := 1) a b‖ := by simpa using h
  exact hs.trans (norm_holderProduct_le a b)

/-- Restricting the finite sum to high frequencies puts the tail on the fixed conjugate multiplier. -/
theorem sum_norm_holderProduct_tail_le (a : Coeff p) (b : Coeff q) (N : ℕ) (s : Finset ℤ)
    (hs : ∀ n ∈ s, N ≤ n.natAbs) :
    (∑ n ∈ s, ‖a n*b n‖) ≤ ‖a‖*‖fourierTail N b‖ := by
  have he : (∑ n ∈ s, ‖a n*b n‖) = ∑ n ∈ s, ‖a n*fourierTail N b n‖ := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [fourierTail_apply, if_pos (hs n hn)]
  rw [he]
  exact sum_norm_holderProduct_le a (fourierTail N b) s

/-- A fixed finite-exponent multiplier gives uniform absolute tail bounds on any norm-bounded family. -/
theorem uniform_absolute_holder_tails {X : Type*} (a : X → Coeff p) (b : Coeff q) (hq : q ≠ ⊤)
    (u : X → ℤ → ℂ) (S : Set X) (C R : ℝ) (hC : 0 ≤ C)
    (ha : ∀ x ∈ S, ‖a x‖ ≤ R) (hu : ∀ x ∈ S, ∀ n, ‖u x n‖ ≤ C*‖a x n*b n‖) :
    (∀ x ∈ S, ∀ s : Finset ℤ, (∑ n ∈ s, ‖u x n‖) ≤ C*R*‖b‖) ∧
      Tendsto (fun N => C*R*‖fourierTail N b‖) atTop (𝓝 0) ∧
      ∀ N : ℕ, ∀ x ∈ S, ∀ s : Finset ℤ,
        (∀ n ∈ s, N ≤ n.natAbs) → (∑ n ∈ s, ‖u x n‖) ≤ C*R*‖fourierTail N b‖ := by
  have hsum (x : X) (hx : x ∈ S) (s : Finset ℤ) :
      (∑ n ∈ s, ‖u x n‖) ≤ C*(∑ n ∈ s, ‖a x n*b n‖) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun n _ => hu x hx n)
  refine ⟨?_,?_,?_⟩
  · intro x hx s
    exact (hsum x hx s).trans (by
      calc
        _ ≤ C*(‖a x‖*‖b‖) := mul_le_mul_of_nonneg_left (sum_norm_holderProduct_le (a x) b s) hC
        _ ≤ C*(R*‖b‖) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (ha x hx) (norm_nonneg b)) hC
        _ = _ := by ring)
  · simpa using tendsto_const_nhds.mul ((tendsto_fourierTail hq b).norm)
  · intro N x hx s hs
    exact (hsum x hx s).trans (by
      calc
        _ ≤ C*(‖a x‖*‖fourierTail N b‖) := mul_le_mul_of_nonneg_left
          (sum_norm_holderProduct_tail_le (a x) b N s hs) hC
        _ ≤ C*(R*‖fourierTail N b‖) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (ha x hx) (norm_nonneg _)) hC
        _ = _ := by ring)

/-- Products of a bounded Hölder family and a fixed finite-exponent multiplier are uniformly Cauchy. -/
theorem uniformCauchySeqOn_holder_products {X : Type*} (a : X → Coeff p) (b : Coeff q) (hq : q ≠ ⊤)
    (u : X → ℤ → ℂ) (S : Set X) (C R : ℝ) (hC : 0 ≤ C)
    (ha : ∀ x ∈ S, ‖a x‖ ≤ R) (hu : ∀ x ∈ S, ∀ n, ‖u x n‖ ≤ C*‖a x n*b n‖) :
    UniformCauchySeqOn (fun (N : ℕ) x => ∏ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (1+u x n)) atTop S := by
  obtain ⟨hb,ht,hs⟩ := uniform_absolute_holder_tails a b hq u S C R hC ha hu
  exact NLS.ComplexAnalysis.uniformCauchySeqOn_prod_one_add u S _ _ ht hb hs

end NLS.Coeff
