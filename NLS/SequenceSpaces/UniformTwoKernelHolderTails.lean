import NLS.SequenceSpaces.EventualAbsoluteTails

/-! Uniform scalar series tails from two full-l2 source weights and
two fixed full-l2 kernels. Finite low terms are unrestricted. -/
noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.Coeff

theorem uniformCauchySeqOn_two_kernel_holder_tail_sums {X : Type*}
    (a d : X → Coeff 2) (b e : Coeff 2) (u : X → ℤ → ℂ)
    (S : Set X) (K : ℕ) (C R : ℝ) (hC : 0 ≤ C)
    (had : ∀ x ∈ S, ‖a x‖+‖d x‖ ≤ R)
    (hu : ∀ x ∈ S, ∀ k : ℤ, K < k.natAbs →
      ‖u x k‖ ≤ C*(‖a x k‖+‖d x k‖)*(‖b k‖+‖e k‖)) :
    UniformCauchySeqOn (fun (N : ℕ) x => ∑ k ∈ Finset.Icc (-(N:ℤ)) N, u x k) atTop S := by
  apply uniformCauchySeqOn_sum_of_eventual_absolute_tails u S
    (fun N => C*R*(‖fourierTail N b‖+‖fourierTail N e‖))
    (by simpa using tendsto_const_nhds.mul (((tendsto_fourierTail (by norm_num) b).norm).add
      ((tendsto_fourierTail (by norm_num) e).norm))) (K+1)
  intro N hKN x hx s hs
  have hsum : (∑ k ∈ s, ‖u x k‖) ≤ C*
      (((∑ k ∈ s, ‖a x k*b k‖)+(∑ k ∈ s, ‖a x k*e k‖))+
       ((∑ k ∈ s, ‖d x k*b k‖)+(∑ k ∈ s, ‖d x k*e k‖))) := by
    rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib,← Finset.sum_add_distrib,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have h := hu x hx k (by have := hs k hk; omega)
    apply h.trans_eq
    simp only [norm_mul]
    ring
  apply hsum.trans
  calc
    _ ≤ C*((‖a x‖*‖fourierTail N b‖+‖a x‖*‖fourierTail N e‖)+
        (‖d x‖*‖fourierTail N b‖+‖d x‖*‖fourierTail N e‖)) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (add_le_add (sum_norm_holderProduct_tail_le (a x) b N s hs) (sum_norm_holderProduct_tail_le (a x) e N s hs))
        (add_le_add (sum_norm_holderProduct_tail_le (d x) b N s hs) (sum_norm_holderProduct_tail_le (d x) e N s hs))) hC
    _ = C*(‖a x‖+‖d x‖)*(‖fourierTail N b‖+‖fourierTail N e‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (had x hx) hC) (by positivity)

end NLS.Coeff
