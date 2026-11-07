import NLS.SequenceSpaces.PositiveScalarExtension
import NLS.SequenceSpaces.PositiveSignedReciprocalSummability
import NLS.SequenceSpaces.UniformTwoKernelHolderTails

/-! Uniform convergence of positive-index series with two signed
reciprocal kernels. The low selected indices are unrestricted; one
bounded full-l2 source family controls all high selected indices. -/
noncomputable section
open Set Filter Topology NLS.LpSequence
open scoped ENNReal Classical
namespace NLS.Coeff

theorem norm_positive_signed_reciprocal_kernels (n m : ℕ+) (hmn : m ≠ n) :
    ‖shift ((n:ℕ):ℤ) (puncturedLattice 2 (by norm_num)) ((m:ℕ):ℤ)‖+
      ‖shift (-((n:ℕ):ℤ)) (puncturedLattice 2 (by norm_num)) ((m:ℕ):ℤ)‖ =
      1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ) := by
  have hpos : ((m:ℕ):ℤ) ≠ ((n:ℕ):ℤ) := by exact_mod_cast hmn
  have hneg : ((m:ℕ):ℤ) ≠ -((n:ℕ):ℤ) := by have := n.pos; have := m.pos; omega
  rw [norm_shift_puncturedLattice_apply (by norm_num : 1 < (2:ℝ≥0∞)),
    norm_shift_puncturedLattice_apply (by norm_num : 1 < (2:ℝ≥0∞)),if_neg hpos,if_neg hneg]
  push_cast
  rw [sub_neg_eq_add,abs_sub_comm,abs_of_nonneg (by positivity : 0 ≤ ((m:ℕ):ℝ)+(n:ℕ)),add_comm ((m:ℕ):ℝ)]
  simp only [one_div]

theorem tendstoUniformlyOn_positive_series_of_signed_reciprocal_tail {X : Type*}
    (a d : X → Coeff 2) (n : ℕ+) (u : X → ℕ+ → ℂ) (S : Set X)
    (K : ℕ) (C R : ℝ) (hC : 0 ≤ C)
    (hdiag : ∀ x ∈ S, u x n = 0)
    (had : ∀ x ∈ S, ‖a x‖+‖d x‖ ≤ R)
    (hu : ∀ x ∈ S, ∀ m : ℕ+, K < (m:ℕ) → m ≠ n → ‖u x m‖ ≤
      C*(‖a x ((m:ℕ):ℤ)‖+‖d x ((m:ℕ):ℤ)‖)*
        (1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ))) :
    TendstoUniformlyOn
      (fun (N : ℕ) x => ∑ k ∈ Finset.Icc (-(N:ℤ)) N, positiveScalarExtension (u x) k)
      (fun x => ∑' m : ℕ+, u x m) atTop S := by
  let κ := puncturedLattice 2 (by norm_num : 1 < (2:ℝ≥0∞))
  let b := shift ((n:ℕ):ℤ) κ
  let e := shift (-((n:ℕ):ℤ)) κ
  have hbound (x : X) (hx : x ∈ S) (k : ℤ) (hk : K < k.natAbs) :
      ‖positiveScalarExtension (u x) k‖ ≤ C*(‖a x k‖+‖d x k‖)*(‖b k‖+‖e k‖) := by
    by_cases hkr : k ∈ range positiveEmbedding
    · obtain ⟨m,rfl⟩ := hkr
      change K < (((m:ℕ):ℤ)).natAbs at hk
      change ‖positiveScalarExtension (u x) ((m:ℕ):ℤ)‖ ≤ _
      rw [positiveScalarExtension_apply]
      by_cases hmn : m = n
      · subst m
        rw [hdiag x hx,norm_zero]
        positivity
      · change ‖u x m‖ ≤ C*(‖a x ((m:ℕ):ℤ)‖+‖d x ((m:ℕ):ℤ)‖)*(‖b ((m:ℕ):ℤ)‖+‖e ((m:ℕ):ℤ)‖)
        rw [norm_positive_signed_reciprocal_kernels n m hmn]
        exact hu x hx m (by simpa only [Int.natAbs_natCast] using hk) hmn
    · rw [positiveScalarExtension_zero_of_not_mem_range (u x) k hkr,norm_zero]
      positivity
  have hcauchy := uniformCauchySeqOn_two_kernel_holder_tail_sums a d b e
    (fun x => positiveScalarExtension (u x)) S K C R hC had hbound
  apply hcauchy.tendstoUniformlyOn_of_tendsto
  intro x hx
  have hs := summable_norm_positive_of_signed_reciprocal_tail (a x) (d x) n (u x)
    (hdiag x hx) K C hC (hu x hx)
  have ht := ((summable_norm_positiveScalarExtension (u x) hs).of_norm.hasSum).comp Finset.tendsto_Icc_neg
  simpa only [Function.comp_def,tsum_positiveScalarExtension] using ht

end NLS.Coeff
