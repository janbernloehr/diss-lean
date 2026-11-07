import NLS.SequenceSpaces.UniformPositiveReciprocalSeries
import NLS.SequenceSpaces.SandwichMajorant

/-! A single bound controls the complete absolute sum UNIFORMLY in
its positive deleted index. Both shifted reciprocal rows have the same
fixed full-l2 norm. The diagonal is explicitly zero. -/
noncomputable section
open Set NLS.LpSequence
open scoped ENNReal Classical
namespace NLS.Coeff

theorem summable_norm_positive_and_tsum_le_of_signed_reciprocal_bound
    (a d : Coeff 2) (n : ℕ+) (u : ℕ+ → ℂ) (hdiag : u n = 0)
    (C : ℝ) (hC : 0 ≤ C)
    (hu : ∀ m : ℕ+, m ≠ n → ‖u m‖ ≤ C*(‖a ((m:ℕ):ℤ)‖+‖d ((m:ℕ):ℤ)‖)*
      (1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ))) :
    Summable (fun m => ‖u m‖) ∧ (∑' m, ‖u m‖) ≤
      C*(‖a‖+‖d‖)*(2*‖puncturedLattice 2 (by norm_num)‖) := by
  let κ := puncturedLattice 2 (by norm_num : 1 < (2:ℝ≥0∞))
  let b := shift ((n:ℕ):ℤ) κ
  let e := shift (-((n:ℕ):ℤ)) κ
  let B := Coeff.magnitude b+Coeff.magnitude e
  have hBk (k : ℤ) : ‖B k‖ = ‖b k‖+‖e k‖ := by
    simp only [B,lp.coeFn_add,Pi.add_apply,Coeff.magnitude_apply,← Complex.ofReal_add,
      Complex.norm_real,Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  have hB : ‖B‖ ≤ 2*‖κ‖ := by
    apply (norm_add_le _ _).trans_eq
    simp only [Coeff.norm_magnitude,b,e,norm_shift]
    ring
  have hpoint (k : ℤ) : ‖positiveScalarExtension u k‖ ≤ C*(‖a k‖+‖d k‖)*‖B k‖ := by
    rw [hBk]
    by_cases hk : k ∈ range positiveEmbedding
    · obtain ⟨m,rfl⟩ := hk
      change ‖positiveScalarExtension u ((m:ℕ):ℤ)‖ ≤
        C*(‖a ((m:ℕ):ℤ)‖+‖d ((m:ℕ):ℤ)‖)*(‖b ((m:ℕ):ℤ)‖+‖e ((m:ℕ):ℤ)‖)
      rw [positiveScalarExtension_apply]
      by_cases hmn : m = n
      · subst m
        rw [hdiag,norm_zero]
        positivity
      · rw [norm_positive_signed_reciprocal_kernels n m hmn]
        exact hu m hmn
    · rw [positiveScalarExtension_zero_of_not_mem_range u k hk,norm_zero]
      positivity
  have hc : (2:ℝ≥0∞).toReal.HolderConjugate (2:ℝ≥0∞).toReal := Real.HolderConjugate.two_two
  obtain ⟨hsZ,hbound⟩ := summable_norm_of_two_holder_bounds hc a d B (positiveScalarExtension u) C hC hpoint
  have hs := hsZ.comp_injective positiveEmbedding.injective
  change Summable (fun m : ℕ+ => ‖positiveScalarExtension u ((m:ℕ):ℤ)‖) at hs
  simp only [positiveScalarExtension_apply] at hs
  have he := positiveEmbedding.injective.tsum_eq (f := fun k => ‖positiveScalarExtension u k‖) (by
    intro k hk
    by_contra hn
    exact hk (by
      change ‖positiveScalarExtension u k‖ = 0
      rw [positiveScalarExtension_zero_of_not_mem_range u k hn,norm_zero]))
  change (∑' m : ℕ+, ‖positiveScalarExtension u ((m:ℕ):ℤ)‖) = _ at he
  simp only [positiveScalarExtension_apply] at he
  refine ⟨hs,?_⟩
  rw [he]
  exact hbound.trans (mul_le_mul_of_nonneg_left hB (mul_nonneg hC (by positivity)))

theorem norm_positive_sum_le_of_signed_reciprocal_bound
    (a d : Coeff 2) (n : ℕ+) (u : ℕ+ → ℂ) (hdiag : u n = 0)
    (C : ℝ) (hC : 0 ≤ C)
    (hu : ∀ m : ℕ+, m ≠ n → ‖u m‖ ≤ C*(‖a ((m:ℕ):ℤ)‖+‖d ((m:ℕ):ℤ)‖)*
      (1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ))) :
    ‖∑' m : ℕ+, u m‖ ≤ C*(‖a‖+‖d‖)*(2*‖puncturedLattice 2 (by norm_num)‖) := by
  obtain ⟨hs,hb⟩ := summable_norm_positive_and_tsum_le_of_signed_reciprocal_bound a d n u hdiag C hC hu
  exact (norm_tsum_le_tsum_norm hs).trans hb

end NLS.Coeff
