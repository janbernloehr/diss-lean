import NLS.SequenceSpaces.PositiveOperatorFamilyCompact
import Mathlib.Analysis.Normed.Operator.Banach

/-! Uniformly vanishing diagonal tails and common summable off-diagonal
row kernels give operator-norm precompactness of a full positive-index
operator family. -/
noncomputable section
open Set Complex
open scoped ENNReal Classical
namespace NLS.LpSequence

theorem totallyBounded_positive_diagonal_family
    {ι : Type*} (T : ι → lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ i m, ‖T i (lp.single 2 m 1) m‖ ≤ M)
    (htail : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ i (m : ℕ+), N ≤ (m:ℕ) → ‖T i (lp.single 2 m 1) m‖ < ε) :
    TotallyBounded (range (fun i => positiveOperatorDiagonal (T i))) := by
  let u (i : ι) := Coeff.operatorDiagonalSymbol (positiveLiftOperator (T i))
  let D (i : ι) : Coeff 2 →L[ℂ] Coeff 2 := Coeff.multiplierCLM (u i)
  have hub (i : ι) (m : ℤ) : ‖u i m‖ ≤ M := by
    change ‖positiveLiftOperator (T i) (lp.single 2 m 1) m‖ ≤ M
    by_cases hm : 0 < m
    · let r : ℕ+ := ⟨m.toNat,by omega⟩
      have hr : ((r:ℕ):ℤ) = m := Int.toNat_of_nonneg hm.le
      rw [← hr,positiveLiftOperator_entry]
      exact hbound i r
    · rw [positiveLiftOperator_entry_nonpos_output _ _ _ (by omega),norm_zero]
      exact hM
  have hDb (i : ι) : ‖D i‖ ≤ M := by
    apply ContinuousLinearMap.opNorm_le_bound _ hM
    intro a
    exact (Coeff.norm_multiplier_le (u i) a).trans (mul_le_mul_of_nonneg_right
      (lp.norm_le_of_forall_le hM (hub i)) (norm_nonneg _))
  have hTB : TotallyBounded (range D) := by
    apply NLS.totallyBounded_of_bounded_compact_approximations _
      (isBounded_iff_forall_norm_le.mpr ⟨M,by rintro S ⟨i,rfl⟩; exact hDb i⟩)
    intro ε hε
    obtain ⟨N,hN⟩ := htail ε hε
    let s : Finset ℤ := Finset.Icc (-(N:ℤ)) (N:ℤ)
    refine ⟨Coeff.finiteBlockOperatorCLM s s,Coeff.isCompactOperator_finiteBlockOperatorCLM s s,?_⟩
    rintro S ⟨i,rfl⟩
    have heq : Coeff.finiteBlockOperatorCLM s s (D i) = (Coeff.truncateCLM s).comp (D i) := by
      rw [Coeff.finiteBlockOperatorCLM_apply]
      ext a m
      by_cases hm : m ∈ s <;> simp [D,Coeff.truncate_apply,hm]
    rw [heq,norm_sub_rev]
    apply Coeff.norm_multiplier_cutoff_error_le (u i) s hε.le
    intro m hm
    have hmN : N ≤ m.natAbs := by simp only [s,Finset.mem_Icc] at hm; omega
    by_cases hp : 0 < m
    · let r : ℕ+ := ⟨m.toNat,by omega⟩
      have hr : ((r:ℕ):ℤ) = m := Int.toNat_of_nonneg hp.le
      have hNr : N ≤ (r:ℕ) := by rw [← hr,Int.natAbs_natCast] at hmN; exact hmN
      change ‖positiveLiftOperator (T i) (lp.single 2 m 1) m‖ ≤ ε
      rw [← hr,positiveLiftOperator_entry]
      exact (hN i r hNr).le
    · change ‖positiveLiftOperator (T i) (lp.single 2 m 1) m‖ ≤ ε
      rw [positiveLiftOperator_entry_nonpos_output _ _ _ (by omega),norm_zero]
      exact hε.le
  have heq (i : ι) : positiveSandwichOperatorCLM (D i) = positiveOperatorDiagonal (T i) := by
    ext a m
    change u i ((m:ℕ):ℤ)*positiveInsert a ((m:ℕ):ℤ) = positiveOperatorDiagonal (T i) a m
    change positiveLiftOperator (T i) (lp.single 2 ((m:ℕ):ℤ) 1) ((m:ℕ):ℤ)*
      positiveInsert a ((m:ℕ):ℤ) = _
    rw [positiveLiftOperator_entry,positiveInsert_apply,positiveOperatorDiagonal_apply]
  have himage := hTB.image positiveSandwichOperatorCLM.uniformContinuous
  have hrange : positiveSandwichOperatorCLM '' range D = range (fun i => positiveOperatorDiagonal (T i)) := by
    ext S
    constructor
    · rintro ⟨_,⟨i,rfl⟩,rfl⟩; exact ⟨i,(heq i).symm⟩
    · rintro ⟨i,rfl⟩; exact ⟨D i,⟨i,rfl⟩,heq i⟩
  rwa [hrange] at himage

theorem totallyBounded_positive_operators_of_diagonal_tail_and_kernel_entries
    {ι : Type*} (T : ι → lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ i m, ‖T i (lp.single 2 m 1) m‖ ≤ M)
    (htail : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ i (m : ℕ+), N ≤ (m:ℕ) → ‖T i (lp.single 2 m 1) m‖ < ε)
    (b : lp (fun _ : ℕ+ => ℂ) 2) (κ : ℕ+ → lp (fun _ : ℕ+ => ℂ) 2)
    (L : ℝ) (hL : 0 ≤ L) (hκ : ∀ m, ‖κ m‖ ≤ L)
    (he : ∀ i m k, k ≠ m → ‖T i (lp.single 2 k 1) m‖ ≤ ‖b m‖*‖κ m k‖) :
    TotallyBounded (range T) := by
  let D (i : ι) := positiveOperatorDiagonal (T i)
  let K (i : ι) := positiveOperatorOffDiagonal (T i)
  have hD : TotallyBounded (range D) := totallyBounded_positive_diagonal_family T M hM hbound htail
  have hK : TotallyBounded (range K) := by
    apply totallyBounded_positive_operators_of_l2_kernel_entries K b κ L hL hκ
    intro i m k
    rw [positiveOperatorOffDiagonal_entry]
    by_cases hmk : m = k
    · rw [if_pos hmk,norm_zero]; positivity
    · rw [if_neg hmk]; exact he i m k (Ne.symm hmk)
  have hDc : IsCompact (closure (range D)) := hD.closure.isCompact_of_isClosed isClosed_closure
  have hKc : IsCompact (closure (range K)) := hK.closure.isCompact_of_isClosed isClosed_closure
  have hsum := (hDc.prod hKc).image (continuous_fst.add continuous_snd)
  apply hsum.totallyBounded.subset
  rintro S ⟨i,rfl⟩
  exact ⟨(D i,K i),⟨subset_closure ⟨i,rfl⟩,subset_closure ⟨i,rfl⟩⟩,
    (positiveOperator_eq_diagonal_add_offDiagonal (T i)).symm⟩

end NLS.LpSequence
