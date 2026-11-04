import NLS.SequenceSpaces.PositiveOperatorDiagonal
import NLS.SequenceSpaces.CompactRowMajorant

/-! Compactness of a positive-index l2 operator from one l2 row
majorant and a uniformly bounded family of l2 matrix kernels. -/
noncomputable section
open Set Complex Filter Topology
open scoped ENNReal Classical
namespace NLS.LpSequence

theorem isCompactOperator_positive_of_rowMajorant
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2) (b : lp (fun _ : ℕ+ => ℂ) 2)
    (hrow : ∀ m a, ‖T a m‖ ≤ ‖b m‖*‖a‖) : IsCompactOperator T := by
  let S := positiveInsertIsometry.toContinuousLinearMap.comp T
  have hcompact : IsCompactOperator S := by
    apply Coeff.isCompactOperator_of_rowMajorant (by norm_num) S (positiveInsert b)
    intro k a
    by_cases hk : 0 < k
    · let m : ℕ+ := ⟨k.toNat,by omega⟩
      have he : ((m:ℕ):ℤ) = k := Int.toNat_of_nonneg hk.le
      change ‖positiveInsert (T a) k‖ ≤ ‖positiveInsert b k‖*‖a‖
      rw [← he,positiveInsert_apply,positiveInsert_apply]
      exact hrow m a
    · change ‖positiveInsert (T a) k‖ ≤ ‖positiveInsert b k‖*‖a‖
      simp only [positiveInsert_apply_nonpos _ k (by omega),norm_zero,zero_mul,le_refl]
  have he : T = positiveRestrictionCLM.comp S := by
    ext a m
    exact (positiveInsert_apply (T a) m).symm
  rw [he]
  exact hcompact.clm_comp positiveRestrictionCLM

theorem positive_operator_row_bound_of_kernel_entries
    (T : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2)
    (b : lp (fun _ : ℕ+ => ℂ) 2) (κ : ℕ+ → lp (fun _ : ℕ+ => ℂ) 2)
    (L : ℝ) (hκ : ∀ m, ‖κ m‖ ≤ L)
    (hentry : ∀ m r, ‖T (lp.single 2 r 1) m‖ ≤ ‖b m‖*‖κ m r‖)
    (m : ℕ+) (a : lp (fun _ : ℕ+ => ℂ) 2) :
    ‖T a m‖ ≤ ‖b m‖*L*‖a‖ := by
  let ev := (lp.evalCLM ℂ (fun _ : ℕ+ => ℂ) 2 m).comp T
  have ht := (ev.continuous.tendsto a).comp (lp.hasSum_single (by norm_num : (2:ℝ≥0∞) ≠ ⊤) a)
  have hfinite (s : Finset ℕ+) :
      ‖ev (∑ r ∈ s, lp.single 2 r (a r))‖ ≤ ‖b m‖*L*‖a‖ := by
    have hs (r : ℕ+) : (lp.single 2 r (a r) : lp (fun _ : ℕ+ => ℂ) 2) =
        a r • (lp.single 2 r 1 : lp (fun _ : ℕ+ => ℂ) 2) := by
      ext k
      by_cases hkr : k = r <;> simp [lp.single_apply,hkr]
    have he : ev (∑ r ∈ s, lp.single 2 r (a r)) = ∑ r ∈ s, a r*T (lp.single 2 r 1) m := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [hs,map_smul]
      rfl
    rw [he]
    have hh := lp.tsum_mul_le_mul_norm
      (show (2:ℝ≥0∞).toReal.HolderConjugate (2:ℝ≥0∞).toReal from Real.HolderConjugate.two_two) a (κ m)
    calc
      _ ≤ ∑ r ∈ s, ‖a r‖*‖T (lp.single 2 r 1) m‖ := (norm_sum_le _ _).trans_eq (by simp only [norm_mul])
      _ ≤ ∑ r ∈ s, ‖a r‖*(‖b m‖*‖κ m r‖) :=
        Finset.sum_le_sum (fun r _ => mul_le_mul_of_nonneg_left (hentry m r) (norm_nonneg _))
      _ = ‖b m‖*(∑ r ∈ s, ‖a r‖*‖κ m r‖) := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
      _ ≤ ‖b m‖*(∑' r, ‖a r‖*‖κ m r‖) :=
        mul_le_mul_of_nonneg_left (hh.1.sum_le_tsum _ (fun _ _ => by positivity)) (norm_nonneg _)
      _ ≤ ‖b m‖*(‖a‖*‖κ m‖) := mul_le_mul_of_nonneg_left hh.2 (norm_nonneg _)
      _ ≤ ‖b m‖*(‖a‖*L) := by gcongr; exact hκ m
      _ = _ := by ring
  exact le_of_tendsto ht.norm (Eventually.of_forall hfinite)

theorem isCompactOperator_positive_of_kernel_entries
    (T : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2)
    (b : lp (fun _ : ℕ+ => ℂ) 2) (κ : ℕ+ → lp (fun _ : ℕ+ => ℂ) 2)
    (L : ℝ) (hL : 0 ≤ L) (hκ : ∀ m, ‖κ m‖ ≤ L)
    (hentry : ∀ m r, ‖T (lp.single 2 r 1) m‖ ≤ ‖b m‖*‖κ m r‖) :
    IsCompactOperator T := by
  apply isCompactOperator_positive_of_rowMajorant T ((L:ℂ) • b)
  intro m a
  have he : ‖((L:ℂ) • b) m‖ = L*‖b m‖ := by
    simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg hL]
  rw [he,mul_comm L]
  exact positive_operator_row_bound_of_kernel_entries T b κ L hκ hentry m a

end NLS.LpSequence
