import NLS.SequenceSpaces.PositiveKernelCompactness
import NLS.SequenceSpaces.KernelFamilyCompact

/-! Operator-norm compactness of positive-index operator families is
transported through the literal isometric insertion into signed l2. -/
noncomputable section
open Set Complex
open scoped ENNReal Classical
namespace NLS.LpSequence

def positiveSandwichOperatorCLM :
    (Coeff 2 →L[ℂ] Coeff 2) →L[ℂ]
      (lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2) :=
  LinearMap.mkContinuous
    { toFun := fun S => positiveRestrictionCLM.comp (S.comp positiveInsertIsometry.toContinuousLinearMap)
      map_add' := by intros; ext a m; rfl
      map_smul' := by intros; ext a m; rfl }
    1 (by
      intro S
      rw [one_mul]
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro a
      change ‖positiveRestriction (S (positiveInsert a))‖ ≤ ‖S‖*‖a‖
      exact (norm_positiveRestriction_le _).trans (by simpa only [norm_positiveInsert] using S.le_opNorm (positiveInsert a)))

theorem positiveSandwich_lift_operator
    (T : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2) :
    positiveSandwichOperatorCLM (positiveLiftOperator T) = T := by
  ext a m
  change positiveInsert (T (positiveRestriction (positiveInsert a))) ((m:ℕ):ℤ) = T a m
  rw [positiveInsert_apply]
  have he : positiveRestriction (positiveInsert a) = a := by ext k; exact positiveInsert_apply a k
  rw [he]

theorem positiveLiftOperator_entry (T : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2)
    (m k : ℕ+) :
    positiveLiftOperator T (lp.single 2 ((k:ℕ):ℤ) 1) ((m:ℕ):ℤ) = T (lp.single 2 k 1) m := by
  change positiveInsert (T (positiveRestriction (lp.single 2 ((k:ℕ):ℤ) 1))) ((m:ℕ):ℤ) = _
  rw [positiveRestriction_single,positiveInsert_apply]

theorem positiveLiftOperator_entry_nonpos_output
    (T : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2) (m k : ℤ) (hm : m ≤ 0) :
    positiveLiftOperator T (lp.single 2 k 1) m = 0 := positiveInsert_apply_nonpos _ m hm

theorem positiveLiftOperator_entry_nonpos_input
    (T : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2) (m k : ℤ) (hk : k ≤ 0) :
    positiveLiftOperator T (lp.single 2 k 1) m = 0 := by
  have he : positiveRestriction (lp.single 2 k 1) = 0 := by
    ext r
    have hr : ((r:ℕ):ℤ) ≠ k := by have := r.pos; omega
    change (lp.single 2 k 1 : Coeff 2) ((r:ℕ):ℤ) = 0
    simp only [lp.single_apply,Pi.single_apply,if_neg hr]
  change positiveInsert (T (positiveRestriction (lp.single 2 k 1))) m = 0
  rw [he,map_zero]
  exact congrArg (fun a : Coeff 2 => a m) positiveInsertIsometry.map_zero

theorem totallyBounded_positive_operators_of_l2_kernel_entries
    {ι : Type*} (T : ι → lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2)
    (b : lp (fun _ : ℕ+ => ℂ) 2) (κ : ℕ+ → lp (fun _ : ℕ+ => ℂ) 2)
    (L : ℝ) (hL : 0 ≤ L) (hκ : ∀ m, ‖κ m‖ ≤ L)
    (he : ∀ i m k, ‖T i (lp.single 2 k 1) m‖ ≤ ‖b m‖*‖κ m k‖) :
    TotallyBounded (range T) := by
  let g (m : ℤ) : Coeff 2 := if hm : 0 < m then
    positiveInsert (κ ⟨m.toNat,by omega⟩) else 0
  have hg (m : ℤ) : ‖g m‖ ≤ L := by
    dsimp only [g]
    split_ifs
    · rw [norm_positiveInsert]; exact hκ _
    · simpa only [norm_zero] using hL
  have hentry (i : ι) (m k : ℤ) :
      ‖positiveLiftOperator (T i) (lp.single 2 k 1) m‖ ≤ ‖positiveInsert b m‖*‖g m k‖ := by
    by_cases hm : 0 < m
    · let r : ℕ+ := ⟨m.toNat,by omega⟩
      have hr : ((r:ℕ):ℤ) = m := Int.toNat_of_nonneg hm.le
      by_cases hk : 0 < k
      · let s : ℕ+ := ⟨k.toNat,by omega⟩
        have hs : ((s:ℕ):ℤ) = k := Int.toNat_of_nonneg hk.le
        have hgm : g m = positiveInsert (κ r) := dif_pos hm
        rw [hgm,← hr,← hs,positiveLiftOperator_entry,positiveInsert_apply,positiveInsert_apply]
        exact he i r s
      · rw [positiveLiftOperator_entry_nonpos_input _ _ _ (by omega),norm_zero]
        positivity
    · rw [positiveLiftOperator_entry_nonpos_output _ _ _ (by omega),norm_zero]
      positivity
  have hB : TotallyBounded (range (fun i => positiveLiftOperator (T i))) := by
    apply Coeff.totallyBounded_operators_of_l2_kernel_entries _ (positiveInsert b) g L hL hg
    rintro S ⟨i,rfl⟩ m k
    exact hentry i m k
  have hi := hB.image positiveSandwichOperatorCLM.uniformContinuous
  have heq : positiveSandwichOperatorCLM '' range (fun i => positiveLiftOperator (T i)) = range T := by
    ext S
    constructor
    · rintro ⟨_,⟨i,rfl⟩,rfl⟩
      exact ⟨i,(positiveSandwich_lift_operator (T i)).symm⟩
    · rintro ⟨i,rfl⟩
      exact ⟨positiveLiftOperator (T i),⟨i,rfl⟩,positiveSandwich_lift_operator (T i)⟩
  rw [heq] at hi
  exact hi

end NLS.LpSequence
