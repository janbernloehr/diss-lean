import NLS.SequenceSpaces.PositiveSquaredLatticeMap

/-! Isometric zero extension of the original positive-index l2 space
to signed coefficients. Positive labels retain their literal indices. -/
noncomputable section
open Set
open scoped ENNReal Classical
namespace NLS.LpSequence

def positiveEmbedding : ℕ+ ↪ ℤ :=
  ⟨fun m => ((m:ℕ):ℤ),fun _ _ h => Subtype.ext (Int.ofNat.inj h)⟩

def positiveInsert (a : lp (fun _ : ℕ+ => ℂ) 2) : Coeff 2 :=
  ⟨Function.extend positiveEmbedding (fun m : ℕ+ => a m) (0:ℤ → ℂ),by
    change Memℓp (Function.extend positiveEmbedding (fun m : ℕ+ => a m) (0:ℤ → ℂ)) 2
    rw [memℓp_gen_iff (by norm_num : 0 < (2:ℝ≥0∞).toReal)]
    apply (positiveEmbedding.injective.summable_iff (fun k hk => ?_)).mp
    · simpa only [Function.comp_def,positiveEmbedding.injective.extend_apply] using
        (lp.memℓp a).summable (by norm_num)
    · simp [Function.extend_apply' _ _ k hk]⟩

theorem positiveInsert_apply (a : lp (fun _ : ℕ+ => ℂ) 2) (m : ℕ+) :
    positiveInsert a ((m:ℕ):ℤ) = a m := positiveEmbedding.injective.extend_apply a 0 m

theorem positiveInsert_apply_nonpos (a : lp (fun _ : ℕ+ => ℂ) 2) (k : ℤ) (hk : k ≤ 0) :
    positiveInsert a k = 0 := by
  have hn : k ∉ range positiveEmbedding := by
    rintro ⟨m,hm⟩
    have hp : 0 < ((m:ℕ):ℤ) := by exact_mod_cast m.pos
    change ((m:ℕ):ℤ) = k at hm
    omega
  exact Function.extend_apply' (f := positiveEmbedding) a (0:ℤ → ℂ) k hn

theorem norm_positiveInsert (a : lp (fun _ : ℕ+ => ℂ) 2) : ‖positiveInsert a‖ = ‖a‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2:ℝ≥0∞).toReal),
    lp.norm_eq_tsum_rpow (by norm_num : 0 < (2:ℝ≥0∞).toReal)]
  congr 1
  have he := positiveEmbedding.injective.tsum_eq (f := fun k => ‖positiveInsert a k‖^(2:ℝ≥0∞).toReal) (by
    intro k hk
    by_contra hn
    have hz : positiveInsert a k = 0 := Function.extend_apply' (f := positiveEmbedding) a (0:ℤ → ℂ) k hn
    simp [hz] at hk)
  change (∑' m : ℕ+, ‖positiveInsert a ((m:ℕ):ℤ)‖^(2:ℝ≥0∞).toReal) = _ at he
  simpa only [positiveInsert_apply] using! he.symm

def positiveInsertIsometry : lp (fun _ : ℕ+ => ℂ) 2 →ₗᵢ[ℂ] Coeff 2 where
  toFun := positiveInsert
  map_add' a b := by
    ext k
    change positiveInsert (a+b) k = positiveInsert a k+positiveInsert b k
    by_cases hk : 0 < k
    · let m : ℕ+ := ⟨k.toNat,by omega⟩
      have he : ((m:ℕ):ℤ) = k := Int.toNat_of_nonneg hk.le
      rw [← he,positiveInsert_apply,positiveInsert_apply,positiveInsert_apply]
      rfl
    · simp only [positiveInsert_apply_nonpos _ k (by omega),add_zero]
  map_smul' c a := by
    ext k
    change positiveInsert (c • a) k = c*positiveInsert a k
    by_cases hk : 0 < k
    · let m : ℕ+ := ⟨k.toNat,by omega⟩
      have he : ((m:ℕ):ℤ) = k := Int.toNat_of_nonneg hk.le
      rw [← he,positiveInsert_apply,positiveInsert_apply]
      rfl
    · simp only [positiveInsert_apply_nonpos _ k (by omega),mul_zero]
  norm_map' := norm_positiveInsert

end NLS.LpSequence
