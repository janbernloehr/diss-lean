import NLS.ZakharovShabat.TriangularOddFourier

/-! # Lower bounds on dyadic triangular Fourier bands -/
noncomputable section
open scoped BigOperators
namespace NLS.ZakharovShabat

/-- Beyond its height, the boundary kernel has a harmonic lower bound. -/
theorem triangularBoundaryKernel_lower {H n : ℝ} (hH : 0 < H) (hn : H ≤ n) :
    1/(6*n) ≤ triangularBoundaryKernel H n := by
  have hn0 : 0 < n := hH.trans_le hn
  have hsq : H^2 ≤ n^2 := by nlinarith
  have hpi : 1 + Real.pi^2 ≤ 6*Real.pi := by
    have h := mul_le_mul_of_nonneg_right Real.pi_lt_four.le Real.pi_pos.le
    nlinarith [Real.pi_gt_three]
  have hd : H^2+(Real.pi*n)^2 ≤ 6*Real.pi*n^2 := by
    have h := mul_le_mul_of_nonneg_right hpi (sq_nonneg n)
    nlinarith
  unfold triangularBoundaryKernel
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith

/-- Every dyadic block beyond the height contributes at least one twelfth. -/
theorem triangularBoundaryKernel_dyadic_block {H B : ℕ} (hH : 0 < H) (hB : H ≤ B) :
    (1 : ℝ)/12 ≤ ∑ n ∈ Finset.Ico B (2*B), triangularBoundaryKernel H n := by
  have hB0 : 0 < B := hH.trans_le hB
  have hBr : 0 < (B : ℝ) := by exact_mod_cast hB0
  have ht (n : ℕ) (hn : n ∈ Finset.Ico B (2*B)) :
      1/(12*(B : ℝ)) ≤ triangularBoundaryKernel H n := by
    obtain ⟨hnl,hnu⟩ := Finset.mem_Ico.mp hn
    have hnr : 0 < (n : ℝ) := by exact_mod_cast hB0.trans_le hnl
    have hnu' : (n : ℝ) ≤ 2*(B : ℝ) := by exact_mod_cast hnu.le
    calc
      _ ≤ 1/(6*(n : ℝ)) := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        nlinarith
      _ ≤ _ := triangularBoundaryKernel_lower (by exact_mod_cast hH)
        (by exact_mod_cast hB.trans hnl)
  calc
    _ = ∑ _n ∈ Finset.Ico B (2*B), 1/(12*(B : ℝ)) := by
      simp only [Finset.sum_const,Nat.card_Ico,nsmul_eq_mul]
      rw [show 2*B-B=B by omega]
      field_simp
    _ ≤ _ := Finset.sum_le_sum ht

/-- A band spanning P dyadic blocks has kernel mass at least P/12. -/
theorem triangularBoundaryKernel_dyadic_band (P : ℕ) {H : ℕ} (hH : 0 < H) :
    (P : ℝ)/12 ≤ ∑ n ∈ Finset.Ico H (2^P*H), triangularBoundaryKernel H n := by
  induction P with
  | zero => simp
  | succ P ih =>
    have hpow : 1 ≤ 2^P := Nat.one_le_pow P 2 (by norm_num)
    have hlow : H ≤ 2^P*H := by nlinarith
    have hhigh : 2^P*H ≤ 2*(2^P*H) := by omega
    have hb := triangularBoundaryKernel_dyadic_block hH hlow
    rw [pow_succ,show 2^P*2*H = 2*(2^P*H) by ring,
      ← Finset.sum_Ico_consecutive (fun n => triangularBoundaryKernel (H : ℝ) n) hlow hhigh]
    push_cast
    linarith

end NLS.ZakharovShabat
