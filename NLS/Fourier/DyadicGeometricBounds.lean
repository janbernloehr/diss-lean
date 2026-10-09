import NLS.Fourier.OddTentProfile
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.Field.GeomSum

/-! # Uniform bounds for sums of two-scale Fourier envelopes

Splitting at the dyadic frequency scale combines quadratic high-frequency
decay with linear low-frequency cancellation. The resulting bound is
independent of the number of scales.
-/
noncomputable section
open Finset
namespace NLS.Fourier

/-- A finite geometric prefix is bounded by twice its final term. -/
theorem sum_four_pow_range_le (k : ℕ) : ∑ j ∈ range (k+1), (4 : ℝ)^j ≤ 2*4^k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [show k+1+1 = (k+1)+1 by omega, sum_range_succ, pow_succ]
    have hp : 0 ≤ (4 : ℝ)^k := by positivity
    nlinarith

/-- The same geometric bound applies to any subset of the prefix. -/
theorem sum_four_pow_le (S : Finset ℕ) (k : ℕ) (hk : ∀ j ∈ S, j ≤ k) :
    ∑ j ∈ S, (4 : ℝ)^j ≤ 2*4^k := by
  apply le_trans _ (sum_four_pow_range_le k)
  apply sum_le_sum_of_subset_of_nonneg
  · intro j hj
    exact mem_range.mpr (Nat.lt_succ_of_le (hk j hj))
  · intro j _ _
    positivity

/-- Every finite subset of the inverse-dyadic tail has the same tail bound. -/
theorem sum_half_pow_tail_le (S : Finset ℕ) (k : ℕ) (hk : ∀ j ∈ S, k < j) :
    ∑ j ∈ S, (1/2 : ℝ)^j ≤ (1/2)^k := by
  have hsub : S ⊆ Ico (k+1) (S.sup id+1) := by
    intro j hj
    exact mem_Ico.mpr ⟨hk j hj, Nat.lt_succ_of_le (le_sup (f := id) hj)⟩
  have h₁ : ∑ j ∈ S, (1/2 : ℝ)^j ≤ ∑ j ∈ Ico (k+1) (S.sup id+1), (1/2 : ℝ)^j :=
    sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
  have h₂ := geom_sum_Ico_le_of_lt_one (m := k+1) (n := S.sup id+1)
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1)
  apply h₁.trans
  convert h₂ using 1
  rw [pow_succ]
  ring

/-- An integer frequency admits a dyadic bracket with all casts kept explicit. -/
theorem exists_dyadic_frequency_bracket (n : ℤ) (hn : n ≠ 0) :
    ∃ k : ℕ, (2 : ℝ)^k ≤ |(n : ℝ)| ∧ |(n : ℝ)| ≤ 2*2^k := by
  refine ⟨Nat.log 2 n.natAbs,?_,?_⟩
  · have h := Nat.pow_log_le_self 2 (Int.natAbs_ne_zero.mpr hn)
    have hr : (2 : ℝ)^(Nat.log 2 n.natAbs) ≤ (n.natAbs : ℝ) := by exact_mod_cast h
    simpa only [Nat.cast_natAbs,Int.cast_abs] using hr
  · have h := (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n.natAbs).le
    rw [pow_succ] at h
    have hr : (n.natAbs : ℝ) ≤ (2 : ℝ)^(Nat.log 2 n.natAbs)*2 := by exact_mod_cast h
    simpa only [Nat.cast_natAbs,Int.cast_abs,mul_comm] using hr

/-- The two envelopes give a uniform bound, regardless of the chosen finite scales. -/
theorem sum_norm_le_of_dyadic_envelopes (S : Finset ℕ) (a : ℕ → ℂ)
    (n : ℤ) (hn : n ≠ 0)
    (hlow : ∀ j ∈ S, ‖a j‖ ≤ 32*|(n : ℝ)| *(1/2 : ℝ)^j)
    (hhigh : ∀ j ∈ S, |(n : ℝ)|^2 * ‖a j‖ ≤ 8*(4 : ℝ)^j) :
    ∑ j ∈ S, ‖a j‖ ≤ 80 := by
  classical
  obtain ⟨k,hk₁,hk₂⟩ := exists_dyadic_frequency_bracket n hn
  let A := S.filter (fun j => j ≤ k)
  let B := S.filter (fun j => ¬ j ≤ k)
  have hA : |(n : ℝ)|^2 * (∑ j ∈ A, ‖a j‖) ≤ 16*4^k := by
    rw [mul_sum]
    calc
      _ ≤ ∑ j ∈ A, 8*(4 : ℝ)^j := sum_le_sum (fun j hj => hhigh j (mem_filter.mp hj).1)
      _ = 8*∑ j ∈ A, (4 : ℝ)^j := (mul_sum _ _ _).symm
      _ ≤ _ := by
        have h := sum_four_pow_le A k (fun j hj => (mem_filter.mp hj).2)
        linarith
  have hA' : ∑ j ∈ A, ‖a j‖ ≤ 16 := by
    have hnpos : 0 < |(n : ℝ)| := abs_pos.mpr (by exact_mod_cast hn)
    have hpow : (4 : ℝ)^k = ((2 : ℝ)^k)^2 := by rw [← pow_mul, mul_comm k 2, pow_mul]; norm_num
    rw [hpow] at hA
    have hs := sq_le_sq₀ (by positivity : (0 : ℝ) ≤ 2^k) (abs_nonneg (n : ℝ)) |>.mpr hk₁
    apply le_of_mul_le_mul_left (a := |(n : ℝ)|^2) _ (sq_pos_of_pos hnpos)
    nlinarith
  have hB : (∑ j ∈ B, ‖a j‖) ≤ 64 := by
    calc
      _ ≤ ∑ j ∈ B, 32*|(n : ℝ)| *(1/2 : ℝ)^j :=
        sum_le_sum (fun j hj => hlow j (mem_filter.mp hj).1)
      _ = (32*|(n : ℝ)|)*(∑ j ∈ B, (1/2 : ℝ)^j) := (mul_sum _ _ _).symm
      _ ≤ (32*|(n : ℝ)|)*(1/2 : ℝ)^k :=
        mul_le_mul_of_nonneg_left (sum_half_pow_tail_le B k
          (fun j hj => Nat.lt_of_not_ge (mem_filter.mp hj).2)) (by positivity)
      _ ≤ (32*(2*2^k))*(1/2 : ℝ)^k :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk₂ (by norm_num)) (by positivity)
      _ = 64 := by rw [div_pow]; field_simp; ring
  have hsplit := sum_filter_add_sum_filter_not S (fun j => j ≤ k) (fun j => ‖a j‖)
  change (∑ j ∈ A, ‖a j‖)+(∑ j ∈ B, ‖a j‖) = ∑ j ∈ S, ‖a j‖ at hsplit
  linarith

end NLS.Fourier
