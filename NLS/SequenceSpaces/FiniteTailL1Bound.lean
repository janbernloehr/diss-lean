import NLS.SequenceSpaces.FiniteTailDomination
import NLS.SequenceSpaces.FourierTail
import NLS.SequenceSpaces.Weighted

/-! A quantitative ell-one bound combines a uniform finite prefix
with one summable envelope on both signed tails. -/
noncomputable section
open scoped ENNReal
namespace NLS.Coeff

theorem norm_truncate_one_le_card_bound (S : Finset ℤ) (a : Coeff 1) (B : ℝ)
    (hb : ∀ k ∈ S, ‖a k‖ ≤ B) : ‖truncate S a‖ ≤ (S.card:ℝ)*B := by
  calc
    _ ≤ ∑ k ∈ S, ‖(lp.single 1 k (a k) : Coeff 1)‖ :=
      norm_sum_le S (fun k => (lp.single 1 k (a k) : Coeff 1))
    _ = ∑ k ∈ S, ‖a k‖ := by simp
    _ ≤ ∑ k ∈ S, B := Finset.sum_le_sum hb
    _ = _ := by simp

theorem exists_l1_of_uniform_prefix_and_tail (f : ℤ → ℂ) (g : Coeff 1)
    (N : ℕ) (B C : ℝ) (hC : 0 ≤ C)
    (hprefix : ∀ k : ℤ, k.natAbs < N → ‖f k‖ ≤ B)
    (htail : ∀ k : ℤ, N ≤ k.natAbs → ‖f k‖ ≤ C*‖g k‖) :
    ∃ a : Coeff 1, (∀ k, a k=f k) ∧
      ‖a‖ ≤ ((lowFrequencies N).card:ℝ)*B+C*‖g‖ := by
  have hm := NLS.memlp_of_natAbs_tail_norm_le f g (lp.memℓp g) N C hC htail
  let a : Coeff 1 := ⟨f,hm⟩
  have hhead : ‖truncate (lowFrequencies N) a‖ ≤ ((lowFrequencies N).card:ℝ)*B :=
    norm_truncate_one_le_card_bound _ a B (fun k hk => hprefix k ((mem_lowFrequencies N k).mp hk))
  have hrest : ‖a-truncate (lowFrequencies N) a‖ ≤ C*‖g‖ := by
    have hh : ‖a-truncate (lowFrequencies N) a‖ ≤ ‖(C:ℂ) • g‖ := by
      apply lp.norm_mono (by norm_num : (1:ℝ≥0∞) ≠ 0)
      intro k
      change ‖a k-truncate (lowFrequencies N) a k‖ ≤ ‖(C:ℂ)*g k‖
      simp only [truncate_apply, mem_lowFrequencies]
      by_cases hk : k.natAbs < N
      · rw [if_pos hk, sub_self, norm_zero]
        exact norm_nonneg _
      · rw [if_neg hk, sub_zero, norm_mul, Complex.norm_real, Real.norm_of_nonneg hC]
        exact htail k (by omega)
    simpa only [norm_smul, Complex.norm_real, Real.norm_of_nonneg hC] using hh
  refine ⟨a,fun _ => rfl,?_⟩
  have h := norm_le_norm_sub_add a (truncate (lowFrequencies N) a)
  linarith

end NLS.Coeff

namespace NLS.WeightedCoeff

theorem exists_weighted_l1_of_uniform_prefix_and_tail (w : Weight) (f : ℤ → ℂ) (g : Coeff 1)
    (N : ℕ) (B C : ℝ) (hC : 0 ≤ C)
    (hprefix : ∀ k : ℤ, k.natAbs < N → ‖(w k:ℂ)*f k‖ ≤ B)
    (htail : ∀ k : ℤ, N ≤ k.natAbs → ‖(w k:ℂ)*f k‖ ≤ C*‖g k‖) :
    ∃ a : WeightedCoeff w 1, (∀ k, a.val k=f k) ∧
      ‖a‖ ≤ ((Coeff.lowFrequencies N).card:ℝ)*B+C*‖g‖ := by
  obtain ⟨a,ha,hn⟩ := Coeff.exists_l1_of_uniform_prefix_and_tail (fun k => (w k:ℂ)*f k) g N B C hC hprefix htail
  refine ⟨(weightIsometry w 1).symm a,?_,?_⟩
  · intro k
    change a k/(w k:ℂ)=f k
    rw [ha k]
    exact mul_div_cancel_left₀ _ (w.complex_ne_zero k)
  · exact (weightIsometry w 1).symm.norm_map a |>.le.trans hn

end NLS.WeightedCoeff
